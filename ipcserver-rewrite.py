import struct
import sys
import re
import bisect
import hashlib
from functools import partial

from unicorn import *
from unicorn.arm64_const import *
from capstone import *

import nxo64
from demangling import get_demangled
from unicornhelpers import load_nxo_to_unicorn, create_unicorn_arm64

from hashes import all_hashes, all_hashes_300

'''
TODO: try to turn into mangled symbols:

; nn::sf::cmif::server::detail::CmifProcessFunctionTableGetterImplBase<nn::mmnv::IRequest>::ProcessServerMessage(nn::sf::IServiceObject *, nn::sf::cmif::server::CmifServerMessage *, nn::sf::detail::PointerAndSize const&)
_ZN2nn2sf4cmif6server6detail38CmifProcessFunctionTableGetterImplBaseINS_4mmnv8IRequestEE20ProcessServerMessageEPNS0_14IServiceObjectEPNS2_17CmifServerMessageERKNS0_6detail14PointerAndSizeE


; nn::sf::cmif::server::detail::CmifProcessFunctionTableGetterImpl<nn::mmnv::IRequest>::DispatchServerMessage(nn::sf::cmif::CmifOutHeader **, nn::mmnv::IRequest*, nn::sf::cmif::server::CmifServerMessage *, unsigned int, nn::sf::detail::PointerAndSize &&)
_ZN2nn2sf4cmif6server6detail34CmifProcessFunctionTableGetterImplINS_4mmnv8IRequestEE21DispatchServerMessageEPPNS1_13CmifOutHeaderEPS6_PNS2_17CmifServerMessageEjONS0_6detail14PointerAndSizeE


; nn::sf::cmif::server::detail::CmifProcessFunctionTableGetterImpl<nn::mmnv::IRequest>::Process_Initialize(nn::sf::cmif::CmifOutHeader **, nn::mmnv::IRequest*, nn::sf::cmif::server::CmifServerMessage *, nn::sf::detail::PointerAndSize &&)
_ZN2nn2sf4cmif6server6detail34CmifProcessFunctionTableGetterImplINS_4mmnv8IRequestEE18Process_InitializeEPPNS1_13CmifOutHeaderEPS6_PNS2_17CmifServerMessageEONS0_6detail14PointerAndSizeE
'''

DEFAULT_LOAD_BASE = 0x7100000000

def demangle(s):
	value = get_demangled(s)
	pre = 'nn::sf::cmif::server::detail::CmifProcessFunctionTableGetter<'
	post = ', void>::s_Table'
	if value.startswith(pre) and value.endswith(post):
		value = value[len(pre):-len(post)]
	return value


class MemoryChunk(object):
	def __init__(self, name, base, size):
		self.base = base
		self.size = size

	@property
	def end(self):
		return self.base + self.size

	def __repr__(self):
		return 'MemoryChunk(name=%r, base=0x%X, size=0x%X)' % (self.name, self.base, self.size)

class AllocatingChunk(MemoryChunk):
	def __init__(self, name, base, size):
		super(AllocatingChunk, self).__init__(name, base, size)
		self.reset()

	def reset(self):
		self._next_ptr = self.base
		self.bytes_allocated = 0

	def alloc(self, size):
		available = self.end - self._next_ptr
		assert available > 0
		allocation_size = (size + 0xF) & ~0xF
		if allocation_size > available:
			raise Exception('Could not allocate 0x%X bytes from AllocatingChunk %r' % size, self.name)
		result = self._next_ptr
		self._next_ptr += allocation_size
		self.bytes_allocated += size
		return result

	def __repr__(self):
		return 'MemoryChunk(name=%r, base=0x%X, size=0x%X)' % (self.name, self.base, self.size)

class Nx64Simulator(object):
	def __init__(self, nxo, stack_size=0x2000, host_heap_size=0x100000, runtime_heap_size=0x2000, loadbase=DEFAULT_LOAD_BASE, trace_instructions=False):
		self.uc = create_unicorn_arm64()
		self.cs = Cs(CS_ARCH_ARM64, CS_MODE_ARM)
		self.loadbase = loadbase
		load_nxo_to_unicorn(self.uc, nxo, loadbase)

		self._last_chunk_base = 0
		self._chunk_step = 0x100000000
		self._chunks = []

		self.stack = self.create_chunk('stack', stack_size)
		self.host_heap = self.create_chunk('host_heap', host_heap_size, AllocatingChunk)
		self.runtime_heap = self.create_chunk('runtime_heap', runtime_heap_size, AllocatingChunk)
		self.function_pointer_chunk = self.create_chunk('function_pointers', 0)
		self.next_function_pointer = self.function_pointer_chunk.base

		self._data_for_reset = []

		self.current_trace = None

		self._hook_functions = {}

		self.return_pointer = self.create_trace_function_pointer(self.on_return_hook_function)

		self.trace_instructions = trace_instructions

		self.trace_instruction_hooks = []

	def on_return_hook_function(self, uc):
		#print 'on_return_hook_function'
		return False

	def create_trace_function_pointer(self, func):
		function_pointer = self.next_function_pointer
		self.next_function_pointer += 8

		self._hook_functions[function_pointer] = func
		return function_pointer

	def create_chunk(self, name, size, cls=MemoryChunk):
		base = self._last_chunk_base + self._chunk_step
		chunk = cls(name, base, size)
		if size:
			self.uc.mem_map(base, size)
		self._last_chunk_base = base
		return chunk

	def load_host_data(self, data, reset=False):
		p = self.host_heap.alloc(len(data))
		self.uc.mem_write(p, data)
		if reset:
			self._data_for_reset.append((p, data))
		return p

	def dump_regs():
		values = []
		for i in range(28):
			values.append(('X%d' % i, self.uc.reg_read(UC_ARM64_REG_X0+i)))
		values.append(('X29', self.uc.reg_read(UC_ARM64_REG_X29)))
		values.append(('X30', self.uc.reg_read(UC_ARM64_REG_X30)))
		values.append(('SP',  self.uc.reg_read(UC_ARM64_REG_SP)))
		values.append(('PC',  self.uc.reg_read(UC_ARM64_REG_PC)))
		print ', '.join('%s=%X' % i for i in values)

	def qword(self, addr):
		return struct.unpack('<Q', self.uc.mem_read(addr, 8))[0]

	def dword(self, addr):
		return struct.unpack('<I', self.uc.mem_read(addr, 4))[0]

	def write_qword(self, addr, value):
		self.uc.mem_write(addr, struct.pack('<Q', value))

	def write_dword(self, addr, value):
		self.uc.mem_write(addr, struct.pack('<I', value))

	def reset_host_data(self):
		for addr, data in self._data_for_reset:
			self.uc.mem_write(addr, data)

	def get_instruction(self, addr):
		instructions = list(self.cs.disasm(str(self.uc.mem_read(addr, 4)), addr))
		if instructions:
			assert len(instructions) == 1
			return instructions[0]
		return None

	def add_trace_instruction_hook(self, cb):
		self.trace_instruction_hooks.append(cb)

	def trace_call(self, funcptr, args, trace_object=None):
		if trace_object is None:
			trace_object = {}

		self.reset_host_data()

		register_args, stack_args = args[:8],  args[8:]

		for i, v in enumerate(register_args):
			self.uc.reg_write(UC_ARM64_REG_X0 + i, v)

		for i in xrange(len(register_args), 9):
			self.uc.reg_write(UC_ARM64_REG_X0 + i, 0)

		sp = self.stack.end
		if stack_args:
			stack_space = len(stack_args) * 8
			stack_space = (stack_space + 0xF) & ~0xF
			sp -= stack_space
			for i, v in enumerate(v):
				self.write_qword(sp + i * 8, v)

		self.uc.reg_write(UC_ARM64_REG_SP, sp)
		self.uc.reg_write(UC_ARM64_REG_PC, funcptr)

		self.uc.reg_write(UC_ARM64_REG_X30, self.return_pointer)

		assert self.current_trace is None
		self.current_trace = trace_object

		try:
			while True:
				try:
					pc = self.uc.reg_read(UC_ARM64_REG_PC)
					if self.trace_instruction_hooks:
						instruction = self.get_instruction(pc)
						for cb in self.trace_instruction_hooks:
							cb(self.uc, instruction)

					
					if self.trace_instructions:
						instruction = self.get_instruction(pc)
						if instruction is not None:
							print '0x%08x:    %s  %s' % (instruction.address, instruction.mnemonic, instruction.op_str)
						else:
							print '0x%08x:    [INVALID]' % (instruction.address,)
					self.uc.emu_start(self.uc.reg_read(UC_ARM64_REG_PC), 0, count=1)
				except UcError as e:
					pc = self.uc.reg_read(UC_ARM64_REG_PC)
					if pc in self._hook_functions:
						#print 'hook function for %X' % (pc,)
						if self._hook_functions[pc](self.uc):
							continue
						else:
							break

					print 'UcError @ pc 0x%X' % (pc,)
					print '', e
					raise
		finally:
			self.trace_instruction_hooks = []
			self.current_trace = None

	def invoke_trace_method(self, method_name, *args, **kwargs):
		assert self.current_trace is not None
		try:
			method = getattr(self.current_trace, method_name)
		except AttributeError:
			raise NotImplementedError("Class %r does not implement %r" % (self.current_trace.__class__.__name__, method_name))
		return method(*args, **kwargs)



class IPCServerSimulator(Nx64Simulator):
	def __init__(self, nxo):
		super(IPCServerSimulator, self).__init__(nxo)
		self.ipc_magic = 0x49434653
		message_data = self._make_message_data(1600) + ('\x00' * 0x1000)
		self.message_ptr = self.load_host_data(message_data)

		message_struct_data = struct.pack('<QQ', self.message_ptr, len(message_data))
		self.message_struct_ptr = self.load_host_data(message_struct_data, reset=True)

		ipc_functions = [
			partial(self.invoke_trace_method, 'PrepareForProcess'),           # PrepareForProcess(nn::sf::cmif::CmifMessageMetaInfo const&)
			partial(self.invoke_trace_method, 'OverwriteClientProcessId'),    # OverwriteClientProcessId(ulong *)
			partial(self.invoke_trace_method, 'GetBuffers'),                  # GetBuffers(nn::sf::detail::PointerAndSize *)
			partial(self.invoke_trace_method, 'GetInNativeHandles'),          # GetInNativeHandles(nn::sf::NativeHandle *)
			partial(self.invoke_trace_method, 'GetInObjects'),                # GetInObjects(nn::sf::cmif::server::CmifServerObjectInfo *)
			partial(self.invoke_trace_method, 'BeginPreparingForReply'),      # BeginPreparingForReply(nn::sf::detail::PointerAndSize *)
			partial(self.invoke_trace_method, 'SetBuffers'),                  # SetBuffers(nn::sf::detail::PointerAndSize *)
			partial(self.invoke_trace_method, 'SetOutObjects'),               # SetOutObjects(nn::sf::cmif::server::CmifServerObjectInfo *)
			partial(self.invoke_trace_method, 'SetOutNativeHandles'),         # SetOutNativeHandles(nn::sf::NativeHandle *)
			partial(self.invoke_trace_method, 'BeginPreparingForErrorReply'), # BeginPreparingForErrorReply(nn::sf::detail::PointerAndSize *,ulong)
			partial(self.invoke_trace_method, 'EndPreparingForReply'),        # EndPreparingForReply(void)
		]

		ipc_function_pointers = [self.create_trace_function_pointer(i) for i in ipc_functions]

		ipc_vtable_ptr = self.load_host_data(struct.pack('<' + 'Q' * len(ipc_function_pointers), *ipc_function_pointers))
		self.ipc_object_ptr = self.load_host_data(struct.pack('<QQ', ipc_vtable_ptr, 0))


		target_functions = [partial(self.invoke_trace_method, 'target_function', i*8) for i in range(512)]
		target_function_pointers = [self.create_trace_function_pointer(i) for i in target_functions]

		target_vtable_ptr = self.load_host_data(struct.pack('<' + 'Q' * len(target_function_pointers), *target_function_pointers))
		self.target_object_ptr = self.load_host_data(struct.pack('<QQ', target_vtable_ptr, 0))

		ret_instruction_ptr = self.load_host_data(struct.pack('<I', 0xd65f03c0))
		in_object_vtable_ptr = self.load_host_data(struct.pack('<Q', ret_instruction_ptr) * 16)
		self.in_object_ptr = self.load_host_data(struct.pack('<Q', in_object_vtable_ptr) + '\0' * (8*16))

		self.buffer_memory = self.load_host_data('\x00' * 0x1000)
		self.output_memory = self.load_host_data('\x00' * 0x1000)


	def _make_message_data(self, cmd_id):
		ipc_magic = 0x49434653
		return struct.pack('<QQ', ipc_magic, cmd_id)


	def trace_cmd(self, dispatch_func, cmd_id):
		trace = self.try_trace_cmd(dispatch_func, cmd_id, struct.pack('<QQQQQQ', 0, 0, 0, 0, 0, 0))
		if trace.is_correct():
			return trace
		#print 'retry'
		trace = self.try_trace_cmd(dispatch_func, cmd_id, struct.pack('<QQQQQQ', 1, 1, 1, 1, 1, 1))
		if trace.is_correct():
			return trace
		for buffer_size in (128, 33):
			#print 'retry'
			trace = self.try_trace_cmd(dispatch_func, cmd_id, struct.pack('<QQQQ', 0, 0, 0, 0), buffer_size=buffer_size)
			if trace.is_correct():
				return trace
		print 'retry?'
		return trace # oh well

	def try_trace_cmd(self, dispatch_func, cmd_id, data, **kwargs):
		self.uc.mem_write(self.message_ptr, self._make_message_data(cmd_id) + data)
		trace = IPCServerTrace(self, dispatch_func, cmd_id, **kwargs)
		self.trace_call(dispatch_func, [self.target_object_ptr, self.ipc_object_ptr, self.message_struct_ptr], trace)
		return trace


class IPCServerTrace(object):
	def __init__(self, simulator, dispatch_func, cmd_id, buffer_size=0x1000):
		self.dispatch_func = dispatch_func
		self.cmd_id = cmd_id
		self._simulator = simulator
		self.description = None
		self.buffer_size = buffer_size

	def is_correct(self):
		if self.description is None:
			return True
		if 'vt' not in self.description:
			return False
		# TODO: detect missing out-interfaces / in-interfaces
		return True

	def ret(self, uc, value):
		uc.reg_write(UC_ARM64_REG_X0, value)
		uc.reg_write(UC_ARM64_REG_PC, uc.reg_read(UC_ARM64_REG_LR))

	def PrepareForProcess(self, uc):
		arg = uc.reg_read(UC_ARM64_REG_X1)
		metainfo_size = 0x90
		metainfo_bytes = uc.mem_read(arg, metainfo_size)
		metainfo = list(struct.unpack('<' + 'I' * (metainfo_size/4), metainfo_bytes))

		self.bytes_in = metainfo[8/4] - 0x10
		assert 0 <= self.bytes_in <= 0x1000
		self.bytes_out = metainfo[0x10/4] - 0x10
		assert 0 <= self.bytes_out <= 0x1000
		self.buffer_count = metainfo[0x18/4]
		assert self.buffer_count < 20

		self.in_interface_count = metainfo[0x1c/4]
		self.out_interface_count = metainfo[0x20/4]
		self.in_handles_count = metainfo[0x24/4]
		self.out_handles_count = metainfo[0x28/4]

		assert self.in_interface_count < 20
		assert self.out_interface_count < 20
		assert self.in_handles_count < 20
		assert self.out_handles_count < 20
		
		self.description = {
			'inbytes': self.bytes_in,
			'outbytes': self.bytes_out,
			'ininterfaces': [None] * self.in_interface_count,
			'outinterfaces': [None] * self.out_interface_count,
			'inhandles': metainfo[0x4C/4:0x4C/4 + self.in_handles_count],
			'outhandles': metainfo[0x6C/4:0x6C/4 + self.out_handles_count],
			'buffers': metainfo[0x2c/4:0x2c/4 + self.buffer_count],
			'pid': metainfo[0] == 1,
		}
		self.description['lr'] = uc.reg_read(UC_ARM64_REG_LR)

		for i in ['outinterfaces', 'inhandles', 'outhandles', 'buffers', 'pid', 'ininterfaces']:
			if not self.description[i]:
				del self.description[i]

		if self.in_interface_count:
			self._simulator.add_trace_instruction_hook(self.trace_instruction)

		self.ret(uc, 0)
		return True

	def trace_instruction(self, uc, instruction):
		i = instruction
		#print '0x%08x:    %s  %s' % (instruction.address, instruction.mnemonic, instruction.op_str)
		if i.mnemonic == 'cmp' and i.op_str.endswith(', x9') and len(self.description['ininterfaces']) == 1 and self.description['ininterfaces'][0] is None:
			assert i.op_str == 'x8, x9' # oddly specific
			x9 = uc.reg_read(UC_ARM64_REG_X9)
			uc.reg_write(UC_ARM64_REG_X8, x9)
			uc.reg_write(UC_ARM64_REG_NZCV, 0b0100)
			self.description['ininterfaces'][0] = x9
		

	def OverwriteClientProcessId(self, uc):
		o = uc.reg_read(UC_ARM64_REG_X1)
		uc.mem_write(o, struct.pack('<Q', 0))
		#print' OverwriteClientProcessId', hex(struct.unpack('<Q', uc.mem_read(uc.reg_read(UC_ARM64_REG_X1), 8))[0])
		self.ret(uc, 0)
		return True

	def GetBuffers(self, uc):
		outptr = uc.reg_read(UC_ARM64_REG_X1)
		for i in xrange(outptr, outptr+self.buffer_count*0x10, 0x10):
			# necessary for 'nn::nifm::detail::IGeneralService' cmd 26
			uc.mem_write(i, struct.pack('<QQ', self._simulator.buffer_memory, self.buffer_size))
		uc.mem_write(self._simulator.buffer_memory, struct.pack('<Q', 1))
		self.ret(uc, 0)
		return True

	def GetInNativeHandles(self, uc):
		self.ret(uc, 0)
		return True

	def GetInObjects(self, uc):
		outptr = uc.reg_read(UC_ARM64_REG_X1)
		assert self.in_interface_count == 1
		uc.mem_write(outptr, struct.pack('<Q', self._simulator.in_object_ptr))
		self.ret(uc, 0)
		return True

	def BeginPreparingForReply(self, uc):
		o = uc.reg_read(UC_ARM64_REG_X1)
		uc.mem_write(o, struct.pack('<QQ', self._simulator.output_memory, 0x1000))
		self.ret(uc, 0)
		return True

	def SetBuffers(self, uc):
		self.ret(uc, 0)
		return True

	def SetOutObjects(self, uc):
		value = struct.unpack('<Q', uc.mem_read(uc.reg_read(UC_ARM64_REG_X1)+8, 8))[0]
		self.description['outinterfaces'][0] = value
		self.ret(uc, 0)
		return False

	def SetOutNativeHandles(self, uc):
		self.ret(uc, 0)
		return True

	def BeginPreparingForErrorReply(self, uc):
		return False

	def EndPreparingForReply(self, uc):
		self.ret(uc, 0)
		return False

	def target_function(self, offset, uc):
		if self.description is None:
			return False
		self.description['vt'] = offset
		self.ret(uc, 0)
		return True

def iter_traces(command_ids_to_try, simulator, process_function):
	for cmd_id in all_known_command_ids:
		trace = simulator.trace_cmd(process_function, cmd_id)
		if trace.description is not None:
			yield trace

def get_hashes(traces):
	prior_rets = {}
	hash_code_parts = []

	for trace in traces:
		description = trace.description
		# accumulate hash code
		suffix = ''
		if 'outinterfaces' in description:
			out_obj_name = description['outinterfaces'][0]
			if out_obj_name not in prior_rets:
				prior_rets[out_obj_name] = len(prior_rets)
			suffix = ';o%d' % prior_rets[out_obj_name]

		buffers = description.get('buffers', [])
		# didn't realize this was getting counted in the client code, but easier
		# to fix it here
		c_desc_size_extr = (buffers.count(10) + buffers.count(34))*2
		if buffers:
			suffix += ';b' + ','.join('%d' % i for i in buffers)
		suffix += ')'

		hash_code = '%d(%d%s' % (trace.cmd_id, (trace.bytes_in+3+c_desc_size_extr)/4, suffix)
		hash_code2 = '%d(%d%s' % (trace.cmd_id, (trace.bytes_in+3)/4, suffix)
		hash_code_parts.append((description.get('vt'), hash_code, hash_code2))

	hash_code_parts.sort()
	hash_code = ''.join(b for a,b,c in hash_code_parts)
	hash_code2 = ''.join(c for a,b,c in hash_code_parts)
	hashed = hashlib.sha224(hash_code).hexdigest()[:16]
	hashed2 = hashlib.sha224(hash_code2).hexdigest()[:16]

	return (hashed, hashed2, hash_code, hash_code2)

def find_hash_matches(hashed, hashed2):
	probably = None
	old_version = False
	if hashed in all_hashes:
		probably = all_hashes[hashed]
	elif hashed2 in all_hashes:
		probably = all_hashes[hashed2]
	elif hashed in all_hashes_300:
		old_version = True
		probably = all_hashes_300[hashed]
	elif hashed2 in all_hashes_300:
		old_version = True
		probably = all_hashes_300[hashed2]
	return probably, old_version

all_known_command_ids = sorted(set([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 4201, 106, 107, 108, 4205, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 20501, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 2413, 8216, 150, 151, 2201, 2202, 2203, 2204, 2205, 2207, 10400, 2209, 8219, 8220, 8221, 30900, 30901, 30902, 8223, 90300, 190, 8224, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 220, 20701, 222, 223, 230, 231, 250, 251, 252, 2301, 2302, 255, 256, 10500, 261, 2312, 280, 290, 291, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 2101, 20800, 20801, 322, 323, 2102, 8250, 350, 2400, 2401, 2402, 2403, 2404, 2405, 10600, 10601, 2411, 2412, 2450, 2414, 8253, 10610, 2451, 2421, 2422, 2424, 8255, 2431, 8254, 2433, 2434, 406, 8257, 400, 401, 402, 403, 404, 405, 10300, 407, 408, 409, 410, 411, 2460, 20900, 8252, 412, 2501, 10700, 10701, 10702, 8200, 1106, 1107, 500, 501, 502, 503, 504, 505, 506, 507, 508, 510, 511, 512, 513, 520, 521, 90200, 8201, 90201, 540, 30810, 542, 543, 544, 545, 546, 30811, 30812, 8202, 8203, 8291, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 612, 613, 614, 8295, 620, 8204, 8296, 630, 105, 640, 4203, 8225, 2050, 109, 30830, 2052, 8256, 700, 701, 702, 703, 704, 705, 706, 707, 708, 709, 8207, 20600, 8208, 49900, 751, 11000, 127, 8209, 800, 801, 802, 803, 804, 805, 806, 821, 822, 823, 824, 8211, 850, 851, 852, 7000, 2055, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 3000, 3001, 3002, 160, 8012, 8217, 8013, 320, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1020, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1061, 1062, 1063, 21000, 1100, 1101, 1102, 2053, 5202, 5203, 8218, 3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209, 3210, 3211, 3214, 3215, 3216, 3217, 40100, 40101, 541, 1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 8292, 547, 20500, 8293, 2054, 2601, 8294, 40200, 40201, 1300, 1301, 1302, 1303, 1304, 8227, 20700, 221, 8228, 8297, 8229, 4206, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1411, 1421, 1422, 1423, 1424, 30100, 30101, 30102, 1431, 1432, 30110, 30120, 30121, 1451, 1452, 1453, 1454, 1455, 1456, 1457, 1458, 1471, 1472, 1473, 1474, 1500, 1501, 1502, 1503, 1504, 1505, 2300, 30200, 30201, 30202, 30203, 30204, 30205, 30210, 30211, 30212, 30213, 30214, 30215, 30216, 30217, 260, 1600, 1601, 1602, 1603, 60001, 60002, 30300, 2051, 20100, 20101, 20102, 20103, 20104, 20110, 1700, 1701, 1702, 1703, 8222, 30400, 30401, 30402, 631, 20200, 20201, 1800, 1801, 1802, 1803, 2008, 10011, 30500, 7992, 7993, 7994, 7995, 7996, 7997, 7998, 7999, 8000, 8001, 8002, 8011, 20300, 20301, 8021, 1900, 1901, 1902, 6000, 6001, 6002, 10100, 10101, 10102, 10110, 30820, 321, 1941, 1951, 1952, 1953, 8100, 20400, 20401, 8210, 2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 10200, 2009, 2010, 2011, 2012, 2013, 2014, 2015, 2016, 2017, 10211, 2020, 2021, 30700, 2030, 2031, 8251, 90100, 90101, 90102]))
PUBLIC = False
def dump_ipc_filename(fname):
	with open(fname, 'rb') as fileobj:
		f = nxo64.load_nxo(fileobj)

	simulator = IPCServerSimulator(f)

	s_tables = []
	process_functions = []
	process_function_names = {}
	if True:
		stables = []
		for sym in f.symbols:
			if 's_Table' in sym.name:
				stables.append((sym.name, DEFAULT_LOAD_BASE + sym.value))

		for stable_name, addr in stables:
			stable_name = demangle(stable_name)
			# s_Table is removed by the demangler, but only if we're looking at a real IPC interface
			if stable_name in ('nn::sf::hipc::detail::IHipcManager', 'nn::sf::cmif::server::CmifDomainServerObject') or 's_Table' in stable_name:
				continue
			fptr = simulator.qword(addr)
			process_functions.append(fptr)
			s_tables.append(addr)
			process_function_names[fptr] = stable_name

	if not process_functions:
		candidates = []
		for offset, r_type, sym, addend in f.relocations:
			if addend:
				candidates.append((addend, offset))
		candidates.sort()

		# there's a unique error code (0x1A60A) used to find process functions
		# by matching the pattern:
		#   MOV  W?, #0x10000
		#   MOVK W?, #0xA60A
		# this fails on empty interfaces where the error code gets interleaved
		# which could be fixed, but the interfaces are empty and we don't have
		# names for them so I didn't see the point.

		f.binfile.seek(0)
		text_string = f.binfile.read(f.textsize)
		regex = '|'.join(re.escape(chr(0x20 | i) + '\x00\xA0\x52' + chr(0x40 | i) + '\xC1\x94\x72') for i in range(29))
		for i in re.finditer(regex, text_string):
			if i.start() & 3: continue
			idx = bisect.bisect(candidates, (i.start(), 0))
			process_function, s_table = candidates[idx-1]
			if text_string.index('\xC0\x03\x5F\xD6', process_function) > i.start():
				process_functions.append(DEFAULT_LOAD_BASE + process_function)
				s_tables.append(DEFAULT_LOAD_BASE + s_table)

		# 5.x: match on the "SFCI" constant used in the template of s_Table
		#   MOV  W?, #0x4653
		#   MOVK W?, #0x4943, LSL#16
		if not s_tables:
			regex = '|'.join(re.escape(chr(0x60 | i) + '\xCA\x88\x52' + chr(0x60 | i) + '\x28\xA9\x72') for i in range(29))
			for i in re.finditer(regex, text_string):
				if i.start() & 3: continue
				idx = bisect.bisect(candidates, (i.start(), 0))
				process_function, s_table = candidates[idx-1]
				if text_string.index('\xC0\x03\x5F\xD6', process_function) > i.start():
					process_functions.append(DEFAULT_LOAD_BASE + process_function)
					s_tables.append(DEFAULT_LOAD_BASE + s_table)

	process_name = f.get_name()
	if process_name is None:
		process_name = fname

	print '%r: {' % (process_name,)	
	for process_function in process_functions:
		#if process_function != 0x7100003074: continue

		traces = iter_traces(all_known_command_ids, simulator, process_function)

		msg = None
		if process_function in process_function_names:
			name = process_function_names[process_function]
		else:
			# try to figure out name for 4.0+
			traces = list(traces)
			hashed, hashed2, hash_code, hash_code2 = get_hashes(traces)
			probably, old_version = find_hash_matches(hashed, hashed2)

			name = None
			if probably is not None:
				if len(probably) == 1:
					# TODO: need to figure this out earlier
					#name = probably[0]
					msg = 'single hash match %r' % (probably[0],)
				else:
					msg = repr(probably)
				if old_version:
					msg = '3.0.0: ' + msg
			else:
				msg = '%s %r' % (hashed, hash_code)
				if hash_code != hash_code2:
					msg += ' %r' % (hash_code2,)

			if name is None:
				name = '0x%X' % process_function

		if msg is None:
			print '  ' + repr(name) + ': {'
		else:
			print '  ' + repr(name) + ': { #', msg
		for trace in traces:
			description = trace.description
			line = '      ' + ('%d: ' % trace.cmd_id).ljust(7) + '{'
			parts = []
			for k in ('outinterfaces', 'ininterfaces'):
				if k in description:
					description[k] = [(process_function_names.get(simulator.qword(i), '0x%X' % (simulator.qword(i),)) if i is not None else None) for i in description[k]]

			for i in ['vt', 'lr', 'inbytes', 'outbytes', 'buffers', 'inhandles', 'outhandles', 'outinterfaces', 'pid', 'ininterfaces']:
				if i not in description: continue
				if PUBLIC and i in ('vt', 'lr'): continue
				v = description[i]
				if isinstance(v, (list, bool)):
					v = repr(v)
				else:
					if v >= 10:
						v = '0x%X' % v
					else:
						v = str(v)
					v = v.rjust(5)
				parts.append('"%s": %s' % (i, v))
			line += ', '.join(parts)

			line += '},'
			print line

		print '  },'
		#if PUBLIC:
		#	print '  },'
		#else:
		#	print '  }, # ' + msg

	print '},'

	   
def main(fnames):
	for i in fnames:
		dump_ipc_filename(i)

if __name__ == '__main__':
	main(sys.argv[1:])

