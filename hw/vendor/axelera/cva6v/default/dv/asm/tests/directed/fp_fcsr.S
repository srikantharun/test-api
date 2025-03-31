#include "../../env/user_define.h"
.globl _start
.section .text
_start:           
                  #include "../../env/user_init.s"
                  csrr x5, 0xf14
                  li x6, 0
                  beq x5, x6, 0f

0: la x30, h0_start
jalr x0, x30, 0
h0_start:
kernel_sp:        
                  la x8, kernel_stack_end

trap_vec_init:    
                  la x17, mtvec_handler
                  ori x17, x17, 0
                  csrw 0x305, x17 # MTVEC

mepc_setup:       
                  la x17, init
                  csrw 0x341, x17

custom_csr_setup: 
                  nop

init_machine_mode:
                  li x17, 0xa00043800
                  csrw 0x300, x17 # MSTATUS
                  li x17, 0x0
                  csrw 0x304, x17 # MIE
                  mret
init:             
                  li x17, 0
                  fmv.w.x f0, x17
                  li x17, 2147483648
                  fmv.w.x f1, x17
                  li x17, 1722017677
                  fmv.w.x f2, x17
                  li x17, 0
                  fmv.w.x f3, x17
                  li x17, 2960470805
                  fmv.w.x f4, x17
                  li x17, 4293911847
                  fmv.w.x f5, x17
                  li x17, 2139095040
                  fmv.w.x f6, x17
                  li x17, 0
                  fmv.w.x f7, x17
                  li x17, 4286578687
                  fmv.w.x f8, x17
                  li x17, 5303829
                  fmv.w.x f9, x17
                  li x17, 4286578688
                  fmv.w.x f10, x17
                  li x17, 4256983039
                  fmv.w.x f11, x17
                  li x17, 2145832931
                  fmv.w.x f12, x17
                  li x17, 3907672
                  fmv.w.x f13, x17
                  li x17, 2145555252
                  fmv.w.x f14, x17
                  li x17, 4294399694
                  fmv.w.x f15, x17
                  li x17, 2139095039
                  fmv.w.x f16, x17
                  li x17, 1341298635
                  fmv.w.x f17, x17
                  li x17, 2139095040
                  fmv.w.x f18, x17
                  li x17, 1529158934
                  fmv.w.x f19, x17
                  li x17, 2149807355
                  fmv.w.x f20, x17
                  li x17, 4286578687
                  fmv.w.x f21, x17
                  li x17, 4286578687
                  fmv.w.x f22, x17
                  li x17, 2143728254
                  fmv.w.x f23, x17
                  li x17, 1699679
                  fmv.w.x f24, x17
                  li x17, 7745196
                  fmv.w.x f25, x17
                  li x17, 2150179483
                  fmv.w.x f26, x17
                  li x17, 209230
                  fmv.w.x f27, x17
                  li x17, 2152347160
                  fmv.w.x f28, x17
                  li x17, 2147483648
                  fmv.w.x f29, x17
                  li x17, 2147483648
                  fmv.w.x f30, x17
                  li x17, 4286578687
                  fmv.w.x f31, x17
                  fsrmi 4
                  li x0, 0xc07daeda
                  li x1, 0xb
                  li x2, 0xc5dc2799
                  li x3, 0xbba87be4
                  li x4, 0xfcbc73b9
                  li x5, 0xf78fd4b2
                  li x6, 0x21df78bd
                  li x7, 0xf1a78d4f
                  li x9, 0xa
                  li x10, 0xbfcb8ac
                  li x11, 0xec757203
                  li x12, 0xa92d5123
                  li x13, 0xb5ecd92f
                  li x14, 0xffc93986
                  li x15, 0x0
                  li x16, 0xaec8c331
                  li x17, 0x3
                  li x18, 0x628fff3c
                  li x19, 0xf494c143
                  li x20, 0x8ebe2d49
                  li x21, 0x81db5547
                  li x23, 0xfa0057e7
                  li x24, 0xf472169b
                  li x25, 0xd247d79a
                  li x26, 0xfe3e8e9f
                  li x27, 0xf5038595
                  li x28, 0x80000000
                  li x29, 0x45b20441
                  li x30, 0xfbbf247a
                  li x31, 0x3b0af3ce
                  la x22, user_stack_end
                  li                a5, 0x6000 # FPU MSTATUS MASK
                  li x17, 0xa00043800
                  csrw 0x300, x17 # MSTATUS - FP initial state
reserverd_fcsr_bits:
                  li x31, 0xffffffff
                  csrrs t1, fcsr, x0 # Read fcsr
                  csrw fcsr, x31 # write all 1s, include rsvd fields
                  csrrs t1, fcsr, x0 # Read fcsr
                  csrrs t1, mstatus, x0 # Read mstatus - should be dirty
access_fcsr_mstatus_off:
                  csrrc             zero, mstatus, a5 # FPU disable
                  csrrwi            zero, frm, 0x1
                  csrrs             zero, mstatus, a5 # FPU enable
                  csrrc             zero, mstatus, a5 # FPU disable
                  csrrwi            zero, fflags, 0x1
                  csrrs             zero, mstatus, a5 # FPU enable
                  csrrc             zero, mstatus, a5 # FPU disable
                  csrrwi            zero, fcsr, 0x1
                  csrrs             zero, mstatus, a5 # FPU enable
fcsr_access_sets_mstatus_fp_dirty:
                  csrw 0x300, x17 # MSTATUS - FP initial state
                  csrrs t1, mstatus, x0 # Read mstatus
                  csrrwi            zero, frm, 0x1
                  csrrs t1, mstatus, x0 # Read mstatus
                  csrw 0x300, x17 # MSTATUS.FP back to initial
                  csrrs t1, mstatus, x0 # Read mstatus
                  csrrwi            zero, fflags, 0x1
                  csrrs t1, mstatus, x0 # Read mstatus
                  csrw 0x300, x17 # MSTATUS.FP back to initial
                  csrrs t1, mstatus, x0 # Read mstatus
                  csrrwi            zero, fcsr, 0x1
                  csrrs t1, mstatus, x0 # Read mstatus
fp_ops_sets_mstatus_fp_dirty:
                  fsrmi 0
                  csrw 0x300, x17 # MSTATUS.FP back to initial
                  li                s11, 0x518a #start riscv_fpu_only_halfprecision_divbig_arithmetic_stream_100
                  fmv.h.x           fs3, s11
                  li                s11, 0x1d10
                  fmv.h.x           fa2, s11
                  fdiv.h            fa7, fa2, fs3, rtz
                  csrrs t1, mstatus, x0 # Read mstatus
                  csrw 0x300, x17 # MSTATUS.FP back to initial
                  fdiv.h            ft2, fa2, fs3
                  csrrs t1, mstatus, x0 # Read mstatus
                  la x30, test_done
                  jalr x0, x30, 0
test_done:        
                  li gp, 1
                  ecall
write_tohost:     
                  sw gp, tohost, t5
                  fence

_exit:            
                  wfi

debug_rom:        
                  dret

debug_exception:  
                  dret

instr_end:        
                  nop

.section .data
.align 6; .global tohost; tohost: .dword 0;
.align 6; .global fromhost; fromhost: .dword 0;
.section .user_stack,"aw",@progbits;
.align 12
user_stack_start:
.rept 4999
.8byte 0x0
.endr
user_stack_end:
.8byte 0x0
.align 12
kernel_instr_start:
.text
.align 12
mtvec_handler:    
                  addi x8, x8, -8
                  sd  x22, (x8)
                  add x22, x8, zero
                  addi x22, x22, -256
                  sd  x1, 8(x22)
                  sd  x2, 16(x22)
                  sd  x3, 24(x22)
                  sd  x4, 32(x22)
                  sd  x5, 40(x22)
                  sd  x6, 48(x22)
                  sd  x7, 56(x22)
                  sd  x8, 64(x22)
                  sd  x9, 72(x22)
                  sd  x10, 80(x22)
                  sd  x11, 88(x22)
                  sd  x12, 96(x22)
                  sd  x13, 104(x22)
                  sd  x14, 112(x22)
                  sd  x15, 120(x22)
                  sd  x16, 128(x22)
                  sd  x17, 136(x22)
                  sd  x18, 144(x22)
                  sd  x19, 152(x22)
                  sd  x20, 160(x22)
                  sd  x21, 168(x22)
                  sd  x22, 176(x22)
                  sd  x23, 184(x22)
                  sd  x24, 192(x22)
                  sd  x25, 200(x22)
                  sd  x26, 208(x22)
                  sd  x27, 216(x22)
                  sd  x28, 224(x22)
                  sd  x29, 232(x22)
                  sd  x30, 240(x22)
                  sd  x31, 248(x22)
                  add x8, x22, zero
                  csrr x17, 0x300 # MSTATUS
                  csrr x17, 0x342 # MCAUSE
                  srli x17, x17, 63
                  bne x17, x0, mmode_intr_handler

mmode_exception_handler:
                  csrr x17, 0x341 # MEPC
                  csrr x17, 0x342 # MCAUSE
                  li x31, 0x3 # BREAKPOINT
                  beq x17, x31, ebreak_handler
                  li x31, 0x8 # ECALL_UMODE
                  beq x17, x31, ecall_handler
                  li x31, 0x9 # ECALL_SMODE
                  beq x17, x31, ecall_handler
                  li x31, 0xb # ECALL_MMODE
                  beq x17, x31, ecall_handler
                  li x31, 0x1
                  beq x17, x31, instr_fault_handler
                  li x31, 0x4
                  beq x17, x31, load_address_misaligned_handler
                  li x31, 0x5
                  beq x17, x31, load_fault_handler
                  li x31, 0x6
                  beq x17, x31, store_amo_address_misaligned_handler
                  li x31, 0x7
                  beq x17, x31, store_fault_handler
                  li x31, 0xc
                  beq x17, x31, pt_fault_handler
                  li x31, 0xd
                  beq x17, x31, pt_fault_handler
                  li x31, 0xf
                  beq x17, x31, pt_fault_handler
                  li x31, 0x2 # ILLEGAL_INSTRUCTION
                  beq x17, x31, illegal_instr_handler
                  csrr x31, 0x343 # MTVAL
                  1: la x30, test_done
                  jalr x1, x30, 0

ecall_handler:    
                  la x17, _start
                  sd x0, 0(x17)
                  sd x1, 8(x17)
                  sd x2, 16(x17)
                  sd x3, 24(x17)
                  sd x4, 32(x17)
                  sd x5, 40(x17)
                  sd x6, 48(x17)
                  sd x7, 56(x17)
                  sd x8, 64(x17)
                  sd x9, 72(x17)
                  sd x10, 80(x17)
                  sd x11, 88(x17)
                  sd x12, 96(x17)
                  sd x13, 104(x17)
                  sd x14, 112(x17)
                  sd x15, 120(x17)
                  sd x16, 128(x17)
                  sd x17, 136(x17)
                  sd x18, 144(x17)
                  sd x19, 152(x17)
                  sd x20, 160(x17)
                  sd x21, 168(x17)
                  sd x22, 176(x17)
                  sd x23, 184(x17)
                  sd x24, 192(x17)
                  sd x25, 200(x17)
                  sd x26, 208(x17)
                  sd x27, 216(x17)
                  sd x28, 224(x17)
                  sd x29, 232(x17)
                  sd x30, 240(x17)
                  sd x31, 248(x17)
                  la x30, write_tohost
                  jalr x0, x30, 0

instr_fault_handler:
                  add x22, x8, zero
                  ld  x1, 8(x22)
                  ld  x2, 16(x22)
                  ld  x3, 24(x22)
                  ld  x4, 32(x22)
                  ld  x5, 40(x22)
                  ld  x6, 48(x22)
                  ld  x7, 56(x22)
                  ld  x8, 64(x22)
                  ld  x9, 72(x22)
                  ld  x10, 80(x22)
                  ld  x11, 88(x22)
                  ld  x12, 96(x22)
                  ld  x13, 104(x22)
                  ld  x14, 112(x22)
                  ld  x15, 120(x22)
                  ld  x16, 128(x22)
                  ld  x17, 136(x22)
                  ld  x18, 144(x22)
                  ld  x19, 152(x22)
                  ld  x20, 160(x22)
                  ld  x21, 168(x22)
                  ld  x22, 176(x22)
                  ld  x23, 184(x22)
                  ld  x24, 192(x22)
                  ld  x25, 200(x22)
                  ld  x26, 208(x22)
                  ld  x27, 216(x22)
                  ld  x28, 224(x22)
                  ld  x29, 232(x22)
                  ld  x30, 240(x22)
                  ld  x31, 248(x22)
                  addi x22, x22, 256
                  add x8, x22, zero
                  ld  x22, (x8)
                  addi x8, x8, 8
                  mret

load_fault_handler:
                  add x22, x8, zero
                  ld  x1, 8(x22)
                  ld  x2, 16(x22)
                  ld  x3, 24(x22)
                  ld  x4, 32(x22)
                  ld  x5, 40(x22)
                  ld  x6, 48(x22)
                  ld  x7, 56(x22)
                  ld  x8, 64(x22)
                  ld  x9, 72(x22)
                  ld  x10, 80(x22)
                  ld  x11, 88(x22)
                  ld  x12, 96(x22)
                  ld  x13, 104(x22)
                  ld  x14, 112(x22)
                  ld  x15, 120(x22)
                  ld  x16, 128(x22)
                  ld  x17, 136(x22)
                  ld  x18, 144(x22)
                  ld  x19, 152(x22)
                  ld  x20, 160(x22)
                  ld  x21, 168(x22)
                  ld  x22, 176(x22)
                  ld  x23, 184(x22)
                  ld  x24, 192(x22)
                  ld  x25, 200(x22)
                  ld  x26, 208(x22)
                  ld  x27, 216(x22)
                  ld  x28, 224(x22)
                  ld  x29, 232(x22)
                  ld  x30, 240(x22)
                  ld  x31, 248(x22)
                  addi x22, x22, 256
                  add x8, x22, zero
                  ld  x22, (x8)
                  addi x8, x8, 8
                  mret

store_fault_handler:
                  add x22, x8, zero
                  ld  x1, 8(x22)
                  ld  x2, 16(x22)
                  ld  x3, 24(x22)
                  ld  x4, 32(x22)
                  ld  x5, 40(x22)
                  ld  x6, 48(x22)
                  ld  x7, 56(x22)
                  ld  x8, 64(x22)
                  ld  x9, 72(x22)
                  ld  x10, 80(x22)
                  ld  x11, 88(x22)
                  ld  x12, 96(x22)
                  ld  x13, 104(x22)
                  ld  x14, 112(x22)
                  ld  x15, 120(x22)
                  ld  x16, 128(x22)
                  ld  x17, 136(x22)
                  ld  x18, 144(x22)
                  ld  x19, 152(x22)
                  ld  x20, 160(x22)
                  ld  x21, 168(x22)
                  ld  x22, 176(x22)
                  ld  x23, 184(x22)
                  ld  x24, 192(x22)
                  ld  x25, 200(x22)
                  ld  x26, 208(x22)
                  ld  x27, 216(x22)
                  ld  x28, 224(x22)
                  ld  x29, 232(x22)
                  ld  x30, 240(x22)
                  ld  x31, 248(x22)
                  addi x22, x22, 256
                  add x8, x22, zero
                  ld  x22, (x8)
                  addi x8, x8, 8
                  mret

ebreak_handler:   
                  csrr  x17, 0x341
                  addi  x17, x17, 4
                  csrw  0x341, x17
                  add x22, x8, zero
                  ld  x1, 8(x22)
                  ld  x2, 16(x22)
                  ld  x3, 24(x22)
                  ld  x4, 32(x22)
                  ld  x5, 40(x22)
                  ld  x6, 48(x22)
                  ld  x7, 56(x22)
                  ld  x8, 64(x22)
                  ld  x9, 72(x22)
                  ld  x10, 80(x22)
                  ld  x11, 88(x22)
                  ld  x12, 96(x22)
                  ld  x13, 104(x22)
                  ld  x14, 112(x22)
                  ld  x15, 120(x22)
                  ld  x16, 128(x22)
                  ld  x17, 136(x22)
                  ld  x18, 144(x22)
                  ld  x19, 152(x22)
                  ld  x20, 160(x22)
                  ld  x21, 168(x22)
                  ld  x22, 176(x22)
                  ld  x23, 184(x22)
                  ld  x24, 192(x22)
                  ld  x25, 200(x22)
                  ld  x26, 208(x22)
                  ld  x27, 216(x22)
                  ld  x28, 224(x22)
                  ld  x29, 232(x22)
                  ld  x30, 240(x22)
                  ld  x31, 248(x22)
                  addi x22, x22, 256
                  add x8, x22, zero
                  ld  x22, (x8)
                  addi x8, x8, 8
                  mret

illegal_instr_handler:
                  csrr  x17, 0x341
                  addi  x17, x17, 4
                  csrw  0x341, x17
                  add x22, x8, zero
                  ld  x1, 8(x22)
                  ld  x2, 16(x22)
                  ld  x3, 24(x22)
                  ld  x4, 32(x22)
                  ld  x5, 40(x22)
                  ld  x6, 48(x22)
                  ld  x7, 56(x22)
                  ld  x8, 64(x22)
                  ld  x9, 72(x22)
                  ld  x10, 80(x22)
                  ld  x11, 88(x22)
                  ld  x12, 96(x22)
                  ld  x13, 104(x22)
                  ld  x14, 112(x22)
                  ld  x15, 120(x22)
                  ld  x16, 128(x22)
                  ld  x17, 136(x22)
                  ld  x18, 144(x22)
                  ld  x19, 152(x22)
                  ld  x20, 160(x22)
                  ld  x21, 168(x22)
                  ld  x22, 176(x22)
                  ld  x23, 184(x22)
                  ld  x24, 192(x22)
                  ld  x25, 200(x22)
                  ld  x26, 208(x22)
                  ld  x27, 216(x22)
                  ld  x28, 224(x22)
                  ld  x29, 232(x22)
                  ld  x30, 240(x22)
                  ld  x31, 248(x22)
                  addi x22, x22, 256
                  add x8, x22, zero
                  ld  x22, (x8)
                  addi x8, x8, 8
                  mret

load_address_misaligned_handler:
                  csrr  x17, 0x341 # Load MEPC
                  csrr  x5, 0x300 # Load MSTATUS
                  srli  x5, x5, 11 # Get MPP (priv mode)
                  andi  x5, x5, 0x3 # Extract MPP
                  li  x31, 0x3 # Machine mode
                  beq  x5, x31, lame_handle_compressed
                  li  x31, 0x2000000000 # Load base PA
                  add  x17, x17, x31 # translate VA -> PA
                  lame_handle_compressed:
                  lhu  x31, 0(x17) # Load lower 16b
                  addi  x17, x17, 2 # Handle misaligned compressed instr
                  andi  x31, x31, 0x3 # Extract lower 2b
                  li  x23, 0x3 # Noncompressed LSBs == 3
                  blt  x31, x23, lame_update_mepc_handle_va
                  addi  x17, x17, 2 # Handle regular misaligned instr - 2 more bytes
                  lame_update_mepc_handle_va:
                  li  x31, 0x3 # Machine mode
                  beq  x5, x31, lame_update_mepc
                  li  x31, -0x2000000000 # Load base PA
                  add  x17, x17, x31 # translate PA -> VA
                  lame_update_mepc: 
                  csrw  0x341, x17 # MEPC
                  add x22, x8, zero
                  ld  x1, 8(x22)
                  ld  x2, 16(x22)
                  ld  x3, 24(x22)
                  ld  x4, 32(x22)
                  ld  x5, 40(x22)
                  ld  x6, 48(x22)
                  ld  x7, 56(x22)
                  ld  x8, 64(x22)
                  ld  x9, 72(x22)
                  ld  x10, 80(x22)
                  ld  x11, 88(x22)
                  ld  x12, 96(x22)
                  ld  x13, 104(x22)
                  ld  x14, 112(x22)
                  ld  x15, 120(x22)
                  ld  x16, 128(x22)
                  ld  x17, 136(x22)
                  ld  x18, 144(x22)
                  ld  x19, 152(x22)
                  ld  x20, 160(x22)
                  ld  x21, 168(x22)
                  ld  x22, 176(x22)
                  ld  x23, 184(x22)
                  ld  x24, 192(x22)
                  ld  x25, 200(x22)
                  ld  x26, 208(x22)
                  ld  x27, 216(x22)
                  ld  x28, 224(x22)
                  ld  x29, 232(x22)
                  ld  x30, 240(x22)
                  ld  x31, 248(x22)
                  addi x22, x22, 256
                  add x8, x22, zero
                  ld  x22, (x8)
                  addi x8, x8, 8
                  mret

store_amo_address_misaligned_handler:
                  csrr  x17, 0x341 # Load MEPC
                  csrr  x5, 0x300 # Load MSTATUS
                  srli  x5, x5, 11 # Get MPP (priv mode)
                  andi  x5, x5, 0x3 # Extract MPP
                  li  x31, 0x3 # Machine mode
                  beq  x5, x31, same_handle_compressed
                  li  x31, 0x2000000000 # Load base PA
                  add  x17, x17, x31 # translate VA -> PA
                  same_handle_compressed:
                  lhu  x31, 0(x17) # Load lower 16b
                  addi  x17, x17, 2 # Handle misaligned compressed instr
                  andi  x31, x31, 0x3 # Extract lower 2b
                  li  x23, 0x3 # Noncompressed LSBs == 3
                  blt  x31, x23, same_update_mepc_handle_va
                  addi  x17, x17, 2 # Handle regular misaligned instr - 2 more bytes
                  same_update_mepc_handle_va:
                  li  x31, 0x3 # Machine mode
                  beq  x5, x31, same_update_mepc
                  li  x31, -0x2000000000 # Load base PA
                  add  x17, x17, x31 # translate PA -> VA
                  same_update_mepc: 
                  csrw  0x341, x17 # MEPC
                  add x22, x8, zero
                  ld  x1, 8(x22)
                  ld  x2, 16(x22)
                  ld  x3, 24(x22)
                  ld  x4, 32(x22)
                  ld  x5, 40(x22)
                  ld  x6, 48(x22)
                  ld  x7, 56(x22)
                  ld  x8, 64(x22)
                  ld  x9, 72(x22)
                  ld  x10, 80(x22)
                  ld  x11, 88(x22)
                  ld  x12, 96(x22)
                  ld  x13, 104(x22)
                  ld  x14, 112(x22)
                  ld  x15, 120(x22)
                  ld  x16, 128(x22)
                  ld  x17, 136(x22)
                  ld  x18, 144(x22)
                  ld  x19, 152(x22)
                  ld  x20, 160(x22)
                  ld  x21, 168(x22)
                  ld  x22, 176(x22)
                  ld  x23, 184(x22)
                  ld  x24, 192(x22)
                  ld  x25, 200(x22)
                  ld  x26, 208(x22)
                  ld  x27, 216(x22)
                  ld  x28, 224(x22)
                  ld  x29, 232(x22)
                  ld  x30, 240(x22)
                  ld  x31, 248(x22)
                  addi x22, x22, 256
                  add x8, x22, zero
                  ld  x22, (x8)
                  addi x8, x8, 8
                  mret

pt_fault_handler: 
                  nop

.align 12
mmode_intr_handler:
                  csrr  x17, 0x300 # MSTATUS;
                  csrr  x17, 0x304 # MIE;
                  csrr  x17, 0x344 # MIP;
                  csrrc x17, 0x344, x17 # MIP;
                  add x22, x8, zero
                  ld  x1, 8(x22)
                  ld  x2, 16(x22)
                  ld  x3, 24(x22)
                  ld  x4, 32(x22)
                  ld  x5, 40(x22)
                  ld  x6, 48(x22)
                  ld  x7, 56(x22)
                  ld  x8, 64(x22)
                  ld  x9, 72(x22)
                  ld  x10, 80(x22)
                  ld  x11, 88(x22)
                  ld  x12, 96(x22)
                  ld  x13, 104(x22)
                  ld  x14, 112(x22)
                  ld  x15, 120(x22)
                  ld  x16, 128(x22)
                  ld  x17, 136(x22)
                  ld  x18, 144(x22)
                  ld  x19, 152(x22)
                  ld  x20, 160(x22)
                  ld  x21, 168(x22)
                  ld  x22, 176(x22)
                  ld  x23, 184(x22)
                  ld  x24, 192(x22)
                  ld  x25, 200(x22)
                  ld  x26, 208(x22)
                  ld  x27, 216(x22)
                  ld  x28, 224(x22)
                  ld  x29, 232(x22)
                  ld  x30, 240(x22)
                  ld  x31, 248(x22)
                  addi x22, x22, 256
                  add x8, x22, zero
                  ld  x22, (x8)
                  addi x8, x8, 8
                  mret;

kernel_instr_end: nop
.section .kernel_stack,"aw",@progbits;
.align 12
kernel_stack_start:
.rept 3999
.8byte 0x0
.endr
kernel_stack_end:
.8byte 0x0
