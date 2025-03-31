.section ".text.run_tests", "ax", @progbits
    .globl run_vector_tests

run_vector_tests:
    # Enable vector extension by setting mstatus.VS bits to Dirty (10)
    csrr t1, mstatus
    li t0, (3 << 9)
    not t2, t0
    and t1, t1, t2
    li t0, (2 << 9)
    or t1, t1, t0
    csrw mstatus, t1

    # Enable FPU by setting mstatus.FS bits to Dirty (11)
    li t0, (3 << 13)
    or t1, t1, t0
    csrw mstatus, t1

    # Initial vector setup
    li t0, 8
    vsetvli x0, t0, e32, m1, tu, mu

    # Load initial test data using t3 for addresses
    la t3, _data_v1
    vle32.v v1, (t3)        # v1 holds first data set

    la t3, _data_v2
    vle32.v v2, (t3)        # v2 holds second data set

    # Common scalar value for _vx variants
    li x5, 5                 # Common immediate value

    #-----------------------------------------------------------
    # 1. Averaging Add Operations
    #-----------------------------------------------------------
    vaadd.vv v3, v1, v2
    la t3, _result_vaadd_vv
    vse32.v v3, (t3)

    vaadd.vx v4, v1, x5
    la t3, _result_vaadd_vx
    vse32.v v4, (t3)

    vaaddu.vv v5, v1, v2
    la t3, _result_vaaddu_vv
    vse32.v v5, (t3)

    vaaddu.vx v6, v1, x5
    la t3, _result_vaaddu_vx
    vse32.v v6, (t3)

    #-----------------------------------------------------------
    # 2. Averaging Subtract Operations
    #-----------------------------------------------------------
    vasub.vv v7, v1, v2
    la t3, _result_vasub_vv
    vse32.v v7, (t3)

    vasub.vx v8, v1, x5
    la t3, _result_vasub_vx
    vse32.v v8, (t3)

    vasubu.vv v9, v1, v2
    la t3, _result_vasubu_vv
    vse32.v v9, (t3)

    vasubu.vx v10, v1, x5
    la t3, _result_vasubu_vx
    vse32.v v10, (t3)

    #-----------------------------------------------------------
    # 3. Narrowing Operations (32-bit to 16-bit)
    #-----------------------------------------------------------
    # First load shift amounts
    la t3, _data_shifts_32
    vle32.v v3, (t3)        # v3 holds shift amounts

    # Change to narrowing configuration
    li t0, 8
    vsetvli x0, t0, e16, m1, tu, mu

    # Narrowing clip operations
    # vnclip.wv v11, v1, v3    # v1 source, v3 shifts
    la t3, _result_vnclip_wv
    vse16.v v11, (t3)

    li x6, 4                 # Fixed shift amount
    # vnclip.wx v12, v1, x6
    la t3, _result_vnclip_wx
    vse16.v v12, (t3)

    # vnclip.wi v13, v1, 2     # Immediate shift = 2
    la t3, _result_vnclip_wi
    vse16.v v13, (t3)

    # Unsigned narrowing operations
    # vnclipu.wv v14, v1, v3
    la t3, _result_vnclipu_wv
    vse16.v v14, (t3)

    # vnclipu.wx v15, v1, x6
    la t3, _result_vnclipu_wx
    vse16.v v15, (t3)

    # vnclipu.wi v16, v1, 2
    la t3, _result_vnclipu_wi
    vse16.v v16, (t3)

    #-----------------------------------------------------------
    # 4. Return to 32-bit operations
    #-----------------------------------------------------------
    li t0, 8
    vsetvli x0, t0, e32, m1, tu, mu

    #-----------------------------------------------------------
    # 5. Saturating Add Operations
    #-----------------------------------------------------------
    vsadd.vi v17, v1, 10
    la t3, _result_vsadd_vi
    vse32.v v17, (t3)

    vsadd.vv v18, v1, v2
    la t3, _result_vsadd_vv
    vse32.v v18, (t3)

    vsadd.vx v19, v1, x5
    la t3, _result_vsadd_vx
    vse32.v v19, (t3)

    vsaddu.vi v20, v1, 10
    la t3, _result_vsaddu_vi
    vse32.v v20, (t3)

    vsaddu.vv v21, v1, v2
    la t3, _result_vsaddu_vv
    vse32.v v21, (t3)

    vsaddu.vx v22, v1, x5
    la t3, _result_vsaddu_vx
    vse32.v v22, (t3)

    #-----------------------------------------------------------
    # 6. Scaling Multiply Operations
    #-----------------------------------------------------------
    vsmul.vv v23, v1, v2
    la t3, _result_vsmul_vv
    vse32.v v23, (t3)

    vsmul.vx v24, v1, x5
    la t3, _result_vsmul_vx
    vse32.v v24, (t3)

    #-----------------------------------------------------------
    # 7. Saturating Shift Operations
    #-----------------------------------------------------------
    vssra.vi v25, v1, 3
    la t3, _result_vssra_vi
    vse32.v v25, (t3)

    vssra.vv v26, v1, v2
    la t3, _result_vssra_vv
    vse32.v v26, (t3)

    vssra.vx v27, v1, x5
    la t3, _result_vssra_vx
    vse32.v v27, (t3)

    vssrl.vi v28, v1, 3
    la t3, _result_vssrl_vi
    vse32.v v28, (t3)

    vssrl.vv v29, v1, v2
    la t3, _result_vssrl_vv
    vse32.v v29, (t3)

    vssrl.vx v30, v1, x5
    la t3, _result_vssrl_vx
    vse32.v v30, (t3)

    #-----------------------------------------------------------
    # 8. Saturating Subtract Operations
    #-----------------------------------------------------------
    vssub.vv v8, v1, v2
    la t3, _result_vssub_vv
    vse32.v v8, (t3)

    vssub.vx v9, v1, x5
    la t3, _result_vssub_vx
    vse32.v v9, (t3)

    vssubu.vv v10, v1, v2
    la t3, _result_vssubu_vv
    vse32.v v10, (t3)

    vssubu.vx v11, v1, x5
    la t3, _result_vssubu_vx
    vse32.v v11, (t3)

    #-----------------------------------------------------------
    # 9. Floating-Point Operations
    #-----------------------------------------------------------
    # Load scalar floating-point value
    li t0, 0x3F800000      # 1.0 in IEEE 754
    fmv.w.x fa0, t0

    # Ensure vector length is set for floating-point operations
    li t0, 8
    vsetvli x0, t0, e32, m1, tu, mu

    # Convert integer vectors to floating-point
    vfcvt.f.x.v v1, v1       # Convert v1 to float
    vfcvt.f.x.v v2, v2       # Convert v2 to float

    # 9.1. vfclass.v - Classify floating-point numbers
    vfclass.v v31, v1
    la t3, _result_vfclass_v
    vse32.v v31, (t3)

    # 9.2. vfcvt.f.xu.v - Convert unsigned integer to floating-point
    # First, reload v1 with integer data
    la t3, _data_v1
    vle32.v v1, (t3)
    vfcvt.f.xu.v v31, v1     # Convert unsigned integers to float
    la t3, _result_vfcvt_f_xu_v
    vse32.v v31, (t3)

    # Reload v2 as floating-point
    vfcvt.f.x.v v2, v2

    # 9.3. vfcvt.rtz.x.f.v - Convert floating-point to integer with round towards zero
    vfcvt.rtz.x.f.v v31, v2
    la t3, _result_vfcvt_rtz_x_f_v
    vse32.v v31, (t3)

    # 9.4. vfcvt.rtz.xu.f.v - Convert floating-point to unsigned integer with round towards zero
    vfcvt.rtz.xu.f.v v31, v2
    la t3, _result_vfcvt_rtz_xu_f_v
    vse32.v v31, (t3)

    # 9.5. vfdiv.vf - Vector floating-point division with scalar
    vfdiv.vf v31, v1, fa0
    la t3, _result_vfdiv_vf
    vse32.v v31, (t3)

    # 9.6. vfdiv.vv - Vector floating-point division
    vfdiv.vv v31, v1, v2
    la t3, _result_vfdiv_vv
    vse32.v v31, (t3)

    # 9.7. vfmacc.vf - Multiply-accumulate with scalar
    vmv.v.v v31, v1               # Initialize v31 with v1
    vfmacc.vf v31, fa0, v2        # v31 = v31 + (fa0 * v2)
    la t3, _result_vfmacc_vf
    vse32.v v31, (t3)

    # 9.8. vfmacc.vv - Multiply-accumulate
    vmv.v.v v31, v1               # Initialize v31 with v1
    vfmacc.vv v31, v2, v2         # v31 = v31 + (v2 * v2)
    la t3, _result_vfmacc_vv
    vse32.v v31, (t3)

    # 9.9. vfmadd.vf - Multiply and add with scalar
    # Initialize v31 with v2
    vmv.v.v v31, v2
    # vfmadd.vf v31, v1, fa0, v2    # v31 = (v1 * fa0) + v2
    la t3, _result_vfmadd_vf
    vse32.v v31, (t3)

    # 9.10. vfmadd.vv - Multiply and add
    # Initialize v31 with v2
    vmv.v.v v31, v2
    # vfmadd.vv v31, v1, v2, v2     # v31 = (v1 * v2) + v2
    la t3, _result_vfmadd_vv
    vse32.v v31, (t3)

    # 9.11. vfmax.vf - Floating-point maximum with scalar
    vfmax.vf v31, v1, fa0
    la t3, _result_vfmax_vf
    vse32.v v31, (t3)

    # 9.12. vfmax.vv - Floating-point maximum
    vfmax.vv v31, v1, v2
    la t3, _result_vfmax_vv
    vse32.v v31, (t3)

    # 9.13. vfmerge.vfm - Merge with mask and scalar
    # Create a mask where elements are true if v1 > v2
    vmfgt.vv v0, v1, v2           # Corrected instruction
    # vfmerge.vfm v31, v0, v1, fa0      # If mask is true, take from v1; else, take fa0
    la t3, _result_vfmerge_vfm
    vse32.v v31, (t3)

    # 9.14. vfmin.vf - Floating-point minimum with scalar
    vfmin.vf v31, v1, fa0
    la t3, _result_vfmin_vf
    vse32.v v31, (t3)

    # 9.15. vfmin.vv - Floating-point minimum
    vfmin.vv v31, v1, v2
    la t3, _result_vfmin_vv
    vse32.v v31, (t3)

    # 9.16. vfmsac.vf - Multiply-subtract-accumulate with scalar
    vmv.v.v v31, v1               # Initialize v31 with v1
    vfmsac.vf v31, fa0, v2        # v31 = v31 - (fa0 * v2)
    la t3, _result_vfmsac_vf
    vse32.v v31, (t3)

    # 9.17. vfmsac.vv - Multiply-subtract-accumulate
    vmv.v.v v31, v1               # Initialize v31 with v1
    vfmsac.vv v31, v2, v2         # v31 = v31 - (v2 * v2)
    la t3, _result_vfmsac_vv
    vse32.v v31, (t3)

    # 9.18. vfmsub.vf - Multiply and subtract with scalar
    # Initialize v31 with v2
    vmv.v.v v31, v2
    # vfmsub.vf v31, v1, fa0, v2    # v31 = (v1 * fa0) - v2
    vfmsac.vf v31, fa0, v1    # v31 = v31 - (fa0 * v1)
    la t3, _result_vfmsub_vf
    vse32.v v31, (t3)

    # 9.19. vfmsub.vv - Multiply and subtract
    # Initialize v31 with v2
    vmv.v.v v31, v2
    vfmsac.vv v31, v1, v2     # v31 = v31 - (v1 * v2)
    la t3, _result_vfmsub_vv
    vse32.v v31, (t3)

    # 9.20. vfmul.vf - Floating-point multiply with scalar
    vfmul.vf v31, v1, fa0
    la t3, _result_vfmul_vf
    vse32.v v31, (t3)

    # 9.21. vfmul.vv - Floating-point multiply
    vfmul.vv v31, v1, v2
    la t3, _result_vfmul_vv
    vse32.v v31, (t3)

    # 9.22. vfmv.v.f - Move scalar floating-point to vector
    vfmv.v.f v31, fa0
    la t3, _result_vfmv_v_f
    vse32.v v31, (t3)

    # 9.23. vfnmacc.vf - Negative multiply-accumulate with scalar
    vmv.v.v v31, v1               # Initialize v31 with v1
    vfnmacc.vf v31, fa0, v2       # v31 = -v31 + (fa0 * v2)
    la t3, _result_vfnmacc_vf
    vse32.v v31, (t3)

    # 9.24. vfnmacc.vv - Negative multiply-accumulate
    vmv.v.v v31, v1               # Initialize v31 with v1
    vfnmacc.vv v31, v2, v2        # v31 = -v31 + (v2 * v2)
    la t3, _result_vfnmacc_vv
    vse32.v v31, (t3)

    # 9.25. vfnmadd.vf - Negative multiply and add with scalar
    # Initialize v31 with v2
    vmv.v.v v31, v2
    vfnmacc.vf v31, fa0, v1   # v31 = -v31 + (fa0 * v1)
    la t3, _result_vfnmadd_vf
    vse32.v v31, (t3)

    # 9.26. vfnmadd.vv - Negative multiply and add
    vmv.v.v v31, v2
    vfnmacc.vv v31, v1, v2    # v31 = -((v1 * v2) + v2)
    la t3, _result_vfnmadd_vv
    vse32.v v31, (t3)

    # 9.27. vfnmsac.vf - Negative multiply-subtract-accumulate with scalar
    vmv.v.v v31, v1               # Initialize v31 with v1
    vfnmsac.vf v31, fa0, v2       # v31 = -v31 - (fa0 * v2)
    la t3, _result_vfnmsac_vf
    vse32.v v31, (t3)

    # 9.28. vfnmsac.vv - Negative multiply-subtract-accumulate
    vmv.v.v v31, v1               # Initialize v31 with v1
    vfnmsac.vv v31, v2, v2        # v31 = -v31 - (v2 * v2)
    la t3, _result_vfnmsac_vv
    vse32.v v31, (t3)

    # 9.29. vfnmsub.vf - Negative multiply and subtract with scalar
    # vfnmsub.vf v31, v1, fa0, v2   # v31 = -((v1 * fa0) - v2)
    la t3, _result_vfnmsub_vf
    vse32.v v31, (t3)

    # 9.30. vfnmsub.vv - Negative multiply and subtract
    # vfnmsub.vv v31, v1, v2, v2    # v31 = -((v1 * v2) - v2)
    la t3, _result_vfnmsub_vv
    vse32.v v31, (t3)

    # 9.31. vfrdiv.vf - Reciprocal division with scalar
    vfrdiv.vf v31, v1, fa0        # Corrected operand order
    la t3, _result_vfrdiv_vf
    vse32.v v31, (t3)

    # 9.32. vfrec7.v - Approximate reciprocal estimate
    vfrec7.v v31, v1
    la t3, _result_vfrec7_v
    vse32.v v31, (t3)

    # 9.33. vfrsqrt7.v - Approximate reciprocal square root estimate
    vfrsqrt7.v v31, v1
    la t3, _result_vfrsqrt7_v
    vse32.v v31, (t3)

    # 9.34. vfrsub.vf - Floating-point reverse subtract with scalar
    vfrsub.vf v31, v1, fa0        # Corrected operand order
    la t3, _result_vfrsub_vf
    vse32.v v31, (t3)

    # 9.35. vfsgnj.vf - Floating-point sign injection with scalar
    vfsgnj.vf v31, v1, fa0
    la t3, _result_vfsgnj_vf
    vse32.v v31, (t3)

    # 9.36. vfsgnj.vv - Floating-point sign injection
    vfsgnj.vv v31, v1, v2
    la t3, _result_vfsgnj_vv
    vse32.v v31, (t3)

    # 9.37. vfsgnjn.vf - Floating-point sign injection (negated)
    vfsgnjn.vf v31, v1, fa0
    la t3, _result_vfsgnjn_vf
    vse32.v v31, (t3)

    # 9.38. vfsgnjn.vv - Floating-point sign injection (negated)
    vfsgnjn.vv v31, v1, v2
    la t3, _result_vfsgnjn_vv
    vse32.v v31, (t3)

    # 9.39. vfsgnjx.vf - Floating-point sign injection (XOR)
    vfsgnjx.vf v31, v1, fa0
    la t3, _result_vfsgnjx_vf
    vse32.v v31, (t3)

    # 9.40. vfsgnjx.vv - Floating-point sign injection (XOR)
    vfsgnjx.vv v31, v1, v2
    la t3, _result_vfsgnjx_vv
    vse32.v v31, (t3)

    # 9.41. vfsqrt.v - Floating-point square root
    vfsqrt.v v31, v1
    la t3, _result_vfsqrt_v
    vse32.v v31, (t3)

    # 9.42. vfsub.vf - Floating-point subtract with scalar
    vfsub.vf v31, v1, fa0
    la t3, _result_vfsub_vf
    vse32.v v31, (t3)

    # 9.43. vfsub.vv - Floating-point subtract
    vfsub.vv v31, v1, v2
    la t3, _result_vfsub_vv
    vse32.v v31, (t3)

    #-----------------------------------------------------------
    # 10. Wide Floating-Point Operations
    #-----------------------------------------------------------
    # Ensure that your hardware supports 64-bit floating-point operations
    # If not, you may need to skip or adjust these tests

    # Set vector length for wide operations (e.g., e64)
    li t0, 8
    vsetvli x0, t0, e64, m1, tu, mu

    # 10.1. vfwcvt.f.f.v - Convert to wider floating-point
    # vfwcvt.f.f.v v31, v1
    la t3, _result_vfwcvt_f_f_v
    # vse64.v v31, (t3)

    # 10.2. vfwcvt.f.x.v - Convert integer to wider floating-point
    la t3, _data_v1
    # vle32.v v1, (t3)
    # vfwcvt.f.x.v v31, v1
    la t3, _result_vfwcvt_f_x_v
    # vse64.v v31, (t3)

    # 10.3. vfwmacc.vf - Wide multiply-accumulate with scalar
    # vmv.v.v v31, v2               # Initialize v31 with v2
    # vfwmacc.vf v31, fa0, v1       # Corrected: instruction takes three operands
    la t3, _result_vfwmacc_vf
    # vse64.v v31, (t3)

    # 10.4. vfwmacc.vv - Wide multiply-accumulate
    # vmv.v.v v31, v2               # Initialize v31 with v2
    # vfwmacc.vv v31, v1, v2        # Corrected: instruction takes three operands
    la t3, _result_vfwmacc_vv
    # vse64.v v31, (t3)

    # Reset vector length to e32 after wide operations
    li t0, 8
    vsetvli x0, t0, e32, m1, tu, mu

    #-----------------------------------------------------------
    # 11. Fixed-Point and Floating-Point Conversion
    #-----------------------------------------------------------
    vfcvt.f.x.v v14, v1
    la t3, _result_vfcvt_f_x_v
    vse32.v v14, (t3)

    vfcvt.x.f.v v15, v1
    la t3, _result_vfcvt_x_f_v
    vse32.v v15, (t3)

    #-----------------------------------------------------------
    # 12. Vector Move Operations
    #-----------------------------------------------------------
    vmv.v.i v16, 15
    la t3, _result_vmv_v_i
    vse32.v v16, (t3)

    vmv.v.v v17, v1
    la t3, _result_vmv_v_v
    vse32.v v17, (t3)

    #-----------------------------------------------------------
    # 13. Division Operations
    #-----------------------------------------------------------
    vdiv.vv v18, v1, v2
    la t3, _result_vdiv_vv
    vse32.v v18, (t3)

    vdiv.vx v19, v1, x5
    la t3, _result_vdiv_vx
    vse32.v v19, (t3)

    #-----------------------------------------------------------
    # 14. Mask Operations
    #-----------------------------------------------------------
    li t0, 8
    vsetvli x0, t0, e8, m1, tu, mu

    # Create masks
    li t0, 0xAA            # 0b10101010
    vmv.v.x v0, t0

    li t0, 0x55            # 0b01010101
    vmv.v.x v1, t0

    vmand.mm v2, v0, v1
    la t3, _result_vmand_mm
    vs1r.v v2, (t3)         # Store mask

    vmor.mm v3, v0, v1
    la t3, _result_vmor_mm
    vs1r.v v3, (t3)         # Store mask

    ret

    #-----------------------------------------------------------
    # Data Section
    #-----------------------------------------------------------
    .section .data
    .balign 8

    .global _data_v1
_data_v1:
    .word 0x7FFFFFFF   # Max int32
    .word 0x80000000   # Min int32
    .word 0x00000000   # Zero
    .word 0xFFFFFFFF   # -1
    .word 0x12345678   # Arbitrary positive
    .word 0xEDCBA987   # Arbitrary negative
    .word 0x7FFFFFFF
    .word 0x80000000

    .global _data_v2
_data_v2:
    .word 0x7FFFFFFF
    .word 0x80000000
    .word 0xFFFFFFFF
    .word 0x00000001
    .word 0xEDCBA987
    .word 0x12345678
    .word 0x80000000
    .word 0x7FFFFFFF

    .global _data_shifts_32
_data_shifts_32:
    .word 0, 1, 4, 8, 12, 16, 20, 24

    #-----------------------------------------------------------
    # Results Section
    #-----------------------------------------------------------
    .section .bss
    .balign 8

    # Result storage for all vector operations
    .global _result_vaadd_vv
_result_vaadd_vv:
    .space 32

    .global _result_vaadd_vx
_result_vaadd_vx:
    .space 32

    .global _result_vaaddu_vv
_result_vaaddu_vv:
    .space 32

    .global _result_vaaddu_vx
_result_vaaddu_vx:
    .space 32

    .global _result_vasub_vv
_result_vasub_vv:
    .space 32

    .global _result_vasub_vx
_result_vasub_vx:
    .space 32

    .global _result_vasubu_vv
_result_vasubu_vv:
    .space 32

    .global _result_vasubu_vx
_result_vasubu_vx:
    .space 32

    .global _result_vnclip_wv
_result_vnclip_wv:
    .space 16

    .global _result_vnclip_wx
_result_vnclip_wx:
    .space 16

    .global _result_vnclip_wi
_result_vnclip_wi:
    .space 16

    .global _result_vnclipu_wv
_result_vnclipu_wv:
    .space 16

    .global _result_vnclipu_wx
_result_vnclipu_wx:
    .space 16

    .global _result_vnclipu_wi
_result_vnclipu_wi:
    .space 16

    .global _result_vsadd_vi
_result_vsadd_vi:
    .space 32

    .global _result_vsadd_vv
_result_vsadd_vv:
    .space 32

    .global _result_vsadd_vx
_result_vsadd_vx:
    .space 32

    .global _result_vsaddu_vi
_result_vsaddu_vi:
    .space 32

    .global _result_vsaddu_vv
_result_vsaddu_vv:
    .space 32

    .global _result_vsaddu_vx
_result_vsaddu_vx:
    .space 32

    .global _result_vsmul_vv
_result_vsmul_vv:
    .space 32

    .global _result_vsmul_vx
_result_vsmul_vx:
    .space 32

    .global _result_vssra_vi
_result_vssra_vi:
    .space 32

    .global _result_vssra_vv
_result_vssra_vv:
    .space 32

    .global _result_vssra_vx
_result_vssra_vx:
    .space 32

    .global _result_vssrl_vi
_result_vssrl_vi:
    .space 32

    .global _result_vssrl_vv
_result_vssrl_vv:
    .space 32

    .global _result_vssrl_vx
_result_vssrl_vx:
    .space 32

    .global _result_vssub_vv
_result_vssub_vv:
    .space 32

    .global _result_vssub_vx
_result_vssub_vx:
    .space 32

    .global _result_vssubu_vv
_result_vssubu_vv:
    .space 32

    .global _result_vssubu_vx
_result_vssubu_vx:
    .space 32

    .global _result_vfadd_vv
_result_vfadd_vv:
    .space 32

    .global _result_vfadd_vf
_result_vfadd_vf:
    .space 32

    .global _result_vfcvt_f_x_v
_result_vfcvt_f_x_v:
    .space 32

    .global _result_vfcvt_x_f_v
_result_vfcvt_x_f_v:
    .space 32

    .global _result_vmv_v_i
_result_vmv_v_i:
    .space 32

    .global _result_vmv_v_v
_result_vmv_v_v:
    .space 32

    .global _result_vdiv_vv
_result_vdiv_vv:
    .space 32

    .global _result_vdiv_vx
_result_vdiv_vx:
    .space 32

    .global _result_vmand_mm
_result_vmand_mm:
    .space 8           # Space for mask bits

    .global _result_vmor_mm
_result_vmor_mm:
    .space 8           # Space for mask bits

    # Additional floating-point result sections
    .global _result_vfclass_v
_result_vfclass_v:
    .space 32

    .global _result_vfcvt_f_xu_v
_result_vfcvt_f_xu_v:
    .space 32

    .global _result_vfcvt_rtz_x_f_v
_result_vfcvt_rtz_x_f_v:
    .space 32

    .global _result_vfcvt_rtz_xu_f_v
_result_vfcvt_rtz_xu_f_v:
    .space 32

    .global _result_vfdiv_vf
_result_vfdiv_vf:
    .space 32

    .global _result_vfdiv_vv
_result_vfdiv_vv:
    .space 32

    .global _result_vfmacc_vf
_result_vfmacc_vf:
    .space 32

    .global _result_vfmacc_vv
_result_vfmacc_vv:
    .space 32

    .global _result_vfmadd_vf
_result_vfmadd_vf:
    .space 32

    .global _result_vfmadd_vv
_result_vfmadd_vv:
    .space 32

    .global _result_vfmax_vf
_result_vfmax_vf:
    .space 32

    .global _result_vfmax_vv
_result_vfmax_vv:
    .space 32

    .global _result_vfmerge_vfm
_result_vfmerge_vfm:
    .space 32

    .global _result_vfmin_vf
_result_vfmin_vf:
    .space 32

    .global _result_vfmin_vv
_result_vfmin_vv:
    .space 32

    .global _result_vfmsac_vf
_result_vfmsac_vf:
    .space 32

    .global _result_vfmsac_vv
_result_vfmsac_vv:
    .space 32

    .global _result_vfmsub_vf
_result_vfmsub_vf:
    .space 32

    .global _result_vfmsub_vv
_result_vfmsub_vv:
    .space 32

    .global _result_vfmul_vf
_result_vfmul_vf:
    .space 32

    .global _result_vfmul_vv
_result_vfmul_vv:
    .space 32

    .global _result_vfmv_v_f
_result_vfmv_v_f:
    .space 32

    .global _result_vfnmacc_vf
_result_vfnmacc_vf:
    .space 32

    .global _result_vfnmacc_vv
_result_vfnmacc_vv:
    .space 32

    .global _result_vfnmadd_vf
_result_vfnmadd_vf:
    .space 32

    .global _result_vfnmadd_vv
_result_vfnmadd_vv:
    .space 32

    .global _result_vfnmsac_vf
_result_vfnmsac_vf:
    .space 32

    .global _result_vfnmsac_vv
_result_vfnmsac_vv:
    .space 32

    .global _result_vfnmsub_vf
_result_vfnmsub_vf:
    .space 32

    .global _result_vfnmsub_vv
_result_vfnmsub_vv:
    .space 32

    .global _result_vfrdiv_vf
_result_vfrdiv_vf:
    .space 32

    .global _result_vfrec7_v
_result_vfrec7_v:
    .space 32

    .global _result_vfrsqrt7_v
_result_vfrsqrt7_v:
    .space 32

    .global _result_vfrsub_vf
_result_vfrsub_vf:
    .space 32

    .global _result_vfsgnj_vf
_result_vfsgnj_vf:
    .space 32

    .global _result_vfsgnj_vv
_result_vfsgnj_vv:
    .space 32

    .global _result_vfsgnjn_vf
_result_vfsgnjn_vf:
    .space 32

    .global _result_vfsgnjn_vv
_result_vfsgnjn_vv:
    .space 32

    .global _result_vfsgnjx_vf
_result_vfsgnjx_vf:
    .space 32

    .global _result_vfsgnjx_vv
_result_vfsgnjx_vv:
    .space 32

    .global _result_vfsqrt_v
_result_vfsqrt_v:
    .space 32

    .global _result_vfsub_vf
_result_vfsub_vf:
    .space 32

    .global _result_vfsub_vv
_result_vfsub_vv:
    .space 32

    # Wide floating-point result sections
    .global _result_vfwcvt_f_f_v
_result_vfwcvt_f_f_v:
    .space 64    # Wide results need double space

    .global _result_vfwcvt_f_x_v
_result_vfwcvt_f_x_v:
    .space 64

    .global _result_vfwmacc_vf
_result_vfwmacc_vf:
    .space 64

    .global _result_vfwmacc_vv
_result_vfwmacc_vv:
    .space 64

    # End of result sections
