What to remember!:
Set initial mode with +boot_mode=m|s|u, otherwise its random :)

Ratios are done in a pretty dumb way:
1)
    +illegal_instr_ratio=5
This means 5 out of 1k instructions will be illegal/malformed. So for 10k instr_cnt you get 50.
2)
    +directed_instr_0=riscv_int_numeric_corner_stream,5
This one on the other hand inserts 5 streams per 1k instructions, if we look at source code, each stream is in (15,30) range, so for 10k we'll get 5*10*(15,30)=750 to 1500 instructions

What only work if:
1)
    +enable_misaligned_instr=1
Only works if +num_of_subprogram > 1, because it generates misaligned jumps to subprograms only, probably for controllable starts in these programs.
A specially crafted next instruction will be the addi sp +2 if decoded as misaligned???

What doesn't work:
1)
    +enable_misaligned_instr=1
    +illegal_instr_ratio=5
Since first option generates misaligned jumps to subprograms only, there could be a case where it will be a illegal instruction that will cause a deadlock in exception handler and program go crazy.

Notes:
1) If core supports compressed instructions, it's impossible to exercise instruction misaligned exception?
