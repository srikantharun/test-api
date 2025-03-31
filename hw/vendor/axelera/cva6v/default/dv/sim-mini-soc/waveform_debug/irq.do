onerror resume
wave tags sim
wave update off
wave zoom range 0 7773668
wave add hdl_top.i_rvvi_tracer.irq_trap_taken_cnt -tag sim -radix decimal
wave add hdl_top.i_rvvi_tracer.irq_trap_idxs -tag sim -radix decimal
wave add hdl_top.i_rvvi_tracer.irq_trap_taken_state -tag sim -radix hexadecimal
wave add hdl_top.i_rvvi_tracer.start_irq_driving -tag sim -radix hexadecimal
wave add hdl_top.i_rvvi_tracer.end_irq_driving -tag sim -radix hexadecimal
wave add hdl_top.irq_tb_line -tag sim -radix hexadecimal
wave add hdl_top.tb_exit_o -tag sim -radix hexadecimal
wave add {hdl_top.i_gc_system.irq[0]} -tag sim -radix hexadecimal -subitemconfig { {hdl_top.i_gc_system.irq[0][1]} {-radix hexadecimal} {hdl_top.i_gc_system.irq[0][0]} {-radix hexadecimal} } -select
wave add {hdl_top.i_gc_system.platform_irq[0]} -tag sim -radix hexadecimal -select
wave add hdl_top.dump_mstatus -tag sim -radix hexadecimal
wave add hdl_top.dump_mie -tag sim -radix hexadecimal
wave add hdl_top.dump_mip -tag sim -radix hexadecimal
wave add hdl_top.dump_mepc -tag sim -radix hexadecimal
wave add hdl_top.dump_mcause -tag sim -radix hexadecimal
wave add hdl_top.dump_mtval -tag sim -radix hexadecimal
wave add hdl_top.dump_mtvec -tag sim -radix hexadecimal
wave add hdl_top.dump_mideleg -tag sim -radix hexadecimal
wave group {hdl_top.rvvi_dump_if[0]} -backgroundcolor #004466
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].XLEN} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].FLEN} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].VLEN} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].CSR_NUM} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].clk_i} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].rst_ni} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].valid} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].order} -tag sim -radix decimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].insn} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].trap} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].debug_mode} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].pc_rdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].x_wdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].x_wb} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].f_wdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].f_wb} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].v_wdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].v_wb} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].csr} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].csr_wb} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].lrsc_cancel} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].pc_wdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].intr} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].halt} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].ixl} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[0]} {hdl_top.rvvi_dump_if[0].mode} -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group {hdl_top.rvvi_dump_if[1]} -backgroundcolor #006666
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].XLEN} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].FLEN} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].VLEN} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].CSR_NUM} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].clk_i} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].rst_ni} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].valid} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].order} -tag sim -radix decimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].insn} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].trap} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].debug_mode} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].pc_rdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].x_wdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].x_wb} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].f_wdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].f_wb} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].v_wdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].v_wb} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].csr} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].csr_wb} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].lrsc_cancel} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].pc_wdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].intr} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].halt} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].ixl} -tag sim -radix hexadecimal
wave add -group {hdl_top.rvvi_dump_if[1]} {hdl_top.rvvi_dump_if[1].mode} -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave update on
wave top 0
