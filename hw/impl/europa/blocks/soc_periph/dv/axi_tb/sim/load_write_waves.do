onerror resume
wave tags F0
wave update off
wave zoom range 0 7790000
wave add {axi_stress_top_tb.th.axi_if.master_if[0].awvalid} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].awready} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].awid} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].awaddr} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].bready} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].bvalid} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].bid} -tag F0 -radix hexadecimal -select
wave add {axi_stress_top_tb.th.axi_if.master_if[0].bresp} -tag F0 -radix hexadecimal
wave update on
wave top 0
