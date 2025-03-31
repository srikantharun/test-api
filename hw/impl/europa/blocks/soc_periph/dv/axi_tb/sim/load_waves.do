onerror resume
wave tags  F0
wave update off
wave zoom range 0 930000
wave spacer -backgroundcolor Salmon {Write signals}
wave add {axi_stress_top_tb.th.axi_if.master_if[0].aresetn} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].awvalid} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].awaddr} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].awburst} -tag F0 -radix hexadecimal -select
wave add {axi_stress_top_tb.th.axi_if.master_if[0].awlen} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].awsize} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].awid} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].awready} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].wvalid} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].wlast} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].wdata} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].wstrb} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].wready} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].wid} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].bvalid} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].bresp} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].bid} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].bready} -tag F0 -radix hexadecimal
wave spacer {}
wave spacer -backgroundcolor Salmon {Read signals}
wave add {axi_stress_top_tb.th.axi_if.master_if[0].arvalid} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].araddr} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].arlen} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].arsize} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].arburst} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].arlock} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].arcache} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].arprot} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].arid} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].arready} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].rvalid} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].rlast} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].rdata} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].rresp} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].rid} -tag F0 -radix hexadecimal
wave add {axi_stress_top_tb.th.axi_if.master_if[0].rready} -tag F0 -radix hexadecimal
wave update on
wave top 0
