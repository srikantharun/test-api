onerror resume
wave tags  F1
wave update off
wave zoom range 0 930000
wave spacer -backgroundcolor Salmon {Write signals}
wave add {spike_top_tb.th.axi_if.master_if[0].aresetn} -tag F1 -radix hexadecimal -select
wave add {spike_top_tb.th.axi_if.master_if[0].awvalid} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].awaddr} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].awlen} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].awsize} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].awid} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].awready} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].wvalid} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].wlast} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].wdata} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].wstrb} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].wready} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].wid} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].bvalid} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].bresp} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].bid} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].bready} -tag F1 -radix hexadecimal
wave spacer {}
wave spacer -backgroundcolor Salmon {Read signals}
wave add {spike_top_tb.th.axi_if.master_if[0].arvalid} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].araddr} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].arlen} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].arsize} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].arburst} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].arlock} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].arcache} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].arprot} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].arid} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].arready} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].rvalid} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].rlast} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].rdata} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].rresp} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].rid} -tag F1 -radix hexadecimal
wave add {spike_top_tb.th.axi_if.master_if[0].rready} -tag F1 -radix hexadecimal
wave update on
wave top 0
