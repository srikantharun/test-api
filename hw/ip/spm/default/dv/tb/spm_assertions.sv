`ifndef SPM_SVA
`define SPM_SVA

module spm_assertions
  (
    input wire                          clk,
    input wire                          rst_n,

    input spm_pkg::spm_error_status_t   spm_scp_error_status,
    input wire                          spm_irq,
    input wire                          spm_scp_ecc_disable
   );




    property irq_is_never_deasserted_p;
        @(posedge clk) disable iff (!rst_n | spm_scp_ecc_disable)
        spm_irq
        |=> spm_irq;
    endproperty

    irq_is_never_deasserted_a: assert property (irq_is_never_deasserted_p) else $display("Error: irq qas 1 and it went to 0 without reset");


endmodule // spm_assertions

`endif //SPM_SVA
