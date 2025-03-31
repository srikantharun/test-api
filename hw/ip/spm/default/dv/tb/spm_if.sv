 /* Abstract:
 * This is a passive interface. It will be used for monitoring error irq and
 * to probe signals for coverage.
 */
`ifndef GUARD_SPM_IF_SVI
`define GUARD_SPM_IF_SVI

interface spm_if();
    import spm_pkg::*;

    logic               spm_if_clk;
    logic               spm_if_rst_n;
    logic               spm_if_scp_ecc_disable;
    spm_error_status_t  spm_if_scp_error_status;
    logic               spm_if_irq;


endinterface
`endif // GUARD_SPM_IF_SVI

