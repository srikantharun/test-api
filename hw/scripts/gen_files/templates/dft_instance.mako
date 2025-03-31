## DFT Instance
<% 
dftSignals = {
    "i_ijtag_tck": "ijtag_tck",
    "i_ijtag_rst_n": "ijtag_reset",
    "i_ijtag_sel": "ijtag_sel",
    "i_ijtag_ue": "ijtag_ue",
    "i_ijtag_se": "ijtag_se",
    "i_ijtag_ce": "ijtag_ce",
    "ijtag_si": "ijtag_si",
    "i_test_clk": "test_clk",
    "i_edt_update": "edt_update",
    "i_scan_en": "scan_en",
    "i_scan_in": "",  # Placeholder if applicable
    "o_scan_out": ""  # Placeholder if applicable
} 
dftParams = {
  "N_SCAN_CHAINS": 8
}
%>\

%if dft and dftParams and dftSignals:
  dft_wrapper_physblock_top #(
      .N_SCAN_CHAINS (${dftParams["N_SCAN_CHAINS"]})
    ) u_dft_physblock_top (
      %for sig_name, mapped_name in dftSignals.items():
      .${sig_name}(${mapped_name})${',' if not loop.last else ''}
  %endfor
    );
%endif
