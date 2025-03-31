<%page args="ignore_ports"/>\
<%
dft_sig = []
if dft == "default":
    dft_sig = [
        ("ijtag_tck",          "input  wire ",  1),
        ("ijtag_reset",        "input  wire ",  1),
        ("ijtag_sel",          "input  logic",  1),
        ("ijtag_ue",           "input  logic",  1),
        ("ijtag_se",           "input  logic",  1),
        ("ijtag_ce",           "input  logic",  1),
        ("ijtag_si",           "input  logic",  1),
        ("ijtag_so",           "output logic",  1),
        ("test_clk",           "input  wire ",  1),
        ("test_mode",          "input  logic",  1),
        ("edt_update",         "input  logic",  1),
        ("scan_en",            "input  logic",  1),
        ("scan_in",            "input  logic",  8),
        ("scan_out",           "output logic",  8),
        ("bisr_clk",           "input  wire ",  1),
        ("bisr_reset",         "input  wire ",  1),
        ("bisr_shift_en",      "input  logic",  1),
        ("bisr_si",            "input  logic",  1),
        ("bisr_so",            "output logic",  1)
    ]
elif dft == "no_mem":
    dft_sig = [
        ("ijtag_tck",          "input  wire ",  1),
        ("ijtag_reset",        "input  wire ",  1),
        ("ijtag_sel",          "input  logic",  1),
        ("ijtag_ue",           "input  logic",  1),
        ("ijtag_se",           "input  logic",  1),
        ("ijtag_ce",           "input  logic",  1),
        ("ijtag_si",           "input  logic",  1),
        ("ijtag_so",           "output logic",  1),
        ("test_clk",           "input  wire ",  1),
        ("test_mode",          "input  logic",  1),
        ("edt_update",         "input  logic",  1),
        ("scan_en",            "input  logic",  1),
        ("scan_in",            "input  logic",  8),
        ("scan_out",           "output logic",  8)
    ]
elif dft == "ssn":
    dft_sig = [
        ("ijtag_tck",          "input  wire ",  1),
        ("ijtag_reset",        "input  wire ",  1),
        ("ijtag_sel",          "input  logic",  1),
        ("ijtag_ue",           "input  logic",  1),
        ("ijtag_se",           "input  logic",  1),
        ("ijtag_ce",           "input  logic",  1),
        ("ijtag_si",           "input  logic",  1),
        ("ijtag_so",           "output logic",  1),
        ("ssn_bus_clk",        "input  wire ",  1),
        ("ssn_bus_data_in",    "input  logic",  25),
        ("ssn_bus_data_out",   "input  logic",  25),
        ("bisr_clk",           "input  wire ",  1),
        ("bisr_reset",         "input  wire ",  1),
        ("bisr_shift_en",      "input  logic",  1),
        ("bisr_si",            "input  logic",  1),
        ("bisr_so",            "output logic",  1)
    ]
%>
  //-------------------------------
  // DFT Interface
  //-------------------------------
% for sig_item in dft_sig:
<%
  sig_dir = sig_item[1]
  sig_name = sig_item[0]
  sig_width = ""
  if sig_item[2] > 1:
    sig_width = f'[{sig_item[2]}-1: 0]'
  last = "" if loop.last else ","
%>\
% if sig_name not in ignore_ports:
  ${sig_dir} ${sig_width} ${sig_name}${last}
%endif
%endfor
