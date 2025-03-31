`ifndef PRELOAD_EMMC_SOFTMODEL_SV
`define PRELOAD_EMMC_SOFTMODEL_SV

function automatic string get_plusarg(string arg_name, bit fatal = 0);
  string value;
  if (!$value$plusargs($sformatf("%s=%%s", arg_name), value)) begin
    string message = $sformatf("%s was not provided!", arg_name);
    if (fatal) begin
      `uvm_fatal("emmc_preload", message)
    end else begin
      `uvm_warning("emmc_preload", message)
    end
  end
  return value;
endfunction

// TODO: Add this to preload package ?
function automatic preload_emmc_softmodel();
  string cid_filename = get_plusarg("CID_FILE", 1);
  string csd_filename = get_plusarg("CSD_FILE", 1);
  string ocr_filename = get_plusarg("OCR_FILE", 1);
  string ext_csd_filename = get_plusarg("EXT_CSD_FILE", 1);
  string user_partition_0_filename = get_plusarg("EMMC_USER_0_MEM_0_FILE");
  string user_partition_1_filename = get_plusarg("EMMC_USER_0_MEM_1_FILE");

  $readmemh(cid_filename, i_hdl_top.i_emmc_softmodel.core_0.RESP_GEN_0.CID_0.mem);
  $readmemh(csd_filename, i_hdl_top.i_emmc_softmodel.core_0.RESP_GEN_0.CSD_0.mem);
  $readmemh(ocr_filename, i_hdl_top.i_emmc_softmodel.core_0.RESP_GEN_0.OCR_0.mem);
  $readmemh(ext_csd_filename, i_hdl_top.i_emmc_softmodel.core_0.MFSM_0.Ext_CSD_0.mem);

  if (user_partition_0_filename != "") begin
    $readmemh(user_partition_0_filename, i_hdl_top.i_emmc_softmodel.core_0.EMEM_0.user_0.mem_0);
  end

  if (user_partition_1_filename != "") begin
    $readmemh(user_partition_1_filename, i_hdl_top.i_emmc_softmodel.core_0.EMEM_0.user_0.mem_1);
  end
endfunction

`endif
