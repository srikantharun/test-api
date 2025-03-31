`ifndef SPM_UTILS_SV
`define SPM_UTILS_SV

typedef struct {
    int b_idx;
    int sb_idx;
    int mb_idx;
    int sr_idx;
    bit [12:0] addr;
} spm_indexes_t;

function automatic spm_indexes_t get_aic_spm_mem_idx(bit [63:0] addr);
  spm_indexes_t spm_idxs;
  // The addrs is composed like following:
  // [18] bank sel
  // [17] minibank sel
  // [16] cell sel
  // [15:3] cell line address
  // [2:0] byte addressing inside the 64bline

  // address inside the cell
  spm_idxs.addr = addr[15:3];

  // sram idx, 2 sram cells
  spm_idxs.sr_idx = addr[16];

  // minib idx, 2 minibanks
  spm_idxs.mb_idx = addr[17];

  // subbank idx, 1 subbank
  spm_idxs.sb_idx = 0;

  // bank idx, 2 banks
  spm_idxs.b_idx = addr[18];

  return spm_idxs;
endfunction : get_aic_spm_mem_idx

function automatic spm_indexes_t get_pve_spm_mem_idx(bit [63:0] addr);
  spm_indexes_t spm_idxs;
  // The addrs is composed like following:
  // [17] bank sel
  // [16] subbank sel
  // [15] minibank sel
  // [14] cell sel
  // [13:3] cell line address
  // [2:0] byte addressing inside the 64bline

  // address insie the cell
  spm_idxs.addr = addr[13:3];

  // sram idx, 2 sram cells
  spm_idxs.sr_idx = addr[14];

  // minib idx, 2 minibanks
  spm_idxs.mb_idx = addr[15];

  // subbank idx, 2 subbanks
  spm_idxs.sb_idx = addr[16];

  // bank idx, 2 banks
  spm_idxs.b_idx = addr[17];

  return spm_idxs;
endfunction : get_pve_spm_mem_idx

function automatic spm_indexes_t get_sys_spm_mem_idx(bit [63:0] addr);
  spm_indexes_t spm_idxs;
  // The addrs is composed like following:
  // [22:21] bank sel
  // [20:19] subbank sel
  // [18:17] minibank sel
  // [16] cell sel
  // [15:3] cell line address
  // [2:0] byte addressing inside the 64bline

  // address inside the cell
  spm_idxs.addr = addr[15:3];

  // sram idx, 2 sram cells
  spm_idxs.sr_idx = addr[16];

  // minib idx, 2 minibanks
  spm_idxs.mb_idx = addr[18:17];

  // subbank idx, 2 subbanks
  spm_idxs.sb_idx = addr[20:19];

  // bank idx, 2 banks
  spm_idxs.b_idx = addr[22:21];

  return spm_idxs;
endfunction: get_sys_spm_mem_idx

function automatic logic [71:0] add_spm_ecc (logic [63:0] data_wo_ecc);
  logic [71:0] data_w_ecc;

  data_w_ecc = 72'(data_wo_ecc);

  data_w_ecc[64] = 1'b0 ^ ^(data_w_ecc & 72'h00B9000000001FFFFF);
  data_w_ecc[65] = 1'b0 ^ ^(data_w_ecc & 72'h005E00000FFFE0003F);
  data_w_ecc[66] = 1'b0 ^ ^(data_w_ecc & 72'h0067003FF003E007C1);
  data_w_ecc[67] = 1'b0 ^ ^(data_w_ecc & 72'h00CD0FC0F03C207842);
  data_w_ecc[68] = 1'b0 ^ ^(data_w_ecc & 72'h00B671C711C4438884);
  data_w_ecc[69] = 1'b0 ^ ^(data_w_ecc & 72'h00B5B65926488C9108);
  data_w_ecc[70] = 1'b0 ^ ^(data_w_ecc & 72'h00CBDAAA4A91152210);
  data_w_ecc[71] = 1'b0 ^ ^(data_w_ecc & 72'h007AED348D221A4420);

  return data_w_ecc;
endfunction

`endif // SPM_UTILS_SV
