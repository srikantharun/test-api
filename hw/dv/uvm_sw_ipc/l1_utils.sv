`ifndef L1_UTILS_SV
`define L1_UTILS_SV

typedef struct {
        int sb_idx;
        int mb_idx;
        bit msb_half;
        bit [11:0] addr;
    } aic_l1_indexes_t;

function static aic_l1_indexes_t get_l1_mem_idx(bit [63:0] addr);
    aic_l1_indexes_t l1_idxs;
    bit [63:0] temp;

    // The addrs is composed like following:
    // [21:10] cell line address
    // [9:6] minibank sel
    // [5:4] subbank sel
    // [3:0] byte addressing inside the 128bline


    //if the address is in the first 64 or in the second 64 bits
    l1_idxs.msb_half = addr[3];

    // address used to define the line in the cell
    l1_idxs.addr = addr[21:10];

    // minib idx, 16 minibaks
    l1_idxs.mb_idx = addr[9:6];

    // bank idx, 4 banks
    l1_idxs.sb_idx = addr[5:4];

    return l1_idxs;
  endfunction : get_l1_mem_idx


`endif // L1_UTILS_SV
