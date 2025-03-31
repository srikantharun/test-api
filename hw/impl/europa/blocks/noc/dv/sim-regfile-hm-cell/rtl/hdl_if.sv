interface noc_mem_rd_if #(int unsigned DATAW=1, int unsigned ADDRW=1) (input bit clk, input bit rst_n);

    logic             en;
    logic [ADDRW-1:0] addr;
    logic [DATAW-1:0] data;

endinterface : noc_mem_rd_if

interface noc_mem_wr_if #(int unsigned DATAW=1, int unsigned ADDRW=1) (input bit clk, input bit rst_n);

    logic             en;
    logic [ADDRW-1:0] addr;
    logic [DATAW-1:0] data;
    logic [DATAW-1:0] ben;

endinterface : noc_mem_wr_if
