interface i2c_master_if;
  logic wb_clk_i;        // master clock input
  logic arst_i;          // asynchronous reset
  logic [2:0] wb_adr_i;  // lower address bits
  logic [7:0] wb_dat_i;  // databus input
  logic [7:0] wb_dat_o;  // databus output
  logic wb_we_i;         // write enable input
  logic wb_stb_i;        // stobe/core select signal
  logic wb_cyc_i;        // valid bus cycle input
  logic wb_ack_o;        // bus cycle acknowledge output
  logic wb_inta_o;       // interrupt request signal output

  // I2C signals
  // i2c clock line
  logic scl_pad_i;    // SCL-line input
  logic scl_pad_o;    // SCL-line output (always 1'b0)
  logic scl_padoen_o; // SCL-line output enable  (active low)

  // i2c data line
  logic sda_pad_i;    // SDA-line input
  logic sda_pad_o;    // SDA-line output (always 1'b0)
  logic sda_padoen_o; // SDA-line output enable  (active low)

  // Tasks to use the wishbone bus to read and write to the register interface

  clocking cb_wb @(posedge wb_clk_i);
    output wb_we_i;
    output wb_cyc_i;
    output wb_stb_i;
    output wb_dat_i;
    output wb_adr_i;
    input wb_dat_o;
    input wb_ack_o;
  endclocking

  task automatic read_reg(input logic [2:0] addr, output logic [7:0] data);
    cb_wb.wb_we_i <= 1'b0;
    cb_wb.wb_cyc_i <= 1'b1;
    cb_wb.wb_stb_i <= 1'b1;
    cb_wb.wb_adr_i <= addr;
    do begin
      @(cb_wb);
    end while(cb_wb.wb_ack_o !== 1'b1);
    data = cb_wb.wb_dat_o;
    cb_wb.wb_cyc_i <= 1'b0;
    cb_wb.wb_stb_i <= 1'b0;
    do begin
      @(cb_wb);
    end while(cb_wb.wb_ack_o !== 1'b0);
  endtask

  task automatic write_reg(input logic [2:0] addr, input logic [7:0] data);
    cb_wb.wb_we_i <= 1'b1;
    cb_wb.wb_cyc_i <= 1'b1;
    cb_wb.wb_stb_i <= 1'b1;
    cb_wb.wb_adr_i <= addr;
    cb_wb.wb_dat_i <= data;
    do begin
      @(cb_wb);
    end while(cb_wb.wb_ack_o !== 1'b1);
    cb_wb.wb_cyc_i <= 1'b0;
    cb_wb.wb_stb_i <= 1'b0;
    do begin
      @(cb_wb);
    end while(cb_wb.wb_ack_o !== 1'b0);
  endtask
endinterface
