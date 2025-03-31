// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DPI tc_sram
// Owner: Domenic Wüthrich <domenic.wuethrich@axelera.ai>

module mini_soc_tc_sram #(
  parameter int unsigned NumWords     = 32'd1024, // Number of Words in data array
  parameter int unsigned DataWidth    = 32'd128,  // Data signal width
  parameter int unsigned ByteWidth    = 32'd8,    // Width of a data byte
  parameter int unsigned NumPorts     = 32'd2,    // Number of read and write ports
  parameter int unsigned Latency      = 32'd1,    // Latency when the read data is available
  parameter              SimInit      = "none",   // Simulation initialization
  parameter bit          PrintSimCfg  = 1'b0,     // Print configuration
  parameter              ImplKey      = "none",   // Reference to specific implementation
  // DEPENDENT PARAMETERS, DO NOT OVERWRITE!
  parameter int unsigned AddrWidth    = (NumWords > 32'd1) ? $clog2(NumWords) : 32'd1,
  parameter int unsigned BeWidth      = (DataWidth + ByteWidth - 32'd1) / ByteWidth, // ceil_div
  parameter type         addr_t       = logic [AddrWidth-1:0],
  parameter type         data_t       = logic [DataWidth-1:0],
  parameter type         be_t         = logic [BeWidth-1:0],
  parameter int          BusAlign     = $clog2(BeWidth)
) (
  input  logic                 clk_i,      // Clock
  input  logic                 rst_ni,     // Asynchronous reset active low
  // input ports
  input  logic  [NumPorts-1:0] req_i,      // request
  input  logic  [NumPorts-1:0] we_i,       // write enable
  input  addr_t [NumPorts-1:0] addr_i,     // request address
  input  data_t [NumPorts-1:0] wdata_i,    // write data
  input  be_t   [NumPorts-1:0] be_i,       // write byte enable
  // output ports
  output data_t [NumPorts-1:0] rdata_o,    // read data
  input  longint               addr_offset_i
);


  import "DPI-C" function void tb_memory_read(
      input longint addr,
      input int len,
      output byte data[]
  );
  import "DPI-C" function void tb_memory_write(
      input longint addr,
      input int len,
      input byte data[],
      input bit strb[]
  );

  initial begin : sanity_check
    if (SimInit != "none") begin
      $fatal(0, "SimInit not supported yet");
    end

    if (ByteWidth != 8) begin
      $fatal(0, "ByteWidth != 8 not supported yet");
    end

    if (Latency == 0) begin
      $fatal(0, "Latency of `0` not supported yet");
    end
  end

  data_t [NumPorts-1:0] rdata;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      for (int i = 0; i < NumPorts; i++) begin
        rdata[i] <= '0;
      end
    end else begin

      for (int unsigned i = 0; i < NumPorts; i++) begin
        if (req_i[i]) begin
          automatic byte data[BeWidth];
          automatic longint addr;
          automatic bit strb[BeWidth];

          addr = longint'(addr_i[i]) << BusAlign;
          addr += addr_offset_i;
          ///////////
          // Write //
          ///////////
          if (we_i[i]) begin
            for (int j = 0; j < BeWidth; j++) begin
              data[j] = wdata_i[i][j*8+:8];
              strb[j] = be_i[i][j];
            end
            // $display("[SRAM] Write addr=%x data=%x", addr, wdata_i);
            // update value when write is set at clock
            tb_memory_write(addr, BeWidth, data, strb);
          ///////////
          // READ //
          //////////
          end else begin
            tb_memory_read(addr, BeWidth, data);
            for (int j = 0; j < BeWidth; j++) rdata[i][j*8+:8] <= data[j];
            // $display("[SRAM] Read addr=%x data=%x", addr, rdata[i]);
          end
        end
      end
    end
  end
  for (genvar i = 0; i < NumPorts; i++) begin : gen_rdata_delay
    cva6v_shift_reg #(
      .dtype  ( data_t      ),
      .Depth  ( Latency - 1 )
    ) i_rdata_shift_reg (
      .clk_i  ( clk_i       ),
      .rst_ni ( rst_ni      ),
      .d_i    ( rdata[i]    ),
      .d_o    ( rdata_o[i]  )
    );
  end

endmodule
