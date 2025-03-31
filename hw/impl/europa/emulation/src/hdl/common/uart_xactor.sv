module uart_xactor #(
    parameter CLK_SAMPLES = 4,
    parameter SERVER_PING_CYCLES = CLK_SAMPLES * 100,
    parameter int server_idx = 0
) (
    input clk,
    input rx,
    output reg tx
);

`ifndef UART_XACTOR_NO_DPI
  import "DPI-C" context task dpi_uart_start_server(int idx);
  import "DPI-C" function int dpi_uart_get_char(
    input int idx,
    output bit [1*8-1:0] chars
  );
  import "DPI-C" function void dpi_uart_send_char(
    input int idx,
    input bit [1*8-1:0] chars
  );
`endif


  int fp;
  string filename;
  bit server_has_started = 0;
  initial begin
    tx = 1;
    filename = $sformatf("uart_%0d.log", server_idx);
    fp = $fopen(filename, "w");
`ifndef UART_XACTOR_NO_DPI
    dpi_uart_start_server(server_idx);
    server_has_started = 1;
`endif
  end

  task wait_n_cycles(int n);
    repeat (n) begin
      @(posedge clk);
    end
  endtask


  //-----------------------------------------------------------
  // tx: from client to DUT
  //-----------------------------------------------------------
  task send_char(input logic [7:0] c);
    int i;

    // start bit
    tx <= 1'b0;
    wait_n_cycles(CLK_SAMPLES);

    for (i = 0; i < 8; i++) begin
      tx <= c[i];
      wait_n_cycles(CLK_SAMPLES);
    end

    // stop bit
    tx <= 1'b1;
    wait_n_cycles(CLK_SAMPLES);
  endtask

`ifndef UART_XACTOR_NO_DPI
  always @(posedge clk) begin
    if (server_has_started) begin
      bit [7:0] c;
      int char_received;
      char_received = dpi_uart_get_char(server_idx, c);
      if (char_received) begin
        send_char(c);
      end else begin
        wait_n_cycles(SERVER_PING_CYCLES);
      end
    end
  end
`endif


  //-----------------------------------------------------------
  // rx: from DUT to client
  //-----------------------------------------------------------
  bit prev_rx;
  always @(posedge clk) begin
    prev_rx <= rx;
  end

  always @(posedge clk) begin
    bit [7:0] character;
    receive_char(character);

    // print
    $write("%c", character);
    $fwrite(fp, "%c", character);
    if (character == 8'h0A) begin  // ASCII newline (\n)
      $fflush(fp);
    end
`ifndef UART_XACTOR_NO_DPI
    dpi_uart_send_char(server_idx, character);
`endif
  end

  task receive_char(output bit [7:0] character);
    // stop: detect rx negedge
    while (!(prev_rx && !rx)) begin
      @(posedge clk);
    end

    // start
    wait_n_cycles(CLK_SAMPLES);

    // data
    for (int i = 0; i <= 7; i++) begin
      wait_n_cycles(CLK_SAMPLES >> 1);
      character[i] <= rx;
      wait_n_cycles(CLK_SAMPLES >> 1);
    end
  endtask
endmodule
