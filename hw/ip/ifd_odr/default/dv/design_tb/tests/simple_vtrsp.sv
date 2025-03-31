// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Simple test to verify the functionality of the Vectorized Transpose module (vtrsp)
// Owner: Abhishek Maringanti <Abhishek.Maringanti@axelera.ai>

`ifndef SIMPLE_VTRSP_SV
`define SIMPLE_VTRSP_SV

task vtrsp_test;
  automatic logic [7:0] stream_number = '0;
  automatic integer j = 0;
  wait (tb_rst_n);
  repeat (20) @(posedge tb_clk);

  for (j = 0; j < 1; j = j + 1) begin
    stream_number = stream_number + 1;
    $display("VTRSP: Sending the command no %0d to enable transpose, %0t", j + 1, $time());
    send_cmd(1'b1, 3'b001);

    $display("Sending AXIS Data Stream no: %0d at %0t", stream_number, $time());
    send_axis_data(1, 1);
  end  // for

endtask

task vtrsp_test_mixed;
  automatic integer num_str = 0, pkt_num = 0;
  automatic logic [7:0] stream_number = '0;
  automatic logic [2:0] num_pkts_stream = '0;
  automatic logic [2:0] num_stream = 7; //{$urandom} % 8;
  automatic logic error_enable = 1'b1;

  if (num_stream == 0) num_stream = {$urandom} % 8;
  wait (tb_rst_n);
  repeat (20) @(posedge tb_clk);

  $display("Test parameters: Number of Streams: %0d at time %0t", num_stream, $time());
  for (num_str = 0; num_str < num_stream; num_str = num_str + 1) begin
    // Randomize the number of 64-PW sets in a stream. 
    num_pkts_stream = ({$urandom} % 7) + 1;
    $display("Start of the stream number %0d, containing %0d total number of packets at time %0t",
             num_str + 1, num_pkts_stream, $time());

    stream_number = stream_number + 1;
    //    cmd_mode[0]   = {$urandom} % 2;
    //    cmd_mode[2:1] = {$urandom} % 3;
    cmd_mode = stream_number % 4;
    if (|cmd_mode)
      $display("VTRSP_TB: Sending the command no %0d in Transpose Mode with FP-MODE = %0d, %0t",
               (num_str + 1), cmd_mode[1:0], $time());
    else
      $display("VTRSP_TB: Sending the command no %0d in Bypass Mode, %0t", (num_str + 1), $time());
    send_cmd(1'b1, cmd_mode);

    //    for (pkt_num = 0; pkt_num < num_pkts_stream; pkt_num = pkt_num + 1)
    //    begin
    $display("Sending AXIS Data Stream no: %0d with %0d num of packets at %0t", stream_number,
             num_pkts_stream, $time());
    send_axis_data(num_pkts_stream, cmd_mode);
    //    end // for
  end  // for

endtask

task send_cmd(input cmd_valid, input [2:0] cmd_data);
  begin
    wait (tb_cmd_ready);
    @(posedge tb_clk);
    #0.1;
    tb_cmd_data  = cmd_data;
    tb_cmd_valid = cmd_valid;
    @(posedge tb_clk);
    #0.1;
    tb_cmd_valid = 1'b0;
    $display("Exiting the SEND_CMD TASK");
  end
endtask

task send_axis_data(input logic [7:0] num_pkts_stream, input logic [1:0] mode);
  begin
    automatic integer i = 0;
    automatic integer num_pkts_to_send = 0;
    automatic integer i_data = 0;
    automatic reg [511:0] data = '0;
    automatic integer err_trig = 0;
    automatic integer err_flag_brk = 0;
    automatic integer err_pkt = 0;
    automatic integer num_data = 0;
    error_enable = 0;  //$urandom % 2;
    if (error_enable) begin
      err_trig = $urandom % (aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES - 1);
      err_pkt  = $urandom % (num_pkts_stream - 1);
      $display("Error enabled for current stream, err_pkt: %0d, err_trig: %0d", err_pkt, err_trig,
               $time());
    end
`ifdef DISPLAY_DATA
    $display("VTRSP_TB: Entering the SEND_AXIS_DATA TASK");
`endif
    for (
        num_pkts_to_send = 0;
        num_pkts_to_send < num_pkts_stream;
        num_pkts_to_send = num_pkts_to_send + 1
    ) begin
      check_cmd_mode_mb.put(mode); // store mode for the data checking
      rcv_cmd_mode_mb.put(mode); // store mode for the data checking

      $display("VTRSP_TB: SEND_AXIS_DATA TASK: pkt number: %0d", num_pkts_to_send + 1);
      num_data = ~|mode[1:0] ? aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES : aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES / (2 ** (mode[1:0] - 1));
      for (i = 0; i < num_data; i = i + 1) begin
        @(posedge tb_clk);
        #0.1;
        data = i;
        //      tb_axis_s_tvalid = 1'b1;
        //randomizing the valid signal for the AXI-S Data Stream.
        do begin
          tb_axis_s_tvalid = 1;//$urandom;
          if (~tb_axis_s_tvalid) begin
            @(posedge tb_clk);
            #0.1;
          end
        end while (tb_axis_s_tvalid == 1'b0);

        tb_axis_s_tdata = '0;
        for (i_data = 0; i_data < num_data; i_data = i_data + 1) begin
          data = i_data + num_pkts_to_send + i;
          tb_axis_s_tdata |= (data << 8 * i_data);
          data = '0;
        end

        if ((i == num_data - 1) && (num_pkts_to_send == (num_pkts_stream - 1))) begin
          //        tb_axis_s_tdata  = {64{data}};
          tb_axis_s_tlast = 1'b1;
          $display("VTRSP_TB: pkt number: %0d, setting tb_axis_s_tlast to 1'b1",
                   num_pkts_to_send + 1);
        end else begin
          if (error_enable & (i == err_trig) & (num_pkts_to_send == err_pkt)) begin
            $display("Setting error by enabling tlast", $time());
            tb_axis_s_tlast = 1'b1;
            #0.1 wait (tb_axis_s_tready);
            #0.1 @(posedge tb_clk);
            tb_axis_s_tlast = 1'b0;
            err_flag_brk = 1;
            break;
          end else tb_axis_s_tlast = 1'b0;
        end

        #0.5;
        wait (tb_axis_s_tready == 1'b1);
        #0.1;
        wait (tb_axis_s_tready == 1'b1);
`ifdef DISPLAY_DATA
        $display(
            "VTRSP_TB: TASK SEND_DATA : Sending %0d PWord with data = 0x%0h @time %0t",
            i, tb_axis_s_tdata, $time());
`endif
        case (mode)
          2'b01:   inp_data_matrix_fp8[pkt_send][i] = tb_axis_s_tdata;
          2'b10:   inp_data_matrix_fp16[pkt_send][i] = tb_axis_s_tdata;
          2'b11:   inp_data_matrix_fp32[pkt_send][i] = tb_axis_s_tdata;
          default: inp_data_matrix_bp[pkt_send][i] = tb_axis_s_tdata;
        endcase
      end  // for
      if (err_flag_brk) begin
        #0.1 err_flag_brk = 0;
        break;
      end
      case (mode)
        2'b01:   transp_matrix_fp8(pkt_send);
        2'b10:   transp_matrix_fp16(pkt_send);
        2'b11:   transp_matrix_fp32(pkt_send);
        default: transp_matrix_bp(pkt_send);
      endcase
      pkt_send = pkt_send + 1;
    end  // for
`ifdef DISPLAY_DATA
    $display("exiting the for loop in send_axis_data task %0d", i);
`endif
    @(posedge tb_clk);
    #0.1;
    if (i == num_data) begin
      tb_axis_s_tlast = 1'b0;
      tb_axis_s_tvalid = 1'b0;
      i = 0;
      num_pkts_to_send = 0;
    end
    //  $display("VTRSP_TB: Exiting the SEND_AXIS_DATA TASK");
  end
endtask

task verify_transposed_data(int pkt);
  logic [1:0] cmd_mode;
  begin
    check_cmd_mode_mb.get(cmd_mode);
    $display("in verify_transposed_data task: cmd_mode %0d, at time %0t", cmd_mode, $time());
    if ($time() == 0) return;
    case (cmd_mode)
      2'b00: begin
        if (vtrsp_tb.tb_inp_data_tmatrix_bp[pkt] == out_data_tmatrix_bp[pkt])
          $display("Bypass matrix output is correct. FP_MODE:8 CMD Mode: %0d, %0t",
                   cmd_mode[1:0], $time());
        else begin
          $display(
              "Error: FATAL: bypassed matrix output does not match input data. FP_MODE:8 CMD Mode: %0d, %0t",
              cmd_mode[1:0], $time());
          foreach (vtrsp_tb.tb_inp_data_tmatrix_bp[pkt][i])
            // if (vtrsp_tb.tb_inp_data_tmatrix_bp[pkt][i] != out_data_tmatrix_bp[pkt][i])
              $display("i: %0d Expected data: %0x \t Received data: %0x", i,
                     vtrsp_tb.tb_inp_data_tmatrix_bp[pkt][i], out_data_tmatrix_bp[pkt][i]);
        end
      end
      2'b01: begin
        if (vtrsp_tb.tb_inp_data_tmatrix_fp8[pkt] == out_data_tmatrix_fp8[pkt])
          $display("transposed matrix output is correct. FP_MODE:8 CMD Mode: %0d, %0t",
                   cmd_mode[1:0], $time());
        else begin
          $display(
              "Error: FATAL: transposed matrix output does not match input data. FP_MODE:8 CMD Mode: %0d, %0t",
              cmd_mode[1:0], $time());
          foreach (vtrsp_tb.tb_inp_data_tmatrix_fp8[pkt][i])
            // if (vtrsp_tb.tb_inp_data_tmatrix_fp8[pkt][i] != out_data_tmatrix_fp8[pkt][i])
              $display("i: %0d Expected data: %0x \t Received data: %0x", i,
                     vtrsp_tb.tb_inp_data_tmatrix_fp8[pkt][i], out_data_tmatrix_fp8[pkt][i]);
        end
      end
      2'b10: begin
        if (vtrsp_tb.tb_inp_data_tmatrix_fp16[pkt] == out_data_tmatrix_fp16[pkt])
          $display("transposed matrix output is correct. FP_MODE:16 CMD Mode: %0d, %0t",
                   cmd_mode[1:0], $time());
        else begin
          $display(
              "Error: FATAL: transposed matrix output does not match input data. FP_MODE:16 CMD Mode: %0d, %0t",
              cmd_mode[1:0], $time());
          foreach (vtrsp_tb.tb_inp_data_tmatrix_fp16[pkt][i])
            // if (vtrsp_tb.tb_inp_data_tmatrix_fp16[pkt][i] != out_data_tmatrix_fp16[pkt][i])
              $display("i: %0d Expected data: %0x \t Received data: %0x", i,
                     vtrsp_tb.tb_inp_data_tmatrix_fp16[pkt][i], out_data_tmatrix_fp16[pkt][i]);
        end
      end
      2'b11: begin
        if (vtrsp_tb.tb_inp_data_tmatrix_fp32[pkt] == out_data_tmatrix_fp32[pkt])
          $display("transposed matrix output is correct. FP_MODE:32 CMD Mode: %0d, %0t",
                   cmd_mode[1:0], $time());
        else begin
          $display(
              "Error: FATAL: transposed matrix output does not match input data. FP_MODE:32 CMD Mode: %0d, %0t",
              cmd_mode[1:0], $time());
          foreach (vtrsp_tb.tb_inp_data_tmatrix_fp32[pkt][i])
            // if !(vtrsp_tb.tb_inp_data_tmatrix_fp32[pkt][i] == out_data_tmatrix_fp32[pkt][i])
              $display("i: %0d Expected data: %0x \t Received data: %0x", i,
                     vtrsp_tb.tb_inp_data_tmatrix_fp32[pkt][i], out_data_tmatrix_fp32[pkt][i]);
        end
      end
    endcase
  end
endtask

task transp_matrix_bp(int pkt=0);
  begin
    tb_inp_data_tmatrix_bp[pkt] = inp_data_matrix_bp[pkt];
  end
endtask

task transp_matrix_fp8(int pkt=0);
  begin
    automatic integer row_fp8 = 0;
    automatic integer col_fp8 = 0;
    for (row_fp8 = 0; row_fp8 < aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES; row_fp8++) begin
      for (col_fp8 = 0; col_fp8 < aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES; col_fp8++)
        tb_inp_data_tmatrix_fp8[pkt][row_fp8][col_fp8*8 + 7 -: 8] = inp_data_matrix_fp8[pkt][col_fp8][row_fp8*8+7 -: 8];
    end
  end
endtask

task transp_matrix_fp16(int pkt=0);
  begin
    automatic integer row_fp16 = 0;
    automatic integer col_fp16 = 0;
    for (row_fp16 = 0; row_fp16 < aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES / 2; row_fp16++) begin
      for (col_fp16 = 0; col_fp16 < aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES / 2; col_fp16++)
        tb_inp_data_tmatrix_fp16[pkt][row_fp16][col_fp16*16 + 15 -: 16] = inp_data_matrix_fp16[pkt][col_fp16][row_fp16*16 + 15 -: 16];
    end
  end
endtask

task transp_matrix_fp32(int pkt=0);
  begin
    automatic integer row_fp32 = 0;
    automatic integer col_fp32 = 0;
    for (row_fp32 = 0; row_fp32 < aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES / 4; row_fp32++) begin
      for (col_fp32 = 0; col_fp32 < aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES / 4; col_fp32++)
        tb_inp_data_tmatrix_fp32[pkt][row_fp32][col_fp32*32 +31 -: 32] = inp_data_matrix_fp32[pkt][col_fp32][row_fp32*32 + 31 -: 32];
    end
  end
endtask

`endif  // SIMPLE_VTRSP_SV

