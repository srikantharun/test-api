`ifdef DUMP_IMC_BANKS
module imc_bank_to_file #(
  parameter AXIS_NB_DATA_WORDS = 4,
  parameter AXIS_WORD_WIDTH = 8,
  parameter REVERSE_WORDS = 0,
  parameter RANDOM_READY = 1,
  parameter RANDOM_CHANCE = 0
) (
  input logic clk_i,
  output logic tready_o,
  input logic tvalid_i,
  input logic tlast_i,
  input logic [AXIS_NB_DATA_WORDS*AXIS_WORD_WIDTH-1:0] tdata_i,
  input logic [AXIS_NB_DATA_WORDS-1:0] tstrb_i
);

  logic tready_ff = 0;
  bit tready_int = 0;
  int fileId, fileIdStrb;
  int randValue = 0;
  task openDumpFile;
    input string fileName;
    begin
      tready_int = 1;
      fileId = $fopen(fileName, "w");
      $display("INFO: dumping incoming axi stream to %s", fileName);
    end
  endtask

  bit strb_dump_on = 0;
  task openDumpFileStrb;
    input string fileName;
    begin
      strb_dump_on = 1;
      fileIdStrb   = $fopen(fileName, "w");
      $display("INFO: dumping incoming axi stream strb values to %s", fileName);
    end
  endtask

  task closeDumpFile;
    begin
      $fflush(fileId);
      $fclose(fileId);
      tready_int = 0;
    end
  endtask

  task closeDumpFileStrb;
    begin
      $fflush(fileIdStrb);
      $fclose(fileIdStrb);
      strb_dump_on = 0;
    end
  endtask

  // Randomize tready_o
  always_ff @(posedge clk_i, negedge tready_int) begin
    if (tready_int) begin
      if (RANDOM_READY == 1) tready_ff <= $urandom_range(0, 10) > RANDOM_CHANCE;
      else tready_ff <= 1'b1;
    end else begin
      tready_ff <= 0;
    end
  end

  assign tready_o = tready_ff & tvalid_i;


  // File dumping
  always_ff @(posedge clk_i) begin
    if (tvalid_i && tready_o) begin
      for (int i = 0; i < AXIS_NB_DATA_WORDS; i++) begin
        if (REVERSE_WORDS) begin
          if (i == AXIS_NB_DATA_WORDS - 1)
            $fwrite(
                fileId, "%h\n",
                tdata_i[(AXIS_NB_DATA_WORDS-1)*AXIS_WORD_WIDTH-i*AXIS_WORD_WIDTH+:AXIS_WORD_WIDTH]);
          else
            $fwrite(
                fileId, "%h_",
                tdata_i[(AXIS_NB_DATA_WORDS-1)*AXIS_WORD_WIDTH-i*AXIS_WORD_WIDTH+:AXIS_WORD_WIDTH]);
        end else begin
          if (i == AXIS_NB_DATA_WORDS - 1)
            $fwrite(fileId, "%h\n", tdata_i[i*AXIS_WORD_WIDTH+:AXIS_WORD_WIDTH]);
          else $fwrite(fileId, "%h_", tdata_i[i*AXIS_WORD_WIDTH+:AXIS_WORD_WIDTH]);
        end
      end
      if (strb_dump_on) $fwrite(fileIdStrb, "%h\n", tstrb_i);
    end
  end

endmodule
`endif // DUMP_IMC_BANKS
