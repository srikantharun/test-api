// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Unpack for commands of different types
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _CMDBLOCK_CMD_UNPACK_SV_
`define _CMDBLOCK_CMD_UNPACK_SV_

module cmdblock_cmd_unpack #(
  parameter int NR_FIELDS = 3,
  parameter int NR_FORMATS = 3,
  parameter int TOT_WIDTH = 41,
  parameter int FIELD_SIZE[NR_FIELDS] = {32'd16, 32'd8, 32'd17},
  parameter int FIELD_OUTP_IDX[NR_FIELDS] = {32'd0, 32'd16, 32'd24},
  parameter longint FIELD_DEFAULT_VAL[NR_FORMATS][NR_FIELDS] = '{
    {64'd0, 64'd0, 64'd1}, {64'd0, 64'd0, 64'd1}, {64'd0, 64'd0, 64'd1}
  },

  parameter int FORMAT_IDX[NR_FORMATS][NR_FIELDS] = '{'{32'd0, 32'd16, 32'd24}, '{32'd8, -32'd1, 32'd0}, '{-32'd1, 32'd0, -32'd1}}
) (
  input logic [cc_math_pkg::index_width(NR_FORMATS)-1:0] format,
  input logic [TOT_WIDTH-1:0] inp,
  output logic [TOT_WIDTH-1:0] outp
);

  localparam int unsigned FmtDw = NR_FORMATS;

  logic [FmtDw-1:0][TOT_WIDTH-1:0] fmt_outp;

  // check if there is a field that would overflow the total width:
  //synopsys translate_off
  for (genvar f = 0; f < NR_FIELDS; f++) begin : g_chk_fields
    if (FIELD_OUTP_IDX[f] + FIELD_SIZE[f] > TOT_WIDTH)
      $fatal(
          1,
          "CMD Unpack configuration error! Field %d with idx %d and width %d is overflowing the total width of %d",
          f,
          FIELD_OUTP_IDX[f],
          FIELD_SIZE[f],
          TOT_WIDTH
      );
    for (genvar fmt = 0; fmt < NR_FORMATS; fmt++) begin : g_chk_fmt
      if (FORMAT_IDX[fmt][f] >= 0) begin :  g_fmt_ge0
        if (FORMAT_IDX[fmt][f] + FIELD_SIZE[f] > TOT_WIDTH)
          $fatal(
              1,
              "CMD Unpack configuration error! Field %d with remapped idx %d for format %d and width %d is overflowing the total width of %d",
              f,
              FORMAT_IDX[fmt][f],
              fmt,
              FIELD_SIZE[f],
              TOT_WIDTH
          );
      end
    end
  end
  //synopsys translate_on

  ///////////////////////
  //// functions to determine unused bits that can be driven to zero for spyglass
    // check if bit is in use in any field:
  function automatic bit field_bit_in_use(int b);
    for (int f = 0; f < NR_FIELDS; f++)
      if ((b >= FIELD_OUTP_IDX[f]) && (b<(FIELD_OUTP_IDX[f]+FIELD_SIZE[f])))
        return 1;
    return 0;
  endfunction

    // find the lowest LSB that is still not in use.
    // return -1 if the provided MSB is actually in use
  function automatic int field_not_in_use_lsb(int msb);
    // out of range, pretend to be in use:
    if (msb<0)
      return -1;

    // check if there is a field using that bit
    if (field_bit_in_use(msb))
      return -1;

    // find LSB :
    for (int b = msb; b >=0; b--)
      if (field_bit_in_use(b))
        return b+1;

    return 0;
  endfunction
  ///////////////////////

  // check per format what to assign to each field
  // either a default value, as stated in field_default_val, or
  // an input value, defined by the position of the input vector by FORMAT_IDX[fmt][f]
  for (genvar fmt = 0; fmt < NR_FORMATS; fmt++) begin : g_format_sel
    for (genvar f = 0; f < NR_FIELDS; f++) begin : g_field_mux
      // check if bits before this one should be set to 0 or not:
      if (field_not_in_use_lsb(FIELD_OUTP_IDX[f]-1) >= 0)
        always_comb fmt_outp[fmt][FIELD_OUTP_IDX[f]-1:field_not_in_use_lsb(FIELD_OUTP_IDX[f]-1)] = '0;
      if (FORMAT_IDX[fmt][f] < 0) begin : g_def_val
        always_comb fmt_outp[fmt][FIELD_OUTP_IDX[f]+:FIELD_SIZE[f]] = unsigned'(FIELD_DEFAULT_VAL[fmt][f]);
      end else begin : g_inp_val
        always_comb fmt_outp[fmt][FIELD_OUTP_IDX[f]+:FIELD_SIZE[f]] = inp[FORMAT_IDX[fmt][f]+:FIELD_SIZE[f]];
      end
    end
    // check if top part is in use, else set to 0 as well:
    if (field_not_in_use_lsb($bits(fmt_outp[fmt])-1) >= 0)
      always_comb fmt_outp[fmt][$bits(fmt_outp[fmt])-1:field_not_in_use_lsb($bits(fmt_outp[fmt])-1)] = '0;
  end

  // select the actual used format mapping
  // not all bits will be driven if there is a gap between fields.
  // These won't be used (else they would have been used) and will be synthesized away
  always_comb outp = fmt_outp[format];

endmodule

`endif  // _CMDBLOCK_CMD_UNPACK_SV_

