// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Package containing pure simulation helper functions
///
package axi_sim_pkg;
  import axi_pkg::*;

  /// Index of lowest byte in beat (see A3-51).
  function automatic shortint unsigned axi_beat_lower_byte(
    axi_largest_addr_t addr,
    axi_size_t         size,
    axi_len_t          len,
    axi_burst_t        burst,
    shortint unsigned  strobe_width,
    shortint unsigned  i_beat
  );
    axi_largest_addr_t addr_of_beat;
    axi_largest_addr_t addr_to_return;
    addr_of_beat   = axi_beat_addr(addr, size, len, burst, i_beat);
    addr_to_return = addr_of_beat - (addr_of_beat / strobe_width) * strobe_width;
    return addr_to_return[$bits(shortint)-1:0];
  endfunction

  /// Index of highest byte in beat (see A3-51).
  function automatic shortint unsigned axi_beat_upper_byte(
    axi_largest_addr_t addr,
    axi_size_t         size,
    axi_len_t          len,
    axi_burst_t        burst,
    shortint unsigned  strobe_width,
    shortint unsigned  i_beat
  );
    if (i_beat == 0) begin
      return   axi_aligned_addr(addr, size)
             + (axi_num_bytes(size) - 1)
             - (addr / strobe_width) * strobe_width;
    end else begin
      return   axi_beat_lower_byte(addr, size, len, burst, strobe_width, i_beat)
             + axi_num_bytes(size)
             - 1;
    end
  endfunction

endpackage
