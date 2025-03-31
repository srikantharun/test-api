// COPYRIGHT (c) Breker Verification Systems
// This software has been provided pursuant to a License Agreement
// containing restrictions on its use.  This software contains
// valuable trade secrets and proprietary information of
// Breker Verification Systems and is protected by law.  It may
// not be copied or distributed in any form or medium, disclosed
// to third parties, reverse engineered or used in any manner not
// provided for in said License Agreement except with the prior
// written authorization from Breker Verification Systems.

`ifndef GUARD__TREK_CHECK_PORT__SV
`define GUARD__TREK_CHECK_PORT__SV

/// This class is styled on uvm_pkg::uvm_sqr_if_base class.
///
/// It provides a mechanism for user-defined sequences to push
/// traffic to Trek5 over a hsi::check_port.
///
/// Typically, `T1` is a "request" and `T2` is unused.
///
virtual class trek_check_port#(
    type T1 = int,
    type T2 = T1)
    extends trek_port_base#(T1, T2);

  function new(string name = "");
    super.new(name); // get_name() returns the PSS tb_path
    m_type = CHECK;
  endfunction

  // Immediately send a response or other data to Trek for checking.
  //
  virtual function void put(input T2 t);
    push(t);
  endfunction: put

endclass: trek_check_port

`endif  // GUARD__TREK_CHECK_PORT__SV
