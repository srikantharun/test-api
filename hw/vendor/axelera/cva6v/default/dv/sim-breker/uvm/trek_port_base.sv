// COPYRIGHT (c) Breker Verification Systems
// This software has been provided pursuant to a License Agreement
// containing restrictions on its use.  This software contains
// valuable trade secrets and proprietary information of
// Breker Verification Systems and is protected by law.  It may
// not be copied or distributed in any form or medium, disclosed
// to third parties, reverse engineered or used in any manner not
// provided for in said License Agreement except with the prior
// written authorization from Breker Verification Systems.

`ifndef GUARD__TREK_PORT_BASE__SV
`define GUARD__TREK_PORT_BASE__SV

/// This class is styled on uvm_pkg::uvm_sqr_if_base class.
/// Each of the various TLM port types extend from this class.
///
/// This class DOES NOT have any dependencies from UVM.
///
/// It provides the mechanism for user-defined sequences to push
/// and pull traffic to and from Trek5.
///
/// Typically, `T1` is a "request" and `T2` is a "response".
///
virtual class trek_port_base#(
    type T1 = int,
    type T2 = T1);

  typedef enum { MASTER, CHECK, PUT, GET, UNKNOWN } t_types;
  t_types m_type = UNKNOWN;
  string  m_name;

  function new(string name = "");
    m_name = name;  // get_name() returns PSS "tb_path".
  endfunction

  //
  // These methods are called by the user...
  //

  virtual function string get_name();
    return m_name;
  endfunction

	// Wait for, then retrieve, the next available item from Trek.
	//
	// This method differs from `get()` because this method does NOT
	// call `item_done()`.
	//
  virtual task get_next_item(output T1 t, output bit end_of_test);
    `uvm_fatal(get_name(), {"It is illegal to call get_next_item() ",
      "on a port of this type."})
  endtask: get_next_item

	// Immediately return an item from Trek if one is available, otherwise
	// `t` will be `null`. `end_of_test` will always be valid and has
	// priority.
	//
	// This method differs from `peek()` because this method does NOT
	// block and wait for a request from Trek. `peek()` is blocking.
	//
  virtual task try_next_item(output T1 t, output bit end_of_test);
    `uvm_fatal(get_name(), {"It is illegal to call try_next_item() ",
      "on a port of this type."})
  endtask: try_next_item

	// Immediately indicate to Trek that a request is completed.
	// If one is provided, a response will also be sent back.
	//
  virtual function void item_done(input T2 t = null);
    `uvm_fatal(get_name(), {"It is illegal to call item_done() ",
      "on a port of this type."})
  endfunction: item_done

	// Wait for, then retrieve, the next available item from Trek.
	//
	// It will then call `item_done()` to *pop* the request so the next
	// request can appear. If you use this method, you must be careful
	// to return responses in order.
	//
	// This method differs from `get_next_item()` in that it calls
	// `item_done()` whereas `get_next_item()` does not.
	//
  virtual task get(output T1 t, output bit end_of_test);
    `uvm_fatal(get_name(), {"It is illegal to call get() ",
      "on a port of this type."})
  endtask: get

	// Wait for, then retrieve, the next available request from Trek.
	//
	// If you call this method multiple times, without an intervening
	// `item_done()` it will return the same item. This is because it
	// will `NOT` call `item_done()` to *pop* the request. You must
	// manually call that after you've processed each request.
	//
	// This method differs from `get()` because `peek()` does not call
	// `item_done()`. You must call `item_done()` manually after
	// processing the request.
	//
	// This method differs from `try_next_item()`, because it blocks
	// and waits for data. `try_next_item()` will always return 
	// immediately with or without data.
	//
  virtual task peek(output T1 t, output bit end_of_test);
    `uvm_fatal(get_name(), {"It is illegal to call peek() ",
      "on a port of this type."})
  endtask: peek

  // Immediately send a response or other data to Trek.
  //
  virtual function void put(input T2 t);
    `uvm_fatal(get_name(), {"It is illegal to call put() ",
      "on a port of this type."})
  endfunction: put


  //
  // These methods are called by generated code.
  // Users do not typically call them directly.
  //

  // If provided a transaction in the first argument, Trek will fill
  //   and return the transaction provided. If the first argument remains
  //   null, then Trek will create, fill, and return a new transaction.
  // The second argument indicates whether Trek should call item_done()
  //   on the port to 'pop' the transaction after it has been pulled.
  //   This is useful if your model will provide more than one transaction
  //   over this port in this test.
  virtual function T1 pull(input T1 t = null,
                                     input bit call_item_done = 1'b1);
    `uvm_fatal(get_name(), {"It is illegal to call pull() ",
      "on a port of this type."})
  endfunction: pull

  virtual function void push(input T2 t);
    `uvm_fatal(get_name(), {"It is illegal to call push() ",
      "on a port of this type."})
  endfunction: push

endclass: trek_port_base

`endif  // GUARD__TREK_PORT_BASE__SV
