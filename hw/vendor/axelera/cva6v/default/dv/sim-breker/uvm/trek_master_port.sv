// COPYRIGHT (c) Breker Verification Systems
// This software has been provided pursuant to a License Agreement
// containing restrictions on its use.  This software contains
// valuable trade secrets and proprietary information of
// Breker Verification Systems and is protected by law.  It may
// not be copied or distributed in any form or medium, disclosed
// to third parties, reverse engineered or used in any manner not
// provided for in said License Agreement except with the prior
// written authorization from Breker Verification Systems.

`ifndef GUARD__TREK_MASTER_PORT__SV
`define GUARD__TREK_MASTER_PORT__SV

/// This class is styled on uvm_pkg::uvm_sqr_if_base class.
///
/// It provides a mechanism for user-defined sequences to push
/// and pull traffic to and from Trek5 over a hsi::master_port.
///
/// Typically, `T1` is a "request" and `T2` is a "response".
///
virtual class trek_master_port#(
    type T1 = int,
    type T2 = T1)
    extends trek_port_base#(T1, T2);

  function new(string name = "");
    super.new(name);
    m_type = MASTER;
  endfunction

	// Wait for, then retrieve, the next available item from Trek.
	//
	// This method differs from `get()` because this method does NOT
	// call `item_done()`.
	//
  virtual task get_next_item(output T1 t, output bit end_of_test);
    peek(t, end_of_test);
  endtask: get_next_item

	// Immediately return an item from Trek if one is available, otherwise
	// `t` will be `null`. `end_of_test` will always be valid and has
	// priority.
	//
	// This method differs from `peek()` because this method does NOT
	// block and wait for a request from Trek. `peek()` is blocking.
	//
  virtual task try_next_item(output T1 t, output bit end_of_test);
    end_of_test = 1'b0;
    if (trek_dpi_pkg::trek_done() == 0) begin: test_is_done
      end_of_test = 1'b1;
    end else begin: test_is_not_done
      if (trek_dpi_pkg::trek_can_get(get_name())) begin: data_is_waiting
        get(t, end_of_test);
        return;
      end
    end
    t = null;
  endtask: try_next_item

	// Immediately indicate to Trek that a request is completed.
	// If one is provided, a response will also be sent back.
	//
  virtual function void item_done(input T2 t = null);
    if (t != null) begin: return_response
      put(t);
    end
    void'(trek_dpi_pkg::trek_get_done(get_name()));
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
    uvm_event e = trek_uvm_events::get(get_name());
    e.wait_on(); // Block here and wait for data from Trek
    e.reset();

    t = pull(t, 1'b1); // call item_done() after pulling
    end_of_test = trek_uvm_events::end_of_test();
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
    uvm_event e = trek_uvm_events::get(get_name());
    e.wait_on(); // Block here and wait for data from Trek
    e.reset();

    t = pull(t, 1'b0);  // do not call item_done() after pulling
    end_of_test = trek_uvm_events::end_of_test();
  endtask: peek

  // Immediately send a response or other data to Trek.
  //
  virtual function void put(input T2 t);
    push(t);
  endfunction: put

endclass: trek_master_port

`endif  // GUARD__TREK_MASTER_PORT__SV
