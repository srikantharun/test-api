`ifndef TOKEN_AGENT_SEQUENCE_LIBRARY_SW
`define TOKEN_AGENT_SEQUENCE_LIBRARY_SV

class token_agent_base_sequence extends uvm_sequence#(token_agent_seq_item);
  `uvm_object_utils(token_agent_base_sequence)

  //variable that specifies if this sequence item is related with consumer or producer signals
  token_agent_info_type_enm m_type_enm;

  function new (string name = "");
    super.new (name);
  endfunction : new

  task body();
    token_agent_seq_item tok_trans;

    `uvm_info(get_name(), $sformatf("Starting token_agent_base_sequence"), UVM_HIGH)
    `uvm_create(tok_trans)
    //randomize transaction
    if(!tok_trans.randomize() with {
      m_type_enm == local::m_type_enm;
      m_tok_value == 1'b1;
    }) `uvm_error(get_name, "tok_trans randomization error!");
    /** Send the write transaction and wait for the sequence item to be finished */
    `uvm_send(tok_trans)

    `uvm_info(get_name(), $sformatf("Finish token_agent_base_sequence"), UVM_HIGH)
  endtask: body
endclass : token_agent_base_sequence

class token_agent_cons_sequence extends token_agent_base_sequence;
  `uvm_object_utils(token_agent_cons_sequence)

  function new (string name = "");
    super.new (name);
    //identify that this sequence is identified as a Consumer sequence
    m_type_enm = TOK_CONS_DRV;
  endfunction : new

endclass : token_agent_cons_sequence

class token_agent_prod_sequence extends token_agent_base_sequence;
  `uvm_object_utils(token_agent_prod_sequence)

  function new (string name = "");
    super.new (name);
    //identify that this sequence is identified as a Producer sequence
    m_type_enm = TOK_PROD_DRV;
  endfunction : new

endclass : token_agent_prod_sequence

`endif // TOKEN_AGENT_SEQUENCE_LIBRARY_SV

