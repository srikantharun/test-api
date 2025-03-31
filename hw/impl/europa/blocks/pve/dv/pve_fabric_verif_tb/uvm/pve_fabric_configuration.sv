class pve_fabric_configuration extends uvm_object;
   `uvm_object_utils(pve_fabric_configuration)

   bit pve_conn_matrix[14][12];
   bit [39:0] start_addr;
   bit [39:0] end_addr;

   function new(string name = "pve_fabric_configuration");
      super.new(name);
   endfunction
endclass
