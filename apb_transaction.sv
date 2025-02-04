`ifndef UVM_TRANSACTION
`define UVM_TRANSACTION

class apb_transaction extends uvm_sequence_item;

   // Transaction Signals //
   bit psel;           
   bit penable;
   
   randc bit [31:0]paddr;
   rand bit [31:0]pwdata;
   rand bit pwrite;

   bit pready;
   bit [31:0]prdata;
   bit pslverr;
   string name;
   
   // Factory registration with field macros //
   `uvm_object_utils_begin(apb_transaction);
   `uvm_field_string(name,UVM_ALL_ON);
   `uvm_field_int(psel,UVM_ALL_ON);
   `uvm_field_int(penable,UVM_ALL_ON);
   `uvm_field_int(paddr,UVM_ALL_ON);
   `uvm_field_int(pwdata,UVM_ALL_ON);
   `uvm_field_int(pwrite,UVM_ALL_ON);
   `uvm_field_int(prdata,UVM_ALL_ON);
   `uvm_field_int(pslverr,UVM_ALL_ON);
   `uvm_field_int(pready,UVM_ALL_ON);
   `uvm_object_utils_end;

   // Default Constructor //
   function new(string name = "apb_transaction");
      super.new(name);
   endfunction

   // Constraint on Addr //
   constraint c_addr{paddr inside{[32'h00:32'h0F]};}
   // Constraint on Data //
   constraint c_data{pwdata inside{[32'h00:32'hFF]};}
endclass

`endif
