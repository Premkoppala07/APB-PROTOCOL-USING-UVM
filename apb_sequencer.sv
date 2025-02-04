`ifndef UVM_SEQUENCER
`define UVM_SEQUENCER

class apb_sequencer extends uvm_sequencer#(apb_transaction);
   
   // factory Registration //
   `uvm_component_utils(apb_sequencer)

   // Transaction Handle //
   apb_transaction txn_h;

   // Default Constructor //
   function new(string name = "apb_sequencer", uvm_component parent = null);
      super.new(name,parent);
   endfunction

   // Build Phase //
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info("Sequencer","Build_Phase",UVM_NONE);
   endfunction
   
endclass

`endif
