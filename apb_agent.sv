`ifndef UVM_AGENT
`define UVM_AGENT

class apb_agent extends uvm_agent;

   // Factory Registration //
   `uvm_component_utils(apb_agent)

   // Driver, Sequencer, Monitor instances //
   apb_driver    driv_h;
   apb_sequencer sequ_h;
   apb_monitor   mon_h;

   function new(string name = "apb_agent", uvm_component parent = null);
      super.new(name,parent);
   endfunction

   // Build Phase with Objects creation for Driver, Monitor, Sequencer //
   // With Type id create method //
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info("Agent","Build_Phase",UVM_NONE);
      driv_h = apb_driver::type_id::create("driv_h",this);
      sequ_h = apb_sequencer::type_id::create("sequ_h",this);
      mon_h  = apb_monitor::type_id::create("mon_h",this);
   endfunction

   // Connect phase --- Connect Driver and Sequence with .connect method//
   function void connect_phase(uvm_phase phase);
      `uvm_info("Agent","Connect_Phase",UVM_NONE);
      driv_h.seq_item_port.connect(sequ_h.seq_item_export);
   endfunction
endclass

`endif
