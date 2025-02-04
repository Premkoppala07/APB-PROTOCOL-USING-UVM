`ifndef UVM_MONITOR
`define UVM_MONITOR
`define vint vif.cb_mon

class apb_monitor extends uvm_monitor;

   // Factory Registration //
   `uvm_component_utils(apb_monitor)

   // Virtual Interface Instantiation //
   virtual apb_interface vif;

   // Transaction handle //
   apb_transaction txn_h;

   // Analysis Port //
   uvm_analysis_port#(apb_transaction)mon2scb;
   
   // Default Constructor //
   function new(string name = "apb_monitor", uvm_component parent = null);
      super.new(name,parent);
   endfunction

   // Build Phase //
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info("Monitor","Build_Phase",UVM_NONE);
      if(uvm_config_db#(virtual apb_interface)::get(this,"","intf",vif))begin
         `uvm_info("Monitor","Virtual Interface Established",UVM_NONE);
      end
      else begin
         `uvm_error("Monitor","Interface Not Established");
      end
      mon2scb = new("mon2scb",this);
   endfunction

   // Run Phase //
   task run_phase(uvm_phase phase);
      super.run_phase(phase);
      `uvm_info("Monitor","Run_Phase",UVM_NONE);
      forever begin
         txn_h = apb_transaction::type_id::create("txn_h");
         wait(vif.preset_n == 1);
         if(vif.penable == 1 && vif.pready == 1 && vif.pslverr == 0)begin
            txn_h.pwrite  = `vint.pwrite;
            txn_h.pwdata  = `vint.pwdata;
            txn_h.prdata  = `vint.prdata;
            txn_h.paddr   = `vint.paddr;
            txn_h.name = "MONITOR";
            txn_h.print();
            mon2scb.write(txn_h);
         end
         @(vif.cb_mon);
      end
   endtask

endclass

`endif
