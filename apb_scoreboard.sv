`ifndef UVM_SCOREBOARD
`define UVM_SCOREBOARD

class apb_scoreboard extends uvm_scoreboard;

   // Factory Registration //
   `uvm_component_utils(apb_scoreboard)

   // Transaction Handle //
   apb_transaction txn_h;
   
   // TLM analysis FIFO port //
   uvm_tlm_analysis_fifo #(apb_transaction)mon2scb;

   // Associative Array of address along with data //
   int w_data[int];
   
   // Default Constructor //
   function new(string name = "apb_scoreboard", uvm_component parent = null);
      super.new(name,parent);
   endfunction

   // Build Phase //
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info("Scoreboard","Build_Phase",UVM_NONE);
      mon2scb = new("mon2scb",this);
   endfunction

   // Run Phase //
   task run_phase(uvm_phase phase);
      super.run_phase(phase);
      `uvm_info("Scoreboard","Run_Phase",UVM_NONE);
      forever begin
         mon2scb.get(txn_h);
         txn_h.name = "SCOREBOARD";
         txn_h.print();
         if(txn_h.pwrite == 1)begin
            w_data[txn_h.paddr] = txn_h.pwdata;
         end
         else begin
            compare();
            `uvm_info("WRITE",$sformatf("DATA = %0p",w_data),UVM_NONE);
         end
      end
   endtask

   task compare();
      if(w_data.exists(txn_h.paddr))begin
         w_data[txn_h.paddr] = txn_h.prdata;
         `uvm_info("Transaction Pass","",UVM_NONE);
         w_data.delete(txn_h.paddr);
      end
      else begin
         `uvm_info("Fail -- Reading to Unknown written address","",UVM_NONE);
      end
   endtask

endclass

`endif
