`ifndef APB_COVERAGE
`define APB_COVERAGE

class coverage extends uvm_subscriber#(apb_transaction);

   // Factory Registration //
   `uvm_component_utils(coverage)

   // Analysis Port //
   uvm_tlm_analysis_fifo#(apb_transaction)mon2cov;

   // Transaction Handle //
   apb_transaction txn_h;

   // Covergroup and Coverpoints //
   covergroup apb_covergroup;
      cp1:coverpoint txn_h.pwrite {          // Read and Write Happened or not //
         bins b1 = {1,0};
      }
      cp2:coverpoint txn_h.paddr{            // All address range mentioned is given or not //
         bins b3 = {[0:7]};
         bins b4 = {[8:15]};
      }
      cp3:coverpoint txn_h.pwdata{bins b5 = {[0:255]};}  // WRITE data range //
      cp4:coverpoint txn_h.prdata{bins b6 = {[0:255]};}  // READ data range  //
      cp5:coverpoint txn_h.psel;
      cp3_x_cp1: cross cp3, cp1 {bins b23 = binsof(cp3) intersect {1};} // WRITE data range is written //
      cp4_x_cp1: cross cp4, cp1 {bins b24 = binsof(cp4) intersect {0};} // READ data range is read //
   endgroup

   // Default Constructor //
   function new(string name = "coverage", uvm_component parent = null);
      super.new(name,parent);
      apb_covergroup = new();                  // Memory creation for covergroup //
   endfunction

   // Build Phase //
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      mon2cov = new("mon2cov",this);
   endfunction

   // Write method //
   function void write(T t);                   // Sampling the coverpoints //
      apb_covergroup.sample();
   endfunction

   // Run Phase //
   task run_phase(uvm_phase phase);
      super.run_phase(phase);
      forever begin
         mon2cov.get(txn_h);
         write(txn_h);
         txn_h.name = "SUBSCRIBER";
          `uvm_info("COVERAGE CALCULATED",$sformatf("%0s",txn_h.sprint),UVM_NONE);
          `uvm_info("COVERAGE CALCULATED IS = ",$sformatf("%0d",apb_covergroup.get_coverage()),UVM_NONE);
      end
   endtask

endclass

`endif
