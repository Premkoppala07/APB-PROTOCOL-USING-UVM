`ifndef UVM_ENVIRONEMENT
`define UVM_ENVIRONMENT

class apb_env extends uvm_env;

   // Factory Registration //
   `uvm_component_utils(apb_env)

   // Agent, Scoreboard instances //
   apb_agent       agnt_h;
   apb_scoreboard  scb_h;
   coverage        cov_h;

   // Default Constructor //
   function new(string name = "apb_env", uvm_component parent = null);
      super.new(name,parent);
   endfunction

   // Build Phase //
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info("Environment","Build_Phase",UVM_NONE);
      agnt_h  = apb_agent::type_id::create("agnt_h",this);
      scb_h   = apb_scoreboard::type_id::create("scb_h",this);
      cov_h   = coverage::type_id::create("cov_h",this);
   endfunction

   // Connect Phase //
   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      `uvm_info("Environment","Connect_Phase",UVM_NONE);
      agnt_h.mon_h.mon2scb.connect(scb_h.mon2scb.analysis_export);
      agnt_h.mon_h.mon2scb.connect(cov_h.mon2cov.analysis_export);
   endfunction

endclass

`endif
