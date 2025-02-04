`ifndef UVM_TEST
`define UVM_TEST

class base_test extends uvm_test;

   // Factory Registration //
   `uvm_component_utils(base_test)

   // Environment Handle //
   apb_env env_h;

   // Default_Constructor //
   function new(string name = "base_test", uvm_component parent = null);
      super.new(name,parent);
   endfunction

   // Build Phase //
   virtual function void build_phase(uvm_phase phase);
      `uvm_info("Base Test","Build_Phase",UVM_NONE);
      super.build_phase(phase);
      env_h = apb_env::type_id::create("env_h",this);
   endfunction

   function void end_of_elaboration_phase(uvm_phase phase);
      super.end_of_elaboration_phase(phase);
      uvm_top.print_topology();
   endfunction
endclass

/////////////////////////////////////////////////////////////////////////
//////////////////////////// TEST CASE 1 ////////////////////////////////
/////////////////////////////////////////////////////////////////////////

class test_case_1 extends base_test;

   // Factory Registration //
   `uvm_component_utils(test_case_1)

   sequence1 seq_1h;

   // Default Constructor //
   function new(string name = "test_case_1", uvm_component parent = null);
      super.new(name,parent);
   endfunction

   // Build Phase //
   virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
   endfunction

   virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);
      phase.raise_objection(this);
      seq_1h = sequence1::type_id::create("seq_1h");
      `uvm_info("Test Case 1 Started","",UVM_NONE);
      seq_1h.start(env_h.agnt_h.sequ_h);
      phase.drop_objection(this);
   endtask

endclass

/////////////////////////////////////////////////////////////////////////
//////////////////////////// TEST CASE 2 ////////////////////////////////
/////////////////////////////////////////////////////////////////////////

class test_case_2 extends base_test;

   // Factory Registration
   `uvm_component_utils(test_case_2)

   // Default Constructor //
   function new(string name = "test_case_2", uvm_component parent = null);
      super.new(name,parent);
   endfunction

   // Sequence2 //
   sequence2 seq_2h;

   // Build Phase //
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
   endfunction

   // Run Phase //
   virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);
      phase.raise_objection(this);
      seq_2h = sequence2::type_id::create("seq_2h");
      `uvm_info("TEST CASE 2 Started","",UVM_NONE);
      seq_2h.start(env_h.agnt_h.sequ_h);
      phase.drop_objection(this);
   endtask
endclass

/////////////////////////////////////////////////////////////////////////
//////////////////////////// TEST CASE 3 ////////////////////////////////
/////////////////////////////////////////////////////////////////////////

class test_case_3 extends base_test;

   // Factory Registration //
   `uvm_component_utils(test_case_3)

   // Default Constructor //
   function new(string name = "test_case_3", uvm_component parent = null);
      super.new(name,parent);
   endfunction

   // Sequence3 Handle //
   sequence3 seq_3h;

   // Build Phase //
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
   endfunction

   // Run Phase //
   virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);
      phase.raise_objection(this);
      seq_3h = sequence3::type_id::create("seq_3h");
      `uvm_info("Test Case 3 Started","",UVM_NONE);
      seq_3h.start(env_h.agnt_h.sequ_h);
      phase.drop_objection(this);
   endtask

endclass

class test_case_4 extends base_test;

   // Factory Registration //
   `uvm_component_utils(test_case_4)

   // Default Constructor //
   function new(string name = "test_case_4", uvm_component parent = null);
      super.new(name,parent);
   endfunction

   // Sequence4 Handle //
   sequence4 seq_4h;

   // Build Phase //
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
   endfunction

   // Run Phase //
   virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);
      phase.raise_objection(this);
      seq_4h = sequence4::type_id::create("seq_4h");
      `uvm_info("Test Case 4 Started","",UVM_NONE);
      seq_4h.start(env_h.agnt_h.sequ_h);
      phase.drop_objection(this);
   endtask

endclass

`endif
