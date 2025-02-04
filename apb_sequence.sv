`ifndef UVM_SEQUENCE
`define UVM_SEQUENCE

// Base Sequence //

class base_sequence extends uvm_sequence #(apb_transaction);

   // Factory Registration //
   `uvm_object_utils(base_sequence)

   // Transaction count //
   int PKT_COUNT = 16;

   // Default Constructor //
   function new(string name = "base_sequence");
      super.new(name);
   endfunction
   
endclass

// -------------------------------------------------------------------------- //
// -------------- SINGLE APB WRITE SEQUENCE WITH NO WAIT STATES ------------- //
// -------------------------------------------------------------------------- //
class sequence1 extends base_sequence;

   // Factory Registration //
   `uvm_object_utils(sequence1)
   
   // Transaction handle //
   apb_transaction txn_h;

   // Default Constructor //
   function new(string name = "sequence1");
      super.new(name);
   endfunction

   virtual task body();
      txn_h = apb_transaction::type_id::create("txn_h");
      start_item(txn_h);
      txn_h.randomize()with{pwrite == 1;paddr == 32'h04;};
      txn_h.name = "SEQUENCE_1";
      txn_h.print();
      finish_item(txn_h);
   endtask

endclass

// ------------------------------------------------------------------------- //
// -------------- SINGLE APB READ SEQUENCE WITH NO WAIT STATES ------------- //
// ------------------------------------------------------------------------- //

class sequence2 extends sequence1;

   // Factory Registration //
   `uvm_object_utils(sequence2)

   // Transaction Handle //
   apb_transaction txn_h;

   // Default Constructor //
   function new(string name = "sequence2");
      super.new(name);
   endfunction

   // Body Task //
   virtual task body();
      super.body();
      txn_h = apb_transaction::type_id::create("txn_h");
      start_item(txn_h);
      txn_h.randomize()with{pwrite == 0;paddr == 32'h04;};
      txn_h.name = "SEQUENCE_2";
     txn_h.print(uvm_default_tree_printer);
      finish_item(txn_h);
   endtask
   
endclass

// ------------------------------------------------------------------------- //
// ----------- MULTIPLE APB WRITE SEQUENCE WITH NO WAIT STATES ------------- //
// ------------------------------------------------------------------------- //

class sequence3 extends base_sequence;

   // Factory Registration //
   `uvm_object_utils(sequence3)

   // Default Constructor //
   function new(string name = "sequence3");
      super.new(name);
   endfunction

   // Transaction Handle //
   apb_transaction txn_h;

   // Body task//
   virtual task body();
      txn_h = apb_transaction::type_id::create("txn_h");
      repeat(PKT_COUNT)begin
         start_item(txn_h);
         txn_h.randomize()with{pwrite == 1;};
         txn_h.name = "sequence3";
         txn_h.print();
         finish_item(txn_h);
      end
   endtask

endclass

// ------------------------------------------------------------------------- //
// ----------- MULTIPLE APB READ SEQUENCE WITH NO WAIT STATES -------------- //
// ------------------------------------------------------------------------- //

class sequence4 extends sequence3;

   // Factory Registration //
   `uvm_object_utils(sequence4)

   // Default constructor //
   function new(string name = "sequence4");
      super.new(name);
   endfunction

   // Transaction Handle //
   apb_transaction txn_h;

   // Body Task //
   virtual task body();
      super.body();
      repeat(PKT_COUNT)begin
        txn_h = apb_transaction::type_id::create("sequence4");
        start_item(txn_h);
        txn_h.randomize()with{pwrite == 0;};
        txn_h.name = "SEQUENCE_4";
        txn_h.print();
        //txn_h.print(uvm_default_tree_printer);
        //txn_h.print(uvm_default_line_printer);
        finish_item(txn_h);
      end
   endtask

endclass

`endif
