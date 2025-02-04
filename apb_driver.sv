`ifndef UVM_DRIVER
`define UVM_DRIVER
`define vintf vif.cb_driv

class apb_driver extends uvm_driver#(apb_transaction);

   // Factory Registration //
   `uvm_component_utils(apb_driver)

   // Virtual interface instantion //
   virtual apb_interface vif;

   // Transaction Class handle //
   apb_transaction txn_h;

   // Default Constructor//
   function new(string name = "apb_driver", uvm_component parent = null);
      super.new(name,parent);
   endfunction

   // Build Phase and interface checking //
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info("Driver","Build_Phase",UVM_NONE);
      if(uvm_config_db#(virtual apb_interface)::get(this,"","intf",vif))begin
         `uvm_info("Driver","Virtual Interface Established",UVM_NONE);
      end
      else begin
         `uvm_error("Driver","Interface Not Established");
      end
   endfunction

   // Run Phase //
   task run_phase(uvm_phase phase);
      super.run_phase(phase);
      `uvm_info("Driver","Run Phase",UVM_NONE);
      forever begin
         if(vif.preset_n == 0)begin
            `uvm_info("DRIVER RESET","Driver in Reset Phase",UVM_NONE);
            // Driving the values at the current edge //
            @(vif.cb_driv);
            `vintf.psel    <= 0;
            `vintf.penable <= 0;
            `vintf.pwrite  <= 0;
            `vintf.paddr   <= 0;
            `vintf.pwdata  <= 0;
            wait(vif.preset_n == 1);
         end
         else begin
            if(vif.preset_n == 1)begin
               seq_item_port.get_next_item(txn_h);
               txn_h.name = "DRIVER";

               ////////////////////////////////////////////////
               /////////////////// SETUP PHASE ////////////////
               ////////////////////////////////////////////////

               @(vif.cb_driv);
               `vintf.psel    <= 1;
               `vintf.pwrite  <= txn_h.pwrite;
               `vintf.penable <= 0;
               `vintf.paddr   <= txn_h.paddr;
               if(txn_h.pwrite == 1)begin
                  `vintf.pwdata <= txn_h.pwdata;
               end
               else begin
                  `vintf.pwdata <= 0;
               end
              
               ////////////////////////////////////////////////
               /////////////////// ACCESS PHASE ///////////////
               ////////////////////////////////////////////////

               @(vif.cb_driv);

               `vintf.penable  <= 1;
//              while(vif.pready == 0)begin
//                  @(vif.cb_driv);
//               end
               wait(vif.pready == 1);
               @(vif.cb_driv);

               ////////////////////////////////////////////////
               /////////////////// IDLE PHASE ///////////////
               ////////////////////////////////////////////////

               `vintf.penable  <= 0;
               `vintf.psel     <= 0;
               if(vif.preset_n == 1)begin
                  seq_item_port.item_done();
               end
               txn_h.print();
            end
         end
      end
   endtask
endclass

`endif
