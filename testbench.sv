`include "uvm_macros.svh"
import uvm_pkg::*;

`include "apb_interface.sv"
`include "apb_property.sv"
`include "apb_transaction.sv"
`include "apb_sequence.sv"
`include "apb_sequencer.sv"
`include "apb_driver.sv"
`include "apb_monitor.sv"
`include "apb_agent.sv"
`include "apb_subscriber.sv"
`include "apb_scoreboard.sv"
`include "apb_environment.sv"
`include "apb_test.sv"

module top;
   
   // Global Signals //
   bit pclk,preset_n; 

   // Interface instantiation //
   apb_interface intf(.pclk(pclk),.preset_n(preset_n));

//    input PCLK, PRESET, PSEL, PWRITE, PENABLE,
//    input [31:0] PADDR, PWDATA,
//    output reg [31:0] PRDATA, 
//    output reg PREADY, PSLVERR

   // Design Instantiation //
   AMBA_APB dut(.PCLK(intf.pclk),
                .PRESET(intf.preset_n),
             .PSEL(intf.psel),
             .PWRITE(intf.pwrite),
             .PENABLE(intf.penable),
             .PADDR(intf.paddr),
             .PWDATA(intf.pwdata),
             .PRDATA(intf.prdata),
             .PREADY(intf.pready),
             .PSLVERR(intf.pslverr)
             );
  
  bind AMBA_APB apb_property bind_check(.pclk(intf.pclk),.preset_n(intf.preset_n),.psel(intf.psel),.pwrite(intf.pwrite),.penable(intf.penable),.paddr(intf.paddr),.pwdata(intf.pwdata),.pready(intf.pready),.prdata(intf.prdata),.pslverr(intf.pslverr));
   

   // Clock Generation //
   always #1 pclk = ~pclk;

   // Virtual Interface set //
   initial begin
      uvm_config_db#(virtual apb_interface)::set(null,"*","intf",intf);
   end
   
   // Reset Generation //
   initial begin
      preset_n = 1'b0;
      #2;
      preset_n = 1'b1;
      #10;
   end

   initial begin
     run_test("test_case_4");
   end

endmodule
