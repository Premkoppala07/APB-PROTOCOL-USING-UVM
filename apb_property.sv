import uvm_pkg::*;
`include "uvm_macros.svh"
module apb_property(pclk,preset_n,psel,pwrite,penable,paddr,pwdata,pready,prdata,pslverr);
   input pclk,preset_n;
   input psel,pwrite,penable;
   input [31:0]paddr;input[31:0]pwdata;
   input pready;
   input [31:0]prdata;
   input pslverr;

// Assertions for Protocol Verification //

   // Set-Up sequence //
   sequence SETUP;
      $rose(psel) && $stable(penable);
   endsequence

   // Access Sequence //
   sequence ACCESS;
      $rose(penable) && $stable(psel);
   endsequence

   // Idle Sequence //
   sequence IDLE;
      $fell(penable) && $fell(psel);
   endsequence

   // Assertion for Setup state to Access state //
   property setup_to_access;
      @(posedge pclk) disable iff(!preset_n) ##1 SETUP |=> ACCESS;
   endproperty

   setup_access:assert property(setup_to_access) begin
                     `uvm_info("ASSERTION PASSED setup_access","",UVM_NONE);
                end
                else begin
                   `uvm_fatal("ASSERTION FAILED","in setup to access");
                end

   // Assertion for Access state to Idle state
   property access_to_idle;
      @(posedge pclk) disable iff(!preset_n) ##1 ACCESS |=> ##[0:6]IDLE;
   endproperty

   access_idle:assert property(access_to_idle)begin
                  `uvm_info("ASSERTION PASSED access_idle","",UVM_NONE);
               end
               else begin
                  `uvm_fatal("ASSERTION FAILED","in access to idle");
               end

   // Assertion for PENABLE and PREADY handshaking //
   property penable_to_pready;
      @(posedge pclk)disable iff(!preset_n) ##1 $rose(penable) |-> ##[0:5]$rose(pready);
   endproperty

   handshake_penable_pready:assert property(penable_to_pready) begin
                              `uvm_info("ASSERTION PASSED for Handshake penable pready","",UVM_NONE);
                            end
                         else begin
                            `uvm_fatal("ASSERTION FAILED","in handshake penable pready");
                         end

   // Signal Validity Checkers //
   X_Z_CHECKER_PSEL    : assert property (@(posedge pclk) disable iff(!preset_n) (!$isunknown(psel)));
   X_Z_CHECKER_PENABLE : assert property (@(posedge pclk) disable iff(!preset_n) (!$isunknown(penable)));
   X_Z_CHECKER_PREADY  : assert property (@(posedge pclk) disable iff(!preset_n) (!$isunknown(pready)));
   X_Z_CHECKER_PWDATA  : assert property (@(posedge pclk) disable iff(!preset_n) (!$isunknown(pwdata)));
   X_Z_CHECKER_PSLVERR : assert property (@(posedge pclk) disable iff(!preset_n) (!$isunknown(pslverr)));
//   X_Z_CHECKER_PRDATA  : assert property (@(posedge pclk) disable iff(!preset_n) (!$isunknown(prdata)));
   X_Z_CHECKER_PWRITE  : assert property (@(posedge pclk) disable iff(!preset_n) (!$isunknown(pwrite)));
   
endmodule
