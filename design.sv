module AMBA_APB(
    input PCLK, PRESET, PSEL, PWRITE, PENABLE,
    input [31:0] PADDR, PWDATA,
    output reg [31:0] PRDATA, 
    output reg PREADY, PSLVERR
);
    parameter IDLE=2'b00,SETUP=2'b01,ACCESS=2'b10;
 
    reg [1:0] state, next_state;
 
    reg [31:0] mem [31:0]; // 00 to 20 //
    initial begin
        state = IDLE;
    end
 
    always @(posedge PCLK or negedge PRESET) begin
        if(!PRESET) begin     // Active low //
            state <= IDLE;
            foreach(mem[i]) mem[i] = 32'hffffffff;
        end
        else
            state <= next_state;
    end
 
    always @(state, PSEL, PENABLE) begin
        case (state)
            IDLE:                
            begin
                PSLVERR <= 0;
                PREADY <= 0;
                //PRDATA <= 32'h0;
                if(PSEL) next_state <= SETUP;
                else next_state <= IDLE;
            end
            SETUP:
            begin
                PREADY <= 0;
                PSLVERR<=0;
                if(PENABLE) begin
                    PREADY <= 1;
                    if(PADDR >= 2**5) begin
                        PSLVERR <= 1;
			PRDATA <= 32'h0;
                    	end
                    else if(PWRITE && (PWDATA === 32'hx || PWDATA === 32'hz)) begin
                        PSLVERR <= 1;
			//PRDATA <= 32'h0;
                    end
                    else if(!PWRITE) begin
                        PRDATA <= mem[PADDR[31:0]];
                        if(mem[PADDR[31:0]] == 32'hffffffff)
                            PSLVERR <= 1; 
		    	    //PRDATA <= 32'h0;
 
                        end
		    else if(PWRITE && !PSLVERR) begin
                    	mem[PADDR[31:0]] = PWDATA;
                	end
                    next_state <= ACCESS;
                end   
                else
                    	next_state <= IDLE;
            end
 
            ACCESS:
	    begin
	      	//PREADY<=0;
	      	if(PSEL==0 & PENABLE==0) begin
              		next_state  <= IDLE;
			PREADY<=0;
	      		end
 
	      	else if(PSEL==1 & PENABLE==0)begin
		      	next_state  <= SETUP; 
		      	PREADY<=0;
	      	end
 
              	else
              	       	next_state  <= ACCESS;
             end
       endcase
   end
 
endmodule
