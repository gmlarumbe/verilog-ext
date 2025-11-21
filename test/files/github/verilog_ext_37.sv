// Generate a synchronous reset
// Reset signal (active low) is released on falling edge of the
// clock, to generate timing violation on rising edges on the clock
module reset_generator (/*AUTOARG*/
                        // Outputs
                        rst_n,
                        // Inputs
                        clk, rst_async
                        );

   input wire clk;
   input      rst_async; // asynchronous reset
   output     rst_n;    // synchronous reset

   input      unused, unused2; // Added to test tags for list_of_port_identifiers

   /*AUTOINPUT*/
   /*AUTOOUTPUT*/

   /*AUTOREG*/
   /*AUTOWIRE*/

   reg        rst_async_m; // can be metastable
   reg        rst_async_r; // can be metastable

   always @(negedge clk or negedge rst_async) begin
      if(rst_async == 1'b0) begin
         /*AUTORESET*/
         // Beginning of autoreset for uninitialized flops
         rst_async_m <= 1'h0;
         rst_async_r <= 1'h0;
         // End of automatics
      end
      else begin
         rst_async_m <= 1'b1; // Can be metastable
         rst_async_r <= rst_async_m;
      end
   end

   // renaming
   assign rst_n = rst_async_r;




endmodule : reset_generator
/*
 Local Variables:
 verilog-library-directories:(
 "."
 )
 End:
 */
