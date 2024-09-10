//-----------------------------------------------------------------------------
// Title         : Shift Register
// Project       : 
//-----------------------------------------------------------------------------
// File          : sreg.sv
// Author        : Gonzalo Martinez Larumbe
// Created       : 2020/02/16
// Last modified : 2020/02/16
//-----------------------------------------------------------------------------
// Description :
// 8-bit shift register to load UART rx data into FIFO
//-----------------------------------------------------------------------------
// Copyright (c) Gonzalo Martinez Larumbe  <gonzalomlarumbe@gmail.com> 
//
//------------------------------------------------------------------------------
// Modification history :
// 2020/02/16 : created
//-----------------------------------------------------------------------------


module sreg (
    input logic Clk,
    input logic Rst_n,
    input logic Ena,
    input logic Din,
    output logic [7:0] Qout
    );

    logic [7:0] data_out;

    always_ff @(posedge Clk) begin
        if (!Rst_n) begin
            data_out <= 'h0;
        end else begin
            if(Ena == 1'b1) begin
                data_out[7] <= Din;
                for (int i=1; i<=7; i++) begin
                    data_out[i-1] <= data_out[i];
                end
            end
        end
    end

    assign Qout = data_out;

endmodule
