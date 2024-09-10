//-----------------------------------------------------------------------------
// Title         : General Purpose RAM
// Project       : 
//-----------------------------------------------------------------------------
// File          : gp_ram.sv
// Author        : Gonzalo Martinez Larumbe
// Created       : 2020/02/16
// Last modified : 2020/02/16
//-----------------------------------------------------------------------------
// Description :
// 
//-----------------------------------------------------------------------------
// Copyright (c) Gonzalo Martinez Larumbe  <gonzalomlarumbe@gmail.com> 
//
//------------------------------------------------------------------------------
// Modification history :
// 2020/02/16 : created
//-----------------------------------------------------------------------------

import global_pkg::*;

module gp_ram (
    input logic        Clk,
    input logic        Rst_n,
    input logic        Wen,
    input logic        Oen,
    input logic        Cs,
    input logic [7:0]  Address,
    input logic [7:0]  DataIn,
    output logic [7:0] DataOut
    );


    logic [7:0] mem [RAM_DEPTH];

    always @(posedge Clk) begin
        if (!Rst_n) begin
            DataOut <= 'h0;
        end
        else if (Cs) begin
	    // Write
            if (Wen) begin
                mem[Address] <= DataIn;
	    end
	    // Read
	    else if (Oen)
                DataOut <= mem[Address];
	end
	
	else 
            DataOut <= 'h0;
    end


endmodule
