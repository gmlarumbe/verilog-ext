//-----------------------------------------------------------------------------
// Title         : FIFO wrapper
// Project       : 
//-----------------------------------------------------------------------------
// File          : fifo_wrapper.sv
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


module fifo_wrapper (
    input logic       Clk,
    input logic       Rst_n,
    input logic [7:0] Din,
    input logic       Wren,
    input logic       Rden,
    input logic [7:0] Dout,
    input logic       Full,
    input logic       Empty
    );


    fifo_generator_0 I_FIFO_GENERATOR_0 (
	.clk   (Clk),
	.rst   (~Rst_n),
	.din   (Din),
	.wr_en (Wren),
	.rd_en (Rden),
	.dout  (Dout),
	.full  (Full),
	.empty (Empty)
	);

endmodule: fifo_wrapper
