//-----------------------------------------------------------------------------
// Title         : Testbench clocks
// Project       : 
//-----------------------------------------------------------------------------
// File          : tb_clocks.sv
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


module tb_clocks (
    output logic Clk
    );

    localparam CLKT = 10ns;  // 100 MHz

    // System Clock
    always begin
        #(CLKT/2) Clk = ~Clk;
    end

    // Initial clock values
    initial begin
        Clk = 0;
    end


endmodule: tb_clocks
