//-----------------------------------------------------------------------------
// Title         : Testbench Hierarchy Top
// Project       : 
//-----------------------------------------------------------------------------
// File          : tb_top.sv
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


module tb_top () ;

    logic        Clk;
    logic        Rst_n;
    logic        RXD;
    logic        TXD;
    logic [7:0]  Temp;
    logic [7:0]  Switches;
    logic [11:0] ROM_Data;
    logic [11:0] ROM_Addr;


    // Clocks
    tb_clocks I_TB_CLOCKS (
        .Clk (Clk)
        );


    // Testbench
    tb_program I_TB_PROGRAM (
        .Clk      (Clk),
        .Rst_n    (Rst_n),
        .TXD      (TXD),
        .RXD      (RXD),
        .Temp     (Temp),
        .Switches (Switches),
        .ROM_Data (ROM_Data),
        .ROM_Addr (ROM_Addr)
        );


    // DUT Instantiation
    ucontroller I_UCONTROLLER (
        .Clk      (Clk),
        .Rst_n    (Rst_n),
        .TXD      (TXD),
        .RXD      (RXD),
        .Temp     (Temp),
        .Switches (Switches),
        .ROM_Data (ROM_Data),
        .ROM_Addr (ROM_Addr)
        );


endmodule
