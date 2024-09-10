//-----------------------------------------------------------------------------
// Title         : RAM Top module
// Project       : 
//-----------------------------------------------------------------------------
// File          : ram.sv
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

module ram (
    input logic        Clk,
    input logic        Rst_n,
    input logic        Cs,
    input logic        Wen,
    input logic        Oen,
    input logic [7:0]  Address,
    input logic [7:0]  DataIn,
    output logic [7:0] DataOut,
    output logic [7:0] Switches,
    output logic [7:0] Temp
    );


    enum logic {REGS, GP} last_mem_space;

    logic       Cs_gp;
    logic       Cs_regs;
    logic [7:0] DataOut_gp;
    logic [7:0] DataOut_regs;

    gp_ram I_GP_RAM (
        .Clk     (Clk),
        .Rst_n   (Rst_n),
        .Cs      (Cs_gp),
        .Wen     (Wen),
        .Oen     (Oen),
        .Address (Address),
        .DataIn  (DataIn),
        .DataOut (DataOut_gp)
        );


    regs_ram I_REGS_RAM (
        .Clk      (Clk),
        .Rst_n    (Rst_n),
        .Cs       (Cs_regs),
        .Wen      (Wen),
        .Oen      (Oen),
        .Address  (Address),
        .DataIn   (DataIn),
        .DataOut  (DataOut_regs),
        .Switches (Switches),
        .Temp     (Temp)
        );


    // Aux seq logic to resolve DataOut bus driving
    always_ff @(posedge Clk) begin
        if (!Rst_n)
            last_mem_space <= REGS;
        else if (Cs) begin
            if (Address < GP_RAM_BASE)
                last_mem_space <= REGS;
            else
                last_mem_space <= GP;
        end
    end

    // Aux comb logic to resolve DataOut bus driving
    assign DataOut = (last_mem_space == REGS) ? DataOut_regs : DataOut_gp;

    always_comb begin
        if (Address < GP_RAM_BASE) begin
            Cs_regs = Cs;
            Cs_gp   = 1'b0;
        end
        else begin
            Cs_regs = 1'b0;
            Cs_gp   = Cs;
        end
    end


endmodule
