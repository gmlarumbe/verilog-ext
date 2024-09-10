//-----------------------------------------------------------------------------
// Title         : RAM Arbiter
// Project       : 
//-----------------------------------------------------------------------------
// File          : ram_arbiter.sv
// Author        : Gonzalo Martinez Larumbe
// Created       : 2020/02/16
// Last modified : 2020/02/16
//-----------------------------------------------------------------------------
// Description :
// Arbitrating between DMA and CPU for RAM buses and control signals
//-----------------------------------------------------------------------------
// Copyright (c) Gonzalo Martinez Larumbe  <gonzalomlarumbe@gmail.com> 
//
//------------------------------------------------------------------------------
// Modification history :
// 2020/02/16 : created
//-----------------------------------------------------------------------------


module ram_arbiter (
    input logic        Clk,
    input logic        Rst_n,
    // Input selects
    input logic        DMA_Bus_req,
    input logic        DMA_Bus_grant,
    input logic        DMA_Idle,
    // Arbitrating outputs
    input logic [7:0]  CPU_DataOut,
    input logic [7:0]  DMA_DataOut,
    output logic [7:0] RAM_DataIn,
    input logic [7:0]  CPU_Address,
    input logic [7:0]  DMA_Address,
    output logic [7:0] RAM_Address,
    input logic        CPU_Cs,
    input logic        DMA_Cs,
    output logic       RAM_Cs,
    input logic        CPU_Oen,
    input logic        DMA_Oen,
    output logic       RAM_Oen,
    input logic        CPU_Wen,
    input logic        DMA_Wen,
    output logic       RAM_Wen
    );

    typedef enum logic {GRANT_CPU, GRANT_DMA} state_t;
    state_t state;


    // Seq FSM
    always_ff @(posedge Clk) begin
        if (!Rst_n) begin
            state <= GRANT_CPU;
        end
        else begin
            unique case (state)
                GRANT_CPU: begin
                    if (DMA_Bus_req & DMA_Bus_grant)
                        state <= GRANT_DMA;
                end

                GRANT_DMA: begin
                    if (DMA_Idle)
			state <= GRANT_CPU;
                end

                default : ;
            endcase
        end
    end


    // Comb Logic
    assign RAM_DataIn  = (state == GRANT_CPU) ? CPU_DataOut : DMA_DataOut;
    assign RAM_Address = (state == GRANT_CPU) ? CPU_Address : DMA_Address;
    assign RAM_Cs      = (state == GRANT_CPU) ? CPU_Cs	    : DMA_Cs;
    assign RAM_Wen     = (state == GRANT_CPU) ? CPU_Wen	    : DMA_Wen;
    assign RAM_Oen     = (state == GRANT_CPU) ? CPU_Oen	    : DMA_Oen;

endmodule: ram_arbiter
