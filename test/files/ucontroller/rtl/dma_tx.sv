//-----------------------------------------------------------------------------
// Title         : DMA Tx module
// Project       : 
//-----------------------------------------------------------------------------
// File          : dma_tx.sv
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

module dma_tx (
    input logic        Clk,
    input logic        Rst_n,
    input logic        Ena,
    // System buses
    output logic [7:0] Address,
    input logic [7:0]  Databus,
    // Serial interface
    input logic        TX_Ready,
    output logic       TX_Valid,
    output logic [7:0] TX_Data,
    // RAM Interface
    output logic       Cs,
    output logic       Oen,
    // CPU Interface
    output logic       Bus_req,
    input logic        Bus_grant,
    input logic        Start,
    output logic       Dma_Ready
    );

    typedef enum logic[1:0] {
                 IDLE,
                 BUS_REQUEST,
                 SEND_MSB,
                 SEND_LSB
                 } state_t;

    state_t state, next_state;

    // Comb FSM
    always_comb begin
        next_state = state;
        Address    = '0;
        TX_Data    = '0;
        TX_Valid   = 1'b0;
        Cs         = 1'b0;
        Oen        = 1'b0;
        Bus_req    = 1'b0;
        Dma_Ready  = 1'b0;

        if (Ena) begin
            unique case (state)
                IDLE : begin
                    Dma_Ready = 1'b1;
                    Bus_req   = 1'b0;
                    if (Start) begin
                        next_state = BUS_REQUEST;
                    end
                end

                BUS_REQUEST : begin
                    Bus_req = 1'b1;
                    if (Bus_grant & TX_Ready) begin
                        next_state = SEND_MSB;
                        TX_Valid   = 1'b1;
                    end
                end

                SEND_MSB : begin
                    Bus_req = 1'b1;
                    Cs      = 1'b1;
                    Oen     = 1'b1;
                    Address = DMA_TX_BUFFER_MSB;
                    TX_Data = Databus;
                    if (TX_Ready) begin
                        next_state = SEND_LSB;
                        TX_Valid   = 1'b1;
                    end
                end

                SEND_LSB : begin
                    Bus_req = 1'b1;
                    Cs      = 1'b1;
                    Oen     = 1'b1;
                    Address = DMA_TX_BUFFER_LSB;
                    TX_Data = Databus;
                    if (TX_Ready) begin
                        next_state = IDLE;
                    end
                end

                default : ;

            endcase
        end
    end


    // Seq FSM
    always_ff @(posedge Clk) begin
        if (!Rst_n) begin
            state <= IDLE;
        end else begin
            state <= next_state;
        end
    end


endmodule
