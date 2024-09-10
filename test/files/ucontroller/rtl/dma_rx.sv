//-----------------------------------------------------------------------------
// Title         : DMA Rx module
// Project       : 
//-----------------------------------------------------------------------------
// File          : dma_rx.sv
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

module dma_rx (
    input logic        Clk,
    input logic        Rst_n,
    input logic        Ena,
    output logic       Dma_End,
    // System buses
    output logic [7:0] Address,
    output logic [7:0] Databus,
    // Serial interface
    input logic [7:0]  RX_Data,
    input logic        RX_Full,
    input logic        RX_Empty,
    output logic       Data_Read,
    // RAM Interface
    output logic       Cs,
    output logic       Wena,
    // CPU Interface
    output logic       Bus_req,
    input logic        Bus_grant
    );

    typedef enum logic [3:0] {
                 IDLE,
                 BUS_REQUEST,
                 READ_MSB,
                 RECEIVE_MSB,
                 READ_MID,
                 RECEIVE_MID,
                 READ_LSB,
                 RECEIVE_LSB,
                 DMA_END
                 } state_t;

    state_t state, next_state;


    // Comb FSM
    always_comb begin
        next_state = state;
        Address    = '0;
        Databus    = '0;
        Data_Read  = 1'b0;
        Cs         = 1'b0;
        Wena       = 1'b0;
        Bus_req    = 1'b0;
        Dma_End    = 1'b0;

        if (Ena) begin
            unique case(state)

                IDLE : begin
                    if (!RX_Empty) begin
                        Bus_req = 1'b1;
                        next_state = BUS_REQUEST;
                    end
                end

                BUS_REQUEST : begin
                    Bus_req = 1'b1;
                    if (Bus_grant) begin
                        next_state = READ_MSB;
                    end
                end

                READ_MSB : begin
                    Bus_req    = 1'b1;
                    Data_Read  = 1'b1;
                    next_state = RECEIVE_MSB;
                end

                RECEIVE_MSB : begin
                    Bus_req = 1'b1;
                    Cs      = 1'b1;
                    Wena    = 1'b1;
                    Address = DMA_RX_BUFFER_MSB;
                    Databus = RX_Data;
                    if (!RX_Empty)
                        next_state = READ_MID;
                    else begin
                        next_state = IDLE;
			Dma_End = 1'b1;
		    end
                end

                READ_MID : begin
                    Bus_req    = 1'b1;
                    Data_Read  = 1'b1;
                    next_state = RECEIVE_MID;
                end

                RECEIVE_MID : begin
                    Bus_req = 1'b1;
                    Cs      = 1'b1;
                    Wena    = 1'b1;
                    Address = DMA_RX_BUFFER_MID;
                    Databus = RX_Data;
                    if (!RX_Empty)
                        next_state = READ_LSB;
                    else begin
                        next_state = IDLE;
			Dma_End = 1'b1;
		    end
                end

                READ_LSB : begin
                    Bus_req    = 1'b1;
                    Data_Read  = 1'b1;
                    next_state = RECEIVE_LSB;
                end

                RECEIVE_LSB : begin
                    Bus_req    = 1'b1;
                    Cs         = 1'b1;
                    Wena       = 1'b1;
                    Address    = DMA_RX_BUFFER_LSB;
                    Databus    = RX_Data;
                    next_state = DMA_END;
                end

                DMA_END : begin
                    Dma_End    = 1'b1;
                    Bus_req    = 1'b1;
                    next_state = IDLE;
                end

                default: ;

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
