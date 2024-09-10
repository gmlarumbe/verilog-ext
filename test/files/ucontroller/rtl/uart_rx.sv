//-----------------------------------------------------------------------------
// Title         : UART Rx submodule
// Project       : 
//-----------------------------------------------------------------------------
// File          : uart_rx.sv
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


module uart_rx # (
    parameter logic [31:0] FREQ_CLK = 100000000,
    parameter logic [31:0] TX_SPEED = 115200
    )(
    input logic  Clk,
    input logic  Rst_n,
    input logic  RXD,
    output logic RX_Valid,
    output logic RX_Load
    );

    // Params
    localparam logic [31:0] PULSE_END_OF_COUNT = FREQ_CLK / TX_SPEED;
    localparam logic [31:0] PULSE_END_OF_COUNT_HALF = FREQ_CLK / (2*TX_SPEED);

    // Typedefs
    typedef enum logic[2:0] {
                 IDLE = 0,
                 START_BIT = 1,
                 HALF_BIT_DLY = 2,
                 RCV_DATA = 3,
                 STOP_BIT = 4
                 } state_t;
    state_t state, next_state;

    // Signals
    logic [31:0] period_cnt;
    logic period_ctr_ena;
    logic [31:0] bit_cnt;
    logic bit_ctr_ena;
    logic bit_end;
    logic [31:0] half_bit_cnt;
    logic half_bit_ctr_ena;
    logic half_bit_rstn;
    logic data_rcv_end;


    // Comb logic
    assign bit_end = (state != IDLE && period_cnt == PULSE_END_OF_COUNT) ? 1'b1 : 1'b0;
    assign data_rcv_end = (state == RCV_DATA && bit_cnt == 7 && bit_end) ? 1'b1 : 1'b0;


    // Comb FSM
    always_comb begin
        next_state       = state;
        RX_Valid         = 1'b0;
        RX_Load          = 1'b0;
        half_bit_ctr_ena = 1'b0;
        period_ctr_ena   = 1'b1;
        bit_ctr_ena      = 1'b0;
        half_bit_rstn    = 1'b1;

        unique case (state)

            IDLE : begin
                period_ctr_ena = 1'b0;
                if (RXD == 1'b0)
                    next_state = START_BIT;
                else
                    next_state = IDLE;
            end

            START_BIT : begin
                period_ctr_ena = 1'b0;
                half_bit_ctr_ena = 1'b1;
                if (half_bit_cnt == PULSE_END_OF_COUNT_HALF) begin
                    half_bit_rstn    = 1'b0;
                    half_bit_ctr_ena = 1'b0;
                    next_state       = HALF_BIT_DLY;
                end
            end

            HALF_BIT_DLY : begin
                bit_ctr_ena = 1'b1;
                if (bit_end) begin
                    next_state = RCV_DATA;
                    RX_Valid = 1'b1;
                end
            end

            RCV_DATA : begin
                bit_ctr_ena = 1'b1;
                if (bit_end) begin
                    RX_Valid = 1'b1;
                    if (data_rcv_end) begin
                        next_state = STOP_BIT;
                        bit_ctr_ena = 1'b0;
                    end
                end
            end

            STOP_BIT : begin
                if (bit_end) begin
                    RX_Load = 1'b1;
                    next_state = IDLE;
                end
                else begin
                    next_state = STOP_BIT;
                end
            end

            default : begin
                ;
            end

        endcase
    end


    // Seq FSM
    always_ff @(posedge Clk) begin
        if (!Rst_n) begin
            state <= IDLE;
        end else begin
            state <= next_state;
        end
    end


    // Half-bit counter
    always_ff @(posedge Clk) begin
        if (!Rst_n) begin
            half_bit_cnt <= 0;
        end else begin
            if (half_bit_ctr_ena) begin
                half_bit_cnt <= half_bit_cnt + 1;
            end
            if (!half_bit_rstn) begin
                half_bit_cnt <= 0;
            end
        end
    end


    // Period counter within bits
    always_ff @(posedge Clk) begin
        if (!Rst_n) begin
            period_cnt <= 0;
        end else begin
            if (period_ctr_ena) begin
                if (period_cnt == PULSE_END_OF_COUNT) begin
                    period_cnt <= 0;
                end
                else begin
                    period_cnt <= period_cnt + 1;
                end
            end
        end
    end

    // RX Bit count
    always_ff @(posedge Clk) begin
        if (!Rst_n) begin
            bit_cnt <= 0;
        end else begin
            if (bit_ctr_ena) begin
                if (bit_end)
                    if (bit_cnt == 7)
                        bit_cnt <= 0;
                    else
                        bit_cnt <= bit_cnt + 1;
            end
            else begin
                bit_cnt <= 0;
            end
        end
    end


endmodule
