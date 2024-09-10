//-----------------------------------------------------------------------------
// Title         : UART Tx submodule
// Project       : 
//-----------------------------------------------------------------------------
// File          : uart_tx.sv
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


module uart_tx # (
    parameter logic [31:0] FREQ_CLK=100000000,
    parameter logic [31:0] TX_SPEED=115200
    )(
    input logic       Clk,
    input logic       Rst_n,
    input logic       Start,
    input logic [7:0] Data,
    output logic      EOT,
    output logic      TXD
    );

    // Params
    localparam logic [31:0] PULSE_END_OF_COUNT = FREQ_CLK / TX_SPEED;

    // Typedefs
    typedef enum logic[1:0] {
                 IDLE = 0,
                 START_BIT = 1,
                 SEND_DATA = 2,
                 STOP_BIT = 3
                 } state_t;
    state_t state, next_state;

    // Signals
    logic        load_data;
    logic [7:0]  data_reg;
    logic        bit_end;
    logic        data_send_end;
    logic        bit_ctr_ena;
    logic [31:0] period_cnt;
    logic [31:0] bit_cnt;


    // Comb logic
    assign bit_end = (state != IDLE && period_cnt == PULSE_END_OF_COUNT) ? 1'b1 : 1'b0;
    assign data_send_end = (state == SEND_DATA && bit_cnt == 7 && bit_end) ? 1'b1 : 1'b0;

    // TX line output
    always_comb begin
        unique case (state)
            IDLE:      TXD = 1'b1;
            START_BIT: TXD = 1'b0;
            SEND_DATA: TXD = data_reg[bit_cnt];
            STOP_BIT:  TXD = 1'b1;
            default:   TXD = 1'b1;
        endcase
    end

    // Comb FSM
    always_comb begin
        next_state  = state;
        bit_ctr_ena = 1'b0;
        load_data   = 1'b0;
        EOT         = 1'b0;

        unique case (state)
            IDLE : begin
                EOT = 1'b1;
                bit_ctr_ena = 1'b0;
                if (Start) begin
                    next_state = START_BIT;
                    EOT = 1'b0;
                end
            end

            START_BIT : begin
                bit_ctr_ena = 1'b1;
                load_data = 1'b1;
                if (bit_end) begin
                    next_state = SEND_DATA;
                end
            end

            SEND_DATA : begin
                bit_ctr_ena = 1'b1;
                if (data_send_end) begin
                    next_state = STOP_BIT;
                end
            end

            STOP_BIT : begin
                EOT = 1'b0;
                if (bit_end) begin
                    next_state = IDLE;
                    bit_ctr_ena = 1'b0;
                end
                else begin
                    next_state = STOP_BIT;
                    bit_ctr_ena = 1'b1;
                end
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


    // Period counter within bits
    always_ff @(posedge Clk) begin
        if (!Rst_n) begin
            period_cnt <= 0;
        end
        else if (bit_ctr_ena == 1'b1) begin
            if (period_cnt == PULSE_END_OF_COUNT)
                period_cnt <= 0;
            else
                period_cnt <= period_cnt + 1;
        end
        else
            period_cnt <= 0;
    end


    // Bit count within TX
    always_ff @(posedge Clk) begin
        if (!Rst_n) begin
            bit_cnt <= 0;
        end else begin
            if (state == SEND_DATA) begin
                if (bit_end) begin
                    if (bit_cnt == 7)
                        bit_cnt <= 0;
                    else
                        bit_cnt <= bit_cnt + 1;
                end
            end
            else
                bit_cnt <= 0;
        end
    end


    // Input registering
    always_ff @(posedge Clk) begin
        if (!Rst_n) begin
            data_reg <= 'h0;
        end
        else if (load_data == 1'b1) begin
            data_reg <= Data;
        end
    end


endmodule
