//-----------------------------------------------------------------------------
// Title         : Binary to BCD converter
// Project       :
//-----------------------------------------------------------------------------
// File          : bin2bcd.sv
// Author        : Gonzalo Martinez Larumbe
// Created       : 2020/02/16
// Last modified : 2023/08/26
//-----------------------------------------------------------------------------
// Description :
// Double Dabble based Binary to BCD converter
//   - https://en.wikipedia.org/wiki/Double_dabble
//-----------------------------------------------------------------------------
// Copyright (c) Gonzalo Martinez Larumbe  <gonzalomlarumbe@gmail.com>
//
//------------------------------------------------------------------------------
// Modification history :
// 2020/02/16 : created
//-----------------------------------------------------------------------------

module bin2bcd # (
    parameter BIN_WIDTH = 8,
    parameter DEC_DIGITS = 2
    ) (
    input logic                     Clk,
    input logic                     Rst_n,
    input logic [BIN_WIDTH-1:0]     DataBin,
    input logic                     Start,
    output logic [DEC_DIGITS*4-1:0] DataBCD,
    output logic                    Done
    );

    typedef enum logic [2:0] {
                 IDLE,
                 SHIFT,
                 CHECK_SHIFT_INDEX,
                 ADD,
                 CHECK_DIGIT_INDEX,
                 BCD_DONE
                 } state_t;

    state_t state;
    logic [DEC_DIGITS*4-1:0] bcd_i;          // BCD output vector
    logic [BIN_WIDTH-1:0]    databin_i;      // Input binary data being shifted
    logic [DEC_DIGITS-1:0]   digit_idx;      // Decimal digit being indexed
    logic [7:0]              loop_count = 0; // Number of loops performed = BIN_WIDTH
    logic [3:0]              bcd_digit;      // Current BCD digit


    // Seq FSM
    always_ff @(posedge Clk) begin
        if (!Rst_n) begin
            Done       <= 1'b0;
            bcd_i      <= '0;
            databin_i  <= '0;
            digit_idx  <= '0;
            loop_count <= '0;
            state      <= IDLE;
        end
        else begin
            unique case (state)

                IDLE : begin
                    Done <= 1'b0;
                    if (Start) begin
                        databin_i <= DataBin;
                        state     <= SHIFT;
                        bcd_i     <= 0;
                    end
                end


                SHIFT : begin
                    bcd_i     <= bcd_i << 1;
                    databin_i <= databin_i << 1;
                    bcd_i[0]  <= databin_i[BIN_WIDTH-1];
                    state     <= CHECK_SHIFT_INDEX;
                end


                CHECK_SHIFT_INDEX : begin
                    if (loop_count == BIN_WIDTH-1) begin
                        loop_count <= 0;
                        state      <= BCD_DONE;
                    end
                    else begin
                        loop_count <= loop_count + 1;
                        state      <= ADD;
                    end
                end


                ADD : begin
                    if (bcd_digit > 4) begin
                        bcd_i[(digit_idx*4)+:4] <= bcd_digit + 3;
                    end
                    state <= CHECK_DIGIT_INDEX;
                end


                CHECK_DIGIT_INDEX : begin
                    if (digit_idx == DEC_DIGITS-1) begin
                        digit_idx <= 0;
                        state     <= SHIFT;
                    end
                    else begin
                        digit_idx <= digit_idx + 1;
                        state     <= ADD;
                    end
                end


                BCD_DONE : begin
                    Done  <= 1'b1;
                    state <= IDLE;
                end


                default :
                    state <= IDLE;

            endcase
        end
    end


    // Comb logic and output continous assignment
    assign bcd_digit = bcd_i[digit_idx*4 +: 4];
    assign DataBCD = bcd_i;


endmodule : bin2bcd
