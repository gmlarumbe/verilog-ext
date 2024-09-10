//-----------------------------------------------------------------------------
// Title         : ALU
// Project       :
//-----------------------------------------------------------------------------
// File          : alu.sv
// Author        : Gonzalo Martinez Larumbe
// Created       : 2020/02/16
// Last modified : 2023/05/30
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

module alu (
    input logic        Clk,
    input logic        Rst_n,
    input alu_op       ALU_op,
    input logic [7:0]  InData,
    output logic [7:0] OutData,
    output logic       FlagZ,
    output logic       FlagC,
    output logic       FlagN,
    output logic       FlagE
    );

    localparam logic [7:0] ASCII_BINARY_0 = 8'b00110000;
    localparam logic [7:0] ASCII_BINARY_9 = 8'b00111001;

    logic [7:0] InA, InB, InAcc, InIndex;
    logic       InZ, InC, InN, InE, EnA, EnB, EnAcc, EnIndex, EnZ, EnC, EnN, EnE;
    logic [7:0] OutA, OutB, OutAcc, OutIndex;

    always_comb begin
        OutData   = 'h0;
        EnA = 1'b0;  EnB = 1'b0;  EnAcc = 1'b0;  EnIndex = 1'b0;
        EnZ = 1'b1;  EnC = 1'b1;  EnN   = 1'b1;  EnE = 1'b1;
        InA = 'h0 ;  InB = 'h0;   InAcc = 'h0;   InIndex = 'h0;
        InZ = 1'b0;  InC = 1'b0;  InN   = 1'b0;  InE = 1'b0;

        unique case (ALU_op)
            nop : begin
                ;
            end

            op_lda : begin
                EnA = 1'b1;
                InA = InData;
            end

            op_ldb : begin
                EnB = 1'b1;
                InB = InData;
            end

            op_ldacc : begin
                EnAcc = 1'b1;
                InAcc = InData;
            end

            op_ldid : begin
                EnIndex = 1'b1;
                InIndex = InData;
            end

            op_mvacc2id : begin
                EnIndex = 1'b1;
                InIndex = OutAcc;
            end

            op_mvacc2a : begin
                EnA = 1'b1;
                InA = OutAcc;
            end

            op_mvacc2b : begin
                EnB = 1'b1;
                InB = OutAcc;
            end

            op_add : begin
                EnAcc = 1'b1;
                InAcc = OutA + OutB;

                if ((OutA + OutB) == 8'b00000000) begin
                    InZ = 1'b1;
                end
                if ((OutA + OutB) < OutA || (OutA + OutB) < OutB) begin // Sum is less than any of the operands due to overflow (carry)
                    InC = 1'b1;
                end
                if ((OutA + OutB) > 8'b00001111) begin
                    InN = 1'b1;
                end
            end

            op_sub : begin
                EnAcc = 1'b1;
                InAcc = OutA - OutB;
                if ((OutA - OutB) == 8'b00000000) begin
                    InZ = 1'b1;
                end
                if (OutA < OutB) begin // Negative result due to overflow (carry)
                    InC = 1'b1;
                end
                if ((OutA - OutB) > 8'b00001111) begin
                    InN = 1'b1;
                end
            end

            op_shiftl : begin
                EnAcc = 1'b1;
                InAcc = OutAcc << 1;
            end

            op_shiftr : begin
                EnAcc = 1'b1;
                InAcc = OutAcc >> 1;
            end

            op_and : begin
                EnAcc = 1'b1;
                InAcc = OutA & OutB;
                if ((OutA & OutB) == 'h0) begin
                    InZ = 1'b1;
                end
            end

            op_or : begin
                EnAcc = 1'b1;
                InAcc = OutA | OutB;
                if ((OutA | OutB) == 'h0) begin
                    InZ = 1'b1;
                end
            end

            op_xor : begin
                EnAcc = 1'b1;
                InAcc = OutA ^ OutB;
                if ((OutA ^ OutB) == 'h0) begin
                    InZ = 1'b1;
                end
            end

            op_cmpe : begin
                if (OutA == OutB) begin
                    InZ = 1'b1;
                end
            end

            op_cmpl : begin
                if (OutA < OutB) begin
                    InZ = 1'b1;
                end
            end

            op_cmpg : begin
                if (OutA > OutB) begin
                    InZ = 1'b1;
                end
            end

            op_ascii2bin : begin
                EnAcc = 1'b1;
                if ((OutA < ASCII_BINARY_0) || (OutA > ASCII_BINARY_9)) begin
                    InAcc = 8'b11111111;
                    InE = 1'b1;
                end
                else begin
                    InAcc = OutA - ASCII_BINARY_0;
                end
            end

            op_bin2ascii : begin
                EnAcc = 1'b1;
                if (OutA > 'h9) begin
                    InAcc = 8'b11111111;
                    InE = 1'b1;
                end
                else begin
                    InAcc = OutA + ASCII_BINARY_0;
                end
            end

            op_oeacc : begin
                OutData = OutAcc;
            end

            default : begin
                ;
            end

        endcase
    end


    always_ff @(posedge Clk) begin
        if (!Rst_n) begin
            OutA     <= 'h0;
            OutB     <= 'h0;
            OutAcc   <= 'h0;
            OutIndex <= 'h0;
            FlagZ    <= 1'b0;
            FlagC    <= 1'b0;
            FlagN    <= 1'b0;
            FlagE    <= 1'b0;
        end else begin
            if (EnA)     OutA     <= InA;
            if (EnB)     OutB     <= InB;
            if (EnAcc)   OutAcc   <= InAcc;
            if (EnIndex) OutIndex <= InIndex;
            if (EnZ)     FlagZ    <= InZ;
            if (EnC)     FlagC    <= InC;
            if (EnE)     FlagE    <= InE;
            if (EnN)     FlagN    <= InN;
        end
    end


endmodule
