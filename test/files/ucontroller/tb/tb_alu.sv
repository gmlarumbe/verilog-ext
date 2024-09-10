//-----------------------------------------------------------------------------
// Title         : ALU Testbench
// Project       :
//-----------------------------------------------------------------------------
// File          : tb_alu.sv
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

module automatic tb_alu () ;

    // Simulation parameters
    timeprecision 1ps;
    timeunit      1ns;
    localparam CLKT = 10ns;  // 100 MHz

    logic       Clk   = 1'b0;
    logic       Rst_n = 1'b1;

    logic [7:0] InData;
    logic [7:0] OutData;
    logic       FlagC;
    logic       FlagE;
    logic       FlagN;
    logic       FlagZ;

    alu_op ALU_op;

    // System Clock
    always begin
        #(CLKT/2) Clk = ~Clk;
    end

    // DUT
    alu DUT (
        .Clk     (Clk),
        .Rst_n   (Rst_n),
        .ALU_op  (ALU_op),
        .InData  (InData),
        .OutData (OutData),
        .FlagZ   (FlagZ),
        .FlagC   (FlagC),
        .FlagN   (FlagN),
        .FlagE   (FlagE)
        );


    // Tasks
    task reset_system;
        repeat (10) @(posedge Clk);
        Rst_n = 0;
        repeat (10) @(posedge Clk);
        Rst_n = 1;
        repeat (10) @(posedge Clk);
    endtask : reset_system


    task execute_instruction (input alu_op inst, input logic[7:0] DATA = 'h0);
        localparam integer CYCLES = 10;
        repeat (CYCLES) @(posedge Clk);
        ALU_op = inst;
        InData = DATA;
        repeat (CYCLES) @(posedge Clk);
    endtask : execute_instruction


    task op_one_operand (input logic [7:0] D, input alu_op op);
        execute_instruction(nop);
        execute_instruction(op, D);
        execute_instruction(op_oeacc);
        execute_instruction(nop);
    endtask: op_one_operand


    task op_two_operands (input logic [7:0] A, input logic [7:0] B, input alu_op op);
        execute_instruction(nop);
        execute_instruction(op_lda, A);
        execute_instruction(op_ldb, B);
        execute_instruction(op);
        execute_instruction(op_oeacc);
    endtask: op_two_operands


    task do_add (input logic [7:0] sumA, input logic [7:0] sumB);
        $display("@%0d: Summing %0d and %0d", $time, sumA, sumB);
        op_two_operands(sumA, sumB, op_add);
        assert (OutData == sumA + sumB) $display("@%0d: Obtained: %0d", $time, OutData);
            else $error("@%0d: ERROR: Obtained: %0d", $time, OutData);
    endtask: do_add


    task do_sub (input logic [7:0] subA, input logic [7:0] subB);
        $display("@%0d: Subracting %0d minus %0d", $time, subA, subB);
        op_two_operands(subA, subB, op_sub);
        assert (OutData == subA - subB) $display("@%0d: Obtained: %0d", $time, OutData);
            else $error("@%0d: ERROR: Obtained: %0d", $time, OutData);
    endtask: do_sub


    task do_and (input logic [7:0] andA, input logic [7:0] andB);
        $display("@%0d: ANDing %0x & %0x", $time, andA, andB);
        op_two_operands(andA, andB, op_and);
        assert (OutData == (andA & andB)) $display("@%0d: Obtained: %0x", $time, OutData);
            else $error("@%0d: ERROR: Obtained: %0x", $time, OutData);
    endtask: do_and


    task do_or (input logic [7:0] orA, input logic [7:0] orB);
        $display("@%0d: ORing %0x & %0x", $time, orA, orB);
        op_two_operands(orA, orB, op_or);
        assert (OutData == (orA | orB)) $display("@%0d: Obtained: %0x", $time, OutData);
            else $error("@%0x: ERROR: Obtained: %0d", $time, OutData);
    endtask: do_or


    task do_xor (input logic [7:0] xorA, input logic [7:0] xorB);
        $display("@%0d: XORing %0x & %0x", $time, xorA, xorB);
        op_two_operands(xorA, xorB, op_xor);
        assert (OutData == (xorA ^ xorB)) $display("@%0d: Obtained: %0x", $time, OutData);
            else $error("@%0x: ERROR: Obtained: %0d", $time, OutData);
    endtask: do_xor


    // === TB Setup === \\
    //$timeformat params:
    //1) Scaling factor (–9 for nanoseconds, –12 for picoseconds)
    //2) Number of digits to the right of the decimal point
    //3) A string to print after the time value
    //4) Minimum field width
    initial begin
        $dumpfile("tb_alu.lx2");  // iverilog, vpp & gtkwave
        $dumpvars(0, tb_alu);     // Module Output file
        $timeformat(-9, 3, "ns", 8);
    end


    // Stimuli
    initial begin
        reset_system;
        do_add('h1, 'h1);
        do_add('h3, 'h2);
        do_add('hA, 'hA);
        do_add('hFF, 'h02);

        do_sub('h1, 'h1);
        do_sub('h5, 'h0);
        do_sub('h5, 'h6);
        do_sub('h10, 'h10);

        do_and('hFF, 'h88);
        do_or('h77, 'hCC);
        do_xor('hF0, 'h0F);

        $display("@%0d: TEST PASSED", $time);
        $finish;
    end


endmodule // tb_alu
