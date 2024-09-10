//-----------------------------------------------------------------------------
// Title         : CPU Testbench
// Project       : 
//-----------------------------------------------------------------------------
// File          : tb_cpu.sv
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

module tb_cpu () ;

    // Simulation parameters
    timeprecision 1ps;
    timeunit      1ns;
    localparam CLKT = 10ns;  // 100 MHz

    // Non-auto signals
    logic        Clk         = 1'b0;
    logic        Rst_n       = 1'b1;

    /* DUT Inputs */
    logic [11:0] ROM_Data;
    logic [7:0]  DataIn      = '0;
    logic [7:0]  ALU_DataOut = '0;
    logic        DMA_Ready   = 1'b1;
    logic        DMA_Req     = 1'b0;
    logic        FlagC       = 1'b0;
    logic        FlagE       = 1'b0;
    logic        FlagN       = 1'b0;
    logic        FlagZ       = 1'b0;

    /* DUT Outputs */
    alu_op       ALU_op;
    logic        DMA_Ack;
    logic        DMA_Tx_Start;
    logic [7:0]  Databus;
    logic [7:0]  RAM_Addr;
    logic        RAM_Cs;
    logic        RAM_Oen;
    logic        RAM_Wen;
    logic [11:0] ROM_Addr;
    logic [7:0]  ALU_DataIn;
    logic [7:0]  DataOut;

    // System Clock
    always begin
        #(CLKT/2) Clk = ~Clk;
    end


    cpu I_CPU (
        .Clk          (Clk),
        .Rst_n        (Rst_n),
        // ROM
        .ROM_Addr     (ROM_Addr),
        .ROM_Data     (ROM_Data),
        // DMA
        .DMA_Req      (DMA_Req),
        .DMA_Ready    (DMA_Ready),
        .DMA_Ack      (DMA_Ack),
        .DMA_Tx_Start (DMA_Tx_Start),
        // RAM interface
        .RAM_Addr     (RAM_Addr),
        .RAM_Cs       (RAM_Cs),
        .RAM_Wen      (RAM_Wen),
        .RAM_Oen      (RAM_Oen),
        .DataOut      (DataOut),
        .DataIn       (DataIn),
        // ALU
        .ALU_DataIn   (ALU_DataIn),
        .ALU_DataOut  (ALU_DataOut),
        .ALU_op       (ALU_op),
        .FlagZ        (FlagZ),
        .FlagC        (FlagC),
        .FlagN        (FlagN),
        .FlagE        (FlagE)
        );



    // === TB Setup === \\
    //$timeformat params:
    //1) Scaling factor (–9 for nanoseconds, –12 for picoseconds)
    //2) Number of digits to the right of the decimal point
    //3) A string to print after the time value
    //4) Minimum field width
    initial begin
        $dumpfile("tb_cpu.lx2");  // iverilog, vpp & gtkwave
        $dumpvars(0, tb_cpu);     // Module Output file
        $timeformat(-9, 3, "ns", 8);
    end


    // ROM Model
    logic [11:0] ROM [4096];
    assign ROM_Data = ROM[ROM_Addr];

    task init_rom ();
        $display("@%0d: Initializing ROM", $time);
        // Sum 2 and 3
        ROM['h0]  = {TYPE_3, LD_SRC_CONSTANT, DST_A}; // LD #2 Ra
        ROM['h1]  = 8'h2;
        ROM['h2]  = {TYPE_3, LD_SRC_CONSTANT, DST_B}; // LD #3 Rb
        ROM['h3]  = 8'h3;
        ROM['h4]  = {TYPE_1, ALU_ADD};
        // And store result in memory addres 0x40
        ROM['h5]  = {TYPE_3, WR_SRC_ACC, DST_MEM}; // MV Acc #40
        ROM['h6]  = 8'h40;
        // Readback from address 0x40
        ROM['h7]  = {TYPE_3, LD_SRC_MEM, DST_A}; // LD  0x40 Ra
        ROM['h8]  = 8'h40;
        // Shift operations (acc)
        ROM['h9]  = {TYPE_1, ALU_SHIFTL}; // SHL
        ROM['hA]  = {TYPE_1, ALU_SHIFTR}; // SHR
        // Jump to address 0x30
        ROM['hB] = {TYPE_1, ALU_ASCII2BIN};
        ROM['hC] = {TYPE_1, ALU_BIN2ASCII};
        ROM['hD] = {TYPE_1, ALU_AND};
        // DMA_TX
        ROM['hD] = {TYPE_4, 6'h0};
        ROM['hE] = {TYPE_2, JMP_UNCOND};
        ROM['hF] = 8'h20;
        // Infinite end loop
        ROM['h20] = {TYPE_2, JMP_UNCOND};
        ROM['h21] = 8'h20;
    endtask: init_rom


    // Tasks
    task reset_system;
        repeat (10) @(posedge Clk);
        Rst_n <= 0;
        repeat (10) @(posedge Clk);
        Rst_n <= 1;
        repeat (10) @(posedge Clk);
    endtask : reset_system


    task dma_req ();
	// CPU must grant buses to DMA and stay @ IDLE
	DMA_Req <= 1'b1;
        repeat (1000) @(posedge Clk);
	DMA_Req <= 1'b0;
    endtask: dma_req


    // Stimuli
    initial begin
        init_rom;
        reset_system;
        repeat (1000) @(posedge Clk);
	dma_req;
        repeat (1000) @(posedge Clk);
        $display("@%0d: TEST PASSED", $time);
        $finish;
    end


    // TX DMA Management
    initial begin
	@(posedge DMA_Tx_Start);
	@(posedge Clk);
	DMA_Ready <= 1'b0;
	DMA_Req   <= 1'b1;
	repeat (100) @(posedge Clk);
	DMA_Req   <= 1'b0;
	DMA_Ready <= 1'b1;
    end


endmodule // tb_cpu
