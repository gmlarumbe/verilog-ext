//-----------------------------------------------------------------------------
// Title         : RAM Testbench
// Project       : 
//-----------------------------------------------------------------------------
// File          : tb_ram.sv
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


module tb_ram ();

    // Simulation parameters
    timeprecision 1ps;
    timeunit      1ns;
    localparam CLKT = 10ns;  // 100 MHz

    // Non-auto signals
    logic 	Clk 	= 1'b0;
    logic 	Rst_n 	= 1'b1;

    logic [7:0] Address = '0;
    logic 	Cs 	= '0;
    logic [7:0] DataIn 	= '0;
    logic 	Oen 	= '0;
    logic 	Wen 	= '0;

    /* DUT Outputs */
    logic [7:0] DataOut;
    logic [7:0] Switches;
    logic [7:0] Temp;


    // System Clock
    always begin
        #(CLKT/2) Clk = ~Clk;
    end


    // DUT Instantiation
    ram DUT (
        // Outputs
        .DataOut  (DataOut),
        .Switches (Switches),
        .Temp     (Temp),
        // Inputs
        .Clk      (Clk),
        .Rst_n    (Rst_n),
        .Cs       (Cs),
        .Wen      (Wen),
        .Oen      (Oen),
        .Address  (Address),
        .DataIn   (DataIn)
        );


    // Tasks
    task reset_system;
        repeat (10) @(posedge Clk);
        Rst_n = 0;
        repeat (10) @(posedge Clk);
        Rst_n = 1;
        repeat (10) @(posedge Clk);
    endtask : reset_system


    task write_ram (input logic [7:0] addr, input logic [7:0] data);
        @(posedge Clk);
        Cs      <= 1'b1;
        Wen     <= 1'b1;
        Oen     <= 1'b0;
        Address <= addr;
        DataIn  <= data;
        @(posedge Clk);
        Cs      <= 1'b0;
        Wen     <= 1'b0;
        Address <= 'h0;
        DataIn  <= 'h0;
        @(posedge Clk);
    endtask: write_ram


    task read_ram (input logic [7:0] addr);
        @(posedge Clk);
        Cs      <= 1'b1;
        Wen     <= 1'b0;
        Oen     <= 1'b1;
        Address <= addr;
        @(posedge Clk);
        Cs      <= 1'b0;
        Oen     <= 1'b0;
        Address <= 'h0;
        @(posedge Clk);
    endtask: read_ram


    task test_regs;
        for (int i=0; i<'h40; ++i) begin
            tempdata = i;
            write_ram(i, tempdata);
            read_ram(i);
            assert(DataOut == tempdata) else $display("@%0d: Register not implemented @ address %0x ", $time, i);
        end
    endtask: test_regs


    task test_gp;
        for (int i='h40; i<'hFF; ++i) begin
            tempdata = i;
            write_ram(i, tempdata);
            read_ram(i);
            assert(DataOut == tempdata) else $display("@%0d: GP ram r/w error @ address %0x ", $time, i);
        end
    endtask: test_gp


    // === TB Setup === \\
    //$timeformat params:
    //1) Scaling factor (–9 for nanoseconds, –12 for picoseconds)
    //2) Number of digits to the right of the decimal point
    //3) A string to print after the time value
    //4) Minimum field width
    initial begin
        $dumpfile("tb_ram.lx2");  // iverilog, vpp & gtkwave
        $dumpvars(0, tb_ram);     // Module Output file
        $timeformat(-9, 3, "ns", 8);
    end


    logic [7:0] tempdata;
    // Stimuli
    initial begin
        reset_system;
        test_regs;
        test_gp;
        repeat (100) @(posedge Clk);
        $display("@%0d: TEST PASSED", $time);
        $finish;
    end


endmodule // tb_ram
