//-----------------------------------------------------------------------------
// Title         : Binary to BCD converter Testbench
// Project       : 
//-----------------------------------------------------------------------------
// File          : tb_bin2bcd.sv
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


module tb_bin2bcd () ;

    // Simulation parameters
    timeprecision 1ps;
    timeunit      1ns;
    localparam CLKT = 10ns;  // 100 MHz

    localparam BIN_WIDTH = 8;
    localparam DEC_DIGITS = 2;

    logic 		     Clk = 1'b0;
    logic 		     Rst_n = 1'b1;

    /* DUT Inputs */
    logic [BIN_WIDTH-1:0]    DataBin = 'h0;
    logic 		     Start = 1'b0;
    /* DUT Outputs */
    logic [DEC_DIGITS*4-1:0] DataBCD;
    logic 		     Done;


    // System Clock
    always begin
        #(CLKT/2) Clk = ~Clk;
    end

    // DUT Instantiation
    bin2bcd # (
        .BIN_WIDTH  (BIN_WIDTH),
        .DEC_DIGITS (DEC_DIGITS)
        ) I_DUT (
        .Clk     (Clk),
        .Rst_n   (Rst_n),
        .DataBin (DataBin),
        .Start   (Start),
        .DataBCD (DataBCD),
        .Done    (Done)
        );


    // Tasks
    task reset_system;
        repeat (10) @(posedge Clk);
        Rst_n = 0;
        repeat (10) @(posedge Clk);
        Rst_n = 1;
        repeat (10) @(posedge Clk);
    endtask : reset_system


    task convert_binary2bcd (input logic [BIN_WIDTH-1:0] data);
	DataBin <= data;
	Start <= 1'b1;
	@(posedge Clk)
	Start <= 1'b0;
	@(posedge Done);
	@(posedge Clk);
	$display("@%0d: Conversion for %0h done", $time, DataBin);
    endtask: convert_binary2bcd



    // === TB Setup === \\
    //$timeformat params:
    //1) Scaling factor (–9 for nanoseconds, –12 for picoseconds)
    //2) Number of digits to the right of the decimal point
    //3) A string to print after the time value
    //4) Minimum field width
    initial begin
        $dumpfile("tb_misc.lx2");  // iverilog, vpp & gtkwave
        $dumpvars(0, tb_bin2bcd);     // Module Output file
        $timeformat(-9, 3, "ns", 8);
    end


    // Stimuli
    initial begin
        reset_system;

	convert_binary2bcd(8'd25);
	convert_binary2bcd(8'd30);
	convert_binary2bcd(8'd35);
	convert_binary2bcd(8'd40);

        $display("@%0d: TEST PASSED", $time);
        $finish;
    end


endmodule // tb_bin2bcd
