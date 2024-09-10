//-----------------------------------------------------------------------------
// Title         : DMA Top Testbench
// Project       : 
//-----------------------------------------------------------------------------
// File          : tb_dma.sv
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


module tb_dma () ;

    // Simulation parameters
    timeprecision 1ps;
    timeunit      1ns;
    localparam CLKT = 10ns;  // 100 MHz

    localparam logic [31:0] FREQ_CLK = 100000000;
    localparam logic [31:0] TX_SPEED = 115200;
    localparam integer BIT_CYCLES = FREQ_CLK / TX_SPEED;

    logic       Clk          = 1'b0;
    logic       Rst_n        = 1'b0;

    // INFO: Unisims library force these signals to be declared as nets
    wire        RX_Empty;
    wire        RX_Full;
    wire [7:0]  RX_Data;

    /* DUT Inputs */
    logic       Bus_grant    = 1'b0;
    logic       Dma_Tx_Start = 1'b0;
    logic       RXD          = 1'b1;
    logic [7:0] DataIn       = '0;

    /* DUT Outputs */
    logic       TXD;
    logic       TX_Ready;
    logic [7:0] Address;
    logic       Bus_req;
    logic       Cs;
    logic       Data_Read;
    logic [7:0] DataOut;
    logic       Dma_Tx_Ready;
    logic       Oen;
    logic [7:0] TX_Data;
    logic       TX_Valid;
    logic       Wen;


    // System Clock
    always begin
        #(CLKT/2) Clk = ~Clk;
    end

    // DUT Instantiation
    dma I_DMA (
        .Clk          (Clk),
        .Rst_n        (Rst_n),
        // Serial data
        .RX_Data      (RX_Data),
        .RX_Empty     (RX_Empty),
        .RX_Full      (RX_Full),
        .Data_Read    (Data_Read),
        .TX_Data      (TX_Data),
        .TX_Valid     (TX_Valid),
        .TX_Ready     (TX_Ready),
        // System buses
        .DataIn       (DataIn),
        .DataOut      (DataOut),
        .Address      (Address),
        // RAM interface
        .Cs           (Cs),
        .Wen          (Wen),
        .Oen          (Oen),
        // CPU interface
        .Bus_req      (Bus_req),
        .Bus_grant    (Bus_grant),
        .Dma_Tx_Start (Dma_Tx_Start),
        .Dma_Tx_Ready (Dma_Tx_Ready)
        );


    uart # (
        .FREQ_CLK (FREQ_CLK),
        .TX_SPEED (TX_SPEED)
        ) I_UART (
        .Clk       (Clk),
        .Rst_n     (Rst_n),
        .Data_Read (Data_Read),
        .Data_Out  (RX_Data),
        .Full      (RX_Full),
        .Empty     (RX_Empty),
        .RXD       (RXD),
        .TX_Valid  (TX_Valid),
        .TX_DataIn (DataIn),
        .TX_Ready  (TX_Ready),
        .TXD       (TXD)
        );


    // Tasks
    task reset_system;
        repeat (10) @(posedge Clk);
        Rst_n <= 0;
        repeat (10) @(posedge Clk);
        Rst_n <= 1;
        repeat (10) @(posedge Clk);
    endtask : reset_system


    // RX DMA - UART to Memory
    task serial_rx (input logic [7:0] Data);
        @(posedge Clk);
        // Start bit
        RXD = 1'b0;
        repeat (BIT_CYCLES) @(posedge Clk);
        // Data bits
        for (int i=0; i<8; ++i) begin
            RXD = Data[i];
            repeat (BIT_CYCLES) @(posedge Clk);
        end
        // Stop bit
        RXD = 1'b1;
        repeat (BIT_CYCLES) @(posedge Clk);
        // Wrapup
        $display("@%0d: End of Serial RX", $time);
        @(posedge Clk); // Resync
    endtask: serial_rx


    task receive_1byte ();
        Bus_grant <= 1'b0;
        @(posedge Clk);
        serial_rx('h77);
        repeat (3000) @(posedge Clk);
        Bus_grant <= 1'b1;
        repeat (30) @(posedge Clk);
    endtask: receive_1byte


    task receive_2bytes ();
        Bus_grant <= 1'b0;
        @(posedge Clk);
        serial_rx('h55);
        repeat (3000) @(posedge Clk);
        serial_rx('h55);
        repeat (3000) @(posedge Clk);
        Bus_grant <= 1'b1;
        repeat (30) @(posedge Clk);
    endtask: receive_2bytes


    task receive_3bytes ();
        Bus_grant <= 1'b0;
        @(posedge Clk);
        serial_rx('hAA);
        repeat (3000) @(posedge Clk);
        serial_rx('h03);
        repeat (3000) @(posedge Clk);
        serial_rx('hCC);
        repeat (3000) @(posedge Clk);
        Bus_grant <= 1'b1;
        repeat (30) @(posedge Clk);
    endtask: receive_3bytes


    task rx_dma ();
        receive_1byte;
        receive_2bytes;
        receive_3bytes;
    endtask: rx_dma



    // TX DMA - Memory to UART
    task start_tx_dma;
        @(posedge Clk);
        Dma_Tx_Start <= 1'b1;
        @(posedge Clk);
        Dma_Tx_Start <= 1'b0;
        repeat (15) @(posedge Clk);
    endtask: start_tx_dma


    task get_databus;
        @(posedge Clk);
        Bus_grant <= 1'b1;
        @(posedge Clk);
        Bus_grant <= 1'b0;
        repeat (10) @(posedge Clk);
    endtask: get_databus


    task wait_msb_send_lsb;
        @(posedge TX_Ready);    // MSB
        @(posedge Clk);
        DataIn <= 'hBB;
        @(posedge TX_Ready);    // LSB
    endtask: wait_msb_send_lsb


    task tx_dma;
        start_tx_dma;
        get_databus;
        wait_msb_send_lsb;
    endtask: tx_dma


    // === TB Setup === \\
    //$timeformat params:
    //1) Scaling factor (–9 for nanoseconds, –12 for picoseconds)
    //2) Number of digits to the right of the decimal point
    //3) A string to print after the time value
    //4) Minimum field width
    initial begin
        $dumpfile("tb_dma.lx2");  // iverilog, vpp & gtkwave
        $dumpvars(0, tb_dma);     // Module Output file
        $timeformat(-9, 3, "ns", 8);
    end


    // Stimuli
    initial begin
        reset_system;
        tx_dma;
        repeat (10000) @(posedge Clk);
        rx_dma;
        repeat (10000) @(posedge Clk);
        $display("@%0d: TEST PASSED", $time);
        $finish;
    end


endmodule // tb_dma
