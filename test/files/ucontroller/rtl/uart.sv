//-----------------------------------------------------------------------------
// Title         : UART Top module
// Project       :
//-----------------------------------------------------------------------------
// File          : uart.sv
// Author        : Gonzalo Martinez Larumbe
// Created       : 2020/02/16
// Last modified : 2023-06-06 10:36
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


module uart # (
    parameter logic [31:0] FREQ_CLK = 100000000,
    parameter logic [31:0] TX_SPEED = 115200
    )(
    input logic        Clk,
    input logic        Rst_n,

    input logic        TX_Valid,
    output logic       TX_Ready,
    input logic [7:0]  TX_DataIn,
    output logic       TXD,

    input logic        RXD,
    input logic        Data_Read,
    output logic [7:0] Data_Out,

    output logic       Full,
    output logic       Empty
    );

    // Signals
    logic       TX_Ready_i;
    logic       TX_Start;
    logic       RX_Valid;
    logic [7:0] Fifo_In;
    logic       Fifo_Wren;


    // Instances
    uart_tx # (
        .FREQ_CLK (FREQ_CLK),
        .TX_SPEED (TX_SPEED)
        ) I_UART_TX (
        .Clk   (Clk),
        .Rst_n (Rst_n),
        .Start (TX_Start),
        .Data  (TX_DataIn),
        .EOT   (TX_Ready_i),
        .TXD   (TXD)
        );


    uart_rx # (
        .FREQ_CLK (FREQ_CLK),
        .TX_SPEED (TX_SPEED)
        ) I_UART_RX (
        .Clk      (Clk),
        .Rst_n    (Rst_n),
        .RXD      (RXD),
        .RX_Valid (RX_Valid),
        .RX_Load  (Fifo_Wren)
        );


    sreg I_SREG (
        .Clk   (Clk),
        .Rst_n (Rst_n),
        .Din   (RXD),
        .Ena   (RX_Valid),
        .Qout  (Fifo_In)
        );


    fifo_wrapper I_FIFO (
        .Clk   (Clk),
        .Rst_n (Rst_n),
        .Din   (Fifo_In),
        .Wren  (Fifo_Wren),
        .Rden  (Data_Read),
        .Dout  (Data_Out),
        .Full  (Full),
        .Empty (Empty)
        );


    // Comb logic
    assign TX_Ready = TX_Ready_i;

    // Seq logic
    always_ff @(posedge Clk) begin
        if (!Rst_n) begin
            TX_Start <= 1'b0;
        end else begin
            if (TX_Valid && TX_Ready_i)
                TX_Start <= 1'b1;
            else
                TX_Start <= 1'b0;
        end
    end


endmodule
