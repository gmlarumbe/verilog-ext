//-----------------------------------------------------------------------------
// Title         : DMA Top Module
// Project       : 
//-----------------------------------------------------------------------------
// File          : dma.sv
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


module dma (
    input logic        Clk,
    input logic        Rst_n,
    // Serial data
    input logic [7:0]  RX_Data,
    input logic        RX_Empty,
    output logic       Data_Read,
    input logic        RX_Full,
    output logic [7:0] TX_Data,
    output logic       TX_Valid,
    input logic        TX_Ready,
    // System buses
    output logic [7:0] Address,
    input logic [7:0]  DataIn,
    output logic [7:0] DataOut,
    // RAM interface
    output logic       Cs,
    output logic       Wen,
    output logic       Oen,
    // CPU Interface
    output logic       Bus_req,
    input logic        Bus_grant,
    input logic        Dma_Tx_Start,
    output logic       Dma_Tx_Ready,
    output logic       Dma_Idle
    );


    // Bus resolution auxiliary signals
    logic       Dma_Rx_End;
    logic       Ena_tx;
    logic       Ena_rx;
    logic       Cs_tx;
    logic       Cs_rx;
    logic       Bus_req_tx;
    logic       Bus_req_rx;
    logic [7:0] Address_tx;
    logic [7:0] Address_rx;


    // Instances
    dma_tx I_DMA_TX (
        // Inputs
        .Clk       (Clk),
        .Rst_n     (Rst_n),
        .Ena       (Ena_tx),
        .Databus   (DataIn),
        .TX_Ready  (TX_Ready),
        .Bus_grant (Bus_grant),
        .Start     (Dma_Tx_Start),
        // Outputs
        .Address   (Address_tx),
        .TX_Valid  (TX_Valid),
        .TX_Data   (TX_Data),
        .Cs        (Cs_tx),
        .Oen       (Oen),
        .Bus_req   (Bus_req_tx),
        .Dma_Ready (Dma_Tx_Ready)
        );


    dma_rx I_DMA_RX (
        // Inputs
        .Clk       (Clk),
        .Rst_n     (Rst_n),
        .Ena       (Ena_rx),
        .Dma_End   (Dma_Rx_End),
        .RX_Data   (RX_Data),
        .RX_Full   (RX_Full),
        .RX_Empty  (RX_Empty),
        .Bus_grant (Bus_grant),
        // Outputs
        .Address   (Address_rx),
        .Databus   (DataOut),
        .Data_Read (Data_Read),
        .Cs        (Cs_rx),
        .Wena      (Wen),
        .Bus_req   (Bus_req_rx)
        );



    dma_arbiter I_DMA_ARBITER (
        .Clk          (Clk),
        .Rst_n        (Rst_n),
        // Inputs
        .TX_Start     (Dma_Tx_Start),
        .Dma_Tx_Ready (Dma_Tx_Ready),
        .RX_Pending   (!RX_Empty),
        .Dma_Rx_End   (Dma_Rx_End),
        // TX/RX arbitrating
	.Dma_Idle     (Dma_Idle),
        .Address_tx   (Address_tx),
        .Address_rx   (Address_rx),
        .Cs_tx        (Cs_tx),
        .Cs_rx        (Cs_rx),
        .Bus_req_tx   (Bus_req_tx),
        .Bus_req_rx   (Bus_req_rx),
        .Enable_tx    (Ena_tx),
        .Enable_rx    (Ena_rx),
        .Address      (Address),
        .Cs           (Cs),
        .Bus_req      (Bus_req)
        );


endmodule
