//-----------------------------------------------------------------------------
// Title         : MicroController Top module
// Project       :
//-----------------------------------------------------------------------------
// File          : ucontroller.sv
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


module ucontroller # (
    parameter logic [31:0] FREQ_CLK = 100000000,
    parameter logic [31:0] TX_SPEED = 115200
) (
    input logic         Clk,
    input logic         Rst_n,
    // Serial interface
    input logic         RXD,
    output logic        TXD,
    // ROM
    input logic [11:0]  ROM_Data,
    output logic [11:0] ROM_Addr,
    // Exteral HW
    output logic [7:0]  Temp,
    output logic [7:0]  Switches
);


    // Buses arbitrating
    logic       DMA_Oen;
    logic       DMA_Wen;
    logic       DMA_Cs;
    logic       CPU_Oen;
    logic       CPU_Wen;
    logic       CPU_Cs;
    logic [7:0] CPU_Address;
    logic [7:0] DMA_Address;
    logic [7:0] DMA_DataOut;
    logic [7:0] CPU_DataOut;
    logic       Dma_Idle;
    // Serial <-> DMA
    logic [7:0] TX_Data;
    logic       TX_Ready;
    logic       TX_Valid;
    logic       Data_Read;
    logic [7:0] RX_Data;
    logic       RX_Empty;
    logic       RX_Full;
    // DMA/CPU <-> RAM
    logic [7:0] RAM_DataOut;
    logic [7:0] RAM_DataIn;
    // ALU <-> CPU
    logic [7:0] ALU_DataIn;
    logic [7:0] ALU_DataOut;
    alu_op      ALU_op;
    logic       FlagE;
    logic       FlagN;
    logic       FlagC;
    logic       FlagZ;
    // RAM signals
    logic [7:0] RAM_Address;
    logic       RAM_Wen;
    logic       RAM_Oen;
    logic       RAM_Cs;
    // DMA <-> CPU
    logic       Bus_grant;
    logic       Bus_req;
    logic       Dma_Tx_Ready;
    logic       Dma_Tx_Start;


    // Instances
    cpu I_CPU (
	.Clk,
	.Rst_n,
	// ROM Interface
	.ROM_Data,
	.ROM_Addr,
	// RAM Interface
	.RAM_Addr     (CPU_Address),
	.DataOut      (CPU_DataOut),
	.DataIn       (RAM_DataOut),
	.RAM_Cs       (CPU_Cs),
	.RAM_Wen      (CPU_Wen),
	.RAM_Oen      (CPU_Oen),
	// DMA Interface
	.DMA_Req      (Bus_req),
	.DMA_Ack      (Bus_grant),
	.DMA_Ready    (Dma_Tx_Ready),
	.DMA_Tx_Start (Dma_Tx_Start),
	// ALU inteface
	.ALU_op,
	.ALU_DataOut,
	.ALU_DataIn,
	.FlagZ,
	.FlagC,
	.FlagN,
	.FlagE
    );


    alu I_ALU (
	.Clk,
	.Rst_n,
	.InData  (ALU_DataIn),
	.OutData (ALU_DataOut),
	.ALU_op,
	.FlagZ,
	.FlagC,
	.FlagN,
	.FlagE
    );


    dma I_DMA (
	.Clk,
	.Rst_n,
	// CPU interface
	.Bus_grant,
	.Bus_req,
	.Dma_Tx_Start,
	.Dma_Tx_Ready,
	.Dma_Idle,
	// Serial interface
	.RX_Data,
	.RX_Empty,
	.RX_Full,
	.Data_Read,
	.TX_Ready,
	.TX_Data,
	.TX_Valid,
	// Ram interface
	.Address (DMA_Address),
	.DataOut (DMA_DataOut),
	.DataIn  (RAM_DataOut),
	.Cs      (DMA_Cs),
	.Wen     (DMA_Wen),
	.Oen     (DMA_Oen)
    );


    uart # (
	.FREQ_CLK (FREQ_CLK),
	.TX_SPEED (TX_SPEED)
    ) I_UART (
	.Clk,
	.Rst_n,
	// TX
	.TX_Valid,
	.TX_DataIn (TX_Data),
	.TX_Ready,
	.TXD,
	// RX
	.Data_Read,
	.Data_Out  (RX_Data),
	.RXD,
	.Full      (RX_Full),
	.Empty     (RX_Empty)
    );


    ram_arbiter I_RAM_ARBITER (
	.Clk,
	.Rst_n,
	.DMA_Bus_req   (Bus_req),
	.DMA_Bus_grant (Bus_grant),
	.DMA_Idle      (Dma_Idle),
	.CPU_DataOut,
	.DMA_DataOut,
	.RAM_DataIn,
	.CPU_Address,
	.DMA_Address,
	.RAM_Address,
	.CPU_Cs,
	.DMA_Cs,
	.RAM_Cs,
	.CPU_Oen,
	.DMA_Oen,
	.RAM_Oen,
	.CPU_Wen,
	.DMA_Wen,
	.RAM_Wen
    );



    ram I_RAM (
	.Clk,
	.Rst_n,
	.Cs      (RAM_Cs),
	.Wen     (RAM_Wen),
	.Oen     (RAM_Oen),
	.Address (RAM_Address),
	.DataIn  (RAM_DataIn),
	.DataOut (RAM_DataOut),
	.Switches,
	.Temp
    );




endmodule: ucontroller
