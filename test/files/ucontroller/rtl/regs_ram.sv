//-----------------------------------------------------------------------------
// Title         : RAM Register Address Space
// Project       : 
//-----------------------------------------------------------------------------
// File          : regs_ram.sv
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

module regs_ram (
    input logic        Clk,
    input logic        Rst_n,
    input logic        Wen,
    input logic        Oen,
    input logic        Cs,
    input logic [7:0]  Address,
    input logic [7:0]  DataIn,
    output logic [7:0] DataOut,
    output logic [7:0] Switches,
    output logic [7:0] Temp
    );


    // Registers
    logic [7:0]  DMA_RX_BUFFER_MSB_AUX;
    logic [7:0]  DMA_RX_BUFFER_MID_AUX;
    logic [7:0]  DMA_RX_BUFFER_LSB_AUX;
    logic [7:0]  NEW_INST_AUX;
    logic [7:0]  DMA_TX_BUFFER_MSB_AUX;
    logic [7:0]  DMA_TX_BUFFER_LSB_AUX;
    logic [7:0]  SWITCH_BASE_AUX;
    logic [7:0]  SWITCH_BASE_AUX2;
    logic [7:0]  SWITCH_BASE_AUX3;
    logic [7:0]  SWITCH_BASE_AUX4;
    logic [7:0]  SWITCH_BASE_AUX5;
    logic [7:0]  SWITCH_BASE_AUX6;
    logic [7:0]  SWITCH_BASE_AUX7;
    logic [7:0]  SWITCH_BASE_AUX8;
    logic [7:0]  LEVER_BASE_AUX;
    logic [7:0]  LEVER_BASE_AUX2;
    logic [7:0]  LEVER_BASE_AUX3;
    logic [7:0]  LEVER_BASE_AUX4;
    logic [7:0]  LEVER_BASE_AUX5;
    logic [7:0]  LEVER_BASE_AUX6;
    logic [7:0]  LEVER_BASE_AUX7;
    logic [7:0]  LEVER_BASE_AUX8;
    logic [7:0]  LEVER_BASE_AUX9;
    logic [7:0]  LEVER_BASE_AUX10;
    logic [7:0]  CAL_OP_AUX;
    logic [7:0]  T_STAT_AUX;


    // Binary to BCD for temperature conversion
    localparam BIN2BCD_PERIOD = 1000;

    logic [31:0] bin2bcd_cnt;
    logic 	 bin2bcd_done;
    logic [7:0]  bin2bcd_temp;
    logic 	 bin2bcd_start;



    // Write/read seq logic
    always_ff @(posedge Clk) begin
        if (!Rst_n) begin
            DataOut  <= 'hFF;

            DMA_RX_BUFFER_MSB_AUX <= 'h0;
            DMA_RX_BUFFER_MID_AUX <= 'h0;
            DMA_RX_BUFFER_LSB_AUX <= 'h0;
            NEW_INST_AUX          <= 'h0;
            DMA_TX_BUFFER_MSB_AUX <= 'h0;
            DMA_TX_BUFFER_LSB_AUX <= 'h0;
            SWITCH_BASE_AUX       <= 'h0;
            SWITCH_BASE_AUX2      <= 'h0;
            SWITCH_BASE_AUX3      <= 'h0;
            SWITCH_BASE_AUX4      <= 'h0;
            SWITCH_BASE_AUX5      <= 'h0;
            SWITCH_BASE_AUX6      <= 'h0;
            SWITCH_BASE_AUX7      <= 'h0;
            SWITCH_BASE_AUX8      <= 'h0;
            LEVER_BASE_AUX        <= 'h0;
            LEVER_BASE_AUX2       <= 'h0;
            LEVER_BASE_AUX3       <= 'h0;
            LEVER_BASE_AUX4       <= 'h0;
            LEVER_BASE_AUX5       <= 'h0;
            LEVER_BASE_AUX6       <= 'h0;
            LEVER_BASE_AUX7       <= 'h0;
            LEVER_BASE_AUX8       <= 'h0;
            LEVER_BASE_AUX9       <= 'h0;
            LEVER_BASE_AUX10      <= 'h0;
            CAL_OP_AUX            <= 'h0;
            T_STAT_AUX            <= 8'd25;
        end

        else begin
            if (Cs) begin
                if (Wen) begin
                    unique case (Address)
                        DMA_RX_BUFFER_MSB : DMA_RX_BUFFER_MSB_AUX <= DataIn;
                        DMA_RX_BUFFER_MID : DMA_RX_BUFFER_MID_AUX <= DataIn;
                        DMA_RX_BUFFER_LSB : DMA_RX_BUFFER_LSB_AUX <= DataIn;
                        NEW_INST          : NEW_INST_AUX          <= DataIn;
                        DMA_TX_BUFFER_MSB : DMA_TX_BUFFER_MSB_AUX <= DataIn;
                        DMA_TX_BUFFER_LSB : DMA_TX_BUFFER_LSB_AUX <= DataIn;
                        SWITCH_BASE       : SWITCH_BASE_AUX       <= DataIn;
                        8'h11             : SWITCH_BASE_AUX2      <= DataIn;
                        8'h12             : SWITCH_BASE_AUX3      <= DataIn;
                        8'h13             : SWITCH_BASE_AUX4      <= DataIn;
                        8'h14             : SWITCH_BASE_AUX5      <= DataIn;
                        8'h15             : SWITCH_BASE_AUX6      <= DataIn;
                        8'h16             : SWITCH_BASE_AUX7      <= DataIn;
                        8'h17             : SWITCH_BASE_AUX8      <= DataIn;
                        LEVER_BASE        : LEVER_BASE_AUX        <= DataIn;
                        8'h21             : LEVER_BASE_AUX2       <= DataIn;
                        8'h22             : LEVER_BASE_AUX3       <= DataIn;
                        8'h23             : LEVER_BASE_AUX4       <= DataIn;
                        8'h24             : LEVER_BASE_AUX5       <= DataIn;
                        8'h25             : LEVER_BASE_AUX6       <= DataIn;
                        8'h26             : LEVER_BASE_AUX7       <= DataIn;
                        8'h27             : LEVER_BASE_AUX8       <= DataIn;
                        8'h28             : LEVER_BASE_AUX9       <= DataIn;
                        8'h29             : LEVER_BASE_AUX10      <= DataIn;
                        CAL_OP            : CAL_OP_AUX            <= DataIn;
                        T_STAT            : T_STAT_AUX            <= DataIn;
                        default           :;
                    endcase
                end
		else if (Oen) begin
		    unique case (Address)
                        DMA_RX_BUFFER_MSB : DataOut <= DMA_RX_BUFFER_MSB_AUX;
                        DMA_RX_BUFFER_MID : DataOut <= DMA_RX_BUFFER_MID_AUX;
                        DMA_RX_BUFFER_LSB : DataOut <= DMA_RX_BUFFER_LSB_AUX;
                        NEW_INST          : DataOut <= NEW_INST_AUX;
                        DMA_TX_BUFFER_MSB : DataOut <= DMA_TX_BUFFER_MSB_AUX;
                        DMA_TX_BUFFER_LSB : DataOut <= DMA_TX_BUFFER_LSB_AUX;
                        SWITCH_BASE       : DataOut <= SWITCH_BASE_AUX;
                        8'h11             : DataOut <= SWITCH_BASE_AUX2;
                        8'h12             : DataOut <= SWITCH_BASE_AUX3;
                        8'h13             : DataOut <= SWITCH_BASE_AUX4;
                        8'h14             : DataOut <= SWITCH_BASE_AUX5;
                        8'h15             : DataOut <= SWITCH_BASE_AUX6;
                        8'h16             : DataOut <= SWITCH_BASE_AUX7;
                        8'h17             : DataOut <= SWITCH_BASE_AUX8;
                        LEVER_BASE        : DataOut <= LEVER_BASE_AUX;
                        8'h21             : DataOut <= LEVER_BASE_AUX2;
                        8'h22             : DataOut <= LEVER_BASE_AUX3;
                        8'h23             : DataOut <= LEVER_BASE_AUX4;
                        8'h24             : DataOut <= LEVER_BASE_AUX5;
                        8'h25             : DataOut <= LEVER_BASE_AUX6;
                        8'h26             : DataOut <= LEVER_BASE_AUX7;
                        8'h27             : DataOut <= LEVER_BASE_AUX8;
                        8'h28             : DataOut <= LEVER_BASE_AUX9;
                        8'h29             : DataOut <= LEVER_BASE_AUX10;
                        CAL_OP            : DataOut <= CAL_OP_AUX;
                        T_STAT            : DataOut <= T_STAT_AUX;
                        default           :;
		    endcase
                end
	    end
        end
    end
    


    // Binary to BCD temperature logic
    bin2bcd I_BIN2BCD (
        .Clk     (Clk),
        .Rst_n   (Rst_n),
        .DataBin (T_STAT_AUX),
        .Start   (bin2bcd_start),
        .DataBCD (bin2bcd_temp),
        .Done    (bin2bcd_done)
        );


    always_ff @(posedge Clk) begin : bin2bcd_mgt
        if (!Rst_n) begin
            bin2bcd_start <= 1'h0;
	    bin2bcd_cnt   <= 'h0;
        end
        else begin
            if (bin2bcd_cnt == BIN2BCD_PERIOD) begin
		bin2bcd_cnt <= 0;
                bin2bcd_start <= 1'b1;
	    end
            else begin
		bin2bcd_cnt <= bin2bcd_cnt + 1;
                bin2bcd_start <= 1'b0;
	    end
        end
    end : bin2bcd_mgt


    // Output BCD temperature registering
    always_ff @(posedge Clk) begin : bin2bcd_temperature
        if (!Rst_n) begin
            Temp <= '0;
        end
        else if (bin2bcd_done)
            Temp <= bin2bcd_temp;
    end : bin2bcd_temperature



    // Switches logic
    generate
        for (genvar i=0; i<8; ++i) begin : gen_switches

            assign Switches[i] = SWITCH_BASE_AUX[i];

        end : gen_switches
    endgenerate


endmodule
