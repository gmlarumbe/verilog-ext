//-----------------------------------------------------------------------------
// Title         : CPU
// Project       :
//-----------------------------------------------------------------------------
// File          : cpu.sv
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

module cpu (
    input logic         Clk,
    input logic         Rst_n,
    // ROM Interface
    input logic [11:0]  ROM_Data,
    output logic [11:0] ROM_Addr,
    // RAM Interface
    output logic [7:0]  RAM_Addr,
    output logic        RAM_Cs,
    output logic        RAM_Wen,
    output logic        RAM_Oen,
    output logic [7:0]  DataOut,
    input logic [7:0]   DataIn,
    // DMA interface
    input logic         DMA_Req,
    output logic        DMA_Ack,
    output logic        DMA_Tx_Start,
    input logic         DMA_Ready,
    // ALU interface
    output alu_op       ALU_op,
    input logic [7:0]   ALU_DataOut,
    output logic [7:0]  ALU_DataIn,
    input logic         FlagZ,
    input logic         FlagC,
    input logic         FlagN,
    input logic         FlagE
    );


    // Types
    typedef enum logic[2:0] {
                 IDLE,
                 FETCH,
                 DECODE,
                 EXECUTE,
                 READ_MEM,
		 WAIT_DMA
                 } state_t;

    state_t state, next_state;

    // Signals
    logic 	 pc_ena;
    logic 	 load_inst;
    logic 	 load_inst_auxbyte;
    logic [11:0] rom_instruction;
    logic [11:0] rom_aux;
    logic [11:0] addr = 'h0;
    logic [11:0] addr_aux;
    logic [7:0]  alu_data = 'h0;


    // Auxiliary tasks
    task automatic decode_type1_inst ();
        case (rom_instruction[5:0])
            ALU_ADD       : ALU_op = op_add;
            ALU_SUB       : ALU_op = op_sub;
            ALU_SHIFTL    : ALU_op = op_shiftl;
            ALU_SHIFTR    : ALU_op = op_shiftr;
            ALU_AND       : ALU_op = op_and;
            ALU_OR        : ALU_op = op_or;
            ALU_XOR       : ALU_op = op_xor;
            ALU_CMPE      : ALU_op = op_cmpe;
            ALU_CMPG      : ALU_op = op_cmpg;
            ALU_CMPL      : ALU_op = op_cmpl;
            ALU_ASCII2BIN : ALU_op = op_ascii2bin;
            ALU_BIN2ASCII : ALU_op = op_bin2ascii;
            default       : ;
        endcase

        next_state = IDLE;
    endtask: decode_type1_inst



    task automatic decode_type2_inst ();
        pc_ena            = 1'b1;
        load_inst_auxbyte = 1'b1;
        addr              = addr_aux + 12'h1;
        next_state        = EXECUTE;
    endtask: decode_type2_inst



    task automatic decode_type3_inst ();
        if (rom_instruction[5:3] == LD_SRC_ACC) begin // Acc LD instructions are 1byte
            unique case (rom_instruction[2:0])
                DST_A    : ALU_op = op_mvacc2a;
                DST_B    : ALU_op = op_mvacc2b;
                DST_INDX : ALU_op = op_mvacc2id;
                default  : ;
            endcase // DST_MEM and DST_INDXD_MEM accessed via WR
            next_state = IDLE;
        end

        else begin // 2-byte instructions
            load_inst_auxbyte = 1'b1;
            next_state        = EXECUTE;
        end

        pc_ena = 1'b1;
        addr   = addr_aux + 12'h1;
    endtask: decode_type3_inst



    task automatic decode_type4_inst ();
        unique case (rom_instruction[5:0])
            6'b000000 : DMA_Tx_Start = 1'b1;
            default   : ;
        endcase
        next_state = IDLE;
    endtask: decode_type4_inst



    task automatic execute_type2_inst ();
        unique case (rom_instruction[5:0])
            JMP_UNCOND : addr = rom_aux; // 2nd byte points to jump address
            JMP_COND   : begin
                if (FlagZ)
                    addr = rom_aux;
                else
                    addr = addr_aux + 12'h1;
            end
            default : ;
        endcase
        pc_ena     = 1'b1;
        next_state = IDLE;
    endtask : execute_type2_inst



    task automatic execute_type3_inst ();
        unique case (rom_instruction[5:3])
            LD_SRC_CONSTANT : begin
                unique case (rom_instruction[2:0])
                    DST_ACC  : ALU_op = op_ldacc;
                    DST_A    : ALU_op = op_lda;
                    DST_B    : ALU_op = op_ldb;
                    DST_INDX : ALU_op = op_ldid;
                    default : ;
                endcase
                alu_data = rom_aux[7:0]; // 2nd byte sent to ALU along with the kind of op to perform
                next_state = IDLE;
            end

            LD_SRC_MEM : begin
                RAM_Cs   = 1'b1;
                RAM_Oen  = 1'b1;
                RAM_Addr = rom_aux[7:0];
                next_state = READ_MEM;
            end

            LD_SRC_INDXD_MEM : begin // TODO
                ;
            end

            WR_SRC_ACC : begin
                unique case (rom_instruction[2:0])
                    DST_MEM : begin
                        RAM_Cs   = 1'b1;
                        RAM_Wen  = 1'b1;
                        RAM_Addr = rom_aux[7:0];
                    end
                    default : ;
                endcase
                ALU_op 	   = op_oeacc;
                DataOut    = ALU_DataOut;
                next_state = IDLE;
            end
            default : ;
        endcase

    endtask: execute_type3_inst



    // Comb FSM
    always_comb begin
        // Ports
        DataOut           = 'h0;
        RAM_Addr          = 'h0;
        RAM_Cs            = 1'b0;
        RAM_Wen           = 1'b0;
        RAM_Oen           = 1'b0;
        // DMA_Ack           = 1'b0;
        DMA_Tx_Start      = 1'b0;
        ALU_op            = nop;
        // Internal signals
        pc_ena            = 1'b0;
        load_inst         = 1'b0;
        load_inst_auxbyte = 1'b0;

        unique case (state)
            IDLE : begin
                if (DMA_Req) 
                    next_state = WAIT_DMA;
                else
                    next_state = FETCH;
            end

            FETCH : begin
                load_inst  = 1'b1;
                pc_ena     = 1'b1;
                addr       = addr_aux + 12'h001;
                next_state = DECODE;
            end

            DECODE : begin
                unique case (rom_instruction[7:6])
                    TYPE_1 : decode_type1_inst();  // 1-byte instruction
                    TYPE_2 : decode_type2_inst();  // 2-byte instruction
                    TYPE_3 : decode_type3_inst();
                    TYPE_4 : decode_type4_inst();
                    default : ;
                endcase
            end

            EXECUTE : begin // 2-byte instruction execution state
                unique case (rom_instruction[7:6])
                    TYPE_2 : execute_type2_inst();
                    TYPE_3 : execute_type3_inst();
                    // TODO: Implement further instructions
                    default : ;
                endcase
            end

            READ_MEM : begin    // Memory access has 1 cycle delay
                unique case (rom_instruction[2:0])
                    DST_ACC  : ALU_op = op_ldacc;
                    DST_A    : ALU_op = op_lda;
                    DST_B    : ALU_op = op_ldb;
                    DST_INDX : ALU_op = op_ldid;
                    default : ;
                endcase
                alu_data = DataIn;
                next_state = IDLE;
            end

	    WAIT_DMA : begin
		if (!DMA_Req)
		    next_state = IDLE;
	    end

	    default : ;

        endcase
    end


    // Program Counter
    always_ff @(posedge Clk) begin
        if (!Rst_n) begin
            ROM_Addr <= 'h0;
            addr_aux <= 'h0;
        end else if (pc_ena) begin
            ROM_Addr <= addr;
            addr_aux <= addr;
        end
    end

    // Instruction registering
    always_ff @(posedge Clk) begin
        if (!Rst_n) begin
            rom_instruction <= 'h0;
        end else if (load_inst) begin
            rom_instruction <= ROM_Data;
        end
    end

    // Temporal storage for execution of 2-byte instructions
    always_ff @(posedge Clk) begin
        if (!Rst_n) begin
            rom_aux <= 'h0;
        end else if (load_inst_auxbyte) begin
            rom_aux <= ROM_Data;
        end
    end


    always_ff @(posedge Clk) begin
	if (!Rst_n) begin
	    DMA_Ack <= 1'h0;
	end
	else if (state == IDLE && DMA_Req)
            DMA_Ack <= 1'b1;
	else
            DMA_Ack <= 1'b0;
    end


    // Seq FSM
    always_ff @(posedge Clk) begin
        if (!Rst_n) begin
            state <= IDLE;
        end else begin
            state <= next_state;
        end
    end

    // Aux comb logic
    assign ALU_DataIn = alu_data;


endmodule
