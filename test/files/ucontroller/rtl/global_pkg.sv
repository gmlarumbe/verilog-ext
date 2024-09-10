//-----------------------------------------------------------------------------
// Title         : Global Definitions Package
// Project       :
//-----------------------------------------------------------------------------
// File          : global_pkg.sv
// Author        : Gonzalo Martinez Larumbe
// Created       : 2020/02/16
// Last modified : 2023/08/10
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


package global_pkg;

    // RAM params and addresses
    localparam integer RAM_DEPTH = 256;

    localparam logic [7:0] DMA_RX_BUFFER_MSB = 'h00;
    localparam logic [7:0] DMA_RX_BUFFER_MID = 'h01;
    localparam logic [7:0] DMA_RX_BUFFER_LSB = 'h02;
    localparam logic [7:0] NEW_INST          = 'h03;
    localparam logic [7:0] DMA_TX_BUFFER_MSB = 'h04;
    localparam logic [7:0] DMA_TX_BUFFER_LSB = 'h05;
    localparam logic [7:0] SWITCH_BASE       = 'h10;
    localparam logic [7:0] LEVER_BASE        = 'h20;
    localparam logic [7:0] CAL_OP            = 'h30;
    localparam logic [7:0] T_STAT            = 'h31;
    localparam logic [7:0] GP_RAM_BASE       = 'h40;

    // CPU <-> alu interconnect types
    typedef enum logic[4:0] {
                 nop,                                  // no operation
                 op_lda, op_ldb, op_ldacc, op_ldid,    // external value load
                 op_mvacc2id, op_mvacc2a, op_mvacc2b,  // internal load
                 op_add, op_sub, op_shiftl, op_shiftr, // arithmetic operations
                 op_and, op_or, op_xor,                // logic operations
                 op_cmpe, op_cmpl, op_cmpg,            // compare operations
                 op_ascii2bin, op_bin2ascii,           // conversion operations
                 op_oeacc                              // output enable
                 } alu_op;


    ///////////////////
    /* CPU constants */
    ///////////////////
    // Type 1 instructions (ALU)
    localparam logic [1:0] TYPE_1         = 'b00;
    localparam logic [5:0] ALU_ADD        = 'b000000;
    localparam logic [5:0] ALU_SUB        = 'b000001;
    localparam logic [5:0] ALU_SHIFTL     = 'b000010;
    localparam logic [5:0] ALU_SHIFTR     = 'b000011;
    localparam logic [5:0] ALU_AND        = 'b000100;
    localparam logic [5:0] ALU_OR         = 'b000101;
    localparam logic [5:0] ALU_XOR        = 'b000110;
    localparam logic [5:0] ALU_CMPE       = 'b000111;
    localparam logic [5:0] ALU_CMPG       = 'b001000;
    localparam logic [5:0] ALU_CMPL       = 'b001001;
    localparam logic [5:0] ALU_ASCII2BIN  = 'b001010;
    localparam logic [5:0] ALU_BIN2ASCII  = 'b001011;

    // Type 2 instructions (JUMP)
    localparam logic [1:0] TYPE_2     = 'b01;
    localparam logic [5:0] JMP_UNCOND = 'b000000;
    localparam logic [5:0] JMP_COND   = 'b000001;

    // Type 3 instructions (LOAD & STORE)
    localparam logic [1:0] TYPE_3 = 'b10;
    // Source
    localparam logic [2:0] LD_SRC_ACC       = 'b000;
    localparam logic [2:0] LD_SRC_CONSTANT  = 'b001;
    localparam logic [2:0] LD_SRC_MEM       = 'b010;
    localparam logic [2:0] LD_SRC_INDXD_MEM = 'b011;
    localparam logic [2:0] WR_SRC_ACC       = 'b100;
    // Destination
    localparam logic [2:0] DST_ACC       = 'b000;
    localparam logic [2:0] DST_A         = 'b001;
    localparam logic [2:0] DST_B         = 'b010;
    localparam logic [2:0] DST_INDX      = 'b011;
    localparam logic [2:0] DST_MEM       = 'b100;
    localparam logic [2:0] DST_INDXD_MEM = 'b101;

    // Type 4 instructions (SEND)
    localparam logic [1:0] TYPE_4 = 'b11;



endpackage: global_pkg



