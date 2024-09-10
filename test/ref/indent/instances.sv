//-----------------------------------------------------------------------------
// Title         : Verilog-Ext Instances Test
// Project       : Verilog-Ext
//-----------------------------------------------------------------------------
// File          : instances.sv
// Author        : Gonzalo Larumbe
// Created       : 2022/11/15
// Last modified : 2022/11/15
//-----------------------------------------------------------------------------
// Description :
//
//-----------------------------------------------------------------------------
// Copyright (c) Gonzalo Larumbe <gonzalomlarumbe@gmail.com>
//
//------------------------------------------------------------------------------
// Modification history:
// 2022/11/15 : created
//-----------------------------------------------------------------------------

module instances;

    // Regular block
    block0 I_BLOCK0 (
	.Port0 (Port0),
	.Port1 (Port1),
	.Port2 (Port2)
    );

    // Regular block (no space between instance name and parenthesis)
    block1 I_BLOCK1(
	.Port0 (Port0),
	.Port1 (Port1),
	.Port2 (Port2)
    );

    // Regular block with parameters
    block2 #(
	.Param0 (Param0),
	.Param1 (Param1),
	.Param2 (Param2)
    ) I_BLOCK2 (
	.Port0 (Port0),
	.Port1 (Port1),
	.Port2 (Port2)
    );

    // Regular block with parameters (no spaces in the identifiers)
    block3#(
	.Param0 (Param0),
	.Param1 (Param1),
	.Param2 (Param2)
    )I_BLOCK3(
	.Port0 (Port0),
	.Port1 (Port1),
	.Port2 (Port2)
    );

    // Generate
    generate
	for (genvar i=0; i<VALUE; i++) begin : gen_test

	    block_gen #(
		.Param0 (Param0),
		.Param1 (Param1),
		.Param2 (Param2)
	    ) I_BLOCK_GEN (
		.Port0 (Port0),
		.Port1 (Port1),
		.Port2 (Port2)
	    );

	end : gen_test
    endgenerate


    // Interfaces
    test_if I_TEST_IF (.clk(clk), .rst_n(rst_n));

    test_if_params # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS (.clk(clk), .rst_n(rst_n));

    test_if_params_array # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS_ARRAY[5:0] (.clk(clk), .rst_n(rst_n));

    test_if_params_empty #() I_TEST_IF_PARAMS_EMPTY (.clk(clk), .rst_n(rst_n));


    // Comments and whitespaces
    block_ws_0
	I_BLOCK_WS_0 (
	.Port0 (Port0),
	.Port1 (Port1),
	.Port2 (Port2)
    );

    block_ws_1 // Comment
	#(     // More comments
	.Param0 (Param0),
	.Param1 (Param1),
	.Param2 (Param2)
    ) // Even more comments
    I_BLOCK_WS_1 // More comments here
	(
	.Port0 (Port0),
	.Port1 (Port1),
	.Port2 (Port2)
    );



endmodule
