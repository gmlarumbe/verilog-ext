######################################################
#
#  Makefile for test-hdl with verilog-ext
#
#  Copyright (c) 2022-2024 Gonzalo Larumbe
#  All rights reserved.
# 
######################################################

# Variables
TEST_HDL_PATH = test/test-hdl
ERT_TESTS = $(TEST_HDL_PATH)/ert-tests.sh
PACKAGE = verilog-ext

include $(TEST_HDL_PATH)/Makefile.mk
