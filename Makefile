######################################################
#
#  Makefile for test-hdl with verilog-ext
#
#  Copyright (c) 2022-2023 Gonzalo Larumbe
#  All rights reserved.
# 
######################################################

# Variables
TEST_HDL_PATH = test-hdl
ERT_TESTS = $(TEST_HDL_PATH)/ert-tests.sh
LANGUAGE = verilog
PACKAGE = verilog-ext
PKG_MANAGER ?= straight

include $(TEST_HDL_PATH)/Makefile.mk
