#!/bin/bash

# Copyright (c) 2022-2023 Gonzalo Larumbe
# All rights reserved.

emacs -Q -nw -batch \
      -L $PWD/tests \
      -l verilog-ext-tests-setup \
      -l verilog-ext-tests \
      --eval "(verilog-ext-test-indent-update-dir)"

