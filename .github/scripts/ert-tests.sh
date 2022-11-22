#!/bin/sh

# Copyright (c) 2022 Gonzalo Larumbe
# All rights reserved.

echo "Running ERT tests..."
emacs -batch \
      -l ert \
      -l $HOME/.emacs.d/straight/repos/verilog-ext/tests/verilog-ext-tests-setup.el \
      -l $HOME/.emacs.d/straight/repos/verilog-ext/verilog-ext.el \
      -l $HOME/.emacs.d/straight/repos/verilog-ext/tests/verilog-ext-tests-imenu.el \
      -l $HOME/.emacs.d/straight/repos/verilog-ext/tests/verilog-ext-tests.el \
      -f ert-run-tests-batch-and-exit
echo "Ran tests!"
