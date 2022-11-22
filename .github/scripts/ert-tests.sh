#!/bin/sh

# Copyright (c) 2022 Gonzalo Larumbe
# All rights reserved.

RC=
echo "Running ERT tests..."
emacs -nw -batch \
      -L $PWD/tests \
      -l ert \
      -l verilog-ext-tests-setup \
      -l verilog-ext-tests \
      -f ert-run-tests-batch-and-exit

RC=$?
echo "Exiting with return code $RC"
exit $RC


