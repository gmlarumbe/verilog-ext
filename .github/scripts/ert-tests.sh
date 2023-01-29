#!/bin/bash

# Copyright (c) 2022-2023 Gonzalo Larumbe
# All rights reserved.


if [[ $# -ge 1 ]]; then
    SELECTOR=$1
    CMD="(ert-run-tests-batch-and-exit \"$SELECTOR\")"
else
    CMD="(ert-run-tests-batch-and-exit)"
fi

echo "Removing .elc files"
find . -name "*.elc" -exec rm -v {} \;

RC=
echo "Running ERT tests..."
emacs -Q -nw -batch \
      -L $PWD/tests \
      -l ert \
      -l verilog-ext-tests-setup \
      -l verilog-ext-tests \
      --eval "$CMD"

RC=$?
echo "Exiting with return code $RC"
exit $RC


