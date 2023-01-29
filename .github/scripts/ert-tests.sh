#!/bin/bash

# Copyright (c) 2022-2023 Gonzalo Larumbe
# All rights reserved.


if [[ $# -ge 1 ]]; then
    SELECTOR=$1
    CMD="(ert-run-tests-batch-and-exit \"$SELECTOR\")"
else
    CMD="(ert-run-tests-batch-and-exit)"
fi

# Byte-compiling
echo "####################"
echo "## Byte-compiling ##"
echo "####################"
echo ""
$PWD/.github/scripts/byte-compile.sh recompile
echo ""

# Run tests
echo "#######################"
echo "## Running ERT tests ##"
echo "#######################"
echo ""
RC=
emacs -Q -nw -batch \
      -L $PWD/tests \
      -l ert \
      -l verilog-ext-tests-setup \
      -l verilog-ext-tests \
      --eval "$CMD"

RC=$?
echo "Exiting with return code $RC"
exit $RC


