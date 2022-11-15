#!/bin/sh

# Copyright (c) 2022 Gonzalo Larumbe
# All rights reserved.

echo "Running ERT tests..."
emacs -batch -l ert -l my-tests.el -f ert-run-tests-batch-and-exit
echo "Ran tests!"
