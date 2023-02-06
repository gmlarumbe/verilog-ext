#!/bin/bash

# Copyright (c) 2022-2023 Gonzalo Larumbe
# All rights reserved.


# * Utils
run_elisp_cmd() {
    emacs -Q -nw -batch \
          -L $PWD/tests \
          -l ert \
          -l verilog-ext-tests-setup \
          -l verilog-ext-tests \
          --eval "$1"
}

clean() {
    echo "Removing .elc files"
    find . -name "*.elc" -exec rm -v {} \;
    echo ""
}

compile() {
    echo "####################"
    echo "## Byte-compiling ##"
    echo "####################"
    echo ""
    run_elisp_cmd "(byte-recompile-directory \"$PWD\" 0)"
}

recompile() {
    clean
    compile
}

update_indent_dir () {
    run_elisp_cmd "(verilog-ext-test-indent-update-dir)"
}

run_tests () {
    local RC=

    echo "#######################"
    echo "## Running ERT tests ##"
    echo "#######################"
    echo ""

    if [[ $# -ge 1 ]]; then
        SELECTOR=$1
        CMD="(ert-run-tests-batch-and-exit \"$SELECTOR\")"
    else
        CMD="(ert-run-tests-batch-and-exit)"
    fi

    run_elisp_cmd "$CMD"
    RC=$?
    echo "Exiting with return code $RC"
    return $RC
}

# Main
"$@"
