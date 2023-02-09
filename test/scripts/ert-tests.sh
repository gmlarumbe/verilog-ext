#!/bin/bash

# Copyright (c) 2022-2023 Gonzalo Larumbe
# All rights reserved.


# * Utils
run_elisp_cmd() {
    emacs -Q -nw -batch \
          -L $PWD/test \
          -l ert \
          -l verilog-ext-tests-setup \
          -l verilog-ext-tests \
          --eval "$1"
}

clean() {
    echo "Removing .elc files"
    find . -name "*.elc" -exec rm -v {} \;
    find ../../build/verilog-ext -name "*.elc" -exec rm -v {} \;
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

gen_indent_dir () {
    if [[ $# -ge 1 ]]; then
        run_elisp_cmd "(verilog-ext-test-indent-gen-expected-files :tree-sitter)"
    else
        run_elisp_cmd "(verilog-ext-test-indent-gen-expected-files)"
    fi
}

gen_beautify_dir () {
    run_elisp_cmd "(verilog-ext-test-beautify-gen-expected-files)"
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

recompile_run () {
    recompile
    run_tests $1
}

# Main
"$@"
