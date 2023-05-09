#!/bin/bash

# Copyright (c) 2022-2023 Gonzalo Larumbe
# All rights reserved.


# * Utils
run_elisp_cmd() {
    local SETUP_FILE=

    if [[ $# -ge 2 ]]; then
        SETUP_FILE=verilog-ext-tests-setup-package
    else
        SETUP_FILE=verilog-ext-tests-setup-straight
    fi

    emacs -Q -nw -batch \
          -L $PWD/test \
          -l ert \
          -l $SETUP_FILE \
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
    local PACKAGE_EL=$1

    echo "###############"
    echo "## Compiling ##"
    echo "###############"
    echo ""
    run_elisp_cmd "(verilog-ext-compile-dir \"$PWD\")" $PACKAGE_EL
}

recompile() {
    local PACKAGE_EL=$1

    clean
    compile $PACKAGE_EL
}

gen_font_lock () {
    if [[ $# -ge 1 ]]; then
        run_elisp_cmd "(verilog-ext-test-font-lock-update-dir :tree-sitter)"
    else
        run_elisp_cmd "(verilog-ext-test-font-lock-update-dir)"
    fi
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
    local SELECTOR=
    local PACKAGE_EL=$2

    echo "#######################"
    echo "## Running ERT tests ##"
    echo "#######################"
    echo ""

    if [[ $# -ge 1 ]]; then
        SELECTOR=$1

        if [[ "$SELECTOR" == "t" ]]; then # Don't double-quote t symbol
            CMD="(ert-run-tests-batch-and-exit t)"
        else
            CMD="(ert-run-tests-batch-and-exit \"$SELECTOR\")"
        fi

    else
        CMD="(ert-run-tests-batch-and-exit)"
    fi

    run_elisp_cmd "$CMD" $PACKAGE_EL
    RC=$?
    echo "Exiting with return code $RC"
    return $RC
}

recompile_run () {
    local SELECTOR=$1
    local PACKAGE_EL=$2

    recompile $PACKAGE_EL
    run_tests $SELECTOR $PACKAGE_EL
}

# Main
"$@"
