#!/bin/bash

# Copyright (c) 2022 Gonzalo Larumbe
# All rights reserved.

PKGS_TO_INSTALL=(global universal-ctags python3-pygments silversearcher-ag ripgrep libverilog-perl verilator iverilog)
EXPECTED_INSTALLED_BINARIES=(python global gtags ctags ag rg vhier verilator iverilog)

for pkg in "${PKGS_TO_INSTALL[@]}"; do
    echo ""
    echo "Installing $pkg"
    sudo apt-get install "$pkg"
done

echo ""
echo "Checking binaries PATHs and versions..."

for bin in "${EXPECTED_INSTALLED_BINARIES[@]}"; do
    echo ""
    echo "$bin path: $(which $bin)"
    echo "$bin version: $($bin --version)"
done

# Setup Verible (get latest release)
VERIBLE_GITHUB_URL=https://github.com/chipsalliance/verible
LATEST_RELEASE_URL=releases/download/v0.0-2492-gd122fac8
LATEST_RELEASE_FILE=verible-v0.0-2492-gd122fac8-Ubuntu-22.04-jammy-x86_64.tar.gz

echo ""
echo "Setting up Verible tools..."
curl -L -o $LATEST_RELEASE_FILE $VERIBLE_GITHUB_URL/$LATEST_RELEASE_URL/$LATEST_RELEASE_FILE
tar xvzf $LATEST_RELEASE_FILE
cd verible-*/bin
export PATH=$PWD:$PATH
cd -

echo ""
echo "verible-verilog-ls version $(verible-verilog-ls --version)"
echo "verible-verilog-format version $(verible-verilog-format --version)"
echo "verible-verilog-lint version $(verible-verilog-lint --version)"

