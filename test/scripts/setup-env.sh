#!/bin/bash

# Copyright (c) 2022-2023 Gonzalo Larumbe
# All rights reserved.

PKGS_TO_INSTALL=(global universal-ctags python3-pygments silversearcher-ag ripgrep libverilog-perl verilator iverilog nodejs npm)
EXPECTED_INSTALLED_BINARIES=(python global gtags ctags ag rg vhier verilator iverilog nodejs npm)

sudo apt-get update

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
sudo cp verible-verilog-ls /usr/bin/verible-verilog-ls
sudo cp verible-verilog-format /usr/bin/verible-verilog-format
sudo cp verible-verilog-lint /usr/bin/verible-verilog-lint
cd -

echo ""
echo "verible-verilog-ls version $(verible-verilog-ls --version)"
echo "verible-verilog-format version $(verible-verilog-format --version)"
echo "verible-verilog-lint version $(verible-verilog-lint --version)"

echo ""
echo "Setting up svlangserver..."
npm install -g @imc-trading/svlangserver
echo "svlangserver path: $(which svlangserver)"
echo "svlangserver version: $(svlangserver --version)"

echo ""
echo "Setting up tree-sitter"
git clone https://github.com/tree-sitter/tree-sitter.git
cd tree-sitter
echo ""
echo "Building tree-sitter..."
make all
echo ""
echo "Installing tree-sitter..."
sudo make install
sudo ldconfig # Update ldconfig cache to find libtree-sitter
echo ""
echo "tree-sitter lib path: "
echo "$(sudo ldconfig -p | grep libtree-sitter)"
cd ..

