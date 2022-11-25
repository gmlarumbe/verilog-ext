#!/bin/bash

PKGS_TO_INSTALL=(global universal-ctags python3-pygments silversearcher-ag ripgrep libverilog-perl)
EXPECTED_INSTALLED_BINARIES=(python global gtags ctags ag rg vhier)

for pkg in "${PKGS_TO_INSTALL[@]}"; do
    echo ""
    echo "Installing $pkg"
    sudo apt-get install "$pkg"
done

echo ""
echo "Checking binaries PATHs and versions..."

for bin in "${EXPECTED_INSTALLED_BINARIES[@]}"; do
    which "$bin"
    $bin --version
done

