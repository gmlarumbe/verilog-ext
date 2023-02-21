[![Build Status](https://github.com/gmlarumbe/verilog-ext/workflows/ERT-straight/badge.svg)](https://github.com/gmlarumbe/verilog-ext/actions/workflows/build_straight.yml)
[![MELPA](https://melpa.org/packages/verilog-ext-badge.svg)](https://melpa.org/#/verilog-ext)
[![License: GPL v3](https://img.shields.io/badge/License-GPL%20v3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)

# verilog-ext.el - SystemVerilog Extensions for Emacs #

This package provides some extensions on top of the great Emacs [verilog-mode](https://github.com/veripool/verilog-mode):

* Tree-sitter powered `verilog-ts-mode`
* Improve syntax highlighting
* Hierarchy extraction and navigation
* LSP configuration for `lsp-mode` and `eglot`
* Support for many linters via `flycheck`
* Improve `imenu` entries: detect instances, classes and methods
* Beautify modules and instances
* Code navigation functions for RTL and Verification environments
* Extended collection of custom and `yasnippet` templates insertion via `hydra`
* Code formatter via `apheleia`
* Code folding via `hideshow`
* Enhanced support for `which-func`
* Many additional misc utilities

## Installation ##

### MELPA ###

`verilog-ext` is available on MELPA.

See [Getting Started](https://melpa.org/partials/getting-started.html) for instructions on how to setup and download packages.

`verilog-ts-mode` is not yet available on MELPA. See [notes](https://github.com/gmlarumbe/verilog-ext/wiki/Tree-sitter#notes) for more info.

### straight.el ###

To install it via [straight](https://github.com/radian-software/straight.el) with `use-package`:

```emacs-lisp
(straight-use-package 'use-package)

(use-package verilog-ext
  :straight (:host github :repo "gmlarumbe/verilog-ext"
             :files ("verilog-ext.el" "verilog-ts-mode.el" "snippets")))
```

### Manually ###

First download `verilog-ext` in the desired directory (e.g. `~/.emacs.d`):

```shell
$ cd ~/.emacs.d
$ git clone https://github.com/gmlarumbe/verilog-ext
```

And add the following snippet to your `.emacs` or `init.el`:

```emacs-lisp
(add-to-list 'load-path (expand-file-name "~/.emacs.d/verilog-ext"))
(require 'verilog-ext)
```

## Basic config ##

The most basic configuration just requires setup of the minor-mode and to add it as a hook for `verilog-mode`:

```elisp
(verilog-ext-mode-setup)
(add-hook 'verilog-mode-hook #'verilog-ext-mode)
```

If installed and loaded via `use-package`:

```elisp
(use-package verilog-ext
  :after verilog-mode
  :demand
  :hook ((verilog-mode . verilog-ext-mode))
  :config
  (verilog-ext-mode-setup))
```


## Keybindings ##

Enabling of `verilog-ext-mode` minor-mode creates the following keybindings:

* Features:
  * <kbd>M-i</kbd> `verilog-ext-imenu-list`
  * <kbd>C-c C-l</kbd> `verilog-ext-code-format`
  * <kbd>C-c C-p</kbd> `verilog-ext-preprocess`
  * <kbd>C-c C-f</kbd> `verilog-ext-flycheck-mode-toggle`
  * <kbd>C-c C-t</kbd> `verilog-ext-hydra/body`
  * <kbd>C-c C-v</kbd> `verilog-ext-vhier-current-file`
  * <kbd>C-\<tab\></kbd> `verilog-ext-hs-toggle-hiding`

* Code beautifying
  * <kbd>C-M-i</kbd> `verilog-ext-indent-block-at-point`
  * <kbd>C-c C-b</kbd> `verilog-ext-module-at-point-beautify`

* Dwim navigation
  * <kbd>C-M-a</kbd> `verilog-ext-nav-beg-of-defun-dwim`
  * <kbd>C-M-e</kbd> `verilog-ext-nav-end-of-defun-dwim`
  * <kbd>C-M-d</kbd> `verilog-ext-nav-down-dwim`
  * <kbd>C-M-u</kbd> `verilog-ext-nav-up-dwim`
  * <kbd>C-M-p</kbd> `verilog-ext-nav-prev-dwim`
  * <kbd>C-M-n</kbd> `verilog-ext-nav-next-dwim`

* Module at point
  * <kbd>C-c M-.</kbd> `verilog-ext-jump-to-module-at-point-def`
  * <kbd>C-c M-?</kbd> `verilog-ext-jump-to-module-at-point-ref`

* Jump to parent module
  * <kbd>C-M-.</kbd> `verilog-ext-jump-to-parent-module`

* Port connections
  * <kbd>C-c C-c c</kbd> `verilog-ext-clean-port-blanks`
  * <kbd>C-c C-c t</kbd> `verilog-ext-toggle-connect-port`
  * <kbd>C-c C-c r</kbd> `verilog-ext-connect-ports-recursively`

* Syntax table override functions:
  * <kbd>TAB</kbd> `verilog-ext-tab`
  * <kbd>M-d</kbd> `verilog-ext-kill-word`
  * <kbd>M-f</kbd> `verilog-ext-forward-word`
  * <kbd>M-b</kbd> `verilog-ext-backward-word`
  * <kbd>C-\<backspace\></kbd> `verilog-ext-backward-kill-word`


# Features #

## Tree-sitter ##
The package provides the major-mode `verilog-ts-mode` for syntax highligting and indentation. It is derived from `verilog-mode` making AUTOs and other utilities still available.

`verilog-ts-mode` is still work in progress and aims to provide the same functionality as `verilog-ext` but much faster and efficiently.

For more information see the [wiki](https://github.com/gmlarumbe/verilog-ext/wiki/Tree-sitter).


## Syntax highlighting ##

<img src="https://user-images.githubusercontent.com/51021955/208774894-a0f3159e-0f41-45db-be28-8a8706ad49ec.gif" width=400 height=300>

For face customization: <kbd>M-x</kbd> `customize-group` <kbd>RET</kbd> `verilog-ext-faces`


## Hierarchy extraction ##

<img src="https://user-images.githubusercontent.com/51021955/209574234-eda2d151-87b4-44db-8edd-e41e2e1b79d4.gif" width=400 height=300>

Hierarchy extraction of module at current buffer via [Verilog-Perl](https://github.com/veripool/verilog-perl) `vhier`.

For configuration information, see the [wiki](https://github.com/gmlarumbe/verilog-ext/wiki/Hierarchy).


## Language Server Protocol ##

Auto-configure various SystemVerilog language servers for `lsp-mode` and `eglot`:

- [hdl_checker](https://github.com/suoto/hdl_checker)
- [svlangserver](https://github.com/imc-trading/svlangserver)
- [verible](https://github.com/chipsalliance/verible/tree/master/verilog/tools/ls)
- [svls](https://github.com/dalance/svls)
- [veridian](https://github.com/vivekmalneedi/veridian)

For configuration instructions, see the [wiki](https://github.com/gmlarumbe/verilog-ext/wiki/Language-Server-Protocol)

## Linting ##
Support via `flycheck` for the following linters:

* [Verilator](https://github.com/verilator/verilator)
* [Icarus Verilog](https://github.com/steveicarus/iverilog)
* [Verible](https://github.com/chipsalliance/verible/tree/master/verilog/tools/lint)
* [Slang](https://github.com/MikePopoloski/slang)
* [Svlint](https://github.com/dalance/svlint)
* Cadence HAL

For configuration and usage instructions, see the [wiki](https://github.com/gmlarumbe/verilog-ext/wiki/Linting)

## Imenu ##
Support detection of instances and methods inside classes.

* Instances

<img src="https://user-images.githubusercontent.com/51021955/208779722-9b760d8d-796b-48cb-ad35-f95f1ec48786.gif" width=400 height=300>

* Methods

<img src="https://user-images.githubusercontent.com/51021955/208780855-52166bf0-5897-48d1-83e8-698d0b1d6269.gif" width=400 height=300>

Find more information [here](https://github.com/gmlarumbe/verilog-ext/wiki/Imenu).


## Navigation ##

<img src="https://user-images.githubusercontent.com/51021955/208782492-b2ff09b3-f662-4d22-a46c-64eb69f9f7b9.gif" width=400 height=300>

* Navigate instances inside a module
* Jump to definition/references of module at point
* Jump to parent module
* Context aware dwim functions for RTL/Verification environments

For detailed info see the [wiki](https://github.com/gmlarumbe/verilog-ext/wiki/Navigation).


## Beautify instances ##
Indent and align parameters and ports.

<img src="https://user-images.githubusercontent.com/51021955/208781782-dbf45c3e-df3f-405a-aacc-1d190ab87ae9.gif" width=400 height=300>

Interactive functions:

* `verilog-ext-module-at-point-beautify`: <kbd>C-c C-b</kbd>
* `verilog-ext-beautify-current-buffer`

Batch-mode functions:

* `verilog-ext-beautify-files`
* `verilog-ext-beautify-files-current-dir`

## Snippets ##
* Select between snippets that cover most frequently used SystemVerilog constructs:

    <img src="https://user-images.githubusercontent.com/51021955/209577453-730014b7-d261-4884-9eb2-baa8eaa02a66.gif" width=400 height=300>


* Insert instances in current module from file:

    <img src="https://user-images.githubusercontent.com/51021955/209577185-ad6b688d-158d-476f-94f5-e1d0eeb0fbd8.gif" width=400 height=300>


* Create basic testbench environment from DUT file:

    <img src="https://user-images.githubusercontent.com/51021955/209578258-1db8eb6b-37ce-4be0-8cd6-ec380116d0cd.gif" width=400 height=300>


Functions:

* `verilog-ext-hydra/body`: <kbd>C-c C-t</kbd>

## Code formatter ##

Code-formatter setup via [apheleia](https://github.com/radian-software/apheleia) and [`verible-verilog-format`](https://github.com/chipsalliance/verible).

* See configuration in the [wiki](https://github.com/gmlarumbe/verilog-ext/wiki/Code-formatter).

  <img src="https://user-images.githubusercontent.com/51021955/220176079-f31ba086-7e64-434f-bb23-9c08e3f3ed6d.gif" width=400 height=300>


## Code folding ##

* Code folding via `hideshow`: <kbd>C-\<tab\></kbd>

  <img src="https://user-images.githubusercontent.com/51021955/220174477-06beb019-3b2f-4329-8897-88e739ed5ea7.gif" width=400 height=300>


## Which-func ##

* Enhanced `which-func` support: show current block/instance at point in the mode-line

  <img src="https://user-images.githubusercontent.com/51021955/220174496-b35c99fd-2eb8-424b-9eca-49b9a1d6aa54.gif" width=400 height=300>


## Port connections ##

* Toggle connections of ports under instance at point

  <img src="https://user-images.githubusercontent.com/51021955/220176192-d823ba19-099f-4484-abc7-8269fd92928b.gif" width=400 height=300>

  * `verilog-ext-toggle-connect-port`: <kbd>C-c C-c t</kbd>
  * `verilog-ext-connect-ports-recursively`: <kbd>C-c C-c r</kbd>
  * `verilog-ext-clean-port-blanks`: <kbd>C-c C-c c</kbd>




## Misc ##

* Preprocess files based on binary: `verilator`, `iverilog` or `vppreproc`

   - `verilog-ext-preprocess`: <kbd>C-c C-p</kbd>

* Setup `company` to complete with SystemVerilog keywords

* Wrapper functions to stop cursor at underscores without breaking indentation

  - `verilog-ext-forward-word`: <kbd>M-f</kbd>
  - `verilog-ext-backward-word`: <kbd>M-b</kbd>
  - `verilog-ext-kill-word`: <kbd>M-d</kbd>
  - `verilog-ext-backward-kill-word`: <kbd>C-\<backspace\></kbd> and <kbd>M-DEL</kbd>

* Typedef handling for syntax-higlighting and alignment via `verilog-pretty-declarations`

  - `verilog-ext-typedef-project-update`: see [wiki](https://github.com/gmlarumbe/verilog-ext/wiki/Typedefs)

* Timestamp mode updating (after setting header timestamp regexp)

    - `verilog-ext-time-stamp-mode`: see [wiki](https://github.com/gmlarumbe/verilog-ext/wiki/Timestamp)

* Auto convert block comments to names:

    - `verilog-ext-block-end-comments-to-names-mode`

* Makefile based development:

    - `verilog-ext-makefile-create`
    - `verilog-ext-makefile-compile`


# Contributing #

Contributions are welcome! Just stick to common Elisp conventions and run the ERT suite after testing your changes and before submitting a new PR.

For new functionality add new ERT tests if possible.

## ERT Tests setup ###

To run the whole ERT test suite change directory to the `verilog-ext` root and run the `test` target:

```shell
$ cd ~/.emacs.d/verilog-ext
$ make test
```

To run a subset of tests (e.g. navigation):

```shell
$ cd ~/.emacs.d/verilog-ext
$ tests/scripts/ert-tests.sh recompile_run navigation::
```

## Other packages

* [vhdl-ext](https://github.com/gmlarumbe/vhdl-ext): VHDL Extensions for Emacs
  * Analog package to edit VHDL sources
