[![Build Status](https://github.com/gmlarumbe/verilog-ext/workflows/ERT/badge.svg)](https://github.com/gmlarumbe/verilog-ext/actions)

# verilog-ext.el - SystemVerilog Extensions for Emacs #

This package includes some extensions on top of the great Emacs [verilog-mode](https://github.com/veripool/verilog-mode).

* Tree-sitter support (requires Emacs 29)
* Improve syntax highlighting
* Hierarchy extraction and navigation
* LSP configuration for `lsp-mode` and `eglot`
* Support for many linters via `flycheck`
* Improve `imenu` entries: detect instances, classes and methods
* Code navigation functions for RTL and Verification environments
* Beautify modules and instances
* Extended collection of custom and `yasnippet` templates insertion via `hydra`
* Many additional misc utilities

## Installation ##

### Requirements ###

#### Verilog-mode ####

Latest `verilog-mode` version is required since `verilog-ext` relies on much of its functionality to work correctly.
Using [straight](https://github.com/radian-software/straight.el) and [use-package](https://github.com/jwiegley/use-package):
```emacs-lisp
(straight-use-package 'use-package)
(use-package verilog-mode
  :straight (:repo "veripool/verilog-mode"))
```
For other installation methods refer to [verilog-mode](https://github.com/veripool/verilog-mode) installation options.

#### Binaries and Emacs Lisp packages ####

`verilog-ext` makes use of several binaries as backend engines to support IDE-like functionality. In addition, some third party Emacs Lisp packages serve as frontends for those binaries.

List of required binaries:
- Definitions and references navigation: `global`, `gtags`, `universal-ctags`, `python`, `pygments`
- Jump to parent module: `ag`, `ripgrep`
- Hierarchy extraction: `vhier`
- Linting: `verilator`, `iverilog`, `verible-verilog-lint`, `slang`, `svlint`, `xrun`/`hal`
- LSP: `hdl_checker`, `svlangserver`, `verible-verilog-ls`, `svls`, `veridian`

Installation of required Emacs-lisp packages:
```emacs-lisp
(use-package projectile)
(use-package ggtags)
(use-package ag)
(use-package ripgrep)
(use-package company)
(use-package yasnippet)
(use-package hydra)
(use-package outshine)
(use-package flycheck)
(use-package apheleia)
(use-package lsp-mode)
(use-package eglot)
```

### verilog-ext ###

#### straight.el ####

For the time being `verilog-ext` is still work in progress and is not yet available at [MELPA](https://melpa.org/).
To install it via [straight](https://github.com/radian-software/straight.el):

```emacs-lisp
(straight-use-package 'use-package)
(use-package
    :straight (:repo "gmlarumbe/verilog-ext"))
```

#### Manually ####
```shell
$ cd ~/.emacs.d
$ git clone https://github.com/gmlarumbe/verilog-ext
```
And add the following snippet to your `.emacs` or `init.el`:
```emacs-lisp
(add-to-list 'load-path (expand-file-name "~/.emacs.d/verilog-ext"))
(require 'verilog-ext)
```

### tree-sitter ###
Requires Emacs 29, installation of `tree-sitter` and Verilog grammar.

To install `tree-sitter` there are different options:

* Via [npm](https://www.npmjs.com/package/tree-sitter)
* Manually:
```shell
$ git clone https://github.com/tree-sitter/tree-sitter.git
$ cd tree-sitter
$ make && sudo make install
```

Installation of grammar can be automated through the script:
```shell
$ .github/scripts/install-ts-grammar.sh
```
That will install `libtree-sitter-verilog.so` at `$HOME/.emacs.d/tree-sitter`.


## Basic config ##
By default `verilog-ext` does not create any keybindings. Following snippet shows a configuration example with `use-package`:
```emacs-lisp
(use-package verilog-ext
  :straight (:host github :repo "gmlarumbe/verilog-ext")
  :after verilog-mode
  :demand
  :bind (:map verilog-mode-map
         ;; Default keys override
         ("TAB"           . verilog-ext-electric-verilog-tab)
         ("M-d"           . verilog-ext-kill-word)
         ("M-f"           . verilog-ext-forward-word)
         ("M-b"           . verilog-ext-backward-word)
         ("C-<backspace>" . verilog-ext-backward-kill-word)
         ;; Features
         ("M-i"           . verilog-ext-imenu-list)
         ("C-c C-p"       . verilog-ext-preprocess)
         ("C-c C-f"       . verilog-ext-flycheck-mode-toggle)
         ("C-c C-t"       . verilog-ext-hydra/body)
         ("C-c C-v"       . verilog-ext-vhier-current-file)
         ;; Code beautifying
         ("C-M-i"         . verilog-ext-indent-block-at-point)
         ("C-c b"         . verilog-ext-module-at-point-beautify)
         ;; Dwim navigation
         ("C-M-a"         . verilog-ext-nav-beg-of-defun-dwim)
         ("C-M-e"         . verilog-ext-nav-end-of-defun-dwim)
         ("C-M-d"         . verilog-ext-nav-down-dwim)
         ("C-M-u"         . verilog-ext-nav-up-dwim)
         ("C-M-p"         . verilog-ext-nav-prev-dwim)
         ("C-M-n"         . verilog-ext-nav-next-dwim)
         ;; Module navigation
         ("C-M-."         . verilog-ext-jump-to-parent-module)
         ;; Port connections
         ("C-c c"         . verilog-ext-toggle-connect-port)
         ("C-c C-c"       . verilog-ext-connect-ports-recursively))
  :init
  (setq verilog-ext-snippets-dir "~/.emacs.d/straight/repos/verilog-ext/snippets")
  (setq verilog-ext-flycheck-eldoc-toggle t)
  (setq verilog-ext-flycheck-verible-rules '("-line-length"))
  :config
  (verilog-ext-flycheck-set-linter 'verilog-verible)
  (verilog-ext-add-snippets))
```

# Features #

## Tree-sitter ##
The package includes the major-mode `verilog-ts-mode` for syntax highligting and indentation.
There is some WIP, e.g. Imenu or navigation functions.

## Syntax highlighting ##
Improved fontification via:

  * Tree-sitter: requires Emacs 29
  * Font-lock override

<img src="https://user-images.githubusercontent.com/51021955/208774894-a0f3159e-0f41-45db-be28-8a8706ad49ec.gif" width=400 height=300>

For face customization: <kbd>M-x</kbd> `customize-group` <kbd>RET</kbd> `verilog-ext-faces`


## Hierarchy extraction ##
Extract hierarchy of module at current buffer via [Verilog-Perl](https://github.com/veripool/verilog-perl) `vhier`.

Visualize with `outline-minor-mode` and `outshine`.

<img src="https://user-images.githubusercontent.com/51021955/209574234-eda2d151-87b4-44db-8edd-e41e2e1b79d4.gif" width=400 height=300>

Functions:

* `verilog-ext-vhier-current-file` for hierarchy extraction
* `vhier-outshine-mode` for hierarchy navigation


## Language Server Protocol ##

Auto-configure various SystemVerilog language servers for `lsp-mode` and `eglot`:

- [hdl_checker](https://github.com/suoto/hdl_checker)
- [svlangserver](https://github.com/imc-trading/svlangserver)
- [verible](https://github.com/chipsalliance/verible/tree/master/verilog/tools/ls)
- [svls](https://github.com/dalance/svls)
- [veridian](https://github.com/vivekmalneedi/veridian)

Make sure that Language Server binary is in the $PATH:
```shell
$ which svlangserver
/usr/local/bin/svlangserver
```

Interactively:
<kbd>M-x</kbd> `verilog-ext-lsp-set-server`<kbd>RET</kbd> `ve-svlangserver`

Programatically:
```elisp
;; For `lsp-mode':
(verilog-ext-lsp-set-server 've-svlangserver)
;; For `eglot':
(verilog-ext-eglot-set-server 've-svlangserver)
```

## Linting ##
Support via `flycheck` for the following linters:

* [Verilator](https://github.com/verilator/verilator)
* [Icarus Verilog](https://github.com/steveicarus/iverilog)
* [Verible](https://github.com/chipsalliance/verible/tree/master/verilog/tools/lint)
* [Slang](https://github.com/MikePopoloski/slang)
* [Svlint](https://github.com/dalance/svlint)
* Cadence HAL

Functions:

* `verilog-ext-flycheck-mode-toggle`: enable/disable current linter. Select linter with `prefix-arg`/(`C-u`).


## Imenu ##
Support detection of instances and methods inside classes.

* Instances

<img src="https://user-images.githubusercontent.com/51021955/208779722-9b760d8d-796b-48cb-ad35-f95f1ec48786.gif" width=400 height=300>

* Methods

<img src="https://user-images.githubusercontent.com/51021955/208780855-52166bf0-5897-48d1-83e8-698d0b1d6269.gif" width=400 height=300>

* `imenu-list` is a recommended package to visualize different levels of nesting in the hierarchy.


## Navigation ##

### Instance navigation ###
Navigate through instances inside a module forward/backwards.
Jump to parent module via `ag`/`ripgrep`.

<img src="https://user-images.githubusercontent.com/51021955/208782492-b2ff09b3-f662-4d22-a46c-64eb69f9f7b9.gif" width=400 height=300>

Functions:

* `verilog-ext-find-module-instance-fwd`
* `verilog-ext-find-module-instance-bwd`
* `verilog-ext-jump-to-parent-module`
* `verilog-ext-instance-at-point`

### Jump to definition/reference ###
Jump to definition/reference of module at point via `ggtags` and `xref`.

Functions:

* `verilog-ext-jump-to-module-at-point`
* `verilog-ext-jump-to-module-at-point-def`
* `verilog-ext-jump-to-module-at-point-ref`

### Dwim

Context aware functions (do what I mean) depending on the file being edited.
Modules (RTL) navigate through instances while classes (Verification) navigate through methods/defuns.

Functions:

* `verilog-ext-nav-down-dwim`
* `verilog-ext-nav-up-dwim`
* `verilog-ext-nav-beg-of-defun-dwim`
* `verilog-ext-nav-end-of-defun-dwim`
* `verilog-ext-nav-next-dwim`
* `verilog-ext-nav-prev-dwim`


## Beautify instances ##
Indent and align parameters and ports, interactively and in batch.

<img src="https://user-images.githubusercontent.com/51021955/208781782-dbf45c3e-df3f-405a-aacc-1d190ab87ae9.gif" width=400 height=300>

Functions:

* `verilog-ext-module-at-point-beautify`
* `verilog-ext-beautify-current-buffer`
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


* `verilog-ext-hydra/body`

## Misc ##
* Code formatter setup via [apheleia](https://github.com/radian-software/apheleia)

   - `verilog-ext-code-formatter-setup`

* Preprocess files based on binary: `verilator`, `iverilog` or `vppreproc`

   - `verilog-ext-preprocess`

* Setup `company` to complete with verilog keywords

* Wrapper functions to stop cursor at underscores without breaking indentation

  - `verilog-ext-forward-word`
  - `verilog-ext-backward-word`
  - `verilog-ext-kill-word`
  - `verilog-ext-backward-kill-word`

* Typedef handling for syntax-higlighting and alignment via `verilog-pretty-declarations`

  - `verilog-ext-typedef-project-update`

* Toggle connections of ports under instance at point

  - `verilog-ext-toggle-connect-port`
  - `verilog-ext-connect-ports-recursively`
  - `verilog-ext-clean-port-blanks`

* Timestamp mode updating (after setting header timestamp regexp)

    - `verilog-ext-time-stamp-mode`

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
$ tests/scripts/ert-tests.sh run_tests navigation::
```

If there is a missing dependency, check the file `tests/scripts/setup-env.sh` used by GitHub Actions to configure your environment.


## Other packages

* [vhdl-ext](https://github.com/gmlarumbe/vhdl-ext): VHDL Extensions for Emacs
  * Analog package to edit VHDL sources

