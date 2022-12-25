[![Build Status](https://github.com/gmlarumbe/verilog-ext/workflows/CI/badge.svg)](https://github.com/gmlarumbe/verilog-ext/actions)

# verilog-ext.el - Verilog Extensions for Emacs #

This package includes some extensions on top of the great Emacs [verilog-mode](https://github.com/veripool/verilog-mode).

* Improve syntax highlighting
* Hierarchy extraction and navigation
* LSP configuration for `lsp-mode` and `eglot`
* Support for many linters via `flycheck`
* Improve `imenu` entries: instances, classes and methods
* Code navigation functions: instances, definitions, references, parent module, dwim
* Beautify modules and instances
* Extended collection of custom and `yasnippet` templates insertion via `hydra`
* Many additional misc utilities

## Installation ##

### Requirements ###

#### Verilog-mode ####

Latest `verilog-mode` version is required since `verilog-ext` relies on much of its functionality to work properly.

Using straight:
```emacs-lisp
(straight-use-package 'use-package)
(use-package verilog-mode
  :straight (:repo "veripool/verilog-mode"))
```
For other installation methods refer to [verilog-mode](https://github.com/veripool/verilog-mode) installation options.

#### Binaries and emacs lisp packages ####

`verilog-ext` makes use of several binaries used as backend engines to support IDE-like functionality. In addition, some third party Emacs Lisp packages serve as frontends for those binaries.

List of required binaries:
- global, gtags, universal-ctags
- python, pygments
- ag, rg
- vhier
- Linters: verilog, iverilog, verible-verilog-lint, slang, svlint, xrun/hal
- LSP servers: hdl_checker, svlangserver, verible-verilog-ls, svls, veridian

Emacs-lisp packages required:
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

For the time being `verilog-ext` is still work in progress and is not yet available in MELPA.
To install it via `straight` (recommended):

```emacs-lisp
(straight-use-package 'use-package)
(use-package
    :straight (:repo "gmlarumbe/verilog-ext"))
```

To install it manually::
```shell
$ cd ~/.emacs.d
$ git clone https://github.com/gmlarumbe/verilog-ext
```
And add the following snippet to your `.emacs` or `init.el`:
```emacs-lisp
(add-to-list 'load-path (expand-file-name "~/.emacs.d/verilog-ext"))
(require 'verilog-ext)
```

# Features #

## Syntax highlighting ##
Font-lock based improved fontification.
<table>
<tr>
<th>verilog-mode</th>
<th>verilog-ext</th>
<tr>
<td>
<img src="https://user-images.githubusercontent.com/51021955/208774001-01a164b4-bc16-4860-9bf2-1b2f4d60ef8e.gif" width=300 height=250>
</td>
<td>
<img src="https://user-images.githubusercontent.com/51021955/208774894-a0f3159e-0f41-45db-be28-8a8706ad49ec.gif" width=300 height=250>
</td>
</tr>
<table>

## Hierarchy extraction ##
Extract hierarchy of module at current buffer via [Verilog-Perl](https://github.com/veripool/verilog-perl) `vhier`.
Visualize with `outline-minor-mode` and `outshine`.

Functions:

* `verilog-ext-vhier-current-file`: for hierarchy extraction
* `vhier-outshine-mode`: for hierarchy navigation


## Language Server Protocol ##

Auto-configure various SystemVerilog language servers for `lsp-mode` and `eglot`:

- [hdl_checker](https://github.com/suoto/hdl_checker)
- [svlangserver](https://github.com/imc-trading/svlangserver)
- [verible](https://github.com/chipsalliance/verible/tree/master/verilog/tools/ls)
- [svls](https://github.com/dalance/svls)
- [veridian](https://github.com/vivekmalneedi/veridian)


Functions:

* `verilog-ext-lsp-set-server`
* `verilog-ext-eglot-set-server`


## Imenu ##
Support detection of instances and methods inside classes.
<table>
<tr>
<th>Instances</th>
<th>Methods</th>
<tr>
<td>
<img src="https://user-images.githubusercontent.com/51021955/208779722-9b760d8d-796b-48cb-ad35-f95f1ec48786.gif" width=300 height=250>
</td>
<td>
<img src="https://user-images.githubusercontent.com/51021955/208780855-52166bf0-5897-48d1-83e8-698d0b1d6269.gif" width=300 height=250>
</td>
</tr>
<table>

* `imenu-list` is a recommended package to visualize different levels of nesting in the hierarchy.

## Linting ##
Support via `flycheck` for the following linters:

* [Verilator](https://github.com/verilator/verilator)
* [Icarus Verilog](https://github.com/steveicarus/iverilog)
* [Verible](https://github.com/chipsalliance/verible/tree/master/verilog/tools/lint)
* [Slang](https://github.com/MikePopoloski/slang)
* [Svlint](https://github.com/dalance/svlint)
* Cadence HAL

Functions:

* `verilog-ext-flycheck-mode-toggle`: enable/disable current linter. Select linter with `prefix-arg`.

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
Jump to definition/reference of module at point via ggtags and xref.

Functions:

* `verilog-ext-jump-to-module-at-point`
* `verilog-ext-jump-to-module-at-point-def`
* `verilog-ext-jump-to-module-at-point-ref`

### Dwim

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

Functions:

* `verilog-ext-hydra/body`

## Misc ##
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


* Code formatter setup via `apheleia`

   - `verilog-ext-code-formatter-setup`


* Auto convert block comments to names:

    - `verilog-ext-block-end-comments-to-names-mode`

* Makefile based development:

    - `verilog-ext-makefile-create`
    - `verilog-ext-makefile-compile`


## Contributing ##

Contributions are welcome! Just stick to regular Elisp conventions and run the ERT tests before submitting a new PR.

For new functionality, add a new ERT test that covers that functionality.

### ERT Tests setup ####

Requirements:

```emacs-lisp
(use-package faceup)
(use-package align
  :straight nil
  :config
  (setq align-default-spacing 1)
  (setq align-to-tab-stop nil))
```


### Why not inside `verilog-mode` ? ##

One of the reasons is that `verilog-ext` overrides some functionality of `verilog-mode` (e.g. syntax highlighting).
Since not every user of `verilog-mode` would accept some of these changes, `verilog-ext` offers modularity with respect to which functionality to use.

Another reason is that `verilog-ext` only supports GNU Emacs (tested in 28.1) in contrast to `verilog-mode` which also aims to be compatible with XEmacs.
Backwards compatibility with XEmacs would prevent development from using new neat features such as `lsp` or `tree-sitter`.

On the other hand, since the development of `verilog-ext` happens on GitHub, it is not restricted by the FSF contributor agreement and everyone can easily contribute to the project.
Eventually, maintainers of `verilog-mode` could agree on including some `verilog-ext` functionality inside `verilog-mode` for newer Emacs releases.


## WIP/TODO ##

### Doc website ###

Use a .org file as an input for GitHub README and HTML doc website.

### Tree-sitter ###

There is some work done with `tree-sitter`. Since Emacs 29 includes it as part of the core, many of the functionalities
here could be replaced and optimized by using `tree-sitter` instead of regexp based search.

### Completion ###

A good `completion-at-point` function would include symbols indexing for a project (e.g. same as `ggtags`). This could
be used by a function of `completion-at-point-functions` to determine contextually what type of completion is needed.


### Hierarchy display ###

Right now hierarchy is shown via `outline-minor-mode` and `outshine`. Other alternatives such as builtin `hierarchy`
or `treemacs` could offer better results.

