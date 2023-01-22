;;; verilog-ext.el --- Verilog Extensions  -*- lexical-binding: t -*-

;; Copyright (C) 2022-2023 Gonzalo Larumbe

;; Author: Gonzalo Larumbe <gonzalomlarumbe@gmail.com>
;; URL: https://github.com/gmlarumbe/verilog-ext
;; Version: 0.0.0
;; Keywords: Verilog, IDE, Tools
;; Package-Requires: ((emacs "28.1"))

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Extensions for Verilog Mode:
;;  - Improve syntax highlighting
;;  - Hierarchy extraction and visualization via Verilog-Perl `vhier'
;;  - LSP configuration for `lsp-mode' and `eglot'
;;  - Support for many linters in `flycheck'
;;  - Improve `imenu': detect instances and support methods inside classes
;;  - Navigate through instances in a module
;;  - Jump to definition/reference of module at point via `ggtags' and `xref'
;;  - Beautify modules: indent and align parameters and ports (interactively and in batch)
;;  - Extended collection of custom and `yasnippet' templates insertion via `hydra'
;;  - Setup `company' to complete with verilog keywords
;;  - Wrapper functions to make `kill-word' stop at underscores without breaking indentation

;;; Code:


(defgroup verilog-ext nil
  "Verilog Extensions."
  :group 'languages
  :group 'verilog-mode)

(require 'verilog-utils)
(require 'verilog-editing)
(require 'verilog-navigation)
(require 'verilog-typedef)
(require 'verilog-compile)
(require 'verilog-beautify)
(require 'verilog-imenu)
(require 'verilog-templates)
(require 'verilog-completion)
(require 'verilog-font-lock)
(require 'verilog-vhier)
(require 'verilog-flycheck)
(require 'verilog-lsp)

;; Requires Emacs 29 with tree-sitter support and Verilog grammar
(when (and (>= emacs-major-version 29)
           (treesit-available-p)
           (treesit-language-available-p 'verilog))
  (require 'verilog-tree-sitter))


(provide 'verilog-ext)

;;; verilog-ext.el ends here
