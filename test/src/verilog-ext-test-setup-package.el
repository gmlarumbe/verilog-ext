;;; verilog-ext-test-setup-package.el --- verilog-ext ERT Tests Setup with package.el  -*- lexical-binding: t -*-

;; Copyright (C) 2022-2024 Gonzalo Larumbe

;; Author: Gonzalo Larumbe <gonzalomlarumbe@gmail.com>
;; URL: https://github.com/gmlarumbe/test-hdl

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
;;
;; verilog-ext ERT Tests Setup with package.el
;;
;; INFO: Packages downloaded from MELPA (not MELPA Stable) will fetch the
;; snapshot of the latest commit in the corresponding Git repo and its
;; dependencies. It would therefore have the same effect as testing with
;; straight but with the issue that test/ code in the repo would not be in sync
;; with the code of the downloaded package until the snapshot is updated
;; (various times per day).
;;
;; For MELPA Stable this is different since package.el will download the tagged
;; version of the repo and all its dependencies.
;;
;;; Code:

;;;; Setup package.el
;; INFO: Perform tests in package.el only in MELPA Stable:
;;  - For bleeding-edge versions use straight and package.el basic test
(setq test-hdl-setup-package-archives '(("melpa-stable" . "https://stable.melpa.org/packages/")))
(require 'test-hdl-setup-package)

;;;; Install/setup package
(message "Installing and setting up verilog-ext")
(package-install 'verilog-ext)
(require 'verilog-ext)
(setq verilog-ext-feature-list (remove 'typedefs verilog-ext-feature-list)) ; Do not override `verilog-align-typedef-regexp'
(setq verilog-ext-feature-list (remove 'lsp-bridge verilog-ext-feature-list)) ; Do not autosetup since `lsp-bridge' is not available on MELPA
(setq verilog-ext-feature-list (remove 'lspce verilog-ext-feature-list)) ; Do not autosetup since `lsp-bridge' is not available on MELPA
(setq verilog-ext-cache-enable nil)
(verilog-ext-mode-setup)
(add-hook 'verilog-mode-hook #'verilog-ext-mode)

;;;; Customization
;;;;; align
(require 'align)
(setq align-default-spacing 1)
(setq align-to-tab-stop nil)

;;;;; verilog-mode
(defvar verilog-ext-test-indent-level 4)
(setq verilog-indent-level             verilog-ext-test-indent-level)
(setq verilog-indent-level-module      verilog-ext-test-indent-level)
(setq verilog-indent-level-declaration verilog-ext-test-indent-level)
(setq verilog-indent-level-behavioral  verilog-ext-test-indent-level)
(setq verilog-indent-level-directive   verilog-ext-test-indent-level)
(setq verilog-case-indent              verilog-ext-test-indent-level)
(setq verilog-cexp-indent              verilog-ext-test-indent-level)
(setq verilog-indent-lists                  nil)
(setq verilog-indent-begin-after-if           t)
(setq verilog-tab-always-indent               t) ; Indent even though we are not at the beginning of line
(setq verilog-tab-to-comment                nil)
(setq verilog-date-scientific-format          t)
(setq verilog-case-fold                     nil) ; Regexps should NOT ignore case
(setq verilog-align-ifelse                  nil)
(setq verilog-indent-ignore-regexp      "// \\*") ; Ignore outshine headings
;; Verilog AUTO
(setq verilog-auto-delete-trailing-whitespace t) ; ‘delete-trailing-whitespace’ in ‘verilog-auto’.
(setq verilog-auto-indent-on-newline          t) ; Self-explaining
(setq verilog-auto-lineup                   nil) ; other options are 'declarations or 'all
(setq verilog-auto-newline                  nil)
(setq verilog-auto-endcomments              nil)
(setq verilog-auto-wire-comment             nil)
(setq verilog-minimum-comment-distance        1) ; (default 10) Only applies to AUTOs, called in `verilog-set-auto-endcomments'
;; Alignment
(setq verilog-align-assign-expr t)
(setq verilog-align-typedef-regexp (concat "\\<" verilog-identifier-re "_\\(t\\|if\\|vif\\)\\>"))


(provide 'verilog-ext-test-setup-package)

;;; verilog-ext-test-setup-package.el ends here
