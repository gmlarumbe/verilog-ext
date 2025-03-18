;;; verilog-ext-test-setup-straight.el --- verilog-ext ERT Tests Setup with straight.el -*- lexical-binding: t -*-

;; Copyright (C) 2022-2025 Gonzalo Larumbe

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
;; verilog-ext ERT Tests Setup with straight.el
;;
;;; Code:


(require 'test-hdl-setup-straight)


;;;; Setup built-in dependencies
(use-package align
  :straight nil
  :config
  (setq align-default-spacing 1)
  (setq align-to-tab-stop nil))

;; Overwrite with latest version instead of the one pointed by Package-Requires:
(use-package verilog-mode
  :straight (:repo "veripool/verilog-mode")
  :config
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
  (setq verilog-align-typedef-regexp (concat "\\<" verilog-identifier-re "_\\(t\\|if\\|vif\\)\\>")))


;;;; Install/setup package
(message "Installing and setting up verilog-ext")
;; Always needed since straight.el does not download dependencies of local packages
(use-package verilog-ext
  :hook ((verilog-mode . verilog-ext-mode))
  :config
  (setq verilog-ext-feature-list (remove 'typedefs verilog-ext-feature-list)) ; Do not override `verilog-align-typedef-regexp'
  (setq verilog-ext-feature-list (remove 'lsp-bridge verilog-ext-feature-list)) ; Do not autosetup since `lsp-bridge' is not available on MELPA
  (setq verilog-ext-feature-list (remove 'lspce verilog-ext-feature-list)) ; Do not autosetup since `lsp-bridge' is not available on MELPA
  (setq verilog-ext-cache-enable nil)
  (verilog-ext-mode-setup))

;; Shadow/override with actions/checkout repo, instead of the one downloaded by straight.el
(test-hdl-when-github-action
  (use-package verilog-ext
   :straight nil))

(provide 'verilog-ext-test-setup-straight)

;;; verilog-ext-test-setup-straight.el ends here
