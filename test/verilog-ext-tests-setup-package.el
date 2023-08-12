;;; verilog-ext-tests-setup-package.el --- Verilog Tests Setup with package.el  -*- lexical-binding: t -*-

;; Copyright (C) 2022-2023 Gonzalo Larumbe

;; Author: Gonzalo Larumbe <gonzalomlarumbe@gmail.com>
;; URL: https://github.com/gmlarumbe/verilog-ext

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
;; Setup Emacs environment to run verilog-ext ERT regression
;;
;;; Code:

;;;; Setup package.el
(require 'package)
(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/") t)
;; Comment/uncomment this line to enable MELPA Stable if desired.  See `package-archive-priorities`
;; and `package-pinned-packages`. Most users will not need or want to do this.
(add-to-list 'package-archives '("melpa-stable" . "https://stable.melpa.org/packages/") t)
(package-initialize)

;;;; Setup built-in dependencies
(require 'align)
(setq align-default-spacing 1)
(setq align-to-tab-stop nil)

;;;; Install/setup package
(message "Installing and setting up verilog-ext")
(package-install 'verilog-ext)

;;;; Setup `verilog-mode' and `verilog-ext'
(require 'verilog-mode)
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

(require 'verilog-ext)
(setq verilog-ext-feature-list (remove 'typedefs verilog-ext-feature-list)) ; Do not override `verilog-align-typedef-regexp'
(verilog-ext-mode-setup)
(add-hook 'verilog-mode-hook #'verilog-ext-mode)


;;;; Tree-sitter
(defvar verilog-ext-tests-tree-sitter-available-p nil)

(message "Emacs version: %s" emacs-version)
(when (and (>= emacs-major-version 29)
           (treesit-available-p)
           (treesit-language-available-p 'verilog))
  (require 'treesit)
  (setq verilog-ext-tests-tree-sitter-available-p t)
  (message "verilog-ext-tests-tree-sitter-available-p: %s" verilog-ext-tests-tree-sitter-available-p))

;; TODO: Uncomment when integrated into MELPA
;; (when verilog-ext-tests-tree-sitter-available-p
;;   (package-install 'verilog-ts-mode)
;;   (add-hook 'verilog-ts-mode-hook #'(lambda () (setq treesit-font-lock-level 4))))


(provide 'verilog-ext-tests-setup-package)

;;; verilog-ext-tests-setup-package.el ends here
