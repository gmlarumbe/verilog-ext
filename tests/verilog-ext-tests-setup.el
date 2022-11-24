;;; verilog-ext-tests-setup.el --- Verilog Tests Setup  -*- lexical-binding: t -*-

;; Copyright (C) 2022 Gonzalo Larumbe

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


;;;; Straight bootstrap
(message "Bootstraping straight")

(defvar bootstrap-version)
(let ((bootstrap-file
       (expand-file-name "straight/repos/straight.el/bootstrap.el" user-emacs-directory))
      (bootstrap-version 5))
  (unless (file-exists-p bootstrap-file)
    (with-current-buffer
        (url-retrieve-synchronously
         "https://raw.githubusercontent.com/raxod502/straight.el/develop/install.el"
         'silent 'inhibit-cookies)
      (goto-char (point-max))
      (eval-print-last-sexp)))
  (load bootstrap-file nil 'nomessage))

(message "Bootstraped straight")


;;;; Integration of use-package
(message "Installing use-package")
(straight-use-package 'use-package)
(setq straight-use-package-by-default t)


;;;; Install dependencies
(message "Installing projectile")
(use-package projectile)
(message "Installing ggtags")
(use-package ggtags)
(message "Installing ag")
(use-package ag)
(message "Installing ripgrep")
(use-package ripgrep)
(message "Installing company")
(use-package company)
(message "Installing yasnippet")
(use-package yasnippet)
(message "Installing hydra")
(use-package hydra)
(message "Installing outshine")
(use-package outshine)
(message "Installing flycheck")
(use-package flycheck)
(message "Installing faceup for font-lock ERT regressions")
(use-package faceup)
(message "Setting up align")
(use-package align
  :straight nil
  :config
  (setq align-default-spacing 1)
  (setq align-to-tab-stop nil))
(message "Overwriting verilog-mode with latest version")
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
  (setq verilog-align-assign-expr t))


;;;; Install package
(message "Installing and setting up verilog-ext")
(use-package verilog-ext
  :straight (:host github :repo "gmlarumbe/verilog-ext"))



(provide 'verilog-ext-tests-setup)

;;; verilog-ext-tests-setup.el ends here
