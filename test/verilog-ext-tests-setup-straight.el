;;; verilog-ext-tests-setup-straight.el --- Verilog Tests Setup with straight.el  -*- lexical-binding: t -*-

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


;;;; Setup built-in dependencies
(use-package align
  :straight nil
  :config
  (setq align-default-spacing 1)
  (setq align-to-tab-stop nil))

;; Overwrite with latest version instead of the one pointed by Package-Requires:
(use-package verilog-mode
  :straight (:repo "veripool/verilog-mode")
  ;; :straight nil ; TODO: Uncomment/replace when gnu archive has a newer version where tests pass
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


;;;; Setup package
(message "Installing and setting up verilog-ext")
(use-package verilog-ext
  :after verilog-mode
  :hook ((verilog-mode . verilog-ext-mode))
  :demand
  :config
  (setq verilog-ext-feature-list (remove 'typedefs verilog-ext-feature-list)) ; Do not override `verilog-align-typedef-regexp'
  (verilog-ext-mode-setup)
  (add-hook 'verilog-ts-mode-hook #'(lambda () ; Applies also to verilog-ts-mode since it's derived
                                      (setq treesit-font-lock-level 4))))


(use-package verilog-ts-mode
  :straight (:host github :repo "gmlarumbe/verilog-ext"
             :files ("ts-mode/verilog-ts-mode.el")))


(provide 'verilog-ext-tests-setup-straight)

;;; verilog-ext-tests-setup-straight.el ends here
