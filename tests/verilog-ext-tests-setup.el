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
(message "Overwriting verilog-mode with latest version")
(use-package verilog-mode
  :straight (:repo "veripool/verilog-mode"))


;;;; Install package
(message "Installing and setting up verilog-ext")
(use-package verilog-ext
  :straight (:host github :repo "gmlarumbe/verilog-ext"))


;;;; Test environment
(message "Setting up test environment")
(setq print-level nil)
(setq print-length nil)
(setq eval-expression-print-level nil)
(setq eval-expression-print-length nil)


(provide 'verilog-ext-tests-setup)

;;; verilog-ext-tests-setup.el ends here
