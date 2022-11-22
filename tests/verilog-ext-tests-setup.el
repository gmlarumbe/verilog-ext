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
;; Setup Emacs environment to run verilog-ext ERT testsuite
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

(message "Installing use-package")
(straight-use-package 'use-package)
(setq straight-use-package-by-default t)


(use-package projectile)
(use-package ggtags)
(use-package ag)
(use-package ripgrep)
(use-package company)
(use-package yasnippet)
(use-package hydra)
(use-package outshine)
(use-package flycheck)
(use-package verilog-mode
  :straight (:repo "veripool/verilog-mode"))
(use-package verilog-ext
  :straight (:host github :repo "gmlarumbe/verilog-ext"))


(setq print-level nil)
(setq print-length nil)
(setq eval-expression-print-level nil)
(setq eval-expression-print-length nil)

(provide 'verilog-ext-tests-setup)

;;; verilog-ext-tests-setup.el ends here
