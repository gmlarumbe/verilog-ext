;;; verilog-ext-which-func.el --- Verilog-ext Which Func  -*- lexical-binding: t -*-

;; Copyright (C) 2022-2024 Gonzalo Larumbe

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

;; `which-func' integration.

;;; Code:

(require 'which-func)
(require 'verilog-ext-nav)

(defvar-local verilog-ext-which-func-extra nil
  "Variable to hold extra information for `which-func'.")

(defun verilog-ext-which-func-shorten-block (block-type)
  "Return shortened name of BLOCK-TYPE, if possible."
  (cond ((string= "function"  block-type) "func")
        ((string= "task"      block-type) "task")
        ((string= "class"     block-type) "cls")
        ((string= "module"    block-type) "mod")
        ((string= "interface" block-type) "itf")
        ((string= "package"   block-type) "pkg")
        ((string= "program"   block-type) "pgm")
        ((string= "generate"  block-type) "gen")
        (t block-type)))

(defun verilog-ext-which-func-function ()
  "Retrieve `which-func' candidates."
  (let (data)
    (cond ((and verilog-ext-file-allows-instances
                (setq data (verilog-ext-instance-at-point)))
           (setq verilog-ext-which-func-extra (cadr data))
           (car data))
          ((setq data (verilog-ext-block-at-point))
           (setq verilog-ext-which-func-extra (alist-get 'name data))
           (verilog-ext-which-func-shorten-block (alist-get 'type data)))
          (t
           (setq verilog-ext-which-func-extra nil)
           ""))))

(defun verilog-ext-which-func ()
  "Hook for `verilog-mode' to enable `which-func'."
  (when (eq major-mode 'verilog-mode)
    (setq-local which-func-functions '(verilog-ext-which-func-function))
    (setq-local which-func-format
                `("["
                  (:propertize which-func-current
                   face (which-func :weight bold)
                   mouse-face mode-line-highlight)
                  ":"
                  (:propertize verilog-ext-which-func-extra
                   face which-func
                   mouse-face mode-line-highlight)
                  "]"))))


(provide 'verilog-ext-which-func)

;;; verilog-ext-which-func.el ends here
