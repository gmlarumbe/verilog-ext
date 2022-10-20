;;; verilog-which-func.el --- Verilog which func  -*- lexical-binding: t -*-

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
;; Support and setup for `which-func'.
;;
;;; Code:


(require 'which-func)
(require 'verilog-navigation)


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
    (cond ((setq data (verilog-ext-instance-at-point))
           (setq verilog-ext-which-func-extra (cdr data))
           (car data))
          ((setq data (verilog-ext-block-at-point))
           (setq verilog-ext-which-func-extra (cdr data))
           (verilog-ext-which-func-shorten-block (car data)))
          (t
           (setq verilog-ext-which-func-extra nil)
           ""))))

(defun verilog-ext-which-func ()
  "Hook for `verilog-mode' to enable `which-func'."
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
                "]")))

;;;###autoload
(define-minor-mode verilog-ext-which-func-mode
  "Enhanced extensions for `which-func' in Verilog."
  :lighter ""
  (if verilog-ext-which-func-mode
      (progn
        (add-hook 'verilog-mode-hook #'verilog-ext-which-func)
        (message "Enabled verilog-ext-which-func-mode"))
    (remove-hook 'verilog-mode-hook #'verilog-ext-which-func)
    (message "Disabled verilog-ext-which-func-mode")))



(provide 'verilog-which-func)

;;; verilog-which-func.el ends here
