;;; verilog-ext-hs.el --- Verilog-ext Hideshow  -*- lexical-binding: t -*-

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

;; `hideshow' configuration for code folding.

;;; Code:

(require 'verilog-mode)
(require 'hideshow)

(defconst verilog-ext-hs-block-start-keywords-re
  (eval-when-compile
    (concat "\\("
            "\\(" (regexp-opt '("(" "{" "[")) "\\)"
            "\\|"
            "\\(" (verilog-regexp-words
                 '("begin"
                   "fork"
                   "clocking"
                   "function"
                   "covergroup"
                   "property"
                   "task"
                   "generate"
                   "`ifdef" "`ifndef"))
            "\\)" "\\)")))

(defconst verilog-ext-hs-block-end-keywords-re
  (eval-when-compile
    (concat "\\("
            "\\(" (regexp-opt '(")" "}" "]")) "\\)"
            "\\|"
            "\\(" (verilog-regexp-words
                 '("end"
                   "join" "join_any" "join_none"
                   "endclocking"
                   "endfunction"
                   "endgroup"
                   "endproperty"
                   "endtask"
                   "endgenerate"
                   "`endif"))
            "\\)" "\\)")))

(defun verilog-ext-hs-setup ()
  "Configure `hideshow'."
  (dolist (mode '((verilog-mode    . verilog-forward-sexp-function)
                  (verilog-ts-mode . verilog-ts-forward-sexp)))
    (add-to-list 'hs-special-modes-alist `(,(car mode)
                                           ,verilog-ext-hs-block-start-keywords-re
                                           ,verilog-ext-hs-block-end-keywords-re
                                           nil
                                           ,(cdr mode))))
  (dolist (hook '(verilog-mode-hook verilog-ts-mode-hook))
    (add-hook hook #'hs-minor-mode))
  ;; Workaround to enable `hideshow' on first file visit with lazy loading using
  ;; :config section with `use-package'
  (when (member major-mode '(verilog-mode verilog-ts-mode))
    (hs-minor-mode 1)))

(defun verilog-ext-hs-toggle-hiding (&optional e)
  "Wrapper for `hs-toggle-hiding' depending on current Verilog `major-mode'.

For `verilog-mode' use a modified syntax table.  For `verilog-ts-mode' use
existing one.

Toggle hiding/showing of a block.
See `hs-hide-block' and `hs-show-block'.
Argument E should be the event that triggered this action."
  (interactive (list last-nonmenu-event))
  (cond ((eq major-mode 'verilog-mode)
         (let ((table (make-syntax-table verilog-mode-syntax-table)))
           (modify-syntax-entry ?` "w" table)
           (with-syntax-table table
             (hs-toggle-hiding e))))
        ((eq major-mode 'verilog-ts-mode)
         (hs-toggle-hiding e))
        (t
         (error "Wrong major-mode to run `verilog-ext-hideshow-toggle'"))))


(provide 'verilog-ext-hs)

;;; verilog-ext-hs.el ends here
