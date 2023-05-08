;;; verilog-ext-hs.el --- Verilog-ext Hideshow  -*- lexical-binding: t -*-

;; Copyright (C) 2022-2023 Gonzalo Larumbe

;; Author: Gonzalo Larumbe <gonzalomlarumbe@gmail.com>
;; URL: https://github.com/gmlarumbe/verilog-ext
;; Version: 0.1.0
;; Package-Requires: ((emacs "28.1") (verilog-mode "2022.12.18.181110314"))

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

;; Basic hideshow configuration

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
  "Configure hideshow."
  (dolist (mode '((verilog-mode    . verilog-forward-sexp-function)
                  (verilog-ts-mode . verilog-forward-sexp-function))) ; TODO: Eventually replace with `verilog-ts-mode' forward-sexp function
    (add-to-list 'hs-special-modes-alist `(,(car mode)
                                           ,verilog-ext-hs-block-start-keywords-re
                                           ,verilog-ext-hs-block-end-keywords-re
                                           nil
                                           ,(cdr mode)))))

(defun verilog-ext-hs-toggle-hiding (&optional e)
  "Wrapper for `hs-toggle-hiding' with proper syntax table.
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
