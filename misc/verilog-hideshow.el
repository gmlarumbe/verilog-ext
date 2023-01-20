;;; verilog-hideshow.el --- Verilog Hideshow  -*- lexical-binding: t -*-

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
;; Support and setup for `hideshow'.
;;
;;; Code:


(require 'hideshow)
(require 'verilog-mode)


(defconst verilog-ext-hs-block-start-keywords-re
  (eval-when-compile
    (verilog-regexp-words
     '("begin"
       "fork"
       "clocking"
       "function"
       "covergroup"
       "property"
       "task"
       "generate"))))

(defconst verilog-ext-hs-block-end-keywords-re
  (eval-when-compile
    (verilog-regexp-words
     '("end"
       "join" "join_any" "join_none"
       "endclocking"
       "endfunction"
       "endgroup"
       "endproperty"
       "endtask"
       "endgenerate"))))

;; Config
(add-to-list 'hs-special-modes-alist `(verilog-mode ,verilog-ext-hs-block-start-keywords-re
                                                    ,verilog-ext-hs-block-end-keywords-re
                                                    nil
                                                    verilog-forward-sexp-function))



(provide 'verilog-hideshow)

;;; verilog-hideshow.el ends here
