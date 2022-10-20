;;; verilog-completion.el --- Verilog Completion   -*- lexical-binding: t -*-

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
;; Verilog extension for `company' and placeholder for `completion-at-point' improvements.
;;
;;; Code:

(require 'verilog-mode)
(require 'company-keywords)


;;;; Company keywords for Verilog
(add-to-list 'company-keywords-alist (append '(verilog-mode) verilog-keywords))



(provide 'verilog-completion)

;;; verilog-completion.el ends here

