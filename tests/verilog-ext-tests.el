;;; verilog-ext-tests.el --- Verilog-Ext ERT tests  -*- lexical-binding: t -*-

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
;; ERT Tests
;;
;;; Code:


;;;; Performance utils
(defun verilog-ext-profile-file (file)
  "Use Emacs profiler in FILE."
  (profiler-start 'cpu+mem)
  (find-file file)
  (profiler-stop)
  (profiler-report))

(defun verilog-ext-profile-imenu ()
  "Use Emacs profiler on `verilog-ext-imenu-list'."
  (profiler-start 'cpu+mem)
  (verilog-ext-imenu-list)
  (profiler-stop)
  (profiler-report))


;;;; Tests
(require 'verilog-ext-tests-imenu)



(provide 'verilog-ext-tests)

;;; verilog-ext-tests.el ends here
