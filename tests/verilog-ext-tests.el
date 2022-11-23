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
(require 'profiler)

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
(unless (featurep 'verilog-ext)
  (error "verilog-ext has not been loaded. Cannot run tests!"))
(require 'verilog-ext)

(defvar verilog-ext-tests-root-dir (file-name-directory (locate-library "verilog-ext")))
(defvar verilog-ext-tests-test-dir (if (string-prefix-p (expand-file-name straight-base-dir) verilog-ext-tests-root-dir)
                                       (verilog-ext-path-join (expand-file-name straight-base-dir) "straight/repos/verilog-ext/tests")
                                     (verilog-ext-path-join verilog-ext-tests-root-dir "tests")))
(defvar verilog-ext-tests-examples-dir (verilog-ext-path-join verilog-ext-tests-test-dir "examples"))


(require 'verilog-ext-tests-imenu)
(require 'verilog-ext-tests-navigation)
;; (require 'verilog-ext-tests-utils)
;; (require 'verilog-ext-tests-font-lock)
;; (require 'verilog-ext-tests-beautify)
;; (require 'verilog-ext-tests-vhier)



(provide 'verilog-ext-tests)

;;; verilog-ext-tests.el ends here
