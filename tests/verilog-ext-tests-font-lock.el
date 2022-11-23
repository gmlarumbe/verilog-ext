;;; verilog-ext-tests-font-lock.el --- Verilog-Ext ERT font-lock tests  -*- lexical-binding: t -*-

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
;; ERT font-lock tests:
;; - https://github.com/Lindydancer/faceup
;;
;;; Code:


(require 'faceup)

(defun verilog-ext-test-font-lock-test-file (file)
  "Test that Verilog FILE fontifies as the .faceup file describes."
  (faceup-test-font-lock-file 'verilog-mode
                              (verilog-ext-path-join verilog-ext-tests-examples-dir file)
                              (verilog-ext-path-join verilog-ext-tests-faceup-dir (concat file ".faceup"))))

(faceup-defexplainer verilog-ext-test-font-lock-test-file)


(ert-deftest font-lock::generic ()
  (should (verilog-ext-test-font-lock-test-file "axi_demux.sv"))
  (should (verilog-ext-test-font-lock-test-file "axi_test.sv"))
  (should (verilog-ext-test-font-lock-test-file "instances.sv"))
  (should (verilog-ext-test-font-lock-test-file "tb_program.sv"))
  (should (verilog-ext-test-font-lock-test-file "ucontroller.sv"))
  (should (verilog-ext-test-font-lock-test-file "uvm_component.svh")))

(provide 'verilog-ext-tests-font-lock)

;;; verilog-ext-tests-font-lock.el ends here
