;;; verilog-ext-tests-tree-sitter.el --- Verilog-Ext ERT tree-sitter tests  -*- lexical-binding: t -*-

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
;; ERT Tree-sitter tests:
;;
;;; Code:


(require 'verilog-ext-tests-font-lock)

(ert-deftest tree-sitter::font-lock ()
  (should (verilog-ext-test-font-lock-test-file "axi_demux.sv" :tree-sitter))
  (should (verilog-ext-test-font-lock-test-file "axi_test.sv" :tree-sitter))
  (should (verilog-ext-test-font-lock-test-file "instances.sv" :tree-sitter))
  (should (verilog-ext-test-font-lock-test-file "tb_program.sv" :tree-sitter))
  (should (verilog-ext-test-font-lock-test-file "ucontroller.sv" :tree-sitter))
  (should (verilog-ext-test-font-lock-test-file "uvm_component.svh" :tree-sitter)))


(provide 'verilog-ext-tests-tree-sitter)

;;; verilog-ext-tests-tree-sitter.el ends here

