;;; verilog-ext-tests-workspace.el --- Verilog-Ext ERT Workspace tests  -*- lexical-binding: t -*-

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
;; ERT Workspace Tests
;;
;;; Code:


(defun verilog-ext-test-workspace-get-expected-files ()
  (let* ((verilog-ext-workspace-root-dir verilog-ext-tests-test-dir)
         (verilog-ext-workspace-ignore-dirs `(,(file-name-concat verilog-ext-workspace-root-dir "files/indent")
                                              ,(file-name-concat verilog-ext-workspace-root-dir "files/verilog-mode")
                                              ,(file-name-concat verilog-ext-workspace-root-dir "files/bugs")))
         (verilog-ext-workspace-ignore-files `(,(file-name-concat verilog-ext-workspace-root-dir "files/beautify/axi_demux.beauty.sv")
                                               ,(file-name-concat verilog-ext-workspace-root-dir "files/beautify/instances.beauty.sv")
                                               ,(file-name-concat verilog-ext-workspace-root-dir "files/beautify/ucontroller.beauty.sv"))))
    (mapcar (lambda (file) (string-remove-prefix (file-name-as-directory verilog-ext-workspace-root-dir) file))
            (verilog-ext-workspace-files))))

(ert-deftest workspace::files ()
  (let* ((verilog-ext-workspace-root-dir verilog-ext-tests-test-dir)
         (verilog-ext-workspace-ignore-dirs `(,(file-name-concat verilog-ext-workspace-root-dir "files/indent")
                                              ,(file-name-concat verilog-ext-workspace-root-dir "files/verilog-mode")
                                              ,(file-name-concat verilog-ext-workspace-root-dir "files/bugs")))
         (verilog-ext-workspace-ignore-files `(,(file-name-concat verilog-ext-workspace-root-dir "files/beautify/axi_demux.beauty.sv")
                                               ,(file-name-concat verilog-ext-workspace-root-dir "files/beautify/instances.beauty.sv")
                                               ,(file-name-concat verilog-ext-workspace-root-dir "files/beautify/ucontroller.beauty.sv"))))
    (should (equal (mapcar (lambda (file) (string-remove-prefix (file-name-as-directory verilog-ext-workspace-root-dir) file))
                           (verilog-ext-workspace-files))
                   '("files/common/axi_demux.sv"
                     "files/common/axi_test.sv"
                     "files/common/instances.sv"
                     "files/common/tb_program.sv"
                     "files/common/ucontroller.sv"
                     "files/common/uvm_component.svh"
                     "files/jump-parent/block0.sv"
                     "files/jump-parent/block1.sv"
                     "files/jump-parent/block2.sv"
                     "files/jump-parent/block3.sv"
                     "files/jump-parent/block_gen.sv"
                     "files/jump-parent/block_ws_0.sv"
                     "files/jump-parent/block_ws_1.sv"
                     "files/jump-parent/test_if.sv"
                     "files/jump-parent/test_if_params.sv"
                     "files/jump-parent/test_if_params_array.sv"
                     "files/jump-parent/test_if_params_empty.sv")))))

(provide 'verilog-ext-tests-workspace)

;;; verilog-ext-tests-workspace.el ends here
