;;; verilog-ext-tests-font-lock.el --- Verilog-Ext ERT font-lock tests  -*- lexical-binding: t -*-

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
;; ERT font-lock tests:
;; - https://github.com/Lindydancer/faceup
;;
;;; Code:


(require 'faceup)

(defun verilog-ext-test-font-lock-update-dir (&optional tree-sitter)
  "Update .faceup files.
INFO: Makes sure that additional settings that might change specific font-lock
are disabled for the .faceup generation.
E.g: disables `fic-mode', `untabify-trailing-ws', 'outshine-mode' and the value
of `verilog-align-typedef-regexp'.
At some point tried with `with-temp-buffer' without success."
  (let ((verilog-align-typedef-regexp nil))
    (save-window-excursion
      (when (fboundp 'untabify-trailing-ws-mode)
        (untabify-trailing-ws-mode -1)
        (message "Disabling untabify-trailing-ws-mode..."))
      (dolist (file (directory-files verilog-ext-tests-examples-dir t ".s?vh?$"))
        (find-file file)
        (if tree-sitter
            (verilog-ts-mode)
          (verilog-mode))
        (when (fboundp 'fic-mode)
          (fic-mode -1)
          (message "Disabling fic-mode for file %s" file))
        (when (fboundp 'outshine-mode)
          (outshine-mode -1)
          (message "Disabling outshine-mode for file %s" file))
        (message "Processing %s" file)
        (faceup-write-file (concat (file-name-directory file)
                                   "faceup/"
                                   (file-name-nondirectory file)
                                   (when tree-sitter
                                     ".ts")
                                   ".faceup"))))))

(defun verilog-ext-test-font-lock-test-file (file &optional tree-sitter)
  "Test that Verilog FILE fontifies as the .faceup file describes."
  (let ((verilog-align-typedef-regexp nil)
        (mode (if tree-sitter
                  'verilog-ts-mode
                'verilog-mode)))
    (faceup-test-font-lock-file mode
                                (verilog-ext-path-join verilog-ext-tests-examples-dir file)
                                (verilog-ext-path-join verilog-ext-tests-faceup-dir (concat file
                                                                                            (when tree-sitter
                                                                                              ".ts")
                                                                                            ".faceup")))))

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
