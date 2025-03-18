;;; verilog-ext-test-indent.el --- Verilog-Ext ERT indent tests  -*- lexical-binding: t -*-

;; Copyright (C) 2022-2025 Gonzalo Larumbe

;; Author: Gonzalo Larumbe <gonzalomlarumbe@gmail.com>
;; URL: https://github.com/gmlarumbe/test-hdl

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
;; Verilog-Ext ERT indent tests
;;
;;; Code:

(defconst verilog-ext-test-indent-file-list (append verilog-ext-test-common-file-list
                                                    (test-hdl-directory-files (file-name-concat verilog-ext-test-files-dir "veripool")
                                                                              verilog-ext-file-extension-re)))

(defconst verilog-ext-test-ref-dir-indent (file-name-concat verilog-ext-test-ref-dir "indent"))
(defconst verilog-ext-test-dump-dir-indent (file-name-concat verilog-ext-test-dump-dir "indent"))


(defun verilog-ext-test-indent-fn ()
  (verilog-ext-indent-region (point-min) (point-max)))


(defun verilog-ext-test-indent-gen-expected-files ()
  (test-hdl-gen-expected-files :file-list verilog-ext-test-indent-file-list
                               :dest-dir verilog-ext-test-ref-dir-indent
                               :fn #'test-hdl-indent-buffer
                               :args '(verilog-mode verilog-ext-test-indent-fn)))

(ert-deftest indent ()
  (dolist (file verilog-ext-test-indent-file-list)
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-indent (test-hdl-basename file))
                                                         :fn #'test-hdl-indent-buffer
                                                         :args '(verilog-mode verilog-ext-test-indent-fn))
                                  (file-name-concat verilog-ext-test-ref-dir-indent (test-hdl-basename file))))))


(provide 'verilog-ext-test-indent)

;;; verilog-ext-test-indent.el ends here
