;;; verilog-ext-test-faceup.el --- Verilog-Ext ERT faceup tests  -*- lexical-binding: t -*-

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

;; Verilog-Ext ERT faceup tests

;;; Code:

(defconst verilog-ext-test-faceup-file-list verilog-ext-test-common-file-list)

(defconst verilog-ext-test-ref-dir-faceup (file-name-concat verilog-ext-test-ref-dir "faceup"))
(defconst verilog-ext-test-dump-dir-faceup (file-name-concat verilog-ext-test-dump-dir "faceup"))


(defun verilog-ext-test-faceup-file ()
  (verilog-mode)
  (let ((verilog-ext-time-stamp-pattern nil) ; Prevent auto-update of timestamp
        (verilog-align-typedef-regexp nil))
    (test-hdl-no-messages
      (test-hdl-faceup-test-file 'verilog-mode))))


(defun verilog-ext-test-faceup-gen-expected-files ()
  (test-hdl-gen-expected-files :file-list verilog-ext-test-faceup-file-list
                               :dest-dir verilog-ext-test-ref-dir-faceup
                               :out-file-ext "faceup"
                               :fn #'verilog-ext-test-faceup-file))


(ert-deftest faceup ()
  (dolist (file verilog-ext-test-faceup-file-list)
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-faceup (test-hdl-basename file "faceup"))
                                                         :fn #'verilog-ext-test-faceup-file)
                                  (file-name-concat verilog-ext-test-ref-dir-faceup (test-hdl-basename file "faceup"))))))


(provide 'verilog-ext-test-faceup)


;;; verilog-ext-test-faceup.el ends here
