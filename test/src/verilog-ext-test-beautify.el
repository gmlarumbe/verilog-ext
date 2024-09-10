;;; verilog-ext-test-beautify.el --- Verilog-Ext ERT beautify tests  -*- lexical-binding: t -*-

;; Copyright (C) 2022-2024 Gonzalo Larumbe

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
;; Verilog-Ext ERT beautify tests
;;
;;; Code:

(defconst verilog-ext-test-beautify-file-list (mapcar (lambda (file)
                                                        (file-name-concat verilog-ext-test-files-common-dir file))
                                                      '("axi_demux.sv" "instances.sv" "ucontroller.sv")))

(defconst verilog-ext-test-ref-dir-beautify (file-name-concat verilog-ext-test-ref-dir "beautify"))
(defconst verilog-ext-test-dump-dir-beautify (file-name-concat verilog-ext-test-dump-dir "beautify"))


(defun verilog-ext-test-beautify-file (mode)
  ;; Set mode or ts-mode
  (funcall mode)
  (let* ((identifier-re verilog-identifier-re)
         (beautify-re (concat "\\(?1:^\\s-*\\." identifier-re "\\)\\(?2:\\s-*\\)("))
         (verilog-ext-time-stamp-pattern nil)) ; Prevent auto-update of timestamp for `verilog-ext'
    ;; Clean blanks in ports (similar to `verilog-ext-replace-regexp-whole-buffer')
    (save-excursion
      (goto-char (point-min))
      (while (re-search-forward beautify-re nil t)
        (replace-match "\\1(")))
    ;; Run beautify function
    (test-hdl-no-messages
      (verilog-ext-beautify-current-buffer))))


(defun verilog-ext-test-beautify-gen-expected-files ()
  (test-hdl-gen-expected-files :file-list verilog-ext-test-beautify-file-list
                               :dest-dir verilog-ext-test-ref-dir-beautify
                               :fn #'verilog-ext-test-beautify-file
                               :args '(verilog-mode))
  (test-hdl-gen-expected-files :file-list verilog-ext-test-beautify-file-list
                               :dest-dir verilog-ext-test-ref-dir-beautify
                               :out-file-ext "ts.sv"
                               :fn #'verilog-ext-test-beautify-file
                               :args '(verilog-ts-mode)))

(ert-deftest beautify ()
  (dolist (file verilog-ext-test-beautify-file-list)
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-beautify (test-hdl-basename file))
                                                         :fn #'verilog-ext-test-beautify-file
                                                         :args '(verilog-mode))
                                  (file-name-concat verilog-ext-test-ref-dir-beautify (test-hdl-basename file))))))

(ert-deftest beautify-ts-mode ()
  (dolist (file verilog-ext-test-beautify-file-list)
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-beautify (test-hdl-basename file "ts.sv"))
                                                         :fn #'verilog-ext-test-beautify-file
                                                         :args '(verilog-ts-mode))
                                  (file-name-concat verilog-ext-test-ref-dir-beautify (test-hdl-basename file "ts.sv"))))))


(provide 'verilog-ext-test-beautify)

;;; verilog-ext-test-beautify.el ends here
