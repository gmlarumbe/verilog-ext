;;; verilog-ext-tests-beautify.el --- Verilog-Ext ERT beautify tests  -*- lexical-binding: t -*-

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
;; ERT Beautify Tests
;;
;;; Code:


(defvar verilog-ext-tests-beautify-test-files
  '("axi_demux.sv"
    "instances.sv"
    "ucontroller.sv"))
(defvar verilog-ext-tests-beautify-dump-dir (verilog-ext-path-join verilog-ext-tests-beautify-dir "dump"))
(defvar verilog-ext-tests-beautify-dump-diff-on-error t)


(defun verilog-ext-tests-beautify-ref-file-from-orig (file)
  (concat (file-name-nondirectory (file-name-sans-extension file)) ".beauty.sv"))

(defun verilog-ext-test-beautify-gen-expected-files ()
  (let ((orig-dir verilog-ext-tests-common-dir)
        (dest-dir verilog-ext-tests-beautify-dir)
        (files verilog-ext-tests-beautify-test-files)  ; Only files with instances are relevant
        (verilog-ext-time-stamp-pattern nil))          ; Prevent auto-update of timestamp
    (dolist (file files)
      (copy-file (verilog-ext-path-join orig-dir file)
                 (verilog-ext-path-join dest-dir (verilog-ext-tests-beautify-ref-file-from-orig file)) t))
    (verilog-ext-beautify-dir-files dest-dir)))

(defun verilog-ext-test-beautify-file (file)
  (let ((debug nil)
        (dump-file (verilog-ext-path-join verilog-ext-tests-beautify-dump-dir file)))
    (cl-letf (((symbol-function 'message)
               (lambda (FORMAT-STRING &rest ARGS)
                 nil))) ; Mock `message' to silence all the indentation reporting
      (with-temp-file dump-file
        (when debug
          (clone-indirect-buffer-other-window "*debug*" t))
        (insert-file-contents (verilog-ext-path-join verilog-ext-tests-common-dir file))
        ;; Remove alignments between port connections
        (verilog-ext-replace-regexp-whole-buffer (concat "\\(?1:^\\s-*\\." verilog-identifier-re "\\)\\(?2:\\s-*\\)(") "\\1(")
        ;; Beautify
        (verilog-mode)
        (verilog-ext-beautify-current-buffer)
        dump-file))))

(defun verilog-ext-test-beautify-compare (file)
  "Compare beautified FILE.
Reference beautified version: file.beauty.sv in beautify dir."
  (let ((filename-beautified (verilog-ext-test-beautify-file file)) ; Dump file
        (filename-ref (verilog-ext-path-join verilog-ext-tests-beautify-dir (verilog-ext-tests-beautify-ref-file-from-orig file))))
    (if (equal (with-temp-buffer
                 (insert-file-contents filename-beautified)
                 (buffer-substring-no-properties (point-min) (point-max)))
               (with-temp-buffer
                 (insert-file-contents filename-ref)
                 (buffer-substring-no-properties (point-min) (point-max))))
        (progn
          (delete-file filename-beautified)
          t)
      ;; Dump on error if enabled
      (when verilog-ext-tests-beautify-dump-diff-on-error
        (shell-command (concat
                        "diff " filename-ref " " filename-beautified " > " (concat (file-name-sans-extension filename-beautified)) ".diff")))
      nil)))

(ert-deftest beautify::module-at-point ()
  (let ((test-files verilog-ext-tests-beautify-test-files))
    (delete-directory verilog-ext-tests-beautify-dump-dir :recursive)
    (make-directory verilog-ext-tests-beautify-dump-dir :parents)
    (dolist (file test-files)
      (should (verilog-ext-test-beautify-compare file)))))



(provide 'verilog-ext-tests-beautify)

;;; verilog-ext-tests-beautify.el ends here
