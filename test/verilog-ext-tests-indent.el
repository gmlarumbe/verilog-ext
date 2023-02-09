;;; verilog-ext-tests-indent.el --- Verilog-Ext ERT Indent tests  -*- lexical-binding: t -*-

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
;; ERT indent tests:
;;
;;; Code:


(defvar verilog-ext-tests-indent-test-files (directory-files verilog-ext-tests-common-dir t ".s?vh?$"))
(defvar verilog-ext-tests-indent-dump-dir (verilog-ext-path-join verilog-ext-tests-indent-dir "dump"))
(defvar verilog-ext-tests-indent-dump-diff-on-error t)


(defun verilog-ext-tests-indent-ref-file-from-orig (file &optional tree-sitter)
  (concat (file-name-nondirectory (file-name-sans-extension file))
          (when tree-sitter
            ".ts")
          ".indent.sv"))

(defun verilog-ext-test-indent-buffer (&optional tree-sitter)
  "Perform indentation of current buffer for indentation tests."
  (let ((debug nil))
    (when debug
      (clone-indirect-buffer-other-window "*debug*" t))
    ;; De-indent original file
    (goto-char (point-min))
    (while (< (point) (point-max))
      (delete-horizontal-space)
      (forward-line 1))
    ;; Re-indent buffer
    (if tree-sitter
        (progn
          (verilog-ts-mode)
          (indent-region (point-min) (point-max)))
      ;; Else, verilog-mode and syntax-table overriding
      (verilog-mode)
      (verilog-ext-indent-region (point-min) (point-max)))
    ;; Untabify and clean whitespace
    (untabify (point-min) (point-max))
    (delete-trailing-whitespace (point-min) (point-max))))

(defun verilog-ext-test-indent-gen-expected-files (&optional tree-sitter)
  "Update .indent files manually."
  (save-window-excursion
    (dolist (file verilog-ext-tests-indent-test-files)
      (let ((indented-file (verilog-ext-path-join verilog-ext-tests-indent-dir
                                                  (verilog-ext-tests-indent-ref-file-from-orig file tree-sitter)))
            (verilog-align-typedef-regexp (concat "\\<" verilog-identifier-re "_\\(t\\)\\>")))
        (message "Processing %s" file)
        (with-temp-file indented-file
          (insert-file-contents file)
          (verilog-ext-test-indent-buffer tree-sitter))))))

(defun verilog-ext-test-indent-file (file &optional tree-sitter)
  "Expects FILE absolute path."
  (let* ((verbose nil)
         (dump-file (verilog-ext-path-join verilog-ext-tests-indent-dump-dir
                                           (file-name-nondirectory file))))
    (when verbose
      (message "Indenting %s..." file))
    (cl-letf (((symbol-function 'message)
               (lambda (FORMAT-STRING &rest ARGS)
                 nil))) ; Mock `message' to silence all the indentation reporting
      (with-temp-file dump-file
        (insert-file-contents file)
        (verilog-ext-test-indent-buffer tree-sitter)
        dump-file))))

(defun verilog-ext-test-indent-compare (file &optional tree-sitter)
  "Compare FILE absolute path for indentation.
Reference indented version: file.indent.sv in indent dir."
  (let* ((verbose nil)
         (filename-indented (verilog-ext-test-indent-file file tree-sitter))
         (filename-ref (verilog-ext-path-join verilog-ext-tests-indent-dir
                                              (verilog-ext-tests-indent-ref-file-from-orig file tree-sitter))))
    (when verbose
      (message "Comparing %s" file))
    ;; Comparison
    (if (equal (with-temp-buffer
                 (insert-file-contents filename-indented)
                 (buffer-substring-no-properties (point-min) (point-max)))
               (with-temp-buffer
                 (insert-file-contents filename-ref)
                 (buffer-substring-no-properties (point-min) (point-max))))
        (progn
          (delete-file filename-indented)
          t)
      ;; Dump on error if enabled
      (when verilog-ext-tests-indent-dump-diff-on-error
        (shell-command (concat
                        "diff " filename-ref " " filename-indented " > " (concat (file-name-sans-extension filename-indented)) ".diff")))
      nil)))

(ert-deftest indent::generic ()
  (let ((test-files verilog-ext-tests-indent-test-files))
    (delete-directory verilog-ext-tests-indent-dump-dir :recursive)
    (make-directory verilog-ext-tests-indent-dump-dir :parents)
    (dolist (file test-files)
      (should (verilog-ext-test-indent-compare file)))))



(provide 'verilog-ext-tests-indent)

;;; verilog-ext-tests-indent.el ends here
