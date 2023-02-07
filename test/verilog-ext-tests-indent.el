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


(defvar verilog-ext-test-indent-dump-dir (verilog-ext-path-join verilog-ext-tests-indent-dir "dump"))


(defun verilog-ext-test-indent-buffer (file &optional tree-sitter)
  "Perform indentation of current buffer for indentation tests."
  (let ((debug nil))
    (when debug
      (clone-indirect-buffer-other-window "*debug*" t))
    (insert-file-contents file)
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

(defun verilog-ext-test-indent-update-dir (&optional tree-sitter)
  "Update .indent files manually."
  (save-window-excursion
    (dolist (file (directory-files verilog-ext-tests-examples-dir t ".s?vh?$"))
      (let ((indented-file (concat (file-name-directory file)
                                   "indent/"
                                   (file-name-nondirectory file)
                                   (when tree-sitter
                                     ".ts")
                                   ".indent"))
            (verilog-align-typedef-regexp (concat "\\<" verilog-identifier-re "_\\(t\\)\\>")))
        (message "Processing %s" file)
        (with-temp-file indented-file
          (verilog-ext-test-indent-buffer file tree-sitter))))))

(defun verilog-ext-test-indent-file (file &optional tree-sitter)
  (let* ((verbose nil)
         (filename-indent (verilog-ext-path-join verilog-ext-tests-examples-dir file))
         (dump-file (verilog-ext-path-join verilog-ext-test-indent-dump-dir
                                           (concat (file-name-nondirectory filename-indent) ".dump"))))
    (when verbose
      (message "Indenting %s..." file))
    (cl-letf (((symbol-function 'message)
               (lambda (FORMAT-STRING &rest ARGS)
                 nil))) ; Mock `message' to silence all the indentation reporting
      (with-temp-file dump-file
        (verilog-ext-test-indent-buffer filename-indent tree-sitter)))))

(defun verilog-ext-test-indent-compare (file &optional dump)
  "Compare original and indented versions of FILE.
Expects a file.sv in the examples dir and its indented version file.sv.indent in indent dir."
  (let* ((verbose nil)
         (filename-indent-golden (verilog-ext-path-join verilog-ext-tests-indent-dir (concat file ".indent")))
         (filename-indent (verilog-ext-path-join verilog-ext-tests-examples-dir file))
         (dump-file (verilog-ext-path-join verilog-ext-test-indent-dump-dir
                                           (concat (file-name-nondirectory filename-indent) ".dump"))))
    (when verbose
      (message "Comparing %s" file))
    (verilog-ext-test-indent-file file)
    ;; Comparison
    (string= (with-temp-buffer
               (insert-file-contents filename-indent-golden)
               (buffer-substring-no-properties (point-min) (point-max)))
             (with-temp-buffer
               (insert-file-contents dump-file)
               (buffer-substring-no-properties (point-min) (point-max))))))

(ert-deftest indent::generic ()
  (delete-directory verilog-ext-test-indent-dump-dir :recursive)
  (make-directory verilog-ext-test-indent-dump-dir :parents)
  (dolist (file (directory-files verilog-ext-tests-examples-dir nil ".s?vh?$"))
    (should (verilog-ext-test-indent-compare file))))


(provide 'verilog-ext-tests-indent)

;;; verilog-ext-tests-indent.el ends here
