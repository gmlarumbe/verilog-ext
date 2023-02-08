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


(defvar verilog-ext-test-indent-dump-diff-on-error nil)


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
    (dolist (file (directory-files verilog-ext-tests-common-dir t ".s?vh?$"))
      (let ((indented-file
             (verilog-ext-path-join verilog-ext-tests-indent-dir
                                    (concat
                                     (file-name-sans-extension (file-name-nondirectory file))
                                     (when tree-sitter
                                       ".ts")
                                     ".indent.sv")))
            (verilog-align-typedef-regexp (concat "\\<" verilog-identifier-re "_\\(t\\)\\>")))
        (message "Processing %s" file)
        (with-temp-file indented-file
          (insert-file-contents file)
          (verilog-ext-test-indent-buffer tree-sitter))))))

(defun verilog-ext-test-indent-file (file &optional tree-sitter)
  (let* ((verbose nil)
         (filename-indent (verilog-ext-path-join verilog-ext-tests-common-dir file)))
    (when verbose
      (message "Indenting %s..." file))
    (cl-letf (((symbol-function 'message)
               (lambda (FORMAT-STRING &rest ARGS)
                 nil))) ; Mock `message' to silence all the indentation reporting
      (with-temp-buffer
        (insert-file-contents filename-indent)
        (verilog-ext-test-indent-buffer tree-sitter)
        (buffer-substring-no-properties (point-min) (point-max))))))

(defun verilog-ext-test-indent-compare (file &optional tree-sitter)
  "Compare original and indented versions of FILE.
Expects a file.sv in the examples dir and its indented version file.sv.indent in indent dir."
  (let* ((verbose nil)
         (filename-indent (verilog-ext-path-join verilog-ext-tests-indent-dir
                                                 (concat (file-name-sans-extension (file-name-nondirectory file))
                                                         (when tree-sitter
                                                           ".ts")
                                                         ".indent.sv"))))
    (when verbose
      (message "Comparing %s" file))
    ;; Comparison
    (string= (verilog-ext-test-indent-file file tree-sitter)
             (with-temp-buffer
               (insert-file-contents filename-indent)
               (buffer-substring-no-properties (point-min) (point-max))))))

;; (defun verilog-ext-test-indent-ert-explainer (file &optional tree-sitter)
;;   (let* ((file-reference (verilog-ext-path-join verilog-ext-tests-indent-dir (concat (file-name-sans-extension file) ".indent.sv")))
;;          (string-reference (with-temp-buffer
;;                              (insert-file-contents file-reference)
;;                              (buffer-substring-no-properties (point-min) (point-max))))
;;          (string-actual (verilog-ext-test-indent-file file))
;;          (dump-dir (verilog-ext-path-join verilog-ext-tests-indent-dir "dump"))
;;          (dump-file (verilog-ext-path-join dump-dir file)))
;;     (delete-directory dump-dir :recursive)
;;     (make-directory dump-dir :parents)
;;     (with-temp-file dump-file
;;       (insert string-actual))
;;     (when verilog-ext-test-indent-dump-diff-on-error
;;       (shell-command (concat "diff " file-reference " " dump-file " > " (concat (file-name-sans-extension dump-file)) ".diff")))
;;     (ert--explain-string-equal string-reference string-actual)))


;; (put 'verilog-ext-test-indent-compare 'ert-explainer #'verilog-ext-test-indent-ert-explainer)


(ert-deftest indent::generic ()
  (dolist (file (directory-files verilog-ext-tests-common-dir nil ".s?vh?$"))
    (should (verilog-ext-test-indent-compare (file-name-nondirectory file)))))



(provide 'verilog-ext-tests-indent)

;;; verilog-ext-tests-indent.el ends here
