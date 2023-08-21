;;; verilog-ext-tests-tags.el --- Verilog-Ext ERT tags tests  -*- lexical-binding: t -*-

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
;; ERT Tags Tests
;;
;;; Code:

;; https://stackoverflow.com/questions/18180393/compare-hash-table-in-emacs-lisp
;; Using `ht' could be an alternative, but let's try to reduce the amount of dependencies
(defun hash-equal (hash1 hash2)
  "Compare two hash tables to see whether they are equal."
  (and (= (hash-table-count hash1)
          (hash-table-count hash2))
       (catch 'flag (maphash (lambda (x y)
                               (or (equal (gethash x hash2) y)
                                   (throw 'flag nil)))
                             hash1)
              (throw 'flag t))))

(defun hash-not-equal (hash1 hash2)
  "Compare two hash tables to see whether they are different.

Return differences get a better explanation of the errors in ERT testsuites."
  (or (when (/= (hash-table-count hash1)
                (hash-table-count hash2))
        (message "Hash tables of different sizes: %s %s" (hash-table-count hash1) (hash-table-count hash2)))
      (catch 'flag (maphash (lambda (x y)
                              (or (equal (gethash x hash2) y)
                                  (throw 'flag (list (format "%s" y) (format "%s" (gethash x hash2))))))
                            hash1)
             (throw 'flag nil))))

(defconst verilog-ext-tests-tags-files-alist
  '(("axi_demux.sv"      . top-items)
    ("axi_test.sv"       . top-items)
    ("instances.sv"      . top-items)
    ("tb_program.sv"     . top-items)
    ("ucontroller.sv"    . top-items)
    ("uvm_component.svh" . classes)))

(defun verilog-ext-tests-tags-ref-file-from-orig (file type &optional tree-sitter)
  (cond ((and (eq type 'defs)
              tree-sitter)
         (file-name-concat verilog-ext-tests-tags-dir
                           (concat (file-name-nondirectory (file-name-sans-extension file)) ".ts.defs")))
        ((and (eq type 'refs)
              tree-sitter)
         (file-name-concat verilog-ext-tests-tags-dir
                           (concat (file-name-nondirectory (file-name-sans-extension file)) ".ts.refs")))
        ((and (eq type 'defs)
              (not tree-sitter))
         (file-name-concat verilog-ext-tests-tags-dir
                           (concat (file-name-nondirectory (file-name-sans-extension file)) ".defs")))
        ((and (eq type 'refs)
              (not tree-sitter))
         (file-name-concat verilog-ext-tests-tags-dir
                           (concat (file-name-nondirectory (file-name-sans-extension file)) ".refs")))
        (t
         (error "Wrong combination!"))))

(defun verilog-ext-test-tags-gen-expected-files (&optional tree-sitter)
  "Generate expected files for tags tests."
  (let ((table-defs (make-hash-table :test #'equal))
        (table-refs (make-hash-table :test #'equal))
        (verilog-ext-tags-backend (if tree-sitter
                                      'tree-sitter
                                    'builtin))
        (verilog-align-typedef-regexp nil)
        (files-alist verilog-ext-tests-tags-files-alist)
        dest-file file type)
    (dolist (file-cons files-alist)
      (setq file (car file-cons))
      (setq type (cdr file-cons))
      ;; Gen defs
      (setq dest-file (verilog-ext-tests-tags-ref-file-from-orig file 'defs tree-sitter))
      (with-temp-file dest-file
        (setq table-defs (verilog-ext-test-tags-defs-file file type tree-sitter))
        (pp table-defs (current-buffer)))
      (message "Generated defs for %s (ts: %s)" file tree-sitter)
      ;; Gen refs
      (setq dest-file (verilog-ext-tests-tags-ref-file-from-orig file 'refs tree-sitter))
      (with-temp-file dest-file
        (setq table-refs (verilog-ext-test-tags-refs-file file type tree-sitter))
        (pp table-refs (current-buffer)))
      (message "Generated refs for %s (ts: %s)" file tree-sitter))))

(defun verilog-ext-test-tags-defs-file (file tag-type &optional tree-sitter)
  (let ((table-defs (make-hash-table :test #'equal))
        (verilog-ext-tags-backend (if tree-sitter
                                      'tree-sitter
                                    'builtin))
        (verilog-align-typedef-regexp nil))
    (with-temp-buffer
      (insert-file-contents (file-name-concat verilog-ext-tests-common-dir file))
      ;; Avoid errors in desc when there are tabs and trailing whitespaces
      (untabify (point-min) (point-max))
      (delete-trailing-whitespace (point-min) (point-max))
      ;; Get definitions
      (if tree-sitter
          (progn
            (verilog-ts-mode)
            (verilog-ext-tags-table-push-defs-ts :table table-defs :file file))
        (verilog-mode)
        (verilog-ext-tags-table-push-defs :tag-type tag-type :table table-defs :file file)))
    table-defs))

(defun verilog-ext-test-tags-refs-file (file tag-type &optional tree-sitter)
  "Gather references.

It is needed to also gather definitions as these are used to filter references."
  (let ((table-defs (make-hash-table :test #'equal))
        (table-refs (make-hash-table :test #'equal))
        (verilog-ext-tags-backend (if tree-sitter
                                      'tree-sitter
                                    'builtin))
        (verilog-align-typedef-regexp nil))
    (with-temp-buffer
      (insert-file-contents (file-name-concat verilog-ext-tests-common-dir file))
      ;; Avoid errors in desc when there are tabs and trailing whitespaces
      (untabify (point-min) (point-max))
      (delete-trailing-whitespace (point-min) (point-max))
      ;; Get references
      (if tree-sitter
          (progn
            (verilog-ts-mode)
            (verilog-ext-tags-table-push-defs-ts :table table-defs :file file)
            (verilog-ext-tags-table-push-refs-ts :table table-refs :defs-table table-defs :file file))
        (verilog-mode)
        (verilog-ext-tags-table-push-defs :tag-type tag-type :table table-defs :file file)
        (verilog-ext-tags-table-push-refs :table table-refs :defs-table table-defs :file file)))
    table-refs))

(ert-deftest tags::definitions ()
  (let ((alist verilog-ext-tests-tags-files-alist)
        file tag-type defs)
    (dolist (elm alist)
      (setq file (car elm))
      (setq tag-type (cdr elm))
      (setq defs (with-temp-buffer
                   (insert-file-contents (verilog-ext-tests-tags-ref-file-from-orig file 'defs))
                   (read (buffer-string))))
      (should (hash-equal defs (verilog-ext-test-tags-defs-file file tag-type))))))

(ert-deftest tags::references ()
  (let ((alist verilog-ext-tests-tags-files-alist)
        file tag-type refs)
    (dolist (elm alist)
      (setq file (car elm))
      (setq tag-type (cdr elm))
      (setq refs (with-temp-buffer
                   (insert-file-contents (verilog-ext-tests-tags-ref-file-from-orig file 'refs))
                   (read (buffer-string))))
      (should (hash-equal refs (verilog-ext-test-tags-refs-file file tag-type))))))


(provide 'verilog-ext-tests-tags)

;;; verilog-ext-tests-tags.el ends here
