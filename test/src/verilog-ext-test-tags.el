;;; verilog-ext-test-tags.el --- Verilog-Ext ERT tags tests  -*- lexical-binding: t -*-

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
;; Verilog-Ext ERT tags tests
;;
;;; Code:

;;;; Aux functions (used for capf/hierarchy/xref)
(defconst verilog-ext-test-tags-proj-name "verilog-ext-test-tags")

(cl-defun verilog-ext-test-tags-get (&key backend root files dirs rel-path)
  "Populate the value of the tags tables for test-hdl-verilog project."
  (let ((verilog-ext-tags-backend backend)
        (verilog-ext-project-alist `((,verilog-ext-test-tags-proj-name
                                      :root ,(or root verilog-ext-test-files-common-dir)
                                      :files ,files
                                      :dirs ,dirs)))
        (default-directory verilog-ext-test-files-common-dir)) ; DANGER: Needed to get relative filename for GitHub Actions via advice
    ;; Get tags after setting environment
    (test-hdl-no-messages
      (verilog-ext-tags-clear-cache) ; INFO: This is very important in order to start off with a clean environment
      ;; Make file entries relative to avoid issues in GitHub Actions CI with a different $HOME
      (when rel-path
        (advice-add 'verilog-ext-proj-files :filter-return #'test-hdl-tags-proj-files-relative))
      (verilog-ext-tags-get)
      (when rel-path
        (advice-remove 'verilog-ext-proj-files #'test-hdl-tags-proj-files-relative)))))


;;;; Standalone tests
(defconst verilog-ext-test-tags-file-list verilog-ext-test-common-file-list)

(defconst verilog-ext-test-ref-dir-tags (file-name-concat verilog-ext-test-ref-dir "tags"))
(defconst verilog-ext-test-dump-dir-tags (file-name-concat verilog-ext-test-dump-dir "tags"))

(defconst verilog-ext-test-tags-file-and-tag-type-list
  `((,(file-name-concat verilog-ext-test-files-common-dir "axi_demux.sv")      . top-items)
    (,(file-name-concat verilog-ext-test-files-common-dir "axi_test.sv")       . top-items)
    (,(file-name-concat verilog-ext-test-files-common-dir "instances.sv")      . top-items)
    (,(file-name-concat verilog-ext-test-files-common-dir "tb_program.sv")     . top-items)
    (,(file-name-concat verilog-ext-test-files-common-dir "ucontroller.sv")    . top-items)
    (,(file-name-concat verilog-ext-test-files-common-dir "uvm_component.svh") . classes)))

(defun verilog-ext-test-tags-setup ()
  "Avoid errors in desc when there are tabs and trailing whitespaces."
  (let ((verilog-align-typedef-regexp nil)
        (disable-serialization nil)) ; TODO: Only works for tags, not for capf or xref
    (untabify (point-min) (point-max))
    (delete-trailing-whitespace (point-min) (point-max))
    ;; The lines below are run every time a file is processed in `verilog-ext-tags-get--process-file'
    (setq verilog-ext-tags-defs-current-file (make-hash-table :test #'equal))
    (setq verilog-ext-tags-inst-current-file (make-hash-table :test #'equal))
    (setq verilog-ext-tags-refs-current-file (make-hash-table :test #'equal))
    ;; Avoid cache serialization in batch mode, if set locally
    (when disable-serialization
      (remove-hook 'kill-emacs-hook #'verilog-ext-tags-serialize))))

(defun verilog-ext-test-tags-builtin-defs-file-fn (tag-type file)
  (let ((file (file-relative-name file test-hdl-test-dir)))
    (verilog-ext-test-tags-setup)
    (verilog-ext-with-no-hooks
      (verilog-mode))
    (verilog-ext-tags-table-push-defs :tag-type tag-type :file file)
    verilog-ext-tags-defs-current-file))

(defun verilog-ext-test-tags-builtin-refs-file-fn (file)
  (let ((file (file-relative-name file test-hdl-test-dir)))
    (verilog-ext-test-tags-setup)
    (verilog-ext-with-no-hooks
      (verilog-mode))
    (verilog-ext-tags-table-push-refs file)
    verilog-ext-tags-refs-current-file))

(defun verilog-ext-test-tags-ts-defs-file-fn (file)
  (let ((file (file-relative-name file test-hdl-test-dir)))
    (verilog-ext-test-tags-setup)
    (treesit-parser-create 'verilog)
    (verilog-ext-tags-table-push-defs-ts file)
    verilog-ext-tags-defs-current-file))

(defun verilog-ext-test-tags-ts-refs-file-fn (file)
  (let ((file (file-relative-name file test-hdl-test-dir)))
    (verilog-ext-test-tags-setup)
    (treesit-parser-create 'verilog)
    (verilog-ext-tags-table-push-refs-ts file)
    verilog-ext-tags-refs-current-file))

(defun verilog-ext-test-tags-gen-expected-files ()
  ;; Builtin
  (dolist (file-and-tag-type verilog-ext-test-tags-file-and-tag-type-list)
    (let ((file (car file-and-tag-type))
          (tag-type (cdr file-and-tag-type)))
      ;; Defs
      (test-hdl-gen-expected-files :file-list `(,file)
                                   :dest-dir verilog-ext-test-ref-dir-tags
                                   :out-file-ext "defs.el"
                                   :process-fn 'eval
                                   :fn #'verilog-ext-test-tags-builtin-defs-file-fn
                                   :args `(,tag-type ,file))
      ;; Refs
      (test-hdl-gen-expected-files :file-list `(,file)
                                   :dest-dir verilog-ext-test-ref-dir-tags
                                   :out-file-ext "refs.el"
                                   :process-fn 'eval
                                   :fn #'verilog-ext-test-tags-builtin-refs-file-fn
                                   :args `(,file))))
  ;; Tree-sitter
  (dolist (file verilog-ext-test-tags-file-list)
    ;; Defs
    (test-hdl-gen-expected-files :file-list `(,file)
                                 :dest-dir verilog-ext-test-ref-dir-tags
                                 :out-file-ext "ts.defs.el"
                                 :process-fn 'eval
                                 :fn #'verilog-ext-test-tags-ts-defs-file-fn
                                 :args `(,file))
    ;; Refs
    (test-hdl-gen-expected-files :file-list `(,file)
                                 :dest-dir verilog-ext-test-ref-dir-tags
                                 :out-file-ext "ts.refs.el"
                                 :process-fn 'eval
                                 :fn #'verilog-ext-test-tags-ts-refs-file-fn
                                 :args `(,file))))


(ert-deftest tags::builtin ()
  (dolist (file-and-tag-type verilog-ext-test-tags-file-and-tag-type-list)
    (let ((file (car file-and-tag-type))
          (tag-type (cdr file-and-tag-type)))
      ;; Defs
      (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                           :dump-file (file-name-concat verilog-ext-test-dump-dir-tags (test-hdl-basename file "defs.el"))
                                                           :process-fn 'eval
                                                           :fn #'verilog-ext-test-tags-builtin-defs-file-fn
                                                           :args `(,tag-type ,file))
                                    (file-name-concat verilog-ext-test-ref-dir-tags (test-hdl-basename file "defs.el"))))
      ;; Refs
      (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                           :dump-file (file-name-concat verilog-ext-test-dump-dir-tags (test-hdl-basename file "refs.el"))
                                                           :process-fn 'eval
                                                           :fn #'verilog-ext-test-tags-builtin-refs-file-fn
                                                           :args `(,file))
                                    (file-name-concat verilog-ext-test-ref-dir-tags (test-hdl-basename file "refs.el")))))))


(ert-deftest tags::tree-sitter ()
  (dolist (file verilog-ext-test-tags-file-list)
    ;; Defs
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-tags (test-hdl-basename file "ts.defs.el"))
                                                         :process-fn 'eval
                                                         :fn #'verilog-ext-test-tags-ts-defs-file-fn
                                                         :args `(,file))
                                  (file-name-concat verilog-ext-test-ref-dir-tags (test-hdl-basename file "ts.defs.el"))))
    ;; Refs
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-tags (test-hdl-basename file "ts.refs.el"))
                                                         :process-fn 'eval
                                                         :fn #'verilog-ext-test-tags-ts-refs-file-fn
                                                         :args `(,file))
                                  (file-name-concat verilog-ext-test-ref-dir-tags (test-hdl-basename file "ts.refs.el"))))))


(provide 'verilog-ext-test-tags)

;;; verilog-ext-test-tags.el ends here
