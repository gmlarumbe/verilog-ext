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


(defconst verilog-ext-tests-beautify-test-files
  '("axi_demux.sv"
    "instances.sv"
    "ucontroller.sv"))
(defconst verilog-ext-tests-beautify-dump-dir (file-name-concat verilog-ext-tests-beautify-dir "dump"))
(defconst verilog-ext-tests-beautify-dump-diff-on-error t)


(defun verilog-ext-tests-beautify-ref-file-from-orig (file &optional tree-sitter)
  (if tree-sitter
      (concat (file-name-nondirectory (file-name-sans-extension file)) ".ts.beauty.sv")
    (concat (file-name-nondirectory (file-name-sans-extension file)) ".beauty.sv")))

(defun verilog-ext-test-beautify-gen-expected-files (&optional tree-sitter)
  (let ((orig-dir verilog-ext-tests-common-dir)
        (dest-dir verilog-ext-tests-beautify-dir)
        (files verilog-ext-tests-beautify-test-files)  ; Only files with instances are relevant
        ;; TODO: Ugly hack, it would be better to have ts/ext ref files in different directories
        (verilog-ext-file-extension-re (concat (regexp-opt '("axi_demux" "instances" "ucontroller")) "\\.beauty\\.sv"))
        (verilog-ts-file-extension-re  (concat (regexp-opt '("axi_demux" "instances" "ucontroller")) "\\.ts\\.beauty\\.sv"))
        ;; End of TODO
        (verilog-ext-time-stamp-pattern nil)) ; Prevent auto-update of timestamp
    (dolist (file files)
      (copy-file (file-name-concat orig-dir file)
                 (file-name-concat dest-dir (verilog-ext-tests-beautify-ref-file-from-orig file tree-sitter))
                 t))
    (if tree-sitter
        (verilog-ts-beautify-dir-files dest-dir)
      (verilog-ext-beautify-dir-files dest-dir))))

(defun verilog-ext-test-beautify-file (file &optional tree-sitter)
  (let ((debug nil)
        (dump-file (file-name-concat verilog-ext-tests-beautify-dump-dir file)))
    (cl-letf (((symbol-function 'message)
               (lambda (FORMAT-STRING &rest ARGS)
                 nil))) ; Mock `message' to silence all the indentation reporting
      (with-temp-file dump-file
        (when debug
          (clone-indirect-buffer-other-window "*debug*" t))
        (insert-file-contents (file-name-concat verilog-ext-tests-common-dir file))
        ;; Remove alignments between port connections
        (verilog-ext-replace-regexp-whole-buffer (concat "\\(?1:^\\s-*\\." verilog-identifier-re "\\)\\(?2:\\s-*\\)(") "\\1(")
        ;; Beautify
        (if tree-sitter
            (progn
              (verilog-ts-mode)
              (verilog-ts-beautify-current-buffer))
          (verilog-mode)
          (verilog-ext-beautify-current-buffer))
        dump-file))))

(defun verilog-ext-test-beautify-compare (file &optional tree-sitter)
  "Compare beautified FILE.
Reference beautified version: file.beauty.sv in beautify dir."
  (let ((filename-beautified (verilog-ext-test-beautify-file file tree-sitter)) ; Dump file
        (filename-ref (file-name-concat verilog-ext-tests-beautify-dir (verilog-ext-tests-beautify-ref-file-from-orig file tree-sitter))))
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
