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


(defvar verilog-ext-test-beautify-dump-diff-on-error nil)


(defun verilog-ext-test-beautify-gen-expected-files ()
  (let ((orig-dir verilog-ext-tests-common-dir)
        (dest-dir verilog-ext-tests-beautify-dir)
        (files '("axi_demux.sv" "instances.sv" "ucontroller.sv"))  ; Only files with instances are relevant
        (verilog-ext-time-stamp-pattern nil))                      ; Prevent auto-update of timestamp
    (dolist (file files)
      (copy-file (verilog-ext-path-join orig-dir file)
                 (verilog-ext-path-join dest-dir (concat (file-name-nondirectory (file-name-sans-extension file)) ".beauty.sv")) t))
    (verilog-ext-beautify-dir-files dest-dir)))

(defun verilog-ext-test-beautify-file (file)
  (let ((debug nil))
    (cl-letf (((symbol-function 'message)
               (lambda (FORMAT-STRING &rest ARGS)
                 nil))) ; Mock `message' to silence all the indentation reporting
      (with-temp-buffer
        (when debug
          (clone-indirect-buffer-other-window "*debug*" t))
        (insert-file-contents file)
        ;; Remove alignments between port connections
        (verilog-ext-replace-regexp-whole-buffer (concat "\\(?1:^\\s-*\\." verilog-identifier-re "\\)\\(?2:\\s-*\\)(") "\\1(")
        ;; Beautify
        (verilog-mode)
        (verilog-ext-beautify-current-buffer)
        (buffer-substring-no-properties (point-min) (point-max))))))

(defun verilog-ext-test-beautify-compare (file)
  "Compare raw and beautified versions of FILE.
Expects a file.sv.raw and its beautified version file.sv.beauty in beautify dir."
  (let ((filename-beauty (verilog-ext-path-join verilog-ext-tests-beautify-dir (concat (file-name-nondirectory (file-name-sans-extension file)) ".beauty.sv"))))
    (equal (verilog-ext-test-beautify-file (verilog-ext-path-join verilog-ext-tests-common-dir file))
           (with-temp-buffer
             (insert-file-contents filename-beauty)
             (buffer-substring-no-properties (point-min) (point-max))))))

;; (defun verilog-ext-test-beautify-ert-explainer (file)
;;   (let* ((file-reference (verilog-ext-path-join verilog-ext-tests-beautify-dir (concat (file-name-nondirectory (file-name-sans-extension file)) ".beauty.sv")))
;;          (string-reference (with-temp-buffer
;;                              (insert-file-contents file-reference)
;;                              (buffer-substring-no-properties (point-min) (point-max))))
;;          (file-orig (verilog-ext-path-join verilog-ext-tests-common-dir file))
;;          (string-actual (verilog-ext-test-beautify-file file-orig))
;;          (dump-dir (verilog-ext-path-join verilog-ext-tests-beautify-dir "dump"))
;;          (dump-file (verilog-ext-path-join dump-dir file)))
;;     (delete-directory dump-dir :recursive)
;;     (make-directory dump-dir :parents)
;;     (with-temp-file dump-file
;;       (insert string-actual))
;;     (when verilog-ext-test-beautify-dump-diff-on-error
;;       (shell-command (concat "diff " file-reference " " dump-file " > " (concat (file-name-sans-extension dump-file)) ".diff")))
;;     (ert--explain-string-equal string-reference string-actual)))


;; (put 'verilog-ext-test-beautify-compare 'ert-explainer #'verilog-ext-test-beautify-ert-explainer)


(ert-deftest beautify::module-at-point ()
  (should (verilog-ext-test-beautify-compare "ucontroller.sv"))
  (should (verilog-ext-test-beautify-compare "instances.sv"))
  (should (verilog-ext-test-beautify-compare "axi_demux.sv")))


(provide 'verilog-ext-tests-beautify)

;;; verilog-ext-tests-beautify.el ends here
