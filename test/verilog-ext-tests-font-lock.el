;;; verilog-ext-tests-font-lock.el --- Verilog-Ext ERT font-lock tests  -*- lexical-binding: t -*-

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
;; ERT font-lock tests:
;; - https://github.com/Lindydancer/faceup
;;
;;; Code:


(require 'faceup)

(defun verilog-ext-test-font-lock-update-dir (&optional tree-sitter)
  "Update .faceup files."
  (let ((verilog-align-typedef-regexp nil))
    (save-window-excursion
      (dolist (file (directory-files verilog-ext-tests-common-dir t ".s?vh?$"))
        (find-file file)
        (if tree-sitter
            (verilog-ts-mode)
          (verilog-mode))
        (message "Processing %s" file)
        ;; It is needed to explicitly fontify for batch-mode updates, since by
        ;; default batch mode does not enable font-lock.  Initially tried with
        ;; `font-lock-ensure' but gave different results for tree-sitter.  Plus,
        ;; `faceup-write-file' calls internally `font-lock-fontify-region' so
        ;; it's more consistent
        (font-lock-fontify-region (point-min) (point-max))
        (faceup-write-file (file-name-concat verilog-ext-tests-faceup-dir
                                                  (concat (file-name-nondirectory file)
                                                          (when tree-sitter
                                                            ".ts")
                                                          ".faceup")))))))

(defun verilog-ext-test-font-lock-test-file (file &optional tree-sitter)
  "Test that Verilog FILE fontifies as the .faceup file describes."
  (let ((verilog-align-typedef-regexp nil)
        (mode (if tree-sitter
                  'verilog-ts-mode
                'verilog-mode))
        result)
    (setq result (faceup-test-font-lock-file mode
                                             (file-name-concat verilog-ext-tests-common-dir file)
                                             (file-name-concat verilog-ext-tests-faceup-dir (concat file
                                                                                                         (when tree-sitter
                                                                                                           ".ts")
                                                                                                         ".faceup"))))
    (if (eq t result)
        t ; Propagate 't for the test to pass
      ;; In case of failure, show also which file failed
      (push file result)
      result)))



(ert-deftest font-lock::generic ()
  (let ((default-directory verilog-ext-tests-common-dir)
        (faceup-test-explain t))
    (dolist (file (directory-files verilog-ext-tests-common-dir nil ".s?vh?$"))
      (should (eq t (verilog-ext-test-font-lock-test-file file))))))


(provide 'verilog-ext-tests-font-lock)

;;; verilog-ext-tests-font-lock.el ends here
