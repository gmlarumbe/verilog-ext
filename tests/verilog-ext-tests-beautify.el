;;; verilog-ext-tests-beautify.el --- Verilog-Ext ERT beautify tests  -*- lexical-binding: t -*-

;; Copyright (C) 2022 Gonzalo Larumbe

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



(defun verilog-ext-test-beautify-gen-expected-files ()
  (let ((files-raw (directory-files-recursively verilog-ext-tests-beautify-dir "\\.raw$"))
        files-beauty)
    (dolist (file files-raw)
      (copy-file file (concat (file-name-sans-extension file) ".beauty") t))
    (setq files-beauty (directory-files-recursively verilog-ext-tests-beautify-dir "\\.beauty$"))
    (verilog-ext-beautify-files files-beauty)))

(defun verilog-ext-test-beautify-file (file)
  "Requires switching back to the original table since there could be indentation of "
  (with-temp-buffer
    (insert-file-contents file)
    (verilog-mode)
    (verilog-ext-beautify-current-buffer)
    (untabify (point-min) (point-max))
    (delete-trailing-whitespace (point-min) (point-max))
    (buffer-substring-no-properties (point-min) (point-max))))

(defun verilog-ext-test-beautify-compare (file)
  "Compare raw and beautified versions of FILE.
Expects a file.sv.raw and its beautified version file.sv.beauty in beautify dir."
  (let ((filename-raw (verilog-ext-path-join verilog-ext-tests-beautify-dir (concat file ".raw")))
        (filename-beauty (verilog-ext-path-join verilog-ext-tests-beautify-dir (concat file ".beauty"))))
    (equal (verilog-ext-test-beautify-file filename-raw)
           (with-temp-buffer
             (insert-file-contents filename-beauty)
             (buffer-substring-no-properties (point-min) (point-max))))))



(ert-deftest beautify::module-at-point ()
  (should (verilog-ext-test-beautify-compare "ucontroller.sv"))
  (should (verilog-ext-test-beautify-compare "instances.sv"))
  (should (verilog-ext-test-beautify-compare "axi_demux.sv")))


(provide 'verilog-ext-tests-beautify)

;;; verilog-ext-tests-beautify.el ends here
