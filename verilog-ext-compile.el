;;; verilog-ext-compile.el --- Verilog-ext Compilation Utils -*- lexical-binding: t -*-

;; Copyright (C) 2022-2023 Gonzalo Larumbe

;; Author: Gonzalo Larumbe <gonzalomlarumbe@gmail.com>
;; URL: https://github.com/gmlarumbe/verilog-ext
;; Version: 0.1.0
;; Package-Requires: ((emacs "28.1") (verilog-mode "2022.12.18.181110314"))

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

;; Compilation related SystemVerilog utils

;;; Code:

(require 'verilog-mode)


(defun verilog-ext-preprocess ()
  "Preprocess current file.
Choose among different available programs and update `verilog-preprocessor'
variable."
  (interactive)
  (let (tools-available)
    (dolist (tool '("verilator" "vppreproc" "iverilog"))
      (when (executable-find tool)
        (push tool tools-available)))
    (setq tools-available (reverse tools-available))
    (pcase (completing-read "Select tool: " tools-available)
      ;; Verilator
      ("verilator" (setq verilog-preprocessor "verilator -E __FLAGS__ __FILE__"))
      ;; Verilog-Perl
      ("vppreproc" (setq verilog-preprocessor "vppreproc __FLAGS__ __FILE__"))
      ;; Icarus Verilog:  `iverilog' command syntax requires writing to an output file (defaults to a.out).
      ("iverilog" (let* ((filename-sans-ext (file-name-sans-extension (file-name-nondirectory (buffer-file-name))))
                         (iver-out-file (concat filename-sans-ext "_pp_iver.sv")))
                    (setq verilog-preprocessor (concat "iverilog -E -o" iver-out-file " __FILE__ && "
                                                       "echo \"\" && "
                                                       "cat " iver-out-file " && "
                                                       "rm " iver-out-file)))))
    (verilog-preprocess)
    (pop-to-buffer "*Verilog-Preprocessed*")))


(provide 'verilog-ext-compile)

;;; verilog-ext-compile.el ends here
