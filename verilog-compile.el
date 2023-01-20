;;; verilog-compile.el --- Compile related functions  -*- lexical-binding: t -*-

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
;; Compilation/Makefile mode related functions
;;
;;; Code:

(require 'make-mode)
(require 'verilog-mode)
(require 'verilog-utils)
(require 'verilog-completion)


;;;; Preprocessor
(defun verilog-ext-preprocess ()
  "Preprocess current file.
Choose among different available programs and update `verilog-preprocessor'
variable."
  (interactive)
  (pcase (completing-read "Select tool: " '("verilator" "vppreproc" "iverilog"))
    ;; Verilator
    ("verilator"
     (if (executable-find "verilator")
         (setq verilog-preprocessor "verilator -E __FLAGS__ __FILE__")
       (error "verilator binary not found in $PATH")))
    ;; Verilog-Perl
    ("vppreproc"
     (if (executable-find "vppreproc")
         (setq verilog-preprocessor "vppreproc __FLAGS__ __FILE__")
       (error "vppreproc binary not found in $PATH")))
    ;; Icarus Verilog:  `iverilog' command syntax requires writing to an output file (defaults to a.out).
    ("iverilog"
     (if (executable-find "iverilog")
         (let* ((filename-sans-ext (file-name-sans-extension (file-name-nondirectory (buffer-file-name))))
                (iver-out-file (read-string "Output filename: " (concat filename-sans-ext "_pp.sv"))))
           (setq verilog-preprocessor (concat "iverilog -E -o" iver-out-file " __FILE__ __FLAGS__")))
       (error "iverilog binary not found in $PATH"))))
  (verilog-preprocess)
  (pop-to-buffer "*Verilog-Preprocessed*"))


;;;; Iverilog/verilator Makefiles
(defun verilog-ext-makefile-create ()
  "Create Iverilog/verilator Yasnippet based Makefile.
Create it only if in a project and the Makefile does not already exist."
  (interactive)
  (let ((project-root (verilog-ext-project-root))
        file)
    (if project-root
        (if (file-exists-p (setq file (verilog-ext-path-join project-root "Makefile")))
            (error "File %s already exists!" file)
          (find-file file)
          (verilog-ext-insert-yasnippet "verilog"))
      (error "Not in a project!"))))

(defun verilog-ext-makefile-compile ()
  "Prompt to available Makefile targets and compile.
Compiles them with various verilog regexps."
  (interactive)
  (let ((makefile (verilog-ext-path-join (verilog-ext-project-root) "Makefile"))
        (makefile-need-target-pickup t) ; Force refresh of makefile targets
        target cmd)
    (unless (file-exists-p makefile)
      (error "%s does not exist!" makefile))
    (with-temp-buffer
      (insert-file-contents makefile)
      (makefile-pickup-targets)
      (setq target (completing-read "Target: " makefile-target-table)))
    (setq cmd (concat "cd " (verilog-ext-project-root) " && make " target))
    (compile cmd)))



(provide 'verilog-compile)

;;; verilog-compile.el ends here
