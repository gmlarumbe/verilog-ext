;;; verilog-ext-lsp-bridge.el --- Verilog-ext lsp-bridge setup  -*- lexical-binding: t -*-

;; Copyright (C) 2022-2024 Gonzalo Larumbe

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

;; Support for various SystemVerilog language servers
;;  - Builtin:
;;     - verible: https://github.com/chipsalliance/verible/tree/master/verilog/tools/ls
;;  - Additional:
;;     - hdl_checker: https://github.com/suoto/hdl_checker
;;     - svlangserver: https://github.com/imc-trading/svlangserver
;;     - svls: https://github.com/dalance/svls
;;     - veridian: https://github.com/vivekmalneedi/veridian

;;; Code:

(require 'lsp-bridge nil :noerror) ; Set to :noerror since `lsp-bridge' is not available in MELPA
(require 'verilog-ext-utils)

(defconst verilog-ext-lsp-bridge-langserver-dir
  (expand-file-name "langserver" (file-name-directory (or load-file-name (buffer-file-name)))))

(defvar verilog-ext-lsp-bridge-default-server 've-svlangserver)

(defun verilog-ext-lsp-bridge-set-server (server-id)
  "Configure Verilog for `lsp-bridge' with SERVER-ID server.
Override any previous configuration for `verilog-mode' and `verilog-ts-mode'."
  (interactive (list (intern (completing-read "Server-id: " verilog-ext-lsp-server-ids nil t))))
  (let ((cmd (car (alist-get server-id verilog-ext-lsp-available-servers)))
        (cfg-file (cadr (alist-get server-id verilog-ext-lsp-available-servers)))
        (cfg-dir verilog-ext-lsp-bridge-langserver-dir))
    (unless (featurep 'lsp-bridge)
      (user-error "lsp-bridge not available: check Installation section on https://github.com/manateelazycat/lsp-bridge"))
    (unless cmd
      (error "%s not recognized as a supported server" server-id))
    (if (not (executable-find (if (listp cmd)
                                  (car cmd)
                                cmd)))
        (message "%s not in $PATH, skipping config..." server-id)
      ;; Else configure available server
      (dolist (mode '(verilog-mode verilog-ts-mode))
        (setq lsp-bridge-single-lang-server-mode-list (assq-delete-all mode lsp-bridge-single-lang-server-mode-list))
        (push (cons mode (file-name-concat cfg-dir cfg-file)) lsp-bridge-single-lang-server-mode-list))
      ;; Some reporting
      (message "[verilog-ext lsp-bridge]: %s" server-id))))


(provide 'verilog-ext-lsp-bridge)

;;; verilog-ext-lsp-bridge.el ends here

;; Silence all the lsp-bridge byte-compiler warnings:
;;
;; Local Variables:
;; byte-compile-warnings: (not free-vars)
;; End:

