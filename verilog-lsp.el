;;; verilog-lsp.el --- SystemVerilog LSP Setup  -*- lexical-binding: t -*-

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
;; Support for various SystemVerilog language servers
;;  - Builtin:
;;     - hdl_checker: https://github.com/suoto/hdl_checker
;;     - svlangserver: https://github.com/imc-trading/svlangserver
;;  - Additional:
;;     - verible: https://github.com/chipsalliance/verible/tree/master/verilog/tools/ls
;;     - svls: https://github.com/dalance/svls
;;     - veridian: https://github.com/vivekmalneedi/veridian
;;
;;; Code:



;;;; Common
(defconst verilog-ext-lsp-available-servers
  '((verilog      . "hdl_checker")
    (svlangserver . "svlangserver")
    (verible-ls   . "verible-verilog-ls")
    (svls         . "svls")
    (veridian     . "veridian")))

(defconst verilog-ext-lsp-server-ids
  (mapcar #'car verilog-ext-lsp-available-servers))
(defconst verilog-ext-lsp-server-binaries
  (mapcar #'cdr verilog-ext-lsp-available-servers))


;;;; lsp-mode
(require 'lsp-mode)

(defvar verilog-ext-lsp-mode-default-server 'svlangserver)

(defun verilog-ext-lsp-configure ()
  "Configure Verilog for `lsp-mode'.
Register additional clients."
  (interactive)
  (let (server-id server-bin)
    (dolist (server verilog-ext-lsp-available-servers)
      (setq server-id (car server))
      (setq server-bin (cdr server))
      (when (not (member server-id '(verilog svlangserver))) ; Already registered by `lsp-mode'
        (lsp-register-client
         (make-lsp-client :new-connection (lsp-stdio-connection server-bin)
                          :major-modes '(verilog-mode)
                          :server-id server-id))
        (message "Registered lsp-client: %s" server-id)))))

(defun verilog-ext-lsp-set-server (server-id)
  "Set language server defined by SERVER-ID.
Disable the rest to avoid handling priorities.
Override any previous configuration for `verilog-mode'."
  (interactive (list (intern (completing-read "Server-id: " verilog-ext-lsp-server-ids nil t))))
  (unless (executable-find (cdr (assoc server-id verilog-ext-lsp-available-servers)))
    (error "Error: %s not in $PATH" server-id))
  (let ((server-list verilog-ext-lsp-server-ids))
    (setq lsp-disabled-clients (assq-delete-all 'verilog-mode lsp-disabled-clients))
    (push (cons 'verilog-mode (remove server-id server-list)) lsp-disabled-clients)
    (message "[Verilog LSP]: %s" server-id)))


;;;;; Default config
(verilog-ext-lsp-configure)
(verilog-ext-lsp-set-server verilog-ext-lsp-mode-default-server)


;;;; eglot
(require 'eglot)

(defvar verilog-ext-eglot-default-server 'svlangserver)

(defun verilog-ext-eglot-set-server (server-id)
  "Configure Verilog for `eglot'.
Override any previous configuration for `verilog-mode'."
  (interactive (list (intern (completing-read "Server-id: " verilog-ext-lsp-server-ids nil t))))
  (unless (executable-find (cdr (assoc server-id verilog-ext-lsp-available-servers)))
    (error "Error: %s not in $PATH" server-id))
  (setq eglot-server-programs (assq-delete-all 'verilog-mode eglot-server-programs))
  (push (list 'verilog-mode (alist-get server-id verilog-ext-lsp-available-servers))
        eglot-server-programs)
  (message "Set eglot SV server: %s" server-id))


;;;;; Default config
(verilog-ext-eglot-set-server verilog-ext-eglot-default-server)


;;;; Provide package
(provide 'verilog-lsp)

;;; verilog-lsp.el ends here
