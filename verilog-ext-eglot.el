;;; verilog-ext-eglot.el --- Verilog-ext Eglot setup  -*- lexical-binding: t -*-

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
;;     - hdl_checker: https://github.com/suoto/hdl_checker
;;     - svlangserver: https://github.com/imc-trading/svlangserver
;;     - verible: https://github.com/chipsalliance/verible/tree/master/verilog/tools/ls
;;     - svls: https://github.com/dalance/svls
;;     - veridian: https://github.com/vivekmalneedi/veridian

;;; Code:
(require 'eglot)
(require 'verilog-ext-utils)

(defvar verilog-ext-eglot-default-server 've-svlangserver)

;;;; svlangserver
;; These customization values are copied from `lsp-verilog' to make `eglot'
;; config independent from `lsp-mode'.
(defgroup verilog-ext-eglot nil
  "Verilog-ext eglot."
  :group 'verilog-ext
  :link '(url-link "https://github.com/imc-trading/svlangserver"))

(defcustom verilog-ext-eglot-svlangserver-includeIndexing '["**/*.{sv,svh}"]
  "Files included for indexing (glob pattern)."
  :group 'verilog-ext-eglot
  :type '(lsp-repeatable-vector string)
  :safe (lambda (x) (seq-every-p #'stringp x)))

(defcustom verilog-ext-eglot-svlangserver-excludeIndexing '["test/**/*.{sv,svh}"]
  "Files excluded for indexing (glob pattern)."
  :group 'verilog-ext-eglot
  :type '(lsp-repeatable-vector string)
  :safe (lambda (x) (seq-every-p #'stringp x)))

(defcustom verilog-ext-eglot-svlangserver-defines nil
  "Defines needed for linting."
  :group 'verilog-ext-eglot
  :type '(lsp-repeatable-vector string)
  :safe (lambda (x) (seq-every-p #'stringp x)))

(defcustom verilog-ext-eglot-svlangserver-launchConfiguration "verilator -sv --lint-only -Wall"
  "Verilator command used for linting."
  :group 'verilog-ext-eglot
  :type 'string
  :safe (lambda (x) (stringp x)))

(defcustom verilog-ext-eglot-svlangserver-lintOnUnsaved t
  "Enable linting on unsaved files."
  :group 'verilog-ext-eglot
  :type 'boolean
  :safe (lambda (x) (booleanp x)))

(defcustom verilog-ext-eglot-svlangserver-formatCommand "verible-verilog-format"
  "Verible verilog format command."
  :group 'verilog-ext-eglot
  :type 'string
  :safe (lambda (x) (stringp x)))

(defcustom verilog-ext-eglot-svlangserver-disableCompletionProvider nil
  "Disable auto completion provided by the language server."
  :group 'verilog-ext-eglot
  :type 'boolean
  :safe (lambda (x) (booleanp x)))

(defcustom verilog-ext-eglot-svlangserver-disableHoverProvider nil
  "Disable hover over help provided by the language server."
  :group 'verilog-ext-eglot
  :type 'boolean
  :safe (lambda (x) (booleanp x)))

(defcustom verilog-ext-eglot-svlangserver-disableSignatureHelpProvider nil
  "Disable signature help provided by the language server."
  :group 'verilog-ext-eglot
  :type 'boolean
  :safe (lambda (x) (booleanp x)))

(defcustom verilog-ext-eglot-svlangserver-disableLinting nil
  "Disable verilator linting."
  :group 'verilog-ext-eglot
  :type 'boolean
  :safe (lambda (x) (booleanp x)))


(defun verilog-ext-eglot-svlangserver-configuration ()
  "Configure settings for svlangserver with `eglot'.
Configure in the same way as for `lsp-verilog'."
  (setq eglot-workspace-configuration
        `((:systemverilog
           (:includeIndexing ,verilog-ext-eglot-svlangserver-includeIndexing)
           (:excludeIndexing ,verilog-ext-eglot-svlangserver-excludeIndexing)
           (:defines ,verilog-ext-eglot-svlangserver-defines)
           (:launchConfiguration ,verilog-ext-eglot-svlangserver-launchConfiguration)
           (:lintOnUnsaved ,verilog-ext-eglot-svlangserver-lintOnUnsaved)
           (:formatCommand ,verilog-ext-eglot-svlangserver-formatCommand)
           (:disableCompletionProvider ,verilog-ext-eglot-svlangserver-disableCompletionProvider)
           (:disableHoverProvider ,verilog-ext-eglot-svlangserver-disableHoverProvider)
           (:disableSignatureHelpProvider ,verilog-ext-eglot-svlangserver-disableSignatureHelpProvider)
           (:disableLinting ,verilog-ext-eglot-svlangserver-disableLinting)))))

(defun verilog-ext-eglot-svlangserver-command (command &optional args)
  "Execute svlangserver COMMAND with ARGS with `eglot'."
  (let ((eglot-server (eglot-current-server))
        (verilog-mode-ls (car (alist-get 'verilog-mode eglot-server-programs)))
        (verilog-ts-mode-ls (car (alist-get 'verilog-ts-mode eglot-server-programs))))
    (unless eglot-server
      (user-error "Couldn't find (eglot-current-server), is eglot enabled?"))
    (unless (and (string= verilog-mode-ls "svlangserver")
                 (string= verilog-ts-mode-ls "svlangserver"))
      (user-error "Ve-svlangserver not configured as current server for eglot"))
    (eglot-execute-command (eglot-current-server) command args)
    (message "Ran svlangserver command: %s" command)))

(defun verilog-ext-eglot-svlangserver-build-index ()
  "Execute command to build index with svlangserver."
  (interactive)
  (verilog-ext-eglot-svlangserver-command "systemverilog.build_index"))

(defun verilog-ext-eglot-svlangserver-report-hierarchy ()
  "Execute command to report hierarchy of current buffer module with svlangserver."
  (interactive)
  (verilog-ext-eglot-svlangserver-command "systemverilog.report_hierarchy" (vector (verilog-ext-select-file-module))))

;;; Set server
(defun verilog-ext-eglot-set-server (server-id)
  "Configure Verilog for `eglot' with SERVER-ID server.
Override any previous configuration for `verilog-mode' and `verilog-ts-mode'."
  (interactive (list (intern (completing-read "Server-id: " verilog-ext-lsp-server-ids nil t))))
  (let ((cmd (car (alist-get server-id verilog-ext-lsp-available-servers))))
    (unless cmd
      (error "%s not recognized as a supported server" server-id))
    (if (not (executable-find (if (listp cmd)
                                  (car cmd)
                                cmd)))
        (message "%s not in $PATH, skipping config..." server-id)
      ;; Else configure available server
      (dolist (mode '(verilog-mode verilog-ts-mode))
        (setq eglot-server-programs (assq-delete-all mode eglot-server-programs))
        (if (listp cmd)
            (push `(,mode ,@cmd) eglot-server-programs)
          (push `(,mode ,cmd) eglot-server-programs)))
      ;; Additional settings depending on chosen server-id
      (when (equal server-id 've-svlangserver)
        (dolist (hook '(verilog-mode-hook verilog-ts-mode-hook))
          (add-hook hook #'verilog-ext-eglot-svlangserver-configuration)))
      ;; Some reporting
      (message "[verilog-ext eglot]: %s" server-id))))


(provide 'verilog-ext-eglot)

;;; verilog-ext-eglot.el ends here
