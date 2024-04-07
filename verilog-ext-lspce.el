;;; verilog-ext-lspce.el --- Verilog-ext lspce setup  -*- lexical-binding: t -*-

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

(require 'lspce nil :noerror) ; Set to :noerror since `lspce' is not available in MELPA
(require 'verilog-ext-utils)

(defvar verilog-ext-lspce-default-server 've-svlangserver)

;;;; svlangserver
;; These customization values are copied from `lsp-verilog' to make `lspce'
;; config independent from `lsp-mode'.
(defgroup verilog-ext-lspce nil
  "Verilog-ext lspce."
  :group 'verilog-ext
  :link '(url-link "https://github.com/imc-trading/svlangserver"))

(defcustom verilog-ext-lspce-svlangserver-includeIndexing '["**/*.{sv,svh}"]
  "Files included for indexing (glob pattern)."
  :group 'verilog-ext-lspce
  :type '(lsp-repeatable-vector string)
  :safe (lambda (x) (seq-every-p #'stringp x)))

(defcustom verilog-ext-lspce-svlangserver-excludeIndexing '["test/**/*.{sv,svh}"]
  "Files excluded for indexing (glob pattern)."
  :group 'verilog-ext-lspce
  :type '(lsp-repeatable-vector string)
  :safe (lambda (x) (seq-every-p #'stringp x)))

(defcustom verilog-ext-lspce-svlangserver-defines nil
  "Defines needed for linting."
  :group 'verilog-ext-lspce
  :type '(lsp-repeatable-vector string)
  :safe (lambda (x) (seq-every-p #'stringp x)))

(defcustom verilog-ext-lspce-svlangserver-launchConfiguration "verilator -sv --lint-only -Wall"
  "Verilator command used for linting."
  :group 'verilog-ext-lspce
  :type 'string
  :safe (lambda (x) (stringp x)))

(defcustom verilog-ext-lspce-svlangserver-lintOnUnsaved t
  "Enable linting on unsaved files."
  :group 'verilog-ext-lspce
  :type 'boolean
  :safe (lambda (x) (booleanp x)))

(defcustom verilog-ext-lspce-svlangserver-formatCommand "verible-verilog-format"
  "Verible verilog format command."
  :group 'verilog-ext-lspce
  :type 'string
  :safe (lambda (x) (stringp x)))

(defcustom verilog-ext-lspce-svlangserver-disableCompletionProvider nil
  "Disable auto completion provided by the language server."
  :group 'verilog-ext-lspce
  :type 'boolean
  :safe (lambda (x) (booleanp x)))

(defcustom verilog-ext-lspce-svlangserver-disableHoverProvider nil
  "Disable hover over help provided by the language server."
  :group 'verilog-ext-lspce
  :type 'boolean
  :safe (lambda (x) (booleanp x)))

(defcustom verilog-ext-lspce-svlangserver-disableSignatureHelpProvider nil
  "Disable signature help provided by the language server."
  :group 'verilog-ext-lspce
  :type 'boolean
  :safe (lambda (x) (booleanp x)))

(defcustom verilog-ext-lspce-svlangserver-disableLinting nil
  "Disable verilator linting."
  :group 'verilog-ext-lspce
  :type 'boolean
  :safe (lambda (x) (booleanp x)))


(defun verilog-ext-lspce-svlangserver-initializationOptions ()
  "Configure settings for svlangserver with `lspce'."
  (let ((options (make-hash-table :test #'equal)))
    (lspce--add-option "settings.systemverilog.includeIndexing" verilog-ext-lspce-svlangserver-includeIndexing options)
    (lspce--add-option "settings.systemverilog.excludeIndexing" verilog-ext-lspce-svlangserver-excludeIndexing options)
    (lspce--add-option "settings.systemverilog.defines" verilog-ext-lspce-svlangserver-defines options)
    (lspce--add-option "settings.systemverilog.launchConfiguration" verilog-ext-lspce-svlangserver-launchConfiguration options)
    (lspce--add-option "settings.systemverilog.lintOnUnsaved" verilog-ext-lspce-svlangserver-lintOnUnsaved options)
    (lspce--add-option "settings.systemverilog.formatCommand" verilog-ext-lspce-svlangserver-formatCommand options)
    (lspce--add-option "settings.systemverilog.disableCompletionProvider" verilog-ext-lspce-svlangserver-disableCompletionProvider options)
    (lspce--add-option "settings.systemverilog.disableHoverProvider" verilog-ext-lspce-svlangserver-disableHoverProvider options)
    (lspce--add-option "settings.systemverilog.disableSignatureHelpProvider" verilog-ext-lspce-svlangserver-disableSignatureHelpProvider options)
    (lspce--add-option "settings.systemverilog.disableLinting" verilog-ext-lspce-svlangserver-disableLinting options)))

(defun verilog-ext-lspce-svlangserver-command (command &optional args)
  "Execute svlangserver COMMAND with ARGS with `lspce'."
  (unless (featurep 'lspce)
    (user-error "lspce not available: check README.md on https://github.com/zbelial/lspce"))
  (lspce--execute-command command args)
  (message "Cmd: %s: check `lspce' log (previously set via `lspce-set-log-file')" command))

(defun verilog-ext-lspce-svlangserver-build-index ()
  "Execute command to build index with svlangserver."
  (interactive)
  (verilog-ext-lspce-svlangserver-command "systemverilog.build_index"))

(defun verilog-ext-lspce-svlangserver-report-hierarchy ()
  "Execute command to report hierarchy of current buffer module with svlangserver."
  (interactive)
  (verilog-ext-lspce-svlangserver-command "systemverilog.report_hierarchy" (vector (verilog-ext-select-file-module))))


;;; Set server
(defun verilog-ext-lspce-set-server (server-id)
  "Configure Verilog for `lspce' with SERVER-ID server.
Override any previous configuration for `verilog-mode' and `verilog-ts-mode'."
  (interactive (list (intern (completing-read "Server-id: " verilog-ext-lsp-server-ids nil t))))
  (let* ((cmd (car (alist-get server-id verilog-ext-lsp-available-servers)))
         (settings (when (eq server-id 've-svlangserver)
                     'verilog-ext-lspce-svlangserver-initializationOptions)))
    (unless (featurep 'lspce)
      (user-error "lspce not available: check README.md on https://github.com/zbelial/lspce"))
    (unless cmd
      (error "%s not recognized as a supported server" server-id))
    (if (not (executable-find (if (listp cmd)
                                  (car cmd)
                                cmd)))
        (message "%s not in $PATH, skipping config..." server-id)
      ;; Else configure available server
      (setq lspce-server-programs (assoc-delete-all "verilog" lspce-server-programs))
      (if (listp cmd)
          (push `("verilog" ,(car cmd) ,(cadr cmd) ,settings) lspce-server-programs)
        (push `("verilog" ,cmd "" ,settings) lspce-server-programs))
      ;; Some reporting
      (message "[verilog-ext lspce]: %s" server-id))))


(provide 'verilog-ext-lspce)

;;; verilog-ext-lspce.el ends here

;; Silence all the lspce byte-compiler warnings:
;;
;; Local Variables:
;; byte-compile-warnings: (not unresolved free-vars)
;; End:

