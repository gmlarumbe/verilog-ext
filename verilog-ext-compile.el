;;; verilog-ext-compile.el --- Verilog-ext Compilation Utils -*- lexical-binding: t -*-

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

;; Compilation-related SystemVerilog functions.
;;
;; This file provides functions to perform compilations with syntax highlighting
;; and jump to error based on `compilation-mode':
;;
;; - Interactive functions examples:
;;   - `verilog-ext-compile-project': compile using :compile-cmd of `verilog-ext-project-alist'
;;
;; - Non-interactive function usage examples:
;;   - (verilog-ext-compile "make")
;;   - (verilog-ext-compile-verilator (concat "verilator --lint-only " buffer-file-name))
;;   - (verilog-ext-compile-iverilog (concat "iverilog " buffer-file-name))
;;   - (verilog-ext-compile-verible (concat "verible-verilog-lint " buffer-file-name))
;;   - (verilog-ext-compile-slang (concat "slang --color-diagnostics=false " buffer-file-name))
;;   - (verilog-ext-compile-svlint (concat "svlint -1 " buffer-file-name))
;;   - (verilog-ext-compile-surelog (concat "surelog -parseonly " buffer-file-name))
;;
;; It also includes a function to preprocess current buffer: `verilog-ext-preprocess'

;;; Code:

(require 'verilog-mode)
(require 'verilog-ext-utils)
(require 'make-mode)


(defgroup verilog-ext-compile nil
  "Verilog-ext compilation."
  :group 'verilog-ext)

(defconst verilog-ext-compile-msg-code-face 'verilog-ext-compile-msg-code-face)
(defface verilog-ext-compile-msg-code-face
  '((t (:inherit font-lock-comment-face)))
  "Face for compilation message codes."
  :group 'verilog-ext-compile)

(defconst verilog-ext-compile-bin-face 'verilog-ext-compile-bin-face)
(defface verilog-ext-compile-bin-face
  '((t (:inherit font-lock-function-name-face)))
  "Face for compilation binaries."
  :group 'verilog-ext-compile)


;;;; Compilation-re
(defconst verilog-ext-compile-filename-re "[a-zA-Z0-9-_\\.\\/]+")

(defconst verilog-ext-compile-verilator-re
  `((verilator-error   ,(concat "^%\\(?1:Error: Internal Error\\): \\(?2:" verilog-ext-compile-filename-re "\\):\\(?3:[0-9]+\\):\\(?4:[0-9]+\\)") 2 3 4 2 nil (1 compilation-error-face))
    (verilator-error2  ,(concat "^%\\(?1:Error\\): \\(?2:" verilog-ext-compile-filename-re "\\):\\(?3:[0-9]+\\):\\(?4:[0-9]+\\): ") 2 3 4 2 nil (1 compilation-error-face))
    (verilator-error3  ,(concat "^%\\(?1:Error\\)-\\(?2:[^:]+\\): \\(?3:" verilog-ext-compile-filename-re "\\):\\(?4:[0-9]+\\):\\(?5:[0-9]+\\): ") 3 4 5 2 nil (1 compilation-error-face) (2 verilog-ext-compile-msg-code-face))
    (verilator-error4  "^%\\(?1:Error\\): " nil nil nil 2 nil (1 compilation-error-face))
    (verilator-warning ,(concat "^%\\(?1:Warning\\)-\\(?2:[^:]+\\): \\(?3:" verilog-ext-compile-filename-re "\\):\\(?4:[0-9]+\\):\\(?5:[0-9]+\\): ") 3 4 5 1 nil (1 compilation-warning-face) (2 verilog-ext-compile-msg-code-face)))
  "Verilator regexps.")

(defconst verilog-ext-compile-iverilog-re
  '((iverilog-unsupported  "\\(?1:.*\\):\\(?2:[0-9]+\\):.*sorry:" 1 2 nil 0 nil (1 compilation-info-face) (2 compilation-line-face))
    (iverilog-warning      "\\(?1:.*\\):\\(?2:[0-9]+\\):.*warning:" 1 2 nil 1 nil (1 compilation-warning-face) (2 compilation-line-face))
    (iverilog-warning2     "^\\(?1:warning\\):" 1 nil nil 1 nil )
    (iverilog-error        "\\(?1:.*\\):\\(?2:[0-9]+\\):.*error:" 1 2 nil 2 nil (1 compilation-error-face) (2 compilation-line-face))
    (iverilog-error2       "\\(?1:.*\\):\\(?2:[0-9]+\\):.*syntax error" 1 2 nil 2 nil (1 compilation-error-face) (2 compilation-line-face))
    (vvp-warning           "^\\(?1:WARNING\\): \\(?2:.*\\):\\(?3:[0-9]+\\):" 2 3 nil 1 nil (1 compilation-warning-face) (2 compilation-warning-face) (3 compilation-line-face))
    (vvp-error             "^\\(?1:ERROR\\): \\(?2:.*\\):\\(?3:[0-9]+\\):" 2 3 nil 2 nil (1 compilation-warning-face) (2 compilation-warning-face) (3 compilation-line-face))
    (vvp-info              "^\\(?1:LXT2 info\\):" 1 nil nil 0 nil))
  "Icarus Verilog regexps.")

(defconst verilog-ext-compile-verible-re
  `(;; Verible regexps are common for error/warning/infos. It is important to declare errors before warnings below
    (verible-error   ,(concat "^\\(?1:" verilog-ext-compile-filename-re "\\):\\(?2:[0-9]+\\):\\(?3:[0-9]+\\)-*[0-9]*:\\s-*" "syntax error at ") 1 2 3 2 nil)
    (verible-error2  ,(concat "^\\(?1:" verilog-ext-compile-filename-re "\\):\\(?2:[0-9]+\\):\\(?3:[0-9]+\\)-*[0-9]*:\\s-*" "preprocessing error at ") 1 2 3 2 nil)
    (verible-warning ,(concat "^\\(?1:" verilog-ext-compile-filename-re "\\):\\(?2:[0-9]+\\):\\(?3:[0-9]+\\)-*[0-9]*:\\s-*") 1 2 3 1 nil))
  "Verible regexps.")

(defconst verilog-ext-compile-slang-re
  `((slang-error   ,(concat "\\(?1:" verilog-ext-compile-filename-re "\\):\\(?2:[0-9]+\\):\\(?3:[0-9]+\\): error: ") 1 2 3 2 nil)
    (slang-warning ,(concat "\\(?1:" verilog-ext-compile-filename-re "\\):\\(?2:[0-9]+\\):\\(?3:[0-9]+\\): warning: ") 1 2 3 1 nil)
    (slang-info    ,(concat "\\(?1:" verilog-ext-compile-filename-re "\\):\\(?2:[0-9]+\\):\\(?3:[0-9]+\\): note: ") 1 2 3 0 nil))
  "Slang regexps.")

(defconst verilog-ext-compile-svlint-re
  `((svlint-error ,(concat "^\\(?1:Fail\\)\\s-*\\(?2:" verilog-ext-compile-filename-re "\\):\\(?3:[0-9]+\\):\\(?4:[0-9]+\\)\\s-*.*hint: ") 2 3 4 2 nil (1 compilation-error-face))
    (svlint-error2 ,(concat "^\\(?1:Error\\)\\s-*\\(?2:" verilog-ext-compile-filename-re "\\):\\(?3:[0-9]+\\):\\(?4:[0-9]+\\)\\s-*.*hint: ") 2 3 4 2 nil (1 compilation-error-face)))
  "Svlint regexps.")

(defconst verilog-ext-compile-surelog-re
  `((surelog-fatal    ,(concat "^\\[\\(?1:FAT:\\(?2:[A-Z0-9]+\\)\\)\\]\\s-+\\(?3:" verilog-ext-compile-filename-re "\\):\\(?4:[0-9]+\\):\\(?5:[0-9]+\\):\\s-+") 3 4 5 2 nil (1 compilation-error-face) (2 verilog-ext-compile-msg-code-face))
    (surelog-fatal2   ,(concat "^\\[\\(?1:FAT:\\(?2:[A-Z0-9]+\\)\\)\\]\\s-+") nil nil nil 2 nil (1 compilation-info-face) (2 verilog-ext-compile-msg-code-face))
    (surelog-error    ,(concat "^\\[\\(?1:ERR:\\(?2:[A-Z0-9]+\\)\\)\\]\\s-+\\(?3:" verilog-ext-compile-filename-re "\\):\\(?4:[0-9]+\\):\\(?5:[0-9]+\\):\\s-+") 3 4 5 2 nil (1 compilation-error-face) (2 verilog-ext-compile-msg-code-face))
    (surelog-error2   ,(concat "^\\[\\(?1:ERR:\\(?2:[A-Z0-9]+\\)\\)\\]\\s-+") nil nil nil 2 nil (1 compilation-info-face) (2 verilog-ext-compile-msg-code-face))
    (surelog-syntax   ,(concat "^\\[\\(?1:SNT:\\(?2:[A-Z0-9]+\\)\\)\\]\\s-+\\(?3:" verilog-ext-compile-filename-re "\\):\\(?4:[0-9]+\\):\\(?5:[0-9]+\\):\\s-+") 3 4 5 2 nil (1 compilation-error-face) (2 verilog-ext-compile-msg-code-face))
    (surelog-warning  ,(concat "^\\[\\(?1:WRN:\\(?2:[A-Z0-9]+\\)\\)\\]\\s-+\\(?3:" verilog-ext-compile-filename-re "\\):\\(?4:[0-9]+\\):\\(?5:[0-9]+\\):\\s-+") 3 4 5 1 nil (1 compilation-warning-face) (2 verilog-ext-compile-msg-code-face))
    (surelog-warning2 ,(concat "^\\[\\(?1:WRN:\\(?2:[A-Z0-9]+\\)\\)\\]\\s-+") nil nil nil 1 nil (1 compilation-warning-face) (2 verilog-ext-compile-msg-code-face))
    (surelog-note     ,(concat "^\\[\\(?1:NTE:\\(?2:[A-Z0-9]+\\)\\)\\]\\s-+\\(?3:" verilog-ext-compile-filename-re "\\):\\(?4:[0-9]+\\):\\(?5:[0-9]+\\):\\s-+") 3 4 5 0 nil (1 compilation-info-face) (2 verilog-ext-compile-msg-code-face))
    (surelog-note2    ,(concat "^\\[\\(?1:NTE:\\(?2:[A-Z0-9]+\\)\\)\\]\\s-+") nil nil nil 0 nil (1 compilation-info-face) (2 verilog-ext-compile-msg-code-face))
    (surelog-info     ,(concat "^\\[\\(?1:INF:\\(?2:[A-Z0-9]+\\)\\)\\]\\s-+\\(?3:" verilog-ext-compile-filename-re "\\):\\(?4:[0-9]+\\):\\(?5:[0-9]+\\):\\s-+") 3 4 5 0 nil (1 compilation-info-face) (2 verilog-ext-compile-msg-code-face))
    (surelog-info2    ,(concat "^\\[\\(?1:INF:\\(?2:[A-Z0-9]+\\)\\)\\]\\s-+") nil nil nil 0 nil (1 compilation-info-face) (2 verilog-ext-compile-msg-code-face)))
  "Surelog regexps.")

(defconst verilog-ext-compile-all-re (append verilog-ext-compile-verilator-re
                                             verilog-ext-compile-iverilog-re
                                             verilog-ext-compile-verible-re
                                             verilog-ext-compile-slang-re
                                             verilog-ext-compile-svlint-re
                                             verilog-ext-compile-surelog-re))

(defconst verilog-ext-compile-verilator-buf "*verilator*")
(defconst verilog-ext-compile-iverilog-buf "*iverilog*")
(defconst verilog-ext-compile-verible-buf "*verible*")
(defconst verilog-ext-compile-slang-buf "*slang*")
(defconst verilog-ext-compile-svlint-buf "*svlint*")
(defconst verilog-ext-compile-surelog-buf "*surelog*")
(defconst verilog-ext-compile-all-buf "*verilog-ext-compile")

;;;; Compilation-modes and macros
(defmacro verilog-ext-compile-define-mode (name &rest args)
  "Macro to define a compilation derived mode for a Verilog error regexp.

NAME is the name of the created compilation mode.

ARGS is a property list with :desc, :docstring, :compile-re and :buf-name."
  (declare (indent 1) (debug 1))
  (let ((desc (plist-get args :desc))
        (docstring (plist-get args :docstring))
        (compile-re (plist-get args :compile-re))
        (buf-name (plist-get args :buf-name)))
    `(define-compilation-mode ,name ,desc ,docstring
       (setq-local compilation-error-regexp-alist (mapcar #'car ,compile-re))
       (setq-local compilation-error-regexp-alist-alist ,compile-re)
       (when ,buf-name
         (rename-buffer ,buf-name))
       (setq truncate-lines t)
       (goto-char (point-max)))))

(defmacro verilog-ext-compile-define-fn (name &rest args)
  "Macro to define a function to compile with error regexp highlighting.

Function will be callable by NAME.

ARGS is a property list."
  (declare (indent 1) (debug 1))
  (let ((docstring (plist-get args :docstring))
        (buf (plist-get args :buf))
        (comp-mode (plist-get args :comp-mode)))
    `(defun ,name (command)
       ,docstring
       (when (and ,buf (get-buffer ,buf))
         (if (y-or-n-p (format "Buffer %s is in use, kill its process and start new compilation?" ,buf))
             (kill-buffer ,buf)
           (user-error "Aborted")))
       (compile command)
       (,comp-mode))))

(verilog-ext-compile-define-mode verilog-ext-compile-verilator-mode
  :desc "Verilator"
  :docstring "Verilator Compilation mode."
  :compile-re verilog-ext-compile-verilator-re
  :buf-name verilog-ext-compile-verilator-buf)

(verilog-ext-compile-define-fn verilog-ext-compile-verilator
  :docstring "Compile Verilator COMMAND with error regexp highlighting."
  :buf verilog-ext-compile-verilator-buf
  :comp-mode verilog-ext-compile-verilator-mode)

(verilog-ext-compile-define-mode verilog-ext-compile-iverilog-mode
  :desc "Iverilog"
  :docstring "Iverilog Compilation mode."
  :compile-re verilog-ext-compile-iverilog-re
  :buf-name verilog-ext-compile-iverilog-buf)

(verilog-ext-compile-define-fn verilog-ext-compile-iverilog
  :docstring "Compile Iverilog COMMAND with error regexp highlighting."
  :buf verilog-ext-compile-iverilog-buf
  :comp-mode verilog-ext-compile-iverilog-mode)

(verilog-ext-compile-define-mode verilog-ext-compile-verible-mode
  :desc "Verible"
  :docstring "Verible Compilation mode."
  :compile-re verilog-ext-compile-verible-re
  :buf-name verilog-ext-compile-verible-buf)

(verilog-ext-compile-define-fn verilog-ext-compile-verible
  :docstring "Compile Verible COMMAND with error regexp highlighting."
  :buf verilog-ext-compile-verible-buf
  :comp-mode verilog-ext-compile-verible-mode)

(verilog-ext-compile-define-mode verilog-ext-compile-slang-mode
  :desc "Slang"
  :docstring "Slang Compilation mode."
  :compile-re verilog-ext-compile-slang-re
  :buf-name verilog-ext-compile-slang-buf)

(verilog-ext-compile-define-fn verilog-ext-compile-slang
  :docstring "Compile Slang COMMAND with error regexp highlighting."
  :buf verilog-ext-compile-slang-buf
  :comp-mode verilog-ext-compile-slang-mode)

(verilog-ext-compile-define-mode verilog-ext-compile-svlint-mode
  :desc "Svlint"
  :docstring "Svlint Compilation mode."
  :compile-re verilog-ext-compile-svlint-re
  :buf-name verilog-ext-compile-svlint-buf)

(verilog-ext-compile-define-fn verilog-ext-compile-svlint
  :docstring "Compile Svlint COMMAND with error regexp highlighting."
  :buf verilog-ext-compile-svlint-buf
  :comp-mode verilog-ext-compile-svlint-mode)

(verilog-ext-compile-define-mode verilog-ext-compile-surelog-mode
  :desc "Surelog"
  :docstring "Surelog Compilation mode."
  :compile-re verilog-ext-compile-surelog-re
  :buf-name verilog-ext-compile-surelog-buf)

(verilog-ext-compile-define-fn verilog-ext-compile-surelog
  :docstring "Compile Surelog COMMAND with error regexp highlighting."
  :buf verilog-ext-compile-surelog-buf
  :comp-mode verilog-ext-compile-surelog-mode)

(verilog-ext-compile-define-mode verilog-ext-compile-mode
  :desc "Verilog"
  :docstring "All Verilog supported tools Compilation mode."
  :compile-re verilog-ext-compile-all-re
  :buf-name verilog-ext-compile-all-buf)

(verilog-ext-compile-define-fn verilog-ext-compile
  :docstring "Compile Verilog COMMAND with error regexp highlighting."
  :buf verilog-ext-compile-all-buf
  :comp-mode verilog-ext-compile-mode)


;;;; Compilation interactive functions
(defun verilog-ext-compile-makefile ()
  "Prompt to available Makefile targets and compile."
  (interactive)
  (let ((makefile (file-name-concat (verilog-ext-buffer-proj-root) "Makefile"))
        (makefile-need-target-pickup t) ; Force refresh of makefile targets
        target cmd)
    (unless (file-exists-p makefile)
      (error "%s does not exist!" makefile))
    (with-temp-buffer
      (insert-file-contents makefile)
      (makefile-pickup-targets)
      (setq target (completing-read "Target: " makefile-target-table)))
    (setq cmd (mapconcat #'identity `("cd" ,(verilog-ext-buffer-proj-root) "&&" "make" ,target) " "))
    (verilog-ext-compile cmd)))

(defun verilog-ext-compile-project ()
  "Compile using :compile-cmd of `verilog-ext-project-alist' project.

Depending on the command, different syntax highlight will be applied.

The function will detect any of the supported compilation error parsers and will
set the appropriate mode."
  (interactive)
  (let* ((proj (verilog-ext-buffer-proj))
         (compile-cmd (verilog-ext-proj-compile-cmd proj))
         (cmd-list (if (not compile-cmd)
                       (error "You first need to set `:compile-cmd' for current project [%s] in `verilog-ext-project-alist'" proj)
                     (split-string (verilog-ext-proj-compile-cmd))))
         (cmd-args (cdr cmd-list))
         (cmd-bin (car cmd-list))
         (fn (pcase cmd-bin
               ("verilator" #'verilog-ext-compile-verilator)
               ("iverilog" #'verilog-ext-compile-iverilog)
               ("slang" #'verilog-ext-compile-slang)
               ("svlint" #'verilog-ext-compile-svlint)
               ("surelog" #'verilog-ext-compile-surelog)
               ("verible-verilog-lint" #'verilog-ext-compile-verible)
               (_ #'verilog-ext-compile)))
         (cmd-processed (cond (;; For svlint, make sure the -1 arg is present
                               (string= cmd-bin "svlint")
                               (if (member "-1" cmd-args)
                                   compile-cmd
                                 (mapconcat #'identity `(,cmd-bin "-1" ,@cmd-args) " ")))
                              ;; For slang make sure that there is no colored output
                              ((string= cmd-bin "slang")
                               (if (member "--color-diagnostics=false" cmd-args)
                                   compile-cmd
                                 (mapconcat #'identity `(,cmd-bin "--color-diagnostics=false" ,@cmd-args) " ")))
                              ;; For the rest use the provided command
                              (t
                               compile-cmd)))
         (cmd (mapconcat #'identity `("cd" ,(verilog-ext-buffer-proj-root proj) "&&" ,cmd-processed) " ")))
    (funcall fn cmd)))


;;;; Preprocess
(defun verilog-ext-preprocess ()
  "Preprocess current file.

Choose among available programs and update `verilog-preprocessor' variable.

Supports verilator, vppreproc and iverilog."
  (interactive)
  (let ((tools-available (seq-filter (lambda (bin)
                                       (executable-find bin))
                                     '("verilator" "iverilog" "vppreproc"))))
    (pcase (completing-read "Select tool: " tools-available)
      ;; Verilator
      ("verilator" (setq verilog-preprocessor "verilator -E __FLAGS__ __FILE__"))
      ;; Verilog-Perl
      ("vppreproc" (setq verilog-preprocessor "vppreproc __FLAGS__ __FILE__"))
      ;; Icarus Verilog:  `iverilog' command syntax requires writing to an output file (defaults to a.out).
      ("iverilog" (let* ((filename-sans-ext (file-name-sans-extension (file-name-nondirectory (buffer-file-name))))
                         (iver-out-file (concat (temporary-file-directory) filename-sans-ext "_pp_iver.sv")))
                    (setq verilog-preprocessor (concat "iverilog -E -o" iver-out-file " __FILE__ && "
                                                       "echo \"\" && " ; Add blank line between run command and first preprocessed line
                                                       "cat " iver-out-file)))))
    (verilog-preprocess)
    (pop-to-buffer "*Verilog-Preprocessed*")))



(provide 'verilog-ext-compile)

;;; verilog-ext-compile.el ends here
