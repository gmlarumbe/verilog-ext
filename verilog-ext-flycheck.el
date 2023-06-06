;;; verilog-ext-flycheck.el --- Verilog-ext Flycheck Setup  -*- lexical-binding: t -*-

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

;; Add support for the following linters in `flycheck':
;;  - verilator (overrides default parameters)
;;  - iverilog
;;  - verible
;;  - slang
;;  - svlint
;;  - surelog
;;  - Cadence HAL

;;; Code:

(require 'flycheck)
(require 'verilog-ext-utils)

(defgroup verilog-ext-flycheck nil
  "Verilog-ext flycheck."
  :group 'verilog-ext)

(defcustom verilog-ext-flycheck-use-open-buffers t
  "Set to non-nil to use list of open Verilog buffers/dirs for linters."
  :type 'boolean
  :group 'verilog-ext-flycheck)

(defcustom verilog-ext-flycheck-verilator-include-path nil
  "List of include paths for verilator linter."
  :type '(repeat string)
  :group 'verilog-ext-flycheck)

(defcustom verilog-ext-flycheck-verilator-file-list nil
  "List of extra files besides current buffer for verilator linter."
  :type '(repeat string)
  :group 'verilog-ext-flycheck)

(defcustom verilog-ext-flycheck-iverilog-include-path nil
  "List of include paths for iverilog linter."
  :type '(repeat string)
  :group 'verilog-ext-flycheck)

(defcustom verilog-ext-flycheck-iverilog-file-list nil
  "List of extra files besides current buffer for iverilog linter."
  :type '(repeat string)
  :group 'verilog-ext-flycheck)

(defcustom verilog-ext-flycheck-verible-rules nil
  "List of strings containing verible liner rules.
Use - or + prefixes depending on enabling/disabling of rules.
https://chipsalliance.github.io/verible/lint.html"
  :type '(repeat string)
  :group 'verilog-ext-flycheck)

(defcustom verilog-ext-flycheck-slang-include-path nil
  "List of include paths for slang linter."
  :type '(repeat string)
  :group 'verilog-ext-flycheck)

(defcustom verilog-ext-flycheck-slang-file-list nil
  "List of extra files besides current buffer for slang linter."
  :type '(repeat string)
  :group 'verilog-ext-flycheck)

(defcustom verilog-ext-flycheck-svlint-include-path nil
  "List of include paths for svlint linter.

Variables is needed since svlint doesn't allow both source and -f command file
at the same time."
  :type '(repeat string)
  :group 'verilog-ext-flycheck)

(defcustom verilog-ext-flycheck-svlint-file-list nil
  "List of include paths for svlint linter.

Variable is needed since svlint doesn't allow both source and -f command file
at the same time."
  :type '(repeat string)
  :group 'verilog-ext-flycheck)

(defcustom verilog-ext-flycheck-surelog-include-path nil
  "List of include paths for surelog linter."
  :type '(repeat string)
  :group 'verilog-ext-flycheck)

(defcustom verilog-ext-flycheck-surelog-file-list nil
  "List of extra files besides current buffer for surelog linter."
  :type '(repeat string)
  :group 'verilog-ext-flycheck)


(defvar verilog-ext-flycheck-linter 'verilog-verilator
  "Verilog-ext flycheck linter.")

(defconst verilog-ext-flycheck-linters '(verilog-verible
                                         verilog-verilator
                                         verilog-slang
                                         verilog-surelog
                                         verilog-iverilog
                                         verilog-svlint
                                         verilog-cadence-hal)
  "List of supported linters.")


(defvar verilog-ext-flycheck-dirs nil "List of open dirs for `verilog-ext-flycheck'.")
(defvar verilog-ext-flycheck-files nil "List of open files for `verilog-ext-flycheck'.")
(defconst verilog-ext-flycheck-commands-file-name "commands.f")


(defun verilog-ext-flycheck-setup-linter (linter)
  "Setup LINTER before enabling flycheck."
  (pcase linter
    ('verilog-verible
     (verilog-ext-flycheck-verible-rules-fmt))
    ('verilog-cadence-hal
     (verilog-ext-flycheck-setup-hal))))

(defun verilog-ext-flycheck-set-linter (&optional linter)
  "Set LINTER as default and enable it if flycheck is on."
  (interactive)
  (unless linter
    (setq linter (intern (completing-read "Select linter: " verilog-ext-flycheck-linters nil t))))
  (unless (member linter verilog-ext-flycheck-linters)
    (error "Linter %s not available" linter))
  ;; Set it at the head of the list
  (delete linter flycheck-checkers)
  (add-to-list 'flycheck-checkers linter)
  (verilog-ext-flycheck-setup-linter linter)
  (setq verilog-ext-flycheck-linter linter) ; Save state for reporting
  ;; Refresh linter if in a verilog buffer
  (when (eq major-mode 'verilog-mode)
    (flycheck-select-checker linter))
  (message "Linter set to: %s " linter))

(defun verilog-ext-flycheck-setup ()
  "Add available linters from `verilog-ext-flycheck-linters' and set default one."
  (interactive)
  (dolist (checker verilog-ext-flycheck-linters)
    (add-to-list 'flycheck-checkers checker))
  (verilog-ext-flycheck-set-linter verilog-ext-flycheck-linter))

(defun verilog-ext-flycheck-mode (&optional uarg)
  "`flycheck-mode' Verilog wrapper function.
If called with UARG select among available linters and enable flycheck."
  (interactive "P")
  (let (enable)
    (when buffer-read-only
      (error "Flycheck does not work on read-only buffers!"))
    (if uarg
        (progn
          (verilog-ext-flycheck-set-linter)
          (setq enable t))
      (unless flycheck-mode
        (setq enable t)))
    (when (flycheck-disabled-checker-p verilog-ext-flycheck-linter)
      (user-error "[%s] Current checker is disabled by flycheck.\nEnable it with C-u M-x `flycheck-disable-checker'" verilog-ext-flycheck-linter))
    (if enable
        (progn
          (flycheck-mode 1)
          (message "[%s] Flycheck enabled" verilog-ext-flycheck-linter))
      (flycheck-mode -1)
      (message "Flycheck disabled"))))


;;;; Verilator
(flycheck-def-config-file-var flycheck-verilog-verilator-command-file verilog-verilator verilog-ext-flycheck-commands-file-name)

(flycheck-define-checker verilog-verilator
  "A Verilog syntax checker using the Verilator Verilog HDL simulator.

See URL `https://www.veripool.org/wiki/verilator'."
  ;; https://verilator.org/guide/latest/exe_verilator.html
  ;;   The three flags -y, +incdir+<dir> and -I<dir> have similar effect;
  ;;   +incdir+<dir> and -y are fairly standard across Verilog tools while -I<dir> is used by many C++ compilers.
  :command ("verilator" "--lint-only" "-Wall" "-Wno-fatal" "--timing"
            "--bbox-unsup" ; Blackbox unsupported language features to avoid errors on verification sources
            "--bbox-sys"  ;  Blackbox unknown $system calls
            (option-list "-I" verilog-ext-flycheck-verilator-include-path concat)
            (option-list "-I" verilog-ext-flycheck-dirs concat)
            (config-file "-f" flycheck-verilog-verilator-command-file)
            (eval (remove buffer-file-name verilog-ext-flycheck-verilator-file-list))
            (eval (remove buffer-file-name verilog-ext-flycheck-files))
            source)
  :error-patterns
  ((warning line-start "%Warning-" (zero-or-more not-newline) ": " (file-name) ":" line ":" column ": " (message) line-end)
   (error   line-start "%Error: Internal Error: "                  (file-name) ":" line ":" column ": " (message) line-end)
   (error   line-start "%Error: "                                  (file-name) ":" line ":" column ": " (message) line-end)
   (error   line-start "%Error-"   (zero-or-more not-newline) ": " (file-name) ":" line ":" column ": " (message) line-end))
  :modes (verilog-mode verilog-ts-mode))


;;;; Iverilog
(flycheck-def-config-file-var flycheck-verilog-iverilog-command-file verilog-iverilog verilog-ext-flycheck-commands-file-name)

(flycheck-define-checker verilog-iverilog
  "A Verilog syntax checker using Icarus Verilog.

See URL `http://iverilog.icarus.com/'"
  ;; Limitations found:
  ;;   - The command line -y flag will not search for .sv extensions, even though the -g2012 flag is set.
  ;;   - The +libext+.sv will only work with command files (equivalent to -f in xrun), not with command line arguments.
  ;;      - That means that a file that specifies the libraries/plusargs should be used with the -c <COMMAND_FILE> command line argument.
  :command ("iverilog" "-g2012" "-Wall" "-gassertions" "-t" "null" "-i" ; -i ignores missing modules
            (option-list "-I" verilog-ext-flycheck-iverilog-include-path concat)
            (option-list "-I" verilog-ext-flycheck-dirs concat)
            (config-file "-f" flycheck-verilog-iverilog-command-file)
            (eval (remove buffer-file-name verilog-ext-flycheck-iverilog-file-list))
            (eval (remove buffer-file-name verilog-ext-flycheck-files))
            source)
  :error-patterns
  ((info    (file-name) ":" line ":" (zero-or-more not-newline) "sorry:"   (message) line-end) ; Unsupported
   (warning (file-name) ":" line ":" (zero-or-more not-newline) "warning:" (message) line-end)
   (error   (file-name) ":" line ":" (zero-or-more not-newline) "error:"   (message) line-end)
   (error   (file-name) ":" line ":" (message) line-end)) ; 'syntax error' message (e.g. missing package)
  :modes (verilog-mode verilog-ts-mode))


;;;; Verible
(defvar verilog-ext-flycheck-verible-rules-formatted nil
  "Used as a flycheck argument extracted from `verilog-ext-flycheck-verible-rules'.")

(defun verilog-ext-flycheck-verible-rules-fmt ()
  "Format `verilog-ext-flycheck-verible-rules'.
Pass correct arguments to --rules flycheck checker."
  (setq verilog-ext-flycheck-verible-rules-formatted (mapconcat #'identity verilog-ext-flycheck-verible-rules ",")))


(flycheck-define-checker verilog-verible
  "The Verible project's main mission is to parse SystemVerilog (IEEE 1800-2017)
\(as standardized in the SV-LRM) for a wide variety of applications, including
developer tools.

See URL `https://github.com/chipsalliance/verible'."
  ;; From the documentation:
  ;;   Syntax errors cannot be waived. A common source of syntax errors is if the file is not a standalone Verilog program
  ;;   as defined by the LRM, e.g. a body snippet of a module, class, task, or function. In such cases, the parser can be
  ;;   directed to treat the code as a snippet by selecting a parsing mode, which looks like a comment near the top-of-file
  ;;   like // verilog_syntax: parse-as-module-body.
  :command ("verible-verilog-lint"
            (option "--rules=" verilog-ext-flycheck-verible-rules-formatted concat)
            source)
  :error-patterns
  ;; Verible regexps are common for error/warning/infos. It is important to declare errors before warnings below
  ((error    (file-name) ":" line ":" column (zero-or-more "-") (zero-or-more digit) ":" (zero-or-more blank) "syntax error at "        (message) line-end)
   (error    (file-name) ":" line ":" column (zero-or-more "-") (zero-or-more digit) ":" (zero-or-more blank) "preprocessing error at " (message) line-end)
   (warning  (file-name) ":" line ":" column (zero-or-more "-") (zero-or-more digit) ":" (zero-or-more blank)                           (message) line-end))
  :modes (verilog-mode verilog-ts-mode))


;;;; Slang
(flycheck-def-config-file-var flycheck-verilog-slang-command-file verilog-slang verilog-ext-flycheck-commands-file-name)

(flycheck-define-checker verilog-slang
  "SystemVerilog Language Services.

slang is the fastest and most compliant SystemVerilog frontend (according to the
open source chipsalliance test suite).

See URL `https://github.com/MikePopoloski/slang'."
  :command ("slang"
            "--lint-only"
            "--ignore-unknown-modules"
            "--color-diagnostics=false"
            (option-list "-I" verilog-ext-flycheck-slang-include-path concat)
            (option-list "-I" verilog-ext-flycheck-dirs concat)
            (config-file "-f" flycheck-verilog-slang-command-file)
            (eval (remove buffer-file-name verilog-ext-flycheck-slang-file-list))
            (eval (remove buffer-file-name verilog-ext-flycheck-files))
            source)
  :error-patterns
  ((error   (file-name) ":" line ":" column ": error: "   (message))
   (warning (file-name) ":" line ":" column ": warning: " (message))
   (info    (file-name) ":" line ":" column ": note: "    (message)))
  :modes (verilog-mode verilog-ts-mode))


;;;; Svlint
;; For svlint we prefer using variables since it does not allow both source and -f command file at the same time.
(flycheck-def-config-file-var flycheck-verilog-svlint-config-file verilog-svlint ".svlint.toml")

(flycheck-define-checker verilog-svlint
  "A Verilog syntax checker using svlint.

See URL `https://github.com/dalance/svlint'"
  :command ("svlint"
            "-1" ; one-line output
            "--ignore-include"
            (config-file "-c" flycheck-verilog-svlint-config-file)
            (option-list "-i" verilog-ext-flycheck-svlint-include-path concat)
            (option-list "-i" verilog-ext-flycheck-dirs concat)
            (eval (remove buffer-file-name verilog-ext-flycheck-svlint-file-list))
            (eval (remove buffer-file-name verilog-ext-flycheck-files))
            source)
  :error-patterns
  ((warning line-start "Fail"  (zero-or-more blank) (file-name) ":" line ":" column (zero-or-more blank) (zero-or-more not-newline) "hint: " (message) line-end)
   (error   line-start "Error" (zero-or-more blank) (file-name) ":" line ":" column (zero-or-more blank) (zero-or-more not-newline) "hint: " (message) line-end))
  :modes (verilog-mode verilog-ts-mode))


;;;; Surelog
(defconst verilog-ext-flycheck-surelog-directory "/tmp")

(flycheck-def-config-file-var flycheck-verilog-surelog-command-file verilog-surelog verilog-ext-flycheck-commands-file-name)

(defun verilog-ext-flycheck-surelog-directory-fn (_checker)
  "Return directory where surelog is executed.
slpp_all outputs will be stored at this directory.."
  (let ((dir verilog-ext-flycheck-surelog-directory))
    dir))

(flycheck-define-checker verilog-surelog
  "SystemVerilog 2017 Pre-processor, Parser, Elaborator, UHDM Compiler. Provides
  IEEE Design/TB C/C++ VPI and Python AST API.

See URL `https://github.com/chipsalliance/Surelog'"
  :command ("surelog"
            "-parseonly" ; one-line output
            (option-list "-I" verilog-ext-flycheck-surelog-include-path concat)
            (option-list "-I" verilog-ext-flycheck-dirs concat)
            (config-file "-f" flycheck-verilog-surelog-command-file)
            (eval (remove buffer-file-name verilog-ext-flycheck-surelog-file-list))
            (eval (remove buffer-file-name verilog-ext-flycheck-files))
            source)
  :error-patterns
  ((info    line-start "[INF:" (one-or-more alnum) "] " (file-name) ":" line ":" column ":" blank (message) line-end)
   (info    line-start "[NTE:" (one-or-more alnum) "] " (file-name) ":" line ":" column ":" blank (message) line-end)
   (warning line-start "[WRN:" (one-or-more alnum) "] " (file-name) ":" line ":" column ":" blank (message) line-end)
   (error   line-start "[SNT:" (one-or-more alnum) "] " (file-name) ":" line ":" column ":" blank (message) line-end)
   (error   line-start "[ERR:" (one-or-more alnum) "] " (file-name) ":" line ":" column ":" blank (message) line-end)
   (error   line-start "[FAT:" (one-or-more alnum) "] " (file-name) ":" line ":" column ":" blank (message) line-end))
  :working-directory verilog-ext-flycheck-surelog-directory-fn
  :modes (verilog-mode verilog-ts-mode))


;;;; Cadence HAL
(defvar verilog-ext-flycheck-hal-include-path nil)

(defvar verilog-ext-flycheck-hal-directory   "/tmp")
(defvar verilog-ext-flycheck-hal-log-name    "xrun.log")
(defvar verilog-ext-flycheck-hal-script-name "hal.sh")

(defvar verilog-ext-flycheck-hal-log-path    nil)
(defvar verilog-ext-flycheck-hal-script-path nil)


(defun verilog-ext-flycheck-hal-open-log ()
  "Open xrun log file for debug."
  (interactive)
  (unless verilog-ext-flycheck-hal-log-path
    (error "Flycheck HAL not configured yet"))
  (find-file verilog-ext-flycheck-hal-log-path))

(defun verilog-ext-flycheck-hal-directory-fn (_checker)
  "Return directory where hal is executed.
xcelium.d (INCA_libs) and lint logs will be saved at this path."
  (let ((dir verilog-ext-flycheck-hal-directory))
    dir))

(defun verilog-ext-flycheck-hal-script-create ()
  "Create HAL wrapper script.

This is needed since the output of HAL is written to a logfile and
flycheck parses stdout (didn't find the way to redirect xrun output to stdout).

Plus, the :command key arg of `flycheck-define-command-checker' assumes each
of the strings are arguments.  If something such as \"&&\" \"cat\" is used to
try to display the logfile in stdout , it would throw an xrun fatal error as
\"&&\" would not be recognized as a file."
  (let* ((log-path (file-name-concat verilog-ext-flycheck-hal-directory verilog-ext-flycheck-hal-log-name))
         (script-path (file-name-concat verilog-ext-flycheck-hal-directory verilog-ext-flycheck-hal-script-name))
         (script-code (concat "#!/bin/bash
args=\"${@}\"
xrun -hal $args
cat " log-path "
")))
    (setq verilog-ext-flycheck-hal-log-path log-path)
    (setq verilog-ext-flycheck-hal-script-path script-path)
    (unless (file-exists-p script-path)
      (with-temp-buffer
        (insert script-code)
        (write-file script-path)
        (set-file-modes script-path #o755)))))

(defun verilog-ext-flycheck-setup-hal ()
  "Setup Cadence HAL linter.

Wraps the definition of the flycheck checker by using
`flycheck-define-command-checker'.  Similar to `flycheck-define-checker' but
since it is a defun instead of a macro this allows the use of the evaluated
variables `verilog-ext-flycheck-hal-script-path' and
`verilog-ext-flycheck-hal-log-path' inside the first string of the keyword
argument :command

The only difference with `flycheck-define-checker' is that this one requires
keyword arguments to be quoted.

Needed since this linter uses the value of a variable as a command, and might
be undefined when defining the checker."
  (unless (and (executable-find "xrun")
               (executable-find "hal"))
    (error "Could not find 'xrun' and 'hal' in $PATH"))
  (verilog-ext-flycheck-hal-script-create)
  ;; Checker definition
  (flycheck-define-command-checker 'verilog-cadence-hal
    "A Verilog syntax checker using Cadence HAL."
    :command `(,verilog-ext-flycheck-hal-script-path
               "-bb_unbound_comp"
               "-timescale" "1ns/1ps"
               "-l" ,verilog-ext-flycheck-hal-log-path
               "+libext+.v+.vh+.sv+.svh"
               (option-list "-incdir" verilog-ext-flycheck-hal-include-path)
               (option-list "-y" verilog-ext-flycheck-hal-include-path)
               source-original)
    :working-directory #'verilog-ext-flycheck-hal-directory-fn
    :error-patterns
    '((info    (zero-or-more not-newline) ": *N," (zero-or-more not-newline) "(" (file-name) "," line "|" column "): " (message) line-end)
      (warning (zero-or-more not-newline) ": *W," (zero-or-more not-newline) "(" (file-name) "," line "|" column "): " (message) line-end)
      (error   (zero-or-more not-newline) ": *E," (zero-or-more not-newline) "(" (file-name) "," line "|" column "): " (message) line-end))
    :modes '(verilog-mode verilog-ts-mode)))


(provide 'verilog-ext-flycheck)

;;; verilog-ext-flycheck.el ends here
