;;; verilog-ext.el --- Verilog Extensions  -*- lexical-binding: t -*-

;; Copyright (C) 2022-2023 Gonzalo Larumbe

;; Author: Gonzalo Larumbe <gonzalomlarumbe@gmail.com>
;; URL: https://github.com/gmlarumbe/verilog-ext
;; Version: 0.1.0
;; Keywords: Verilog, IDE, Tools
;; Package-Requires: ((emacs "28.1") (verilog-mode "2022.12.18.181110314") (eglot "1.9") (lsp-mode "8.0.1") (ag "0.48") (ripgrep "0.4.0") (ggtags "0.9.0") (hydra "0.15.0") (apheleia "3.1") (yasnippet "0.14.0") (company "0.9.13") (flycheck "33-cvs") (imenu-list "0.9") (outshine "3.1-pre"))

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

;; Extensions for Verilog Mode:
;;  - Tree-sitter support (requires Emacs 29)
;;  - Improve syntax highlighting
;;  - Hierarchy extraction and visualization via Verilog-Perl `vhier'
;;  - LSP configuration for `lsp-mode' and `eglot'
;;  - Support for many linters in `flycheck'
;;  - Improve `imenu': detect instances and support methods inside classes
;;  - Navigate through instances in a module
;;  - Jump to definition/reference of module at point via `ggtags' and `xref'
;;  - Beautify modules: indent and align parameters and ports (interactively and in batch)
;;  - Extended collection of custom and `yasnippet' templates insertion via `hydra'
;;  - Setup `company' to complete with verilog keywords
;;  - Wrapper functions to make `kill-word' stop at underscores without breaking indentation

;;; Code:

(require 'verilog-mode)
(require 'xref)
(require 'make-mode)
(require 'eglot)
(require 'lsp-mode)
(require 'lsp-verilog)
(require 'ag)
(require 'ripgrep)
(require 'imenu-list)
(require 'outshine)
(require 'ggtags)
(require 'hydra)
(require 'apheleia)
(require 'yasnippet)
(require 'flycheck)
(require 'company-keywords)


;;; Customization
(defgroup verilog-ext nil
  "Verilog Extensions."
  :group 'languages
  :group 'verilog-mode)

(defcustom verilog-ext-mode-hook nil
  "Hook run when `verilog-ext-mode' is enabled."
  :type 'hook
  :group 'verilog-ext)

(defcustom verilog-ext-jump-to-parent-module-engine "ag"
  "Default program to find parent module instantiations.
Either `rg' or `ag' are implemented."
  :type '(choice (const :tag "silver searcher" "ag")
                 (const :tag "ripgrep"         "rg"))
  :group 'verilog-ext)

(defcustom verilog-ext-snippets-dir (concat user-emacs-directory "verilog-ext/snippets")
  "Yasnippet verilog-ext snippets directory."
  :type 'string
  :group 'verilog-ext)

(defcustom verilog-ext-templ-resetn "Rst_n"
  "Name of active low reset for templates."
  :type 'string
  :group 'verilog-ext)

(defcustom verilog-ext-templ-clock "Clk"
  "Name of clock for templates."
  :type 'string
  :group 'verilog-ext)

(defcustom verilog-ext-vhier-command-file nil
  "Verilog-ext vhier command file."
  :type 'string
  :group 'verilog-ext)

(defcustom verilog-ext-vhier-output-file nil
  "Verilog-ext vhier output file."
  :type 'string
  :group 'verilog-ext)

(defcustom verilog-ext-flycheck-eldoc-toggle nil
  "Disable `eldoc-mode' if flycheck is enabled and viceversa.
Avoids collisions in the minibufer between eldoc (ggtags) and flycheck."
  :type '(choice
          (const :tag "Enable" t)
          (const :tag "Disable" nil))
  :group 'verilog-ext)

(defcustom verilog-ext-flycheck-verible-rules nil
  "List of strings containing verible liner rules.
Use - or + prefixes depending on enabling/disabling of rules.
https://chipsalliance.github.io/verible/lint.html"
  :type '(repeat string)
  :group 'verilog-ext)

(defcustom verilog-ext-align-typedef-uvm-dir nil
  "Verilog-ext align typedef UVM directory."
  :type 'string
  :group 'verilog-ext)

(defcustom verilog-ext-time-stamp-regex "^// Last modified : "
  "Timestamp regexp."
  :type 'string
  :group 'verilog-ext)

(defcustom verilog-ext-time-stamp-pattern (concat verilog-ext-time-stamp-regex "%%$")
  "Timestamp pattern.  See `time-stamp-pattern'."
  :type 'string
  :group 'verilog-ext)

(defcustom verilog-ext-time-stamp-format  "%:y/%02m/%02d"
  "Timestamp format.  See `time-stamp-format'."
  :type 'string
  :group 'verilog-ext)

(defcustom verilog-ext-time-stamp-start nil
  "If using `time-stamp-start' and `time-stamp-end':
`'time-stamp' deletes the text between the first match of `time-stamp-start'.
and the following match of `time-stamp-end', then writes the time stamp
specified by `time-stamp-format' between them."
  :type 'string
  :group 'verilog-ext)

(defcustom verilog-ext-time-stamp-end nil
  "If using `time-stamp-start' and `time-stamp-end':
`time-stamp' deletes the text between the first match of `time-stamp-start'.
and the following match of `time-stamp-end', then writes the time stamp
specified by `time-stamp-format' between them."
  :type 'string
  :group 'verilog-ext)


;;; Utils
(defconst verilog-ext-keywords-re
  (eval-when-compile
    (regexp-opt verilog-keywords 'symbols)))
(defconst verilog-ext-block-re
  (eval-when-compile
    (regexp-opt
     '("module" "interface" "program" "package" "class" "function" "task"
       "initial" "always" "always_ff" "always_comb" "generate" "property"
       "sequence" "`define")
     'symbols)))

(defconst verilog-ext-top-instantiable-re
  (concat "\\<\\(?1:module\\|interface\\)\\>\\(\\s-+\\<automatic\\>\\)?\\s-+\\(?3:" verilog-identifier-sym-re "\\)"))
(defconst verilog-ext-task-re
  (concat "\\(?1:\\(?:\\(?:static\\|pure\\|virtual\\|local\\|protected\\)\\s-+\\)*task\\)\\s-+\\(?:\\(?:static\\|automatic\\)\\s-+\\)?"
          "\\(?:\\(?2:\\w+\\)::\\)?"
          "\\(?3:" verilog-identifier-sym-re "\\)"))
(defconst verilog-ext-function-re
  (concat "\\(?1:\\(?:\\(?:static\\|pure\\|virtual\\|local\\|protected\\)\\s-+\\)*function\\)\\s-+\\(?:\\(?:static\\|automatic\\)\\s-+\\)?"
          "\\(?:\\w+\\s-+\\)?\\(?:\\(?:un\\)signed\\s-+\\)?" ; Optional Return type
          "\\(?:\\(?2:\\w+\\)::\\)?"
          "\\(?3:" verilog-identifier-sym-re "\\)"))
(defconst verilog-ext-class-re (concat "\\(?1:\\<class\\>\\)\\s-+\\(?3:" verilog-identifier-sym-re "\\)"))
(defconst verilog-ext-top-re (concat "\\<\\(?1:package\\|program\\|module\\|interface\\)\\>\\(\\s-+\\<automatic\\>\\)?\\s-+\\(?3:" verilog-identifier-sym-re "\\)"))


(defvar verilog-ext-buffer-list nil)
(defvar verilog-ext-dir-list nil)
(defvar-local verilog-ext-file-allows-instances nil
  "Non nil if current file includes a module or interface block.")

(defconst verilog-ext-block-end-keywords-re
  (eval-when-compile
    (verilog-regexp-words
     '("end" "join" "join_any" "join_none" "endchecker" "endclass" "endclocking"
       "endconfig" "endfunction" "endgenerate" "endgroup" "endinterface"
       "endmodule" "endpackage" "endprimitive" "endprogram" "endproperty"
       "endsequence" "endtask")))
  "Regexp to match Verilog/SystemVerilog block end keywords.
IEEE 1800-2012 SystemVerilog Section 9.3.4 Block names.")

(defconst verilog-ext-block-end-keywords-complete-re
  (concat "^\\(?1:\\s-*" verilog-ext-block-end-keywords-re "\\)\\s-*"       ; Blanks and block end keyword
          "//\\s-*\\(\\(block:\\|" verilog-identifier-sym-re "\\s-*::\\)\\s-*\\)*" ; Comments
          "\\(?2:" verilog-identifier-sym-re "\\)\\s-*$"))                 ; Block name to be replaced


(defun verilog-ext-forward-syntactic-ws ()
  "Wrap `verilog-forward-syntactic-ws' and return point."
  (verilog-forward-syntactic-ws)
  (point))

(defun verilog-ext-backward-syntactic-ws ()
  "Wrap `verilog-backward-syntactic-ws' and return point."
  (verilog-backward-syntactic-ws)
  (point))

(defun verilog-ext-forward-char ()
  "Wrap `forward-char' and return point."
  (forward-char)
  (point))

(defun verilog-ext-backward-char ()
  "Wrap `backward-char' and return point."
  (backward-char)
  (point))

(defun verilog-ext-forward-sexp ()
  "Wrap `verilog-forward-sexp', ignore errors and return point."
  (ignore-errors
    (verilog-forward-sexp)
    (point)))

(defun verilog-ext-backward-sexp ()
  "Wrap `verilog-backward-sexp' ignore errors and return point."
  (ignore-errors
    (verilog-backward-sexp)
    (point)))

(defun verilog-ext-backward-up-list ()
  "Wrap `backward-up-list' and ignore errors."
  (ignore-errors
    (backward-up-list)))

(defun verilog-ext-down-list ()
  "Wrap `down-list' and ignore errors."
  (ignore-errors
    (down-list)))

(defun verilog-ext-skip-identifier-backwards ()
  "Return non-nil if point skipped backwards verilog identifier chars."
  (< (skip-chars-backward "a-zA-Z0-9_") 0))

(defun verilog-ext-skip-identifier-forward ()
  "Return non-nil if point skipped forward verilog identifier chars."
  (> (skip-chars-forward "a-zA-Z0-9_") 0))

(defmacro verilog-ext-when-t (cond &rest body)
  "Execute BODY when COND is non-nil.
Same function `when' from subr.el but returning t if COND is nil."
  (declare (indent 1) (debug t))
  (list 'if cond (cons 'progn body) t))

(defmacro verilog-ext-while-t (cond &rest body)
  "Execute BODY while COND is non-nil.
Same function `while' but returning t after last condition for use in ands."
  (declare (indent 1) (debug t))
  `(progn
     (while ,cond
       ,@body)
     t))

(defun verilog-ext-path-join (arg1 arg2)
  "Join path of ARG1 and ARG2."
  (if (and arg1 arg2)
      (concat (file-name-as-directory arg1) arg2)
    (error "Cannot join path with nil arguments")
    nil))

(defun verilog-ext-replace-regexp (regexp to-string start end)
  "Wrapper function for programatic use of `replace-regexp'.
Replace REGEXP with TO-STRING from START to END."
  (let* ((marker (make-marker))
         (endpos (when end (set-marker marker end))))
    (save-excursion
      (goto-char start)
      (while (re-search-forward regexp endpos t)
        (replace-match to-string)))))

(defun verilog-ext-replace-regexp-whole-buffer (regexp to-string)
  "Replace REGEXP with TO-STRING on whole `current-buffer'."
  (verilog-ext-replace-regexp regexp to-string (point-min) nil))

(defun verilog-ext-replace-string (string to-string start end &optional fixedcase)
  "Wrapper function for programatic use of `replace-string'.
Replace STRING with TO-STRING from START to END.

If optional arg FIXEDCASE is non-nil, do not alter the case of
the replacement text (see `replace-match' for more info)."
  (let* ((marker (make-marker))
         (endpos (when end (set-marker marker end))))
    (save-excursion
      (goto-char start)
      (while (search-forward string endpos t)
        (replace-match to-string fixedcase)))))

(defun verilog-ext-scan-buffer-modules ()
  "Find modules in current buffer.
Return list with found modules or nil if not found.
Update the value of buffer-local variable `verilog-ext-file-allows-instances'
to be used in optimization of font-lock and imenu."
  (let (modules)
    (save-excursion
      (goto-char (point-min))
      (while (verilog-re-search-forward verilog-ext-top-instantiable-re nil t)
        (push (match-string-no-properties 3) modules)))
    (if modules
        (setq verilog-ext-file-allows-instances t)
      (setq verilog-ext-file-allows-instances nil))
    (delete-dups modules)))

(defun verilog-ext-read-file-modules (&optional file)
  "Find modules in current buffer.
Find modules in FILE if optional arg is non-nil.
Return list with found modules or nil if not found."
  (let ((buf (if file
                 (get-file-buffer file)
               (current-buffer)))
        (debug nil))
    (if buf
        (with-current-buffer buf
          (verilog-ext-scan-buffer-modules))
      ;; If FILE buffer is not being visited, use a temporary buffer
      (with-temp-buffer
        (when debug
          (clone-indirect-buffer-other-window "*debug*" t))
        (insert-file-contents file)
        (verilog-mode)
        (verilog-ext-scan-buffer-modules)))))

(defun verilog-ext-select-file-module (&optional file)
  "Select file module from FILE.
If only one module was found return it as a string.
If more than one module was found, select between available ones.
Return nil if no module was found."
  (let ((modules (verilog-ext-read-file-modules file)))
    (if (cdr modules)
        (completing-read "Select module: " modules)
      (car modules))))

(defun verilog-ext-project-root ()
  "Find current project root, depending on available packages."
  (or (and (project-current)
           (project-root (project-current)))
      (when (featurep 'ggtags)
        (ggtags-current-project-root))
      default-directory))

(defun verilog-ext-class-declaration-is-typedef-p ()
  "Return non-nil if point is at a class declaration.
Ensure it is not a typedef class declaration."
  (save-excursion
    (save-match-data
      (and (looking-at verilog-ext-class-re)
           (verilog-ext-backward-syntactic-ws)
           (backward-word)
           (looking-at "typedef")))))

(defun verilog-ext-looking-at-class-declaration ()
  "Return non-nil if point is at a class declaration (i.e. not a typedef).
Also updates `match-data' with that of `verilog-ext-class-re'."
  (and (looking-at verilog-ext-class-re)
       (not (verilog-ext-class-declaration-is-typedef-p))))

(defun verilog-ext-point-inside-block-p (block)
  "Return non-nil if cursor is inside specified BLOCK type.
Return alist with block type, name and boundaries."
  (let ((pos (point))
        (re (cond ((eq block 'function)  "\\<\\(function\\)\\>")
                  ((eq block 'task)      "\\<\\(task\\)\\>")
                  ((eq block 'class)     "\\<\\(class\\)\\>")
                  ((eq block 'module)    "\\<\\(module\\)\\>")
                  ((eq block 'interface) "\\<\\(interface\\)\\>")
                  ((eq block 'package)   "\\<\\(package\\)\\>")
                  ((eq block 'program)   "\\<\\(program\\)\\>")
                  ((eq block 'always)    "\\<\\(always\\(_ff\\|_comb\\|_latch\\)?\\)\\>")
                  ((eq block 'initial)   "\\<\\(initial\\)\\>")
                  ((eq block 'final)     "\\<\\(final\\)\\>")
                  ((eq block 'generate)  "\\<\\(generate\\)\\>")
                  ((eq block 'begin-end) "\\<\\(begin\\|end\\)\\>")
                  (t (error "Incorrect block argument"))))
        temp-pos block-beg-point block-end-point block-type block-name)
    (save-match-data
      (save-excursion
        (cond (;; Classes
               (equal block 'class)
               (when (verilog-re-search-backward re nil t)
                 (if (verilog-ext-class-declaration-is-typedef-p)
                     ;; Try again if looking at a typedef class declaration
                     (verilog-ext-point-inside-block-p 'class)
                   ;; Else do the same as for function/tasks and top blocks
                   (setq block-type (match-string-no-properties 1))
                   (looking-at verilog-ext-class-re)
                   (setq block-name (match-string-no-properties 3))
                   (setq temp-pos (point))
                   (verilog-re-search-forward ";" nil t)
                   (setq block-beg-point (point))
                   (goto-char temp-pos)
                   (verilog-ext-forward-sexp)
                   (backward-word)
                   (setq block-end-point (point)))))
              ;; Function/tasks and top blocks
              ((member block '(function task module interface package program))
               (and (verilog-re-search-backward re nil t)
                    (save-excursion ; Exclude external func/tasks declarations
                      (save-match-data
                        (verilog-beg-of-statement)
                        (not (looking-at "\\<extern\\>"))))
                    (setq block-type (match-string-no-properties 1))
                    (or (looking-at verilog-ext-function-re)
                        (looking-at verilog-ext-task-re)
                        (looking-at verilog-ext-top-re))
                    (setq block-name (match-string-no-properties 3))
                    (setq temp-pos (point))
                    (verilog-re-search-forward ";" nil t)
                    (setq block-beg-point (point))
                    (goto-char temp-pos)
                    (verilog-ext-forward-sexp)
                    (backward-word)
                    (setq block-end-point (point))))
              ;; Procedural: always, initial and final
              ((member block '(always initial final))
               (and (verilog-re-search-backward re nil t)
                    (if (equal block 'always)
                        (setq block-type "always")
                      (setq block-type (match-string-no-properties 1)))
                    (verilog-ext-skip-identifier-forward)
                    (verilog-ext-forward-syntactic-ws)
                    (setq block-beg-point (point))
                    (setq block-name (buffer-substring-no-properties (point) (line-end-position)))
                    (verilog-re-search-forward "begin" (line-end-position) t)
                    (verilog-ext-forward-sexp)
                    (backward-word)
                    (setq block-end-point (point))))
              ;; Generate
              ((equal block 'generate)
               (and (verilog-re-search-backward re nil t)
                    (setq block-type (match-string-no-properties 1))
                    (verilog-ext-skip-identifier-forward)
                    (save-excursion
                      (verilog-ext-forward-syntactic-ws)
                      (setq block-name (buffer-substring-no-properties (point) (line-end-position))))
                    (setq block-beg-point (point))
                    (verilog-ext-forward-sexp)
                    (backward-word)
                    (setq block-end-point (point))))
              ;; Procedural block (begin-end)
              ((equal block 'begin-end)
               (and (verilog-re-search-backward re nil t)
                    (verilog-ext-while-t (string= (match-string-no-properties 0) "end")
                      (verilog-ext-backward-sexp)
                      (verilog-re-search-backward re nil t))
                    ;; Cover the whole 'begin word to account for nested begin/ends
                    (setq block-beg-point (match-beginning 0))
                    (verilog-ext-forward-sexp)
                    (backward-word)
                    (looking-at "\\<end\\>")
                    ;; Cover the whole 'end word to account for nested begin/ends
                    (setq block-end-point (match-end 0))
                    (setq block-type "begin-end")
                    (setq block-name nil)))
              ;; Default invalid condition
              (t
               (error "Invalid condition")))
        (if (and block-beg-point block-end-point
                 (>= pos block-beg-point)
                 (< pos block-end-point))
            `((type      . ,block-type)
              (name      . ,block-name)
              (beg-point . ,block-beg-point)
              (end-point . ,block-end-point))
          nil)))))

;; TODO: Still gives very poor performance for `which-func' and `verilog-ext-inside-procedural'.
;; `which-func' somehow manages to hide it running while in idle, but it takes a long time anyway.
;; The calls to `verilog-ext-point-inside-block-p' result in many  `verilog-backward-sexp' and
;; `verilog-forward-sexp' which are somehow expensive.
;; This will be way easier with tree-sitter or with a different implementation.
(defun verilog-ext-block-at-point ()
  "Return current block and name at point."
  (or (verilog-ext-point-inside-block-p 'function)
      (verilog-ext-point-inside-block-p 'task)
      (verilog-ext-point-inside-block-p 'class)
      (verilog-ext-point-inside-block-p 'package)
      (verilog-ext-point-inside-block-p 'always)
      (verilog-ext-point-inside-block-p 'initial)
      (verilog-ext-point-inside-block-p 'final)
      (verilog-ext-point-inside-block-p 'generate)
      (verilog-ext-point-inside-block-p 'module)
      (verilog-ext-point-inside-block-p 'interface)
      (verilog-ext-point-inside-block-p 'program)))

(defun verilog-ext-inside-procedural ()
  "Return cons cell with start/end pos if point is inside a procedural block.
If point is inside a begin-end block inside a procedural, return begin-end
positions."
  (save-match-data
    (save-excursion
      (let* ((block-data (verilog-ext-block-at-point))
             (block-type (alist-get 'type block-data))
             (beg-end-data (verilog-ext-point-inside-block-p 'begin-end)))
        (cond (beg-end-data ; If on a begin-end block outside a generate, it will always be procedural
               (unless (string= block-type "generate") ; Relies on `verilog-ext-block-at-point' having higher precedence ...
                 (cons (alist-get 'beg-point beg-end-data) (alist-get 'end-point beg-end-data)))) ; ... for always than for generate
              ;; If outside a begin-end, look for
              ((or (string= block-type "function")
                   (string= block-type "task")
                   (string= block-type "class")
                   (string= block-type "package")
                   (string= block-type "initial")
                   (string= block-type "final")
                   (string= block-type "program"))
               (cons (alist-get 'beg-point block-data) (alist-get 'end-point block-data)))
              ;; Default, not in a procedural block
              (t
               nil))))))

(defun verilog-ext-update-buffer-and-dir-list ()
  "Update Verilog-mode opened buffers and directories lists."
  (let (verilog-buffers verilog-dirs)
    (dolist (buf (buffer-list (current-buffer)))
      (with-current-buffer buf
        (when (or (string-equal major-mode "verilog-mode")
                  (string-equal major-mode "verilog-ts-mode"))
          (push buf verilog-buffers)
          (unless (member default-directory verilog-dirs)
            (push default-directory verilog-dirs)))))
    (setq verilog-ext-buffer-list verilog-buffers)
    (setq verilog-ext-dir-list verilog-dirs)))

(defun verilog-ext-kill-buffer-hook ()
  "Verilog hook to run when killing a buffer."
  (setq verilog-ext-buffer-list (remove (current-buffer) verilog-ext-buffer-list)))


;;; Editing
(defun verilog-ext-kill-word (&optional arg)
  "Make verilog `kill-word' command stop at underscores.
Optional ARG sets number of words to kill."
  (interactive "p")
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (with-syntax-table table
      (kill-word arg))))

(defun verilog-ext-backward-kill-word (&optional arg)
  "Make verilog `backward-kill-word' command stop at underscores.
Optional ARG sets number of words to kill."
  (interactive "p")
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (with-syntax-table table
      (backward-kill-word arg))))

(defun verilog-ext-indent-region (start end &optional column)
  "Wrapper for `indent-region'.
Prevents indentation issues with compiler directives with a modified syntax
table.
Pass the args START, END and optional COLUMN to `indent-region'."
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?` "w" table)
    (with-syntax-table table
      (indent-region start end column))))

(defun verilog-ext-indent-block-at-point ()
  "Indent current block at point."
  (interactive)
  (let ((data (verilog-ext-block-at-point))
        start-pos end-pos block name)
    (unless data
      (user-error "Not inside a block"))
    (save-excursion
      (setq block (alist-get 'type data))
      (setq name (alist-get 'name data))
      (goto-char (alist-get 'beg-point data))
      (setq start-pos (line-beginning-position))
      (goto-char (alist-get 'end-point data))
      (setq end-pos (line-end-position))
      (verilog-ext-indent-region start-pos end-pos)
      (message "Indented %s : %s" block name))))

(defun verilog-ext-code-formatter-setup ()
  "Setup `apheleia' with Verible code formatter."
  (interactive)
  (unless (and (alist-get 'verilog-mode apheleia-mode-alist)
               (alist-get 'verible apheleia-formatters))
    (setq apheleia-mode-alist (assq-delete-all 'verilog-mode apheleia-mode-alist))
    (push '(verilog-mode . verible) apheleia-mode-alist)
    (setq apheleia-formatters (assq-delete-all 'verible apheleia-formatters))
    (push '(verible . ("verible-verilog-format"
                       "--indentation_spaces" (number-to-string verilog-indent-level)
                       "-"))
          apheleia-formatters))
  (if (called-interactively-p 'any)
      (message "Configured %s" (alist-get 'verilog-mode apheleia-mode-alist))
    (alist-get 'verilog-mode apheleia-mode-alist)))

(defun verilog-ext-clean-port-blanks ()
  "Cleans blanks inside port connections of current block."
  (interactive)
  (let ((old-re (concat "\\(?1:^\\s-*\\)\\.\\(?2:" verilog-identifier-re "\\)\\(?3:\\s-*\\)(\\(?4:\\s-*\\)\\(?5:[^ ]+\\)\\(?6:\\s-*\\))"))
        (new-re "\\1.\\2\\3\(\\5\)")
        data start-pos end-pos module-name instance-name)
    (when (setq data (verilog-ext-instance-at-point))
      (setq start-pos (match-beginning 0))
      (setq end-pos (match-end 0))
      (setq module-name (car data))
      (setq instance-name (cadr data))
      (save-excursion
        (goto-char start-pos)
        (while (re-search-forward old-re end-pos :noerror)
          (replace-match new-re)))
      (message "Removed port blanks from %s : %s" module-name instance-name))))

(defun verilog-ext-toggle-connect-port (&optional force-connect)
  "Toggle connect/disconnect port at current line.

Return non-nil if a port regex was found on current line.

If called with universal arg, FORCE-CONNECT will force connection
of current port instead of toggling."
  (interactive "P")
  (let* ((case-fold-search verilog-case-fold)
         (re (concat "\\(?1:^\\s-*\\)\\.\\(?2:" verilog-identifier-re "\\)\\(?3:\\s-*\\)\\(?4:(\\(?5:.*\\))\\)?"))
         port-found port conn sig)
    (save-excursion
      (beginning-of-line)
      (if (verilog-re-search-forward re (line-end-position) t)
          (progn
            (setq port-found t)
            (setq port (match-string-no-properties 2))
            (setq conn (match-string-no-properties 5))
            (if (or (string-equal conn "") force-connect) ; Disconnected or forced connection
                (progn ; Connect
                  (setq sig (read-string (concat "Connect [" port "] to: ") port))
                  (replace-match (concat "\\1.\\2\\3\(" sig "\)") t))
              ;; Else disconnect
              (replace-match (concat "\\1.\\2\\3\(" nil "\)") t)))
        ;; No port found
        (message "No port detected at current line")))
    (when port-found
      (forward-line 1))))

(defun verilog-ext-connect-ports-recursively ()
  "Connect ports of current instance recursively.
Ask for connection of ports until no port is found at current line."
  (interactive)
  (while (verilog-ext-toggle-connect-port :force-connect)
    (verilog-ext-toggle-connect-port :force-connect)))

(defun verilog-ext-block-end-comments-to-names ()
  "Convert valid block-end comments to ': BLOCK_NAME'.

Examples: endmodule // module_name             → endmodule : module_name
          endfunction // some comment          → endfunction // some comment
          endfunction // class_name::func_name → endfunction : func_name
          end // block: block_name             → end : block_name"
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward verilog-ext-block-end-keywords-complete-re nil :noerror)
      (when (not (member (match-string-no-properties 2) verilog-keywords))
        (replace-match "\\1 : \\2")))))

(define-minor-mode verilog-ext-block-end-comments-to-names-mode
  "Minor mode to convert block end comments to block names after saving a file.
See `verilog-ext-block-end-comments-to-names' for an example."
  :global nil
  (if verilog-ext-block-end-comments-to-names-mode
      (add-hook 'before-save-hook #'verilog-ext-block-end-comments-to-names nil :local)
    (remove-hook 'before-save-hook #'verilog-ext-block-end-comments-to-names :local)))

(define-minor-mode verilog-ext-time-stamp-mode
  "Setup `time-stamp' format for Verilog files.
By default `time-stamp' looks for the pattern in the first 8 lines.
This can be changed by setting the local variables `time-stamp-start'
and `time-stamp-end' for custom scenarios."
  :global nil
  (setq-local time-stamp-pattern verilog-ext-time-stamp-pattern)
  (setq-local time-stamp-format verilog-ext-time-stamp-format)
  (setq-local time-stamp-start verilog-ext-time-stamp-start)
  (setq-local time-stamp-end verilog-ext-time-stamp-end)
  (if verilog-ext-time-stamp-mode
      (add-hook 'before-save-hook #'time-stamp nil :local)
    (remove-hook 'before-save-hook #'time-stamp :local)))


;;; Navigation
(defun verilog-ext-forward-word (&optional arg)
  "Make verilog word navigation commands stop at underscores.
Move forward ARG words."
  (interactive "p")
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (with-syntax-table table
      (forward-word arg))))

(defun verilog-ext-backward-word (&optional arg)
  "Make verilog word navigation commands stop at underscores.
Move backward ARG words."
  (interactive "p")
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (with-syntax-table table
      (backward-word arg))))

(defun verilog-ext-tab (&optional arg)
  "Run corresponding TAB function depending on `major-mode'.
If on a `verilog-mode' buffer, run `electric-verilog-tab' with original
`verilog-mode' syntax table.  Prevents indentation issues with compiler
directives with a modified syntax table.
If on a `verilog-ts-mode' buffer, run `indent-for-tab-command' with ARG."
  (interactive "P")
  (cond ((string= major-mode "verilog-mode")
         (let ((table (make-syntax-table verilog-mode-syntax-table)))
           (modify-syntax-entry ?` "w" table)
           (with-syntax-table table
             (electric-verilog-tab))))
        ((string= major-mode "verilog-ts-mode")
         (indent-for-tab-command arg))
        (t
         (error "Wrong major-mode to run `verilog-ext-tab'"))))

(defun verilog-ext-find-function-task (&optional limit bwd interactive-p)
  "Search for a Verilog function/task declaration or definition.
Allows matching of multiline declarations (such as in some UVM source files).

If executing interactively show function/task name in the minibuffer.

Updates `match-data' so that the function can be used in other contexts:
- (match-string 0) = Whole function/task regexp (until semicolon)
- (match-string 1) = Function/task name
- (match-string 2) = Class modifier (if defined externally)
- (match-string 3) = Function return type (if applicable)

Bound search to LIMIT in case optional argument is non-nil.

Search bacwards if BWD is non-nil.

Third arg INTERACTIVE-P specifies whether function call should be treated as if
it was interactive.  This changes the position where point will be at the end of
the function call."
  (let ((case-fold-search verilog-case-fold)
        (tf-re "\\<\\(function\\|task\\)\\>")
        (tf-modifiers-re "\\<\\(extern\\|static\\|pure\\|virtual\\|local\\|protected\\)\\>")
        tf-type tf-kwd-pos-end
        tf-args tf-args-pos-beg tf-args-pos-end
        tf-name tf-name-pos-beg tf-name-pos-end tf-beg-of-statement-pos tf-end-of-statement-pos tf-modifiers
        func-return-type func-return-type-pos-beg func-return-type-pos-end
        class-name class-beg-pos class-end-pos
        found)
    (save-excursion
      (save-match-data
        (and (if bwd
                 (verilog-re-search-backward tf-re limit 'move)
               (verilog-re-search-forward tf-re limit 'move))
             (setq tf-type (match-string-no-properties 0))
             (setq tf-kwd-pos-end (match-end 0))
             (verilog-re-search-forward ";" limit 'move)
             (setq tf-end-of-statement-pos (point))
             (verilog-ext-backward-char)
             (verilog-ext-backward-syntactic-ws)
             (verilog-ext-when-t (eq (preceding-char) ?\))
               (setq tf-args-pos-end (1- (point)))
               (verilog-ext-backward-sexp)
               (setq tf-args-pos-beg (1+ (point)))
               (setq tf-args (split-string (buffer-substring-no-properties tf-args-pos-beg tf-args-pos-end) ","))
               (setq tf-args (mapcar #'string-trim tf-args)))
             (backward-word)
             ;; Func/task name
             (when (looking-at verilog-identifier-re)
               (setq tf-name (match-string-no-properties 0))
               (setq tf-name-pos-beg (match-beginning 0))
               (setq tf-name-pos-end (match-end 0))
               (setq found t))
             ;; Externally defined functions
             (verilog-ext-when-t (eq (preceding-char) ?:)
               (skip-chars-backward ":")
               (backward-word)
               (when (looking-at verilog-identifier-re)
                 (setq class-name (match-string-no-properties 0))
                 (setq class-beg-pos (match-beginning 0))
                 (setq class-end-pos (match-end 0))))
             ;; Automatic kwd and function return value
             (verilog-ext-when-t (string= tf-type "function")
               (verilog-ext-backward-syntactic-ws)
               (setq func-return-type-pos-end (point))
               (goto-char tf-kwd-pos-end)
               (verilog-ext-forward-syntactic-ws)
               (when (looking-at "\\<automatic\\>")
                 (forward-word)
                 (verilog-ext-forward-syntactic-ws))
               (setq func-return-type-pos-beg (point))
               (setq func-return-type (buffer-substring-no-properties func-return-type-pos-beg
                                                                      func-return-type-pos-end)))
             ;; Func/task modifiers
             (setq tf-beg-of-statement-pos (verilog-pos-at-beg-of-statement))
             (while (verilog-re-search-backward tf-modifiers-re tf-beg-of-statement-pos 'move)
               (push (match-string-no-properties 0) tf-modifiers)))))
    (if found
        (progn
          (set-match-data (list tf-beg-of-statement-pos
                                tf-end-of-statement-pos
                                tf-name-pos-beg
                                tf-name-pos-end
                                class-beg-pos
                                class-end-pos
                                func-return-type-pos-beg
                                func-return-type-pos-end))
          (when interactive-p
            (message "%s" tf-name))
          (if bwd
              (goto-char tf-beg-of-statement-pos)
            (goto-char tf-name-pos-beg))
          ;; Return alist
          `((pos         . ,tf-name-pos-beg)
            (name        . ,tf-name)
            (modifiers   . ,tf-modifiers)
            (return-type . ,func-return-type)
            (class-name  . ,class-name)
            (args        . ,tf-args)))
      ;; Not found interactive reporting
      (when interactive-p
        (if bwd
            (message "Could not find any function/task backward")
          (message "Could not find any function/task forward"))))))

(defun verilog-ext-find-function-task-fwd (&optional limit)
  "Search forward for a Verilog function/task declaration or definition.
Bound search to LIMIT in case optional argument is non-nil."
  (interactive)
  (let ((interactive-p (called-interactively-p 'interactive)))
    (verilog-ext-find-function-task limit nil interactive-p)))

(defun verilog-ext-find-function-task-bwd (&optional limit)
  "Search backward for a Verilog function/task declaration or definition.
Bound search to LIMIT in case optional argument is non-nil."
  (interactive)
  (let ((interactive-p (called-interactively-p 'interactive)))
    (verilog-ext-find-function-task limit :bwd interactive-p)))

(defun verilog-ext-find-class (&optional limit bwd interactive-p)
  "Search for a class declaration, skipping typedef declarations.

If executing interactively show class name in the minibuffer.

Updates `match-data' so that the function can be used in other contexts:
- (match-string 0) = Class definition boundaries (without modifier)
- (match-string 1) = Class name
- (match-string 2) = Parent class (if any)

Bound search to LIMIT in case optional argument is non-nil.

Search bacwards if BWD is non-nil.

Third arg INTERACTIVE-P specifies whether function call should be treated as if
it was interactive."
  (interactive)
  (let ((found)
        name name-pos-start name-pos-end
        modifier start-pos end-pos class-kwd-pos
        parent-class parent-class-start-pos parent-class-end-pos
        param-begin param-end param-string)
    (save-excursion
      (save-match-data
        (while (and (not found)
                    (if bwd
                        (verilog-re-search-backward verilog-ext-class-re limit 'move)
                      (verilog-re-search-forward verilog-ext-class-re limit 'move)))
          (when (save-excursion
                  (setq class-kwd-pos (goto-char (match-beginning 1))) ; Dirty workaround to make `verilog-ext-class-declaration-is-typedef-p' work properly ...
                  (not (verilog-ext-class-declaration-is-typedef-p))) ; ... moving point to the beginning of 'class keyword
            (setq found t)
            (setq name (match-string-no-properties 3))
            (setq name-pos-start (match-beginning 3))
            (setq name-pos-end (match-end 3))
            (setq start-pos (point))
            (setq end-pos (or (verilog-pos-at-end-of-statement) ; Dirty workaround when searching forwards ...
                              (progn                            ; ... point might be at the end of the statement ...
                                (goto-char class-kwd-pos)       ; ... and `verilog-pos-at-end-of-statement' might return nil
                                (verilog-pos-at-end-of-statement))))
            ;; Find modifiers (virtual/interface)
            (save-excursion
              (verilog-backward-syntactic-ws)
              (backward-word)
              (when (looking-at "\\<\\(virtual\\|interface\\)\\>")
                (setq modifier (list (match-string-no-properties 0)))))
            ;; Find parameters, if any
            (when (and end-pos
                       (verilog-re-search-forward "#" end-pos t)
                       (verilog-ext-forward-syntactic-ws)
                       (setq param-begin (1+ (point)))
                       (verilog-ext-forward-sexp)
                       (verilog-ext-backward-char)
                       (verilog-ext-backward-syntactic-ws)
                       (setq param-end (point)))
              (setq param-string (buffer-substring-no-properties param-begin param-end)))
            ;; Find parent class, if any
            (when (and (verilog-re-search-forward "\\<extends\\>" end-pos t)
                       (verilog-ext-forward-syntactic-ws)
                       (looking-at verilog-identifier-sym-re))
              (setq parent-class (match-string-no-properties 0))
              (setq parent-class-start-pos (match-beginning 0))
              (setq parent-class-end-pos (match-end 0)))))))
    (if found
        (progn
          (set-match-data (list start-pos
                                end-pos
                                name-pos-start
                                name-pos-end
                                parent-class-start-pos
                                parent-class-end-pos))
          (goto-char start-pos)
          (when interactive-p
            (message "%s" name))
          ;; Return alist
          `((pos      . ,start-pos)
            (name     . ,name)
            (modifier . ,modifier)
            (parent   . ,parent-class)
            (params   . ,param-string)))
      ;; Not found interactive reporting
      (when interactive-p
        (if bwd
            (message "Could not find any class backward")
          (message "Could not find any class forward"))))))

(defun verilog-ext-find-class-fwd (&optional limit)
  "Search forward for a Verilog class declaration.
Bound search to LIMIT in case optional argument is non-nil."
  (interactive)
  (let ((interactive-p (called-interactively-p 'interactive)))
    (verilog-ext-find-class limit nil interactive-p)))

(defun verilog-ext-find-class-bwd (&optional limit)
  "Search backward for a Verilog class declaration.
Bound search to LIMIT in case optional argument is non-nil."
  (interactive)
  (let ((interactive-p (called-interactively-p 'interactive)))
    (verilog-ext-find-class limit :bwd interactive-p)))

(defun verilog-ext-find-function-task-class (&optional limit bwd interactive-p)
  "Find closest declaration of a function/task/class.
Return alist with data associated to the thing found.

Search bacwards if BWD is non-nil.

Bound search to LIMIT in case optional argument is non-nil.

Third arg INTERACTIVE-P specifies whether function call should be treated as if
it was interactive."
  (let ((re "\\<\\(function\\|task\\|class\\)\\>")
        found data pos type name modifiers)
    (save-excursion
      (while (and (not found)
                  (if bwd
                      (verilog-re-search-backward re limit t)
                    (verilog-re-search-forward re limit t)))
        (if (string= (match-string-no-properties 0) "class")
            (unless (save-excursion
                      (goto-char (match-beginning 0)) ; Dirty workaround to make `verilog-ext-class-declaration-is-typedef-p' work properly ...
                      (verilog-ext-class-declaration-is-typedef-p)) ; ... moving point to the beginning of 'class keyword
              (setq found t))
          ;; Functions and tasks
          (setq found t))))
    (when found
      (setq type (match-string-no-properties 0))
      (if (string= type "class")
          (progn
            (setq data (if bwd
                           (verilog-ext-find-class-bwd limit)
                         (verilog-ext-find-class-fwd limit)))
            (setq pos (alist-get 'pos data))
            (setq name (alist-get 'name data))
            (setq modifiers (alist-get 'modifier data)))
        (setq data (if bwd
                       (verilog-ext-find-function-task-bwd limit)
                     (verilog-ext-find-function-task-fwd limit)))
        (setq pos (alist-get 'pos data))
        (setq name (alist-get 'name data))
        (setq modifiers (alist-get 'modifiers data)))
      (if interactive-p
          (message "%s" name)
        ;; Return alist
        `((pos       . ,pos)
          (type      . ,type)
          (name      . ,name)
          (modifiers . ,modifiers))))))

(defun verilog-ext-find-function-task-class-fwd (&optional limit)
  "Search forward for a Verilog function/task/class declaration.
Bound search to LIMIT in case optional argument is non-nil."
  (interactive)
  (let ((interactive-p (called-interactively-p 'interactive)))
    (verilog-ext-find-function-task-class limit nil interactive-p)))

(defun verilog-ext-find-function-task-class-bwd (&optional limit)
  "Search backward for a Verilog function/task/class declaration.
Bound search to LIMIT in case optional argument is non-nil."
  (interactive)
  (let ((interactive-p (called-interactively-p 'interactive)))
    (verilog-ext-find-function-task-class limit :bwd interactive-p)))

(defun verilog-ext-find-block (&optional bwd interactive-p)
  "Search for a Verilog block regexp.
If BWD is non-nil, search backwards.  INTERACTIVE-P specifies whether function
call should be treated as if it was interactive."
  (let ((block-re verilog-ext-block-re)
        (case-fold-search verilog-case-fold)
        pos)
    (save-excursion
      (unless bwd
        (forward-char)) ; Avoid getting stuck
      (if bwd
          (verilog-re-search-backward block-re nil t)
        (verilog-re-search-forward block-re nil t))
      (if interactive-p
          (setq pos (match-beginning 1))
        (setq pos (point))))
    (when interactive-p
      (message (match-string 1)))
    (when pos
      (goto-char pos))))

(defun verilog-ext-find-block-fwd ()
  "Search forward for a Verilog block regexp."
  (interactive)
  (let ((interactive-p (called-interactively-p 'interactive)))
    (verilog-ext-find-block nil interactive-p)))

(defun verilog-ext-find-block-bwd ()
  "Search backwards for a Verilog block regexp."
  (interactive)
  (let ((interactive-p (called-interactively-p 'interactive)))
    (verilog-ext-find-block :bwd interactive-p)))

(defun verilog-ext-find-module-instance--legal-p ()
  "Return non-nil if it point position would be legal for an instantiation.
DANGER: Still very inefficient, removed funcall in
`verilog-ext-find-module-instance-fwd'."
  (and (not (verilog-parenthesis-depth))
       (not (verilog-ext-inside-procedural))))

(defun verilog-ext-find-module-instance--continue (&optional bwd)
  "Auxiliary function for finding module and instance functions.
\(In theory) speeds up the search by skipping sections of code where instances
are not legal.
Continue search backward if BWD is non-nil."
  (cond ((verilog-parenthesis-depth)
         (if bwd
             (verilog-backward-up-list 1)
           (verilog-backward-up-list -1)))
        (t
         (if bwd
             (verilog-backward-syntactic-ws)
           (forward-line)
           (verilog-forward-syntactic-ws)))))

(defun verilog-ext-find-module-instance-fwd (&optional limit)
  "Search forwards for a Verilog module/instance.

If executing interactively place cursor at the beginning of the module name and
show module and instance names in the minibuffer.

If executing programatically move to the end of the module and return point
position.

Updates `match-data' so that the function can be used in other contexts:
- (match-string 0) = Whole module instantiation: from beg of module name to ;
- (match-string 1) = Module name
- (match-string 2) = Instance name

Bound search to LIMIT in case optional argument is non-nil."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (identifier-re (concat "\\(" verilog-identifier-sym-re "\\)"))
        (module-end (make-marker))
        module-name module-pos module-match-data
        instance-name instance-match-data
        pos found)
    ;; Limit the search to files that can instantiate blocks (modules/interfaces)
    (if (not verilog-ext-file-allows-instances)
        (when (called-interactively-p 'interactive)
          (user-error "Not inside a module/interface file"))
      ;; Else do the search
      (save-excursion
        (save-match-data
          (when (called-interactively-p 'interactive)
            (forward-char)) ; Avoid getting stuck if executing interactively
          (while (and (not (eobp))
                      (verilog-ext-when-t limit
                        (> limit (point)))
                      (not (and (verilog-re-search-forward (concat "\\s-*" identifier-re) limit 'move) ; Module name
                                (not (verilog-parenthesis-depth))
                                (unless (member (match-string-no-properties 1) verilog-keywords)
                                  (setq module-name (match-string-no-properties 1))
                                  (setq module-pos (match-beginning 1))
                                  (setq module-match-data (match-data)))
                                (verilog-ext-forward-syntactic-ws)
                                (verilog-ext-when-t (= (following-char) ?\#)
                                  (and (verilog-ext-forward-char)
                                       (verilog-ext-forward-syntactic-ws)
                                       (= (following-char) ?\()
                                       (verilog-ext-forward-sexp)
                                       (= (preceding-char) ?\))
                                       (verilog-ext-forward-syntactic-ws)))
                                (looking-at identifier-re) ; Instance name
                                (unless (member (match-string-no-properties 1) verilog-keywords)
                                  (setq instance-name (match-string-no-properties 1))
                                  (setq instance-match-data (match-data)))
                                (verilog-ext-skip-identifier-forward)
                                (verilog-ext-forward-syntactic-ws)
                                (verilog-ext-when-t (= (following-char) ?\[)
                                  (and (verilog-ext-forward-sexp)
                                       (= (preceding-char) ?\])
                                       (verilog-ext-forward-syntactic-ws)))
                                (= (following-char) ?\()
                                (verilog-ext-forward-sexp)
                                (= (preceding-char) ?\))
                                (verilog-ext-forward-syntactic-ws)
                                (= (following-char) ?\;)
                                (set-marker module-end (1+ (point)))
                                (setq found t)
                                (if (called-interactively-p 'interactive)
                                    (progn
                                      (setq pos module-pos)
                                      (message "%s : %s" module-name instance-name))
                                  (setq pos (point))))))
            (verilog-ext-find-module-instance--continue nil))))
      (if found
          (progn
            (set-match-data (list (nth 0 module-match-data)
                                  module-end
                                  (nth 2 module-match-data)
                                  (nth 3 module-match-data)
                                  (nth 2 instance-match-data)
                                  (nth 3 instance-match-data)))
            (goto-char pos)
            (if (called-interactively-p 'interactive)
                (message "%s : %s" module-name instance-name)
              (point)))
        (when (called-interactively-p 'interactive)
          (message "Could not find any instance forward"))))))

(defun verilog-ext-find-module-instance-bwd (&optional limit)
  "Search backwards for a Verilog module/instance.

If executing interactively place cursor at the beginning of the module name and
show module and instance names in the minibuffer.

If executing programatically move to the beginning of the module and return
point position.

Updates `match-data' so that the function can be used in other contexts:
- (match-string 0) = Whole module instantiation: from beg of module name to ;
- (match-string 1) = Module name
- (match-string 2) = Instance name

Bound search to LIMIT in case it is non-nil."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (identifier-re (concat "\\(" verilog-identifier-sym-re "\\)"))
        (module-end (make-marker))
        module-name module-pos module-match-data
        instance-name instance-match-data
        pos found)
    ;; Limit the search to files that can instantiate blocks (modules/interfaces)
    (if (not verilog-ext-file-allows-instances)
        (when (called-interactively-p 'interactive)
          (user-error "Not inside a module/interface file"))
      ;; Else do the search
      (save-excursion
        (save-match-data
          (while (and (not (bobp))
                      (verilog-ext-when-t limit
                        (< limit (point)))
                      (not (and (set-marker module-end (verilog-re-search-backward ";" limit 'move))
                                (verilog-ext-backward-syntactic-ws)
                                (= (preceding-char) ?\))
                                (verilog-ext-backward-sexp)
                                (= (following-char) ?\()
                                (verilog-ext-backward-syntactic-ws)
                                (verilog-ext-when-t (= (preceding-char) ?\])
                                  (and (verilog-ext-backward-sexp)
                                       (= (following-char) ?\[)
                                       (verilog-ext-backward-syntactic-ws)))
                                (verilog-ext-skip-identifier-backwards)
                                (looking-at identifier-re)
                                (unless (member (match-string-no-properties 1) verilog-keywords)
                                  (setq instance-name (match-string-no-properties 1))
                                  (setq instance-match-data (match-data)))
                                (verilog-ext-backward-syntactic-ws)
                                (verilog-ext-when-t (= (preceding-char) ?\))
                                  (and (verilog-ext-backward-sexp)
                                       (= (following-char) ?\()
                                       (verilog-ext-backward-syntactic-ws)
                                       (= (preceding-char) ?\#)
                                       (verilog-ext-backward-char)
                                       (verilog-ext-backward-syntactic-ws)))
                                (verilog-ext-skip-identifier-backwards)
                                (looking-at identifier-re)
                                (unless (member (match-string-no-properties 1) verilog-keywords)
                                  (setq module-name (match-string-no-properties 1))
                                  (setq module-pos (match-beginning 1))
                                  (setq module-match-data (match-data)))
                                (looking-back "^\\s-*" (line-beginning-position))
                                (setq found t)
                                (if (called-interactively-p 'interactive)
                                    (setq pos module-pos)
                                  (setq pos (point))))))
            ;; Continue searching
            (verilog-ext-find-module-instance--continue :bwd))))
      (if found
          (progn
            (set-match-data (list (nth 0 module-match-data)
                                  module-end
                                  (nth 2 module-match-data)
                                  (nth 3 module-match-data)
                                  (nth 2 instance-match-data)
                                  (nth 3 instance-match-data)))
            (goto-char pos)
            (if (called-interactively-p 'interactive)
                (message "%s : %s" module-name instance-name)
              (point)))
        (when (called-interactively-p 'interactive)
          (message "Could not find any instance backwards"))))))

(defun verilog-ext-find-module-instance-bwd-2 ()
  "Search backwards for a Verilog module/instance.
The difference with `verilog-ext-find-module-instance-bwd' is that it
moves the cursor to current instance if pointing at one."
  (interactive)
  (let (inside-instance-p)
    (save-excursion
      (backward-char)
      (when (verilog-ext-instance-at-point)
        (setq inside-instance-p t)))
    (if inside-instance-p
        (progn
          (goto-char (match-beginning 1))
          (message "%s : %s" (match-string-no-properties 1) (match-string-no-properties 2)))
      (call-interactively #'verilog-ext-find-module-instance-bwd))))

(defun verilog-ext-instance-at-point ()
  "Return list with module and instance names if point is at an instance."
  (let ((point-cur (point))
        point-instance-begin point-instance-end instance-type instance-name)
    (save-excursion
      (when (and (verilog-re-search-forward ";" nil t)
                 (verilog-ext-find-module-instance-bwd)) ; Sets match data
        (setq instance-type (match-string-no-properties 1))
        (setq instance-name (match-string-no-properties 2))
        (setq point-instance-begin (match-beginning 0))
        (setq point-instance-end   (match-end 0))
        (if (and (>= point-cur point-instance-begin)
                 (<= point-cur point-instance-end))
            (list instance-type instance-name)
          nil)))))

(defun verilog-ext-jump-to-module-at-point (&optional ref)
  "Jump to definition of module at point.
If REF is non-nil show references instead."
  (interactive)
  (unless (executable-find "global")
    (error "Couldn't find executable `global' in PATH"))
  (unless (member 'ggtags--xref-backend xref-backend-functions)
    (error "Error: ggtags not configured as an xref backend.  Is ggtags-mode enabled?"))
  (unless (ggtags-current-project-root)
    (error "Error: `ggtags-project-root' not set.  Are GTAGS/GRTAGS/GPATH files created?"))
  (let ((module (car (verilog-ext-instance-at-point))))
    (if module
        (progn
          (if ref
              (xref-find-references module)
            (xref-find-definitions module))
          module) ; Report module name
      (user-error "Not inside a Verilog instance"))))

(defun verilog-ext-jump-to-module-at-point-def ()
  "Jump to definition of module at point."
  (interactive)
  (verilog-ext-jump-to-module-at-point))

(defun verilog-ext-jump-to-module-at-point-ref ()
  "Show references of module at point."
  (interactive)
  (verilog-ext-jump-to-module-at-point :ref))


;;;; Jump to parent module
(defvar verilog-ext-jump-to-parent-module-point-marker nil
  "Point marker to save the state of the buffer where the search was started.
Used in ag/rg end of search hooks to conditionally set the xref marker stack.")
(defvar verilog-ext-jump-to-parent-module-name nil)
(defvar verilog-ext-jump-to-parent-module-dir nil)
(defvar verilog-ext-jump-to-parent-trigger nil
  "Variable to run the post ag/rg command hook.
Runs only when the ag/rg search was triggered by
`verilog-ext-jump-to-parent-module' command.")

(defun verilog-ext-jump-to-parent-module ()
  "Find current module/interface instantiations via `ag'/`rg'.
Configuration should be done so that `verilog-ext-navigation-ag-rg-hook' is run
after the search has been done."
  (interactive)
  (let* ((proj-dir (verilog-ext-project-root))
         (module-name (or (verilog-ext-select-file-module buffer-file-name)
                          (error "No module/interface found @ %s" buffer-file-name)))
         (module-instance-pcre ; Many thanks to Kaushal Modi for this PCRE
          (concat "^\\s*\\K"                          ; Initial blank before module name. Do not highlighting anything till the name
                  "\\b(" module-name ")\\b"           ; Module name identifier
                  "(?="                             ; Lookahead to avoid matching
                  "(\\s+|("                          ; Either one or more spaces before the instance name, or...
                  "(\\s*\#\\s*\\((\\n|.)*?\\))+"           ; ... hardware parameters, '(\n|.)*?' does non-greedy multi-line grep
                  "(\\n|.)*?"                        ; Optional newline/space before instance name/first port name
                  "([^.])*?"                        ; Do not match more than 1 ".PARAM (PARAM_VAL),"
                  "))"                              ; Close capture groups before matching identifier
                  "\\b(" verilog-identifier-re ")\\b" ; Instance name
                  "(?=[^a-zA-Z0-9_]*\\()"             ; Nested lookahead (space/newline after instance name and before opening parenthesis)
                  ")")))                            ; Closing lookahead
    ;; Update variables used by the ag/rg search finished hooks
    (setq verilog-ext-jump-to-parent-module-name module-name)
    (setq verilog-ext-jump-to-parent-module-dir proj-dir)
    ;; Perform project based search
    (cond
     ;; Try ripgrep
     ((and (string= verilog-ext-jump-to-parent-module-engine "rg")
           (executable-find "rg"))
      (let ((rg-extra-args '("-t" "verilog" "--pcre2" "--multiline" "--stats")))
        (setq verilog-ext-jump-to-parent-module-point-marker (point-marker))
        (setq verilog-ext-jump-to-parent-trigger t)
        (ripgrep-regexp module-instance-pcre proj-dir rg-extra-args)))
     ;; Try ag
     ((and (string= verilog-ext-jump-to-parent-module-engine "ag")
           (executable-find "ag"))
      (let ((ag-arguments ag-arguments)
            (extra-ag-args '("--verilog" "--stats")))
        (dolist (extra-ag-arg extra-ag-args)
          (add-to-list 'ag-arguments extra-ag-arg :append))
        (setq verilog-ext-jump-to-parent-module-point-marker (point-marker))
        (setq verilog-ext-jump-to-parent-trigger t)
        (ag-regexp module-instance-pcre proj-dir)))
     ;; Fallback
     (t
      (error "Did not find `rg' nor `ag' in $PATH")))))

(defun verilog-ext-navigation-ag-rg-hook ()
  "Jump to the first result and push xref marker if there were any matches.
Kill the buffer if there is only one match."
  (when verilog-ext-jump-to-parent-trigger
    (let ((module-name (propertize verilog-ext-jump-to-parent-module-name 'face '(:foreground "green")))
          (dir (propertize verilog-ext-jump-to-parent-module-dir 'face '(:foreground "light blue")))
          (num-matches))
      (save-excursion
        (goto-char (point-min))
        (re-search-forward "^\\([0-9]+\\) matches\\s-*$" nil :noerror)
        (setq num-matches (string-to-number (match-string-no-properties 1))))
      (cond ((eq num-matches 1)
             (xref-push-marker-stack verilog-ext-jump-to-parent-module-point-marker)
             (next-error)
             (kill-buffer (current-buffer))
             (message "Jump to only match for [%s] @ %s" module-name dir))
            ((> num-matches 1)
             (xref-push-marker-stack verilog-ext-jump-to-parent-module-point-marker)
             (next-error)
             (message "Showing matches for [%s] @ %s" module-name dir))
            (t
             (kill-buffer (current-buffer))
             (message "No matches found")))
      (setq verilog-ext-jump-to-parent-trigger nil))))


;;;; Defun movement
(defun verilog-ext-goto-begin-up ()
  "Move point to start position of current begin."
  (save-match-data
    (let ((data (verilog-ext-point-inside-block-p 'begin-end)))
      (when data
        (goto-char (alist-get 'beg-point data))))))

(defun verilog-ext-goto-begin-down ()
  "Move point to start position of next nested begin."
  (save-match-data
    (let ((data (verilog-ext-point-inside-block-p 'begin-end)))
      (when data
        (verilog-re-search-forward "\\<begin\\>" (alist-get 'end-point data) t)))))

(defun verilog-ext-defun-level-up ()
  "Move up one defun-level.
Return alist with defun data if point moved to a higher block."
  (interactive)
  (let* ((data (verilog-ext-block-at-point))
         name)
    (when data
      (cond ((verilog-parenthesis-depth)
             (verilog-backward-up-list 1)
             (setq name "("))
            ((and (or (equal (alist-get 'type data) "function")
                      (equal (alist-get 'type data) "task"))
                  (verilog-ext-point-inside-block-p 'begin-end))
             (verilog-ext-goto-begin-up)
             (setq name "begin"))
            (t
             (setq name (alist-get 'name data))
             (goto-char (alist-get 'beg-point data))
             (backward-char)
             (verilog-beg-of-statement))))
    (if (called-interactively-p 'any)
        (message "%s" name)
      name)))

(defun verilog-ext-defun-level-down ()
  "Move down one defun-level.
Return alist with defun data if point moved to a lower block."
  (interactive)
  (let* ((data (save-excursion ; Workaround to properly detect current block boundaries
                 (verilog-re-search-forward ";" (line-end-position) t)
                 (verilog-ext-block-at-point)))
         (block-type (alist-get 'type data))
         (end-pos (alist-get 'end-point data))
         name)
    (when data
      (cond ((or (verilog-parenthesis-depth)
                 (looking-at "("))
             (verilog-ext-down-list)
             (setq name ")"))
            ((verilog-ext-point-inside-block-p 'begin-end)
             (when (verilog-ext-goto-begin-down)
               (setq name "begin")))
            ((or (equal block-type "function")
                 (equal block-type "task"))
             (verilog-re-search-forward "\\<begin\\>" end-pos t)
             (setq name (match-string-no-properties 0)))
            ((equal block-type "class")
             (verilog-ext-find-function-task-fwd end-pos)
             (setq name (match-string-no-properties 1)))
            ((equal block-type "package")
             (verilog-ext-find-function-task-class-fwd end-pos)
             (setq name (match-string-no-properties 1)))
            ((or (equal block-type "module")
                 (equal block-type "interface")
                 (equal block-type "program"))
             (setq data (verilog-ext-find-function-task-fwd end-pos))
             (setq name (match-string-no-properties 1)))
            (t
             nil)))
    (if (called-interactively-p 'any)
        (message "%s" name)
      name)))

;;;; Dwim
(defun verilog-ext-nav-down-dwim ()
  "Context based search downwards.
If in a module/interface look for instantiations.
Otherwise look for functions/tasks."
  (interactive)
  (if (verilog-ext-scan-buffer-modules)
      (call-interactively #'verilog-ext-find-module-instance-fwd)
    (call-interactively #'verilog-ext-defun-level-down)))

(defun verilog-ext-nav-up-dwim ()
  "Context based search upwards.
If in a module/interface look for instantiations.
Otherwise look for functions/tasks."
  (interactive)
  (if (verilog-ext-scan-buffer-modules)
      (call-interactively #'verilog-ext-find-module-instance-bwd-2)
    (call-interactively #'verilog-ext-defun-level-up)))

(defun verilog-ext-nav-beg-of-defun-dwim ()
  "Context based search upwards.
If in a module/interface look for instantiations.
Otherwise look for functions/tasks."
  (interactive)
  (if (verilog-ext-scan-buffer-modules)
      (call-interactively #'verilog-ext-find-block-bwd)
    (call-interactively #'verilog-ext-find-function-task-class-bwd)))

(defun verilog-ext-nav-end-of-defun-dwim ()
  "Context based search upwards.
If in a module/interface look for instantiations.
Otherwise look for functions/tasks."
  (interactive)
  (if (verilog-ext-scan-buffer-modules)
      (call-interactively #'verilog-ext-find-block-fwd)
    (call-interactively #'verilog-ext-find-function-task-class-fwd)))

(defun verilog-ext-nav-next-dwim ()
  "Context based search next.
If in a parenthesis, go to closing parenthesis (Elisp like).
Otherwise move to next paragraph."
  (interactive)
  (if (or (member (following-char) '(?\( ?\[ ?\{ ?\) ?\] ?\}))
          (member (preceding-char) '(?\) ?\] ?\}))
          (string= (symbol-at-point) "begin"))
      (verilog-ext-forward-sexp)
    (forward-paragraph)))

(defun verilog-ext-nav-prev-dwim ()
  "Context based search previous.
If in a parenthesis, go to opening parenthesis (Elisp like).
Otherwise move to previous paragraph."
  (interactive)
  (if (or (member (following-char) '(?\( ?\[ ?\{ ?\) ?\] ?\}))
          (member (preceding-char) '(?\) ?\] ?\}))
          (string= (symbol-at-point) "end"))
      (verilog-ext-backward-sexp)
    (backward-paragraph)))

;;; Typedef
;; Some functions to extract typedefs/classes from a set of directories and
;; update some variables accordingly.
;;
;; This enables the fontification and alignment via
;; `verilog-pretty-declarations' and `verilog-pretty-expr' of these types.
;;
;; To make it efficient it is required to update this regexp with `regexp-opt',
;; but doing it frequently to update the variable (e.g. on file opening, closing
;; or saving) gives a poor performance.  Hence the best approach is to run
;; `verilog-ext-typedef-batch-update' and update manually the value of
;; `verilog-align-typedef-regexp' in some other Elisp configuration file.
;;
;; Usage example:
;;  - Go to project directory, set by projectile, ggtags, project or current dir
;;
;;  - Set the variable `verilog-ext-align-typedef-uvm-dir' to include UVM directories:
;;      (setq verilog-ext-align-typedef-uvm-dir "/home/user/UVM/1800.2-2020-1.1/src/")
;;
;;  - M-x `verilog-ext-typedef-project-update' RET
;;
;;  - Wait for processing (might take some minutes depending on the number of files)
;;
;;  - Check if variables were updated:
;;     - C-h v `verilog-ext-align-typedef-words'
;;     - C-h v `verilog-ext-align-typedef-words-re'
;;     - C-h v `verilog-align-typedef-regexp'
;;
;;  - Update your init file with one of the two following options:
;;      a) Copy the value of `verilog-ext-align-typedef-words-re' and set it to `verilog-align-typedef-regexp'
;;      b) Copy the value of `verilog-ext-align-typedef-words', remove any undesired word and:
;;        - (setq verilog-align-typedef-regexp
;;             (eval-when-compile
;;                (verilog-regexp-words <pasted-value>)))
;;
(defconst verilog-ext-range-optional-re
  (concat "\\(\\s-*" verilog-range-re "\\)?"))
(defconst verilog-ext-range-or-class-params-optional-re
  (concat "\\(\\s-*\\(\\(" verilog-range-re "\\)\\|\\(#\\s-*([^)]*)\\)\\)\\)?"))
(defconst verilog-ext-typedef-var-decl-single-re
  (concat "\\<\\(?1:" verilog-identifier-re "\\)\\>" verilog-ext-range-or-class-params-optional-re "\\s-+"  ; Var type
          "\\<\\(?3:" verilog-identifier-re "\\)\\>\\s-*" verilog-ext-range-optional-re "\\s-*"              ; Var name
          "\\(?4:=.*\\)?" ; Optional initialization value
          ";")
  "Example:
type_t foo;
type_t [10:0] foo;
type_t [10:0] foo = \\='h0;")
(defconst verilog-ext-typedef-var-decl-multiple-re
  (concat "\\<\\(?1:" verilog-identifier-re "\\)\\>" verilog-ext-range-or-class-params-optional-re "\\s-+"  ; Var type
          "\\(?3:\\(" verilog-identifier-re "\\s-*,\\s-*\\)+\\(" verilog-identifier-re "\\s-*\\)\\)"                ; Var names
          ";")
  "Example:
type_t foo1, foo2 , foo4, foo6[], foo7 [25], foo8 ;")
(defconst verilog-ext-typedef-class-params-optional-re "\\(\\s-*#([^)]*)\\)?")
(defconst verilog-ext-typedef-class-re (concat "^\\s-*typedef\\s-+\\(?1:\\<class\\>\\)\\s-+\\(?2:\\<" verilog-identifier-re "\\>\\)"))
(defconst verilog-ext-typedef-generic-re (concat "^\\s-*typedef\\s-+\\(?1:\\<" verilog-identifier-re "\\>\\)"
                                                 "\\(" verilog-ext-typedef-class-params-optional-re "\\|" verilog-ext-range-optional-re "\\)"
                                                 "\\s-*\\(?2:\\<" verilog-identifier-re "\\>\\)"))


(defvar verilog-ext-align-typedef-words nil)
(defvar verilog-ext-align-typedef-words-re nil)


(defun verilog-ext-typedef--var-find (regex &optional limit)
  "Search for REGEX and bound to LIMIT.
Match data is expected to fits that one of
`verilog-ext-typedef-var-decl-single-re' or
`verilog-ext-typedef-var-decl-multiple-re'."
  (let (found pos type)
    (save-excursion
      (while (and (not found)
                  (verilog-re-search-forward regex limit t))
        (setq type (match-string-no-properties 1))
        (unless (or (member type verilog-keywords)
                    (save-excursion
                      (goto-char (match-beginning 1))
                      (verilog-in-parenthesis-p)))
          (setq found t)
          (setq pos (point)))))
    (when found
      (goto-char pos)
      type)))

(defun verilog-ext-typedef--var-buffer-update (regex)
  "Scan REGEX on current buffer and update list of user typedefs.
See `verilog-ext-align-typedef-words'.
Used for fontification and alignment."
  (let (type)
    (save-excursion
      (goto-char (point-min))
      (while (setq type (verilog-ext-typedef--var-find regex))
        (unless (member type verilog-ext-align-typedef-words)
          (push type verilog-ext-align-typedef-words))))))

(defun verilog-ext-typedef--tf-args-buffer-update ()
  "Scan functions/tasks arguments on current buffer to update user typedefs list.
See `verilog-ext-align-typedef-words'.
Used for fontification and alignment."
  (let (tf-args arg-proc) ; tf-args is expected to be a list of strings
    (save-excursion
      (goto-char (point-min))
      ;; Iterate over file functions and tasks
      (while (setq tf-args (alist-get 'args (verilog-ext-find-function-task-fwd)))
        (unless (equal tf-args '(""))
          (dolist (arg tf-args)
            ;; Iterate over words of one argument and process them to obtain the typedef
            (setq arg-proc arg)
            ;; Skip verilog keywords
            (while (string-match (concat "^" verilog-ext-keywords-re "\\s-*") arg-proc)
              (setq arg-proc (substring arg-proc (match-end 0) (length arg-proc))))
            ;; Typedef word will be the first one of the argument
            (when (equal 0 (string-match (string-remove-suffix ";" verilog-ext-typedef-var-decl-single-re) arg-proc))
              (setq arg-proc (car (split-string arg-proc " ")))
              (unless (member arg-proc verilog-ext-align-typedef-words)
                (push arg-proc verilog-ext-align-typedef-words)))))))))

(defun verilog-ext-typedef--class-buffer-update ()
  "Scan class declarations on current buffer to update user typedef list."
  (let (word)
    (save-excursion
      (goto-char (point-min))
      (while (setq word (alist-get 'name (verilog-ext-find-class-fwd)))
        (unless (member word verilog-ext-align-typedef-words)
          (push word verilog-ext-align-typedef-words))))))

(defun verilog-ext-typedef--typedef-buffer-update (regex)
  "Scan REGEX typedef declarations on current buffer to update user typedef list."
  (let (word)
    (save-excursion
      (goto-char (point-min))
      (while (verilog-re-search-forward regex nil t)
        (setq word (match-string-no-properties 2))
        (unless (member word verilog-ext-align-typedef-words)
          (push word verilog-ext-align-typedef-words))))))

(defun verilog-ext-typedef--var-decl-update ()
  "Scan and update Verilog buffers and update `verilog-ext-align-typedef-words'."
  (verilog-ext-typedef--var-buffer-update verilog-ext-typedef-var-decl-single-re)
  (verilog-ext-typedef--var-buffer-update verilog-ext-typedef-var-decl-multiple-re)
  (verilog-ext-typedef--tf-args-buffer-update)
  (verilog-ext-typedef--class-buffer-update)
  (verilog-ext-typedef--typedef-buffer-update verilog-ext-typedef-class-re)
  (verilog-ext-typedef--typedef-buffer-update verilog-ext-typedef-generic-re))

(defun verilog-ext-typedef-batch-update (dirs)
  "Scan recursively all (System)Verilog files under DIRS and udpate typedef list.

It will return the updated value of `verilog-ext-align-typedef-words', which can
be used later along with `verilog-regexp-words' to update the variable
`verilog-align-typedef-regexp'.  This enables the fontification and alignment of
user typedefs."
  (interactive "DDirectory: ")
  (unless (listp dirs)
    (setq dirs (list dirs)))
  (let (dir-files)
    (setq verilog-ext-align-typedef-words nil) ; Reset value
    (dolist (dir dirs)
      (setq dir-files (directory-files-recursively dir "\.s?vh?$" nil nil t)) ; Follow symlinks
      (dolist (file dir-files)
        (message "Processing %s ..." file)
        (with-temp-buffer
          (insert-file-contents file)
          (verilog-mode)
          (verilog-ext-typedef--var-decl-update))))
    ;; Postprocess obtained results (remove keywords and generic types that were uppercase)
    (mapc #'(lambda (elm)
                (when (member elm verilog-keywords)
                  (delete elm verilog-ext-align-typedef-words)))
            verilog-ext-align-typedef-words)
    (let ((case-fold-search nil))
      (setq verilog-ext-align-typedef-words (seq-remove #'(lambda (s)
                                                            (not (string-match-p "[[:lower:]]" s)))
                                                        verilog-ext-align-typedef-words)))
    ;; Store results
    (when verilog-ext-align-typedef-words
      (setq verilog-ext-align-typedef-words-re (verilog-regexp-words verilog-ext-align-typedef-words))
      (setq verilog-align-typedef-regexp verilog-ext-align-typedef-words-re))))

(defun verilog-ext-typedef-project-update ()
  "Update typedef list of current project.

If `verilog-ext-align-typedef-uvm-dir' is non nil, also include it
for the search of typedefs"
  (interactive)
  (let (proj-dir)
  (unless (setq proj-dir (verilog-ext-project-root))
    (error "Could not find project root!"))
  (verilog-ext-typedef-batch-update
   `(,proj-dir ,verilog-ext-align-typedef-uvm-dir))))


;;; Compile/Makefile
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
       (error "Binary verilator not found in $PATH")))
    ;; Verilog-Perl
    ("vppreproc"
     (if (executable-find "vppreproc")
         (setq verilog-preprocessor "vppreproc __FLAGS__ __FILE__")
       (error "Binary vppreproc not found in $PATH")))
    ;; Icarus Verilog:  `iverilog' command syntax requires writing to an output file (defaults to a.out).
    ("iverilog"
     (if (executable-find "iverilog")
         (let* ((filename-sans-ext (file-name-sans-extension (file-name-nondirectory (buffer-file-name))))
                (iver-out-file (read-string "Output filename: " (concat filename-sans-ext "_pp.sv"))))
           (setq verilog-preprocessor (concat "iverilog -E -o" iver-out-file " __FILE__ __FLAGS__")))
       (error "Binary iverilog not found in $PATH"))))
  (verilog-preprocess)
  (pop-to-buffer "*Verilog-Preprocessed*"))

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


;;; Beautify
;; Indent, align parameters and ports:
;;  - Interactively for module at point
;;  - Interactively for current buffer
;;  - In batch for files of current directory

(defun verilog-ext-module-at-point--align (thing)
  "Align THING of current module at point (ports/parameters)."
  (let ((case-fold-search nil)
        (re "\\(\\s-*\\)(")
        (current-ids (verilog-ext-instance-at-point))
        (idx (cond ((eq thing 'parameters) 1)
                   ((eq thing 'ports) 2)
                   (t (error "Invalid thing to align"))))
        current-module beg end)
    (unless current-ids
      (user-error "Not inside an instance!"))
    (setq current-module (car current-ids))
    (save-excursion
      (goto-char (match-beginning idx))
      (verilog-re-search-forward "(" nil t)
      (verilog-forward-syntactic-ws)
      (setq beg (point))
      (verilog-backward-up-list -1)
      (backward-char)
      (verilog-backward-syntactic-ws)
      (setq end (point)))
    (align-regexp beg end re 1 1 nil)
    (if (eq idx 1)
        (message "Parameters of %s aligned..." current-module)
      (message "Ports of %s aligned..." current-module))))

(defun verilog-ext-module-at-point-align-ports ()
  "Align ports of current module."
  (interactive)
  (verilog-ext-module-at-point--align 'ports))

(defun verilog-ext-module-at-point-align-params ()
  "Align parameters of current module."
  (interactive)
  (verilog-ext-module-at-point--align 'parameters))

(defun verilog-ext-module-at-point-indent ()
  "Indent current module."
  (interactive)
  (let ((case-fold-search nil)
        (current-ids (verilog-ext-instance-at-point))
        current-module beg end)
    (unless current-ids
      (user-error "Not inside an instance!"))
    (setq current-module (car current-ids))
    (save-excursion
      (goto-char (match-beginning 0))
      (beginning-of-line)
      (setq beg (point))
      (goto-char (match-end 0))
      (end-of-line)
      (setq end (point)))
    (verilog-ext-indent-region beg end)
    (message "Indented %s" current-module)))

(defun verilog-ext-module-at-point-beautify ()
  "Beautify current module:
- Indent
- Align ports
- Align parameters"
  (interactive)
  (save-excursion
    (verilog-ext-module-at-point-indent)
    (verilog-ext-module-at-point-align-ports)
    (verilog-ext-module-at-point-align-params)))

(defun verilog-ext-beautify-current-buffer ()
  "Beautify current buffer:
- Indent whole buffer
- Beautify every instantiated module
- Untabify and delete trailing whitespace"
  (interactive)
  (save-excursion
    (verilog-ext-indent-region (point-min) (point-max))
    (goto-char (point-min))
    (while (verilog-ext-find-module-instance-fwd)
      (verilog-ext-module-at-point-beautify))
    (untabify (point-min) (point-max))
    (delete-trailing-whitespace (point-min) (point-max))))

(defun verilog-ext-beautify-files (files)
  "Beautify Verilog FILES.
FILES is a list of strings containing the filepaths."
  (dolist (file files)
    (unless (file-exists-p file)
      (error "File %s does not exist! Aborting!" file)))
  (save-window-excursion
    (dolist (file files)
      (find-file file)
      (verilog-mode)
      (verilog-ext-beautify-current-buffer)
      (write-file file))))

(defun verilog-ext-beautify-dir-files (dir)
  "Beautify Verilog files on DIR."
  (interactive "DDirectory: ")
  (let ((files (directory-files-recursively dir "\\.[s]?v[h]?$")))
    (verilog-ext-beautify-files files)))

;;; Imenu
;; Improved `imenu' functionality
;;  - Show instances of current module
;;  - Show classes and their methods
(defconst verilog-ext-imenu-top-re        "^\\s-*\\(?1:connectmodule\\|m\\(?:odule\\|acromodule\\)\\|p\\(?:rimitive\\|rogram\\|ackage\\)\\)\\(\\s-+automatic\\)?\\s-+\\(?2:[a-zA-Z0-9_.:]+\\)")
(defconst verilog-ext-imenu-localparam-re "^\\s-*localparam\\(?1:\\s-+\\(logic\\|bit\\|int\\|integer\\)\\s-*\\(\\[.*\\]\\)?\\)?\\s-+\\(?2:[a-zA-Z0-9_.:]+\\)")
(defconst verilog-ext-imenu-define-re     "^\\s-*`define\\s-+\\([a-zA-Z0-9_.:]+\\)")
(defconst verilog-ext-imenu-assign-re     "^\\s-*assign\\s-+\\([a-zA-Z0-9_.:]+\\)")
(defconst verilog-ext-imenu-generate-re   "^\\s-*generate[ \t\n]*\\(?1:.*\\)")
(defconst verilog-ext-imenu-always-re     "^\\s-*always\\(_ff\\|_comb\\|_latch\\)?\\s-*\\(.*\\)\\(begin\\)?[ |\n]*\\(.*\\)")
(defconst verilog-ext-imenu-initial-re    "^\\s-*initial\\s-+\\(.*\\)\\(begin\\)?[ |\n]*\\(.*\\)")

(defvar verilog-ext-imenu-generic-expression
  `(;; Search by regexp
    ("*Top*"            ,verilog-ext-imenu-top-re 2)
    ("*Localparams*"    ,verilog-ext-imenu-localparam-re 2)
    ("*Defines*"        ,verilog-ext-imenu-define-re 1)
    ("*Assigns*"        ,verilog-ext-imenu-assign-re 1)
    ("*Generates*"      ,verilog-ext-imenu-generate-re 1)
    ("*Always blocks*"  ,verilog-ext-imenu-always-re 4)
    ("*Initial blocks*" ,verilog-ext-imenu-initial-re 3)))

(defun verilog-ext-imenu-find-module-instance-index ()
  "Create imenu entries of modules and instances.
Placing this outside of `imenu--generic-function' avoids running it if
`which-func' is enabled.  It also allows to conditionally disable the index
building if file cannot contain instances."
  (save-excursion
    (goto-char (point-max))
    (let ((group-name "*Instances*")
          index)
      (when verilog-ext-file-allows-instances
        (while (verilog-ext-find-module-instance-bwd)
          ;; Use capture group index 3 to get instance name
          (push (cons (match-string-no-properties 1) (line-beginning-position)) index))
        (when index
          (list (cons group-name index)))))))

(defun verilog-ext-imenu-find-tf-outside-class-index ()
  "Create entries of tasks and functions outside classes.
Group the ones that belong to same external method definitions."
  (save-excursion
    (goto-char (point-max))
    (let ((tf-group-name "*Task/Func*")
          index node data pos name class-name)
      (while (setq data (verilog-ext-find-function-task-bwd))
        (unless (verilog-ext-point-inside-block-p 'class)
          ;; Get information from the subroutine
          (setq pos (alist-get 'pos data))
          (setq name (alist-get 'name data))
          (setq class-name (alist-get 'class-name data))
          ;; Add element to the tree
          (setq node (cons name pos))
          (if class-name
              ;; Externally declared methods
              (if (not (assoc class-name index))
                  (setq index `((,class-name ,node)))
                ;; Add to existing class
                (setf (cdr (assoc class-name index)) (cons node (cdr (assoc class-name index)))))
            ;; Non-methods
            (if (not (assoc tf-group-name index))
                (setq index `((,tf-group-name ,node)))
              (setf (cdr (assoc tf-group-name index)) (cons node (cdr (assoc tf-group-name index))))))))
      index)))

(defun verilog-ext-imenu--format-class-item-label (type name modifiers)
  "Return Imenu label for single node using TYPE, NAME and MODIFIERS."
  (let* ((prop-name (propertize name 'face '(:foreground "goldenrod" :weight bold)))
         (short-type (pcase type
                       ("task"     " [T]")
                       ("function" " [F]")
                       ("class"    "")
                       (_          type)))
         (modifiers-string (mapconcat #'(lambda (x) (substring-no-properties x 0 1)) modifiers ""))
         (prop-modifiers (if (string= modifiers-string "")
                             ""
                           (propertize (concat " (" modifiers-string ")") 'face 'italic))))
    (format "%s%s%s" prop-name short-type prop-modifiers)))

(defun verilog-ext-imenu--class-put-parent (type name pos tree modifiers)
  "Create parent node (classes).
Use TYPE, NAME and MODIFIERS to format the node name.
Create cons cell with the label and the POS if it is a leaf node.
Otherwsise create the cons cell with the label and the TREE."
  (let* ((label (verilog-ext-imenu--format-class-item-label type name modifiers)))
    (if (not tree)
        (cons label pos)
      (cons label tree))))

(defun verilog-ext-imenu--build-class-tree (&optional tree)
  "Build the imenu class alist TREE recursively.
Find recursively tasks and functions inside classes."
  (save-restriction
    (narrow-to-region (point-min) (point))
    (let* ((data (progn
                   (verilog-ext-find-class-bwd)
                   (verilog-forward-sexp)
                   (verilog-ext-find-function-task-class-bwd)))
           (pos (when data
                  (save-excursion
                    (goto-char (alist-get 'pos data))
                    (line-beginning-position))))
           (type (alist-get 'type data))
           (name (alist-get 'name data))
           (modifiers (alist-get 'modifiers data))
           (label (when name
                    (verilog-ext-imenu--format-class-item-label type name modifiers))))
      (cond ((not pos)
             nil)
            ((verilog-ext-looking-at-class-declaration)
             (verilog-ext-imenu--class-put-parent type name pos tree modifiers))
            ((or (string= type "function")
                 (string= type "task"))
             (verilog-ext-imenu--build-class-tree (cons (cons label pos) tree)))
            (t ; Build subtrees recursively
             (verilog-ext-imenu--build-class-tree
              (cons (verilog-ext-imenu--build-class-tree
                     (list (cons label pos))) tree)))))))

(defun verilog-ext-imenu-classes-index ()
  "Create entries of tasks and functions within classes."
  (save-excursion
    (goto-char (point-max))
    (let (index tree)
      (while (setq tree (verilog-ext-imenu--build-class-tree))
        (setq index (cons tree index)))
      (when index
        (list (cons "*Classes*" index))))))

(defun verilog-ext-imenu-index ()
  "Index builder function for Verilog Imenu.
Makes use of `verilog-ext-imenu-generic-expression' for everything but classes
and methods.  These are collected with `verilog-ext-imenu-classes-index'."
  (append (verilog-ext-imenu-find-module-instance-index)
          (verilog-ext-imenu-classes-index)
          (verilog-ext-imenu-find-tf-outside-class-index)
          (imenu--generic-function verilog-ext-imenu-generic-expression)))


;;;; Imenu-list
(defun verilog-ext-imenu-list ()
  "Wrapper for `imenu-list' for Verilog mode with `verilog-ext'."
  (interactive)
  (imenu-list)
  (goto-char (point-min)))


;;; Templates
;; Custom and `yasnippet' templates for insertion with `hydra'.
(defmacro verilog-ext-template (&rest body)
  "Execute BODY, indent region and place point at proper place."
  (declare (indent 0) (debug t))
  `(let ((pos-end (make-marker))
         ind-beg ind-end)
     (setq ind-beg (line-beginning-position))
     ,@body
     (setq ind-end (line-end-position))
     (indent-region ind-beg ind-end)
     (when (marker-position pos-end)
       (goto-char (marker-position pos-end)))
     (electric-verilog-tab)))

(defun verilog-ext-templ-begin-end ()
  "Insert begin/end block."
  (interactive)
  (verilog-ext-template
    (insert "begin")
    (newline)
    (set-marker pos-end (point))
    (newline)
    (insert "end")))

(defun verilog-ext-templ-block-comment (&optional comment)
  "Create a comment block.

  ///////////////////
  // Block COMMENT //
  ///////////////////"
  (interactive)
  (let* ((block-comment-char ?\/)
         (block-comment (or comment (read-string "Name: ")))
         (block-comment-width (string-width block-comment)))
    (verilog-ext-template
      (insert-char block-comment-char (+ block-comment-width 6))
      (newline)
      (insert-char block-comment-char 2)
      (insert " ")
      (insert block-comment)
      (insert " ")
      (insert-char block-comment-char 2)
      (newline)
      (insert-char block-comment-char (+ block-comment-width 6) nil)
      (newline))))

(defun verilog-ext-templ-case (&optional expr cases)
  "Case template.

Read/add expressions until an empty string is entered.

If EXPR is non-nil, use it as case expression.
If CASES is non-nil it must be a list of all the possible
cases to iterate over."
  (interactive)
  (let (param-read)
    (verilog-ext-template
      (insert "case (" (or expr (read-string "Expression: ")) ")\n\n")
      (if cases
          (dolist (case cases)
            (insert (concat case ": begin\n"))
            (insert (concat "// Output statements... \n"))
            (insert (concat "end\n\n")))
        (while (not (string-equal (setq param-read (read-string "Case: ")) ""))
          (insert (concat param-read ": begin\n"))
          (insert (concat "// Output statements... \n"))
          (insert (concat "end\n\n"))))
      (insert "endcase\n"))))

(defun verilog-ext-templ--compute-vector-width ()
  "Prompt for vector width and return expression:
- If a constant identifier is provided return [CONSTANT-1:0].
- If a number greater than 1 is provided, calculate width.
- If set to 0 or 1 (or negative) return a nil string."
  (let* ((width-str (read-string "Width: "))
         (width-num (string-to-number width-str)))
    ;; Cover width eq 0 and 1 cases
    (when (or (string-equal width-str "0")
              (string-equal width-str ""))
      (setq width-num 1))
    (if (not (eq width-num 0)) ; Number different from 0, not a constant
        (if (> width-num 1)    ; Vector with brackets
            (progn
              (setq width-num (1- width-num))
              (setq width-str (number-to-string width-num))
              (concat "[" width-str ":0]"))
          "") ; Width equals 1
      (concat "[" width-str "-1:0]")))) ; Width constant

(defun verilog-ext-templ-enum-typedef (&optional typedef logic name)
  "Insert enum template.

If TYPEDEF is non-nil, declare a typedef enum type.
If LOGIC is non-nil, declare it as logic type.
If NAME is non-nil, set it as the user type.

Read/add labels until an empty string is entered.

Return a list of the enum labels."
  (let ((width "")
        (enum-types '("logic" "bit" "int" "integer" "other"))
        enum-item type enum-labels)
    (verilog-ext-template
      (when typedef
        (insert "typedef "))
      (if logic
          (setq type "logic")
        (setq type (completing-read "Type: " enum-types)))
      (when (string-equal type "other")
        (setq type (read-string "Type: ")))
      (if (or (string-equal type "logic")
              (string-equal type "bit"))
          (setq width (verilog-ext-templ--compute-vector-width))
        (setq width "")) ; Disable width field If not a vector
      (insert "enum " type " " width " {")
      (while (not (string-equal (setq enum-item (read-string "Item: ")) ""))
        (push (upcase enum-item) enum-labels)
        ;; (add-to-list 'enum-labels (upcase enum-item) :append)
        (insert (upcase enum-item) ", "))
      (delete-char -2)
      (insert "} ")
      (if name
          (insert name ";")
        ;; Else
        (if typedef
            (insert (read-string "Type Name: ") ";")
          (insert (read-string "Enum Name: ") ";"))))
    (reverse enum-labels)))

(defun verilog-ext-templ-struct-typedef (&optional typedef union)
  "Insert struct template.

If TYPEDEF is non-nil, declare a typedef struct type.
If UNION is non-nil, declare a union instead of a struct.

Read/add elements of struct until an empty string is entered."
  (let ((width "")
        struct-item type)
    (verilog-ext-template
      (when typedef
        (insert "typedef "))
      (if union
          (insert "union ")
        (insert "struct "))
      (when (yes-or-no-p "Packed?")
        (insert "packed "))
      (insert "{\n")
      (while (not (string-equal (setq struct-item (read-string "Item: ")) ""))
        (setq type (read-string "Type: " "logic"))
        (if (or (string-equal type "logic") (string-equal type "bit"))
            (setq width (verilog-ext-templ--compute-vector-width))
          (setq width "")) ; Disable width field if not a vector
        (insert type " " width " " struct-item ";\n"))
      (insert "} ")
      (if typedef
          (insert (read-string "Type Name: ") ";")
        (insert (read-string "Struct Name: ") ";")))
    ;; Align declarations
    (save-excursion
      (verilog-re-search-backward "(" nil t)
      (forward-char)
      (verilog-forward-syntactic-ws)
      (verilog-pretty-declarations))))

(defun verilog-ext-templ--task-add-port (direction signal)
  "Add SIGNAL with DIRECTION to task template.
DIRECTION should be either input or output."
  (let ((type (read-string "Type: " "logic"))
        width)
    (if (or (string-equal type "logic")
            (string-equal type "bit"))
        (setq width (concat (verilog-ext-templ--compute-vector-width) " "))
      (setq width "")) ; Disable width field if not a vector
    (insert (symbol-name direction) " " type " " width signal ",\n")))

(defun verilog-ext-templ-task ()
  "Insert a task definition."
  (interactive)
  (let (inputs outputs)
    (verilog-ext-template
      (insert "task ")
      (insert (read-string "Task name: ") " (\n")
      (while (not (string-equal (setq inputs (read-string "Input signal: ")) ""))
        (verilog-ext-templ--task-add-port 'input inputs))
      (while (not (string-equal (setq outputs (read-string "Output signal: ")) ""))
        (verilog-ext-templ--task-add-port 'output outputs))
      (delete-char -2)
      (insert "\n);\n")
      (set-marker pos-end (point))
      (insert "\nendtask"))
    ;; Align declarations
    (save-excursion
      (verilog-re-search-backward "(" nil t)
      (forward-char)
      (verilog-forward-syntactic-ws)
      (verilog-pretty-declarations))))

(defun verilog-ext-templ-def-logic ()
  "Insert a definition of signal under point at the beginning of current module."
  (interactive "*")
  (let ((sig (thing-at-point 'symbol :no-prop))
        str)
    (cond ((not sig)
           (user-error "No signal at point"))
          ((not (string-match verilog-identifier-re sig))
           (user-error "Not a valid verilog identifier"))
          ((member sig verilog-keywords)
           (message "object at point (%s) is a keyword" sig))
          (t
           (save-excursion
             (verilog-re-search-backward verilog-ext-top-re nil nil)
             (verilog-end-of-statement)
             (verilog-forward-syntactic-ws)
             (split-line)
             (setq str (concat "logic " (verilog-ext-templ--compute-vector-width) " " sig ";"))
             (insert str)
             (message (concat "[Line " (format "%s" (line-number-at-pos)) "]: " str)))))))

(defun verilog-ext-templ-fsm (&optional async)
  "Insert a state machine custom definition with two always blocks.
One for next state and output logic and one for the state registers.
If ASYNC is non-nil create an asynchronous reset."
  (interactive)
  (let* ((state-type (read-string "Name of state typedef: " "state_t"))
         (state-var  (read-string "Name of state variable: " "state"))
         (next-state-var (concat "next_" state-var))
         (enum-labels))
    ;; Define state enum typedef
    (verilog-ext-template
      (setq enum-labels (verilog-ext-templ-enum-typedef :typedef :logic state-type))
      (newline)
      (insert state-type " " state-var ", " next-state-var ";\n\n"))
    ;; Synchronous logic
    (verilog-ext-template
      (insert "// State FF for " state-var "\n")
      (insert "always_ff @ (posedge " verilog-ext-templ-clock)
      (when async
        (insert " or negedge " verilog-ext-templ-resetn))
      (insert ") begin\n")
      (insert "if (!" verilog-ext-templ-resetn ")\n")
      (insert state-var " <= " (car enum-labels) ";\n")
      (insert "else\n")
      (insert  state-var " <= " next-state-var ";\n")
      (insert "end\n\n"))
    ;; Combinational block
    (verilog-ext-template
      (insert "// Output and next State Logic for " state-var "\n")
      (insert "always_comb begin\n")
      (verilog-ext-templ-case state-var enum-labels)
      (insert "end\n"))))

(defun verilog-ext-templ-header ()
  "Insert a standard Verilog file header."
  (interactive)
  (let (string)
    (save-excursion
      (goto-char (point-min))
      (insert "\
//-----------------------------------------------------------------------------
// Title         : <title>
// Project       : <project>
//-----------------------------------------------------------------------------
// File          : <filename>
// Author        : <author>
// Created       : <credate>
// Last modified : <moddate>
//-----------------------------------------------------------------------------
// Description :
// <description>
//-----------------------------------------------------------------------------
// Copyright (c) <author>
//
//------------------------------------------------------------------------------
// Modification history:
// <modhist>
//-----------------------------------------------------------------------------

")
      (goto-char (point-min))
      (search-forward "<filename>")
      (replace-match (buffer-name) t t)
      (search-forward "<author>")
      (replace-match (user-full-name) t t)
      (search-forward "<credate>")
      (replace-match "" t t)
      (verilog-insert-date)
      (search-forward "<moddate>")
      (replace-match "" t t)
      (verilog-insert-date)
      (search-forward "<author>")
      (replace-match (concat (user-full-name) " <" user-mail-address ">") t t)
      (search-forward "<modhist>")
      (replace-match "" t t)
      (verilog-insert-date)
      (insert " : created")
      (goto-char (point-min))
      (setq string (read-string "Title: "))
      (search-forward "<title>")
      (replace-match string t t)
      (setq string (read-string "Project: " verilog-project))
      (setq verilog-project string)
      (search-forward "<project>")
      (replace-match string t t)
      (search-forward "<description>")
      (replace-match "" t t)
      (insert (read-string "Description: ")))))


;;;; Instances
(defvar verilog-ext-templ-inst-auto-header "// Beginning of Verilog AUTO_TEMPLATE")
(defvar verilog-ext-templ-inst-auto-footer "// End of Verilog AUTO_TEMPLATE")

(defun verilog-ext-templ-inst-auto (template)
  "Insert header and footer to TEMPLATE strings for instantiation."
  (concat "\n" verilog-ext-templ-inst-auto-header " " template " " verilog-ext-templ-inst-auto-footer "\n"))

(defvar verilog-ext-templ-inst-auto-conn-ports
  (verilog-ext-templ-inst-auto "
/* <module> AUTO_TEMPLATE (
 .\\(.*\\) (\\1),
 ); */")
  "Template with connected ports (same signal name as the port).")

(defvar verilog-ext-templ-inst-auto-disc-ports
  (verilog-ext-templ-inst-auto "
/* <module> AUTO_TEMPLATE (
 .\\(.*\\) (),
 ); */")
  "Template with disconnected ports.")

(defvar verilog-ext-templ-inst-auto-conn-ports-ss
  (verilog-ext-templ-inst-auto "
/* <module> AUTO_TEMPLATE (
 .\\(.*\\) (\\1[]),
 ); */")
  "Template with connected ports and subscripts.")

(defvar verilog-ext-templ-inst-auto-simple "\
<module> <instance_name> (/*AUTOINST*/);
")

(defvar verilog-ext-templ-inst-auto-params "\
<module> # (/*AUTOINSTPARAM*/) <instance_name> (/*AUTOINST*/);
")


(defun verilog-ext-templ-inst-auto--choose-template ()
  "Choose current // AUTO_TEMPLATE for instantiation.
Syntactic sugar for `verilog-ext-templ-inst-auto-from-file'."
  (let (templates-list)
    (setq templates-list (completing-read "AUTO_TEMPLATE: " '("Connected Ports" "Disconnected Ports" "Connected Ports with subscripts")))
    (pcase templates-list
      ("Connected Ports"                 verilog-ext-templ-inst-auto-conn-ports)
      ("Disconnected Ports"              verilog-ext-templ-inst-auto-disc-ports)
      ("Connected Ports with subscripts" verilog-ext-templ-inst-auto-conn-ports-ss)
      (_                                 (error "Error @ verilog-ext-templ-choose-template: Unexpected string")))))

(defun verilog-ext-templ-inst-auto--choose-autoinst ()
  "Choose current /*AUTOINST*/ (and /*AUTOPARAMINST*/) for instantiation.
Syntactic sugar for `verilog-ext-templ-inst-auto-from-file'."
  (let (autoinst-list)
    (setq autoinst-list (completing-read "AUTOINST:" '("Simple" "With Parameters")))
    (pcase autoinst-list
      ("Simple"          verilog-ext-templ-inst-auto-simple)
      ("With Parameters" verilog-ext-templ-inst-auto-params)
      (_                 (error "Error @ verilog-ext-templ-choose-autoinst: Unexpected string")))))

(defun verilog-ext-templ-inst-auto--autoinst-processing ()
  "Process AUTOINST generated code after auto expansion.
Syntactic sugar for `verilog-ext-templ-inst-auto-from-file'."
  (let (beg end)
    (save-excursion ;; Remove comments
      (setq beg (point))
      (if (re-search-forward ")[[:blank:]]*;[[:blank:]]*// Templated" nil t)
          (setq end (point))
        (error "Couldn't process AUTOINST.  Does module have ports?"))
      (verilog-ext-replace-regexp "[[:blank:]]*// Templated" "" beg end))
    (save-excursion ;; Open final parenthesis
      (re-search-forward "));")
      (backward-char 2)
      (electric-verilog-terminate-line))
    ;; Remove /*AUTOINST*/
    (save-excursion
      (setq beg (point))
      (setq end (re-search-forward ");")) ; Last /*AUTOINST*/ comment by AUTO_TEMPLATE
      (verilog-ext-replace-string "/*AUTOINST*/" "" beg end))))

(defun verilog-ext-templ-inst-auto--autoparam-processing ()
  "Process AUTOPARAM/AUTOINSTPARAM generated code after auto expansion.
Syntactic sugar for `verilog-ext-templ-inst-auto-from-file'."
  (let (beg end)
    (save-excursion
      (setq beg (point))
      (if (re-search-forward "))" nil t)
          (setq end (point))
        (error "Couldn't process AUTOPARAM Does module have parameters?"))
      (backward-char 1)
      (electric-verilog-terminate-line))
    ;; Remove /*AUTOINSTPARAM*/
    (save-excursion
      (setq beg (point))
      (setq end (re-search-forward ");" nil t))
      (verilog-ext-replace-string "/*AUTOINSTPARAM*/" "" beg end)
      ;; Remove ' // Parameters ' string
      (forward-line 1)
      (beginning-of-line)
      (kill-line 1))))

(defun verilog-ext-templ-inst-auto-from-file (file &optional template inst-template)
  "Instantiate top module present in FILE.

If there is more than one module, prompt for a list of detected modules.

Use auto TEMPLATE or prompt to choose one if nil.
Use inst INST-TEMPLATE or prompt to choose one if nil."
  (interactive "FSelect module from file:\nP")
  (let* ((module-name (verilog-ext-select-file-module file))
         (start-template (point))
         end-template end-instance instance-name start-instance autoparam)
    ;; Checks and env setup
    (unless buffer-file-name
      (error "Current buffer needs to visit a file to instantiate module"))
    (unless module-name
      (error "No module found in %s" file))
    (unless (verilog-ext-point-inside-block-p 'module)
      (error "Point is not inside a module block.  Cannot instantiate block"))
    (setq instance-name (read-string "Instance-name: " (concat "I_" (upcase module-name))))
    (add-to-list 'verilog-library-files file)
    ;; Prepare instantiation template
    (unless template
      (setq template (verilog-ext-templ-inst-auto--choose-template)))
    (unless inst-template
      (setq inst-template (verilog-ext-templ-inst-auto--choose-autoinst)))
    (when (equal inst-template verilog-ext-templ-inst-auto-params)
      (setq autoparam t))
    ;; Instantiate module/instance
    (insert template)
    (setq end-template (point))
    (verilog-ext-replace-string "<module>" module-name start-template end-template)
    (setq start-instance (point))
    (insert inst-template)
    (setq end-instance (point))
    (verilog-ext-replace-string "<module>" module-name start-instance end-instance)
    (verilog-ext-replace-string "<instance_name>" instance-name start-instance end-instance)
    (verilog-auto) ; Might change positions of some variables!
    ;; Postprocess instantiation
    (goto-char (point-min))
    (search-forward verilog-ext-templ-inst-auto-footer)
    (forward-line)
    (verilog-ext-templ-inst-auto--autoinst-processing)
    (when autoparam
      (verilog-ext-templ-inst-auto--autoparam-processing))
    ;; Remove AUTO_TEMPLATE comment code
    (setq start-template (search-backward verilog-ext-templ-inst-auto-header))
    (setq start-instance (search-forward verilog-ext-templ-inst-auto-footer))
    (delete-region start-template (1+ start-instance))
    ;; Beautify (indent and align) instantiation
    (search-forward instance-name)
    (verilog-ext-module-at-point-beautify)))

(defun verilog-ext-templ-inst-auto-from-file-simple (file)
  "Instantiate from FILE with simple template: connected ports and no parameters."
  (interactive "FSelect module from file:")
  (verilog-ext-templ-inst-auto-from-file file
                                         verilog-ext-templ-inst-auto-conn-ports
                                         verilog-ext-templ-inst-auto-simple))

(defun verilog-ext-templ-inst-auto-from-file-params (file)
  "Instantiate from FILE with params template: connected ports with parameters."
  (interactive "FSelect module from file:")
  (verilog-ext-templ-inst-auto-from-file file
                                         verilog-ext-templ-inst-auto-conn-ports
                                         verilog-ext-templ-inst-auto-params))

(defun verilog-ext-templ-inst-auto-from-file-tb-dut (file)
  "Instantiate from FILE with params template:
- Connected ports with subscripts with parameters.
- Required by TB template instantiation to auto detect width of signals."
  (interactive "FSelect module from file:")
  (verilog-ext-templ-inst-auto-from-file file
                                         verilog-ext-templ-inst-auto-conn-ports-ss
                                         verilog-ext-templ-inst-auto-params))

(defun verilog-ext-templ-inst-auto-from-file-prompt (file)
  "Instantiate from FILE and prompt for template and parameters."
  (interactive "FSelect module from file:")
  (verilog-ext-templ-inst-auto-from-file file))


;;;; Testbenches
(defun verilog-ext-templ-testbench-simple-from-file (file outfile)
  "Instantiate basic testbench from FILE's top module into OUTFILE."
  (interactive "FSelect DUT from file:\nFOutput file: ")
  (when (file-exists-p outfile)
    (error "File %s exists" outfile))
  (let ((module-name (verilog-ext-select-file-module file))
        beg end)
    (find-file outfile)
    (insert "\
module tb_<module_name> () ;

    // Simulation parameters
    timeprecision 1ps;
    timeunit      1ns;

    localparam CLKT = 10ns;  // 100 MHz

    // TODO: INIT after (verilog-auto)!!
    // DUT instance parameters
    /*AUTOINOUTPARAM(\"<module_name>\")*/
    // End of /*AUTOINOUTPARAM*/

    // Non-auto signals
    logic <clock> = 1'b0;
    logic <resetn> = 1'b1;

    // TODO: Init during declaration (before simulation time 0) to avoid race conditions
    /* DUT Inputs */
    /*AUTOREGINPUT*/

    /* DUT Outputs */
    /*AUTOLOGIC*/


    // System Clock
    always begin
        #(CLKT/2) <clock> = ~<clock>;
    end

    // TODO: Declare/Connect interfaces
    // axi4_lite_if axil_if_<module_name> (.Clk(<clock>), .Rst_n(<resetn>));
    // ...

    // TODO: Ensure SV interfaces connections
    // DUT Instantiation

    // TODO: Tasks/functions
    // ...

    // TODO: TB Objects
    // axi4_lite_bfm bfm;

    // TODO: Stimuli
    initial begin
        // bfm = new(axil_if_<module_name>);
        //
        // #10 Rst_n = 0;
        //
        // bfm.read();
        // bfm.write();
        // ...
        // ...
        $display(\"@%0d: TEST PASSED\", $time);
        $finish;
    end

endmodule // tb_<module_name>
")
    (setq verilog-ext-file-allows-instances t)
    ;; Replace template parameters, instantiate DUT and create header
    (verilog-ext-replace-string "<module_name>" module-name (point-min) (point-max))
    (verilog-ext-replace-string "<clock>" verilog-ext-templ-clock (point-min) (point-max))
    (verilog-ext-replace-string "<resetn>" verilog-ext-templ-resetn (point-min) (point-max))
    (goto-char (point-min))
    (search-forward "// DUT Instantiation")
    (verilog-ext-templ-inst-auto-from-file-tb-dut file)
    (verilog-ext-templ-header)
    ;; Postprocess /*AUTOINOUTPARAM*/
    (save-excursion
      (goto-char (point-min))
      (setq beg (search-forward (concat "/*AUTOINOUTPARAM(\"" module-name "\")*/")))
      (setq end (search-forward "// End of /*AUTOINOUTPARAM*/"))
      (verilog-ext-replace-regexp (concat "logic\\s-+\\(" verilog-identifier-re "\\)") "localparam \\1 = 0" beg end))
    ;; Beautify declarations and initialize values
    (save-excursion
      (goto-char (point-min))
      (search-forward "/*AUTOREGINPUT*/")
      (save-excursion ; Init to '0 every input signal
        (setq beg (point))
        (forward-paragraph 1)
        (setq end (point))
        (verilog-ext-replace-regexp (concat "\\(logic\\s-+\\(\\[[^]]*\\]\\s-*\\)*" verilog-identifier-re "\\);") "\\1 = '0;" beg end)
        (goto-char beg)
        (forward-line 2)
        (verilog-pretty-declarations)
        (verilog-pretty-expr))
      (save-excursion ; Align // To or // From auto comments if `verilog-auto-wire-comment' is non-nil
        (setq beg (point))
        (forward-paragraph 2)
        (setq end (point))
        (align-regexp beg end "\\(\\s-*\\)//" 1 1 nil)))
    ;; Delete /*AUTO[.*]*/ , generated code and instantiation subscripts (needed to autodetect width of signals)
    (goto-char (point-min))
    (save-excursion
      (search-forward "// DUT Instantiation")
      (verilog-ext-replace-regexp (concat "\\(\\." verilog-identifier-re "\\s-*(" verilog-identifier-re "\\)\\(\\[.*\\]\\)") "\\1"
                                  (point) (verilog-pos-at-end-of-statement)))
    (save-excursion
      (while (re-search-forward "/\\*AUTO.*\*\/" nil t)
        (beginning-of-line)
        (kill-line 1)))
    (save-excursion
      (while (search-forward "// Beginning of automatic" nil t)
        (beginning-of-line)
        (kill-line 1)))
    (save-excursion
      (while (search-forward "// End of automatics" nil t)
        (beginning-of-line)
        (kill-line 1)))
    (search-forward "// TODO")
    (write-file outfile)))


;;;; Yasnippet/Hydra
(defun verilog-ext-insert-yasnippet (snippet)
  "Insert SNIPPET programatically."
  (insert snippet)
  (yas-expand))

(defun verilog-ext-add-snippets ()
  "Add snippets and reload Yasnippet to make them available."
  (add-to-list 'yas-snippet-dirs verilog-ext-snippets-dir)
  (yas-reload-all))

(defhydra verilog-ext-hydra (:color blue
                             :hint nil)
  ("aa"  (verilog-ext-insert-yasnippet "aa")      "always" :column "A-C")
  ("ac"  (verilog-ext-insert-yasnippet "ac")      "always_comb")
  ("af"  (verilog-ext-insert-yasnippet "af")      "always_ff")
  ("ai"  (verilog-ext-insert-yasnippet "ai")      "assert immediate")
  ("ap"  (verilog-ext-insert-yasnippet "ap")      "assert property")
  ("as"  (verilog-ext-insert-yasnippet "as")      "assign")
  ("beg" (verilog-ext-insert-yasnippet "beg")     "begin/end")
  ("cc"  (verilog-ext-templ-case)                 "case")
  ("cls" (verilog-ext-insert-yasnippet "cls")     "class")
  ("cb"  (verilog-ext-insert-yasnippet "cb")      "clocking block")
  ("ct"  (verilog-ext-insert-yasnippet "ct")      "constraint")
  ("cg"  (verilog-ext-insert-yasnippet "cg")      "covergroup")
  ("d"   (verilog-ext-insert-yasnippet "d")       "display" :column "D-F")
  ("ei"  (verilog-ext-insert-yasnippet "ei")      "else if")
  ("el"  (verilog-ext-insert-yasnippet "el")      "else")
  ("en"  (verilog-ext-templ-enum-typedef nil)     "enum")
  ("fl"  (verilog-ext-insert-yasnippet "fl")      "final")
  ("for" (verilog-ext-insert-yasnippet "for")     "for")
  ("fv"  (verilog-ext-insert-yasnippet "fv")      "forever")
  ("fe"  (verilog-ext-insert-yasnippet "fe")      "foreach")
  ("fj"  (verilog-ext-insert-yasnippet "fj")      "fork join")
  ("fa"  (verilog-ext-insert-yasnippet "fa")      "fork join_any")
  ("fn"  (verilog-ext-insert-yasnippet "fn")      "fork join_none")
  ("ff"  (verilog-ext-insert-yasnippet "ff")      "function")
  ("gen" (verilog-ext-insert-yasnippet "gen")     "generate" :column "G-M")
  ("if"  (verilog-ext-insert-yasnippet "if")      "if")
  ("in"  (verilog-ext-insert-yasnippet "in")      "initial")
  ("itf" (verilog-ext-insert-yasnippet "itf")     "interface")
  ("ll"  (verilog-ext-insert-yasnippet "ll")      "logic")
  ("lv"  (verilog-ext-insert-yasnippet "lv")      "logic vector")
  ("lp"  (verilog-ext-insert-yasnippet "lp")      "localparam")
  ("ms"  (verilog-ext-insert-yasnippet "ms")      "module (simple)")
  ("md"  (verilog-ext-insert-yasnippet "md")      "module (params)")
  ("mp"  (verilog-ext-insert-yasnippet "mp")      "modport")
  ("pkg" (verilog-ext-insert-yasnippet "pkg")     "package" :column "P-S")
  ("pgm" (verilog-ext-insert-yasnippet "pgm")     "program")
  ("pm"  (verilog-ext-insert-yasnippet "pm")      "parameter")
  ("pr"  (verilog-ext-insert-yasnippet "pr")      "property")
  ("rp"  (verilog-ext-insert-yasnippet "rp")      "repeat")
  ("seq" (verilog-ext-insert-yasnippet "seq")     "sequence")
  ("st"  (verilog-ext-templ-struct-typedef nil)   "struct")
  ("ta"  (verilog-ext-insert-yasnippet "ta")      "task (one-line)" :column "T-W")
  ("tk"  (verilog-ext-templ-task)                 "task (port prompt)")
  ("td"  (verilog-ext-insert-yasnippet "td")      "typedef generic")
  ("te"  (verilog-ext-templ-enum-typedef t)       "typedef enum")
  ("ts"  (verilog-ext-templ-struct-typedef t)     "typedef struct")
  ("tu"  (verilog-ext-templ-struct-typedef t t)   "typedef union")
  ("un"  (verilog-ext-templ-struct-typedef nil t) "union")
  ("wh"  (verilog-ext-insert-yasnippet "wh")      "while")
  ("wd"  (verilog-ext-insert-yasnippet "wd")      "while-do")

  ("@"   (verilog-ext-insert-yasnippet "@") "Clk posedge" :column "Others")
  ("D"   (verilog-ext-templ-def-logic) "Define signal")
  ("FS"  (verilog-ext-templ-fsm)   "FSM Sync")
  ("FA"  (verilog-ext-templ-fsm t) "FSM Async")
  ("IS"  (call-interactively #'verilog-ext-templ-inst-auto-from-file-simple) "Instance (simple)")
  ("IP"  (call-interactively #'verilog-ext-templ-inst-auto-from-file-params) "Instance (params)")
  ("TS"  (call-interactively #'verilog-ext-templ-testbench-simple-from-file) "TB from DUT (simple)")

  ("uc"  (verilog-ext-insert-yasnippet "uc") "UVM Component" :column "UVM")
  ("uo"  (verilog-ext-insert-yasnippet "uo") "UVM Object")
  ("ut"  (verilog-ext-insert-yasnippet "ut") "UVM TypeId Create")
  ("ui"  (verilog-ext-insert-yasnippet "ui") "UVM Info")
  ("ue"  (verilog-ext-insert-yasnippet "ue") "UVM Error")
  ("uw"  (verilog-ext-insert-yasnippet "uw") "UVM Warning")
  ("ur"  (verilog-ext-insert-yasnippet "ur") "UVM Report")

  ("/*"  (verilog-ext-insert-yasnippet "/*")             "Star comment" :column "Comments")
  ("B"   (verilog-ext-templ-block-comment)               "Block comment")
  ("hd"  (call-interactively #'verilog-ext-templ-header) "Header")

  ;;;;;;;;;;
  ;; Exit ;;
  ;;;;;;;;;;
  ("q"   nil nil :color blue)
  ("C-g" nil nil :color blue))


;;; Completion
;; Verilog extension for `company' and placeholder for `completion-at-point' improvements.
(add-to-list 'company-keywords-alist (append '(verilog-mode) verilog-keywords))

;;; Syntax highlighting
;; Improved syntax highlighting based on `font-lock' keywords overriding.
;;
;; Multiline Font Locking has reliability limitations in Emacs.
;;  - https://www.gnu.org/software/emacs/manual/html_node/elisp/Multiline-Font-Lock.html
;;  - https://www.gnu.org/software/emacs/manual/html_node/elisp/Font-Lock-Multiline.html
;;
;; One way to ensure reliable rehighlighting of multiline font-lock constructs
;; is by using the `font-lock-multiline' text property.
;; - The `font-lock-multiline' variable might seem to be working but is not reliable.
;; - Using the `font-lock-multiline' property might apply to a few lines (such is the case).
;;   For longer sections it is necessary to create font lock custom functions and gets
;;   more complicated.
;;
;; Search based fontification:
;; - https://www.gnu.org/software/emacs/manual/html_node/elisp/Search_002dbased-Fontification.html

;;;; Faces
(defgroup verilog-ext-faces nil
  "Verilog-ext faces."
  :group 'verilog-ext)

(defvar verilog-ext-font-lock-grouping-keywords-face 'verilog-ext-font-lock-grouping-keywords-face)
(defface verilog-ext-font-lock-grouping-keywords-face
  '((t (:foreground "dark olive green")))
  "Face for grouping keywords: begin, end."
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-punctuation-face 'verilog-ext-font-lock-punctuation-face)
(defface verilog-ext-font-lock-punctuation-face
  '((t (:foreground "burlywood")))
  "Face for punctuation symbols, e.g:
!,;:?'=<>*"
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-punctuation-bold-face 'verilog-ext-font-lock-punctuation-bold-face)
(defface verilog-ext-font-lock-punctuation-bold-face
  '((t (:inherit verilog-ext-font-lock-punctuation-face :weight extra-bold)))
  "Face for bold punctuation symbols, such as &^~+-/|."
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-brackets-face 'verilog-ext-font-lock-brackets-face)
(defface verilog-ext-font-lock-brackets-face
  '((t (:foreground "goldenrod")))
  "Face for brackets []."
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-parenthesis-face 'verilog-ext-font-lock-parenthesis-face)
(defface verilog-ext-font-lock-parenthesis-face
  '((t (:foreground "dark goldenrod")))
  "Face for parenthesis ()."
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-curly-braces-face 'verilog-ext-font-lock-curly-braces-face)
(defface verilog-ext-font-lock-curly-braces-face
  '((t (:foreground "DarkGoldenrod2")))
  "Face for curly braces {}."
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-port-connection-face 'verilog-ext-font-lock-port-connection-face)
(defface verilog-ext-font-lock-port-connection-face
  '((t (:foreground "bisque2")))
  "Face for port connections of instances.
.portA (signalA),
.portB (signalB)
);"
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-dot-name-face 'verilog-ext-font-lock-dot-name-face)
(defface verilog-ext-font-lock-dot-name-face
  '((t (:foreground "gray70")))
  "Face for dot-name regexps:
- Interface signals, classes attributes/methods and hierarchical refs.

axi_if.Ready <= 1'b1;
obj.method();"
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-braces-content-face 'verilog-ext-font-lock-braces-content-face)
(defface verilog-ext-font-lock-braces-content-face
  '((t (:foreground "yellow green")))
  "Face for content between braces: arrays, bit vector width and indexing."
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-width-num-face 'verilog-ext-font-lock-width-num-face)
(defface verilog-ext-font-lock-width-num-face
  '((t (:foreground "chartreuse2")))
  "Face for the bit width number expressions.
{1}'b1,
{4}'hF,
{3}'o7,"
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-width-type-face 'verilog-ext-font-lock-width-type-face)
(defface verilog-ext-font-lock-width-type-face
  '((t (:foreground "sea green" :weight bold)))
  "Face for the bit width type expressions.
1'{b}1,
4'{h}F,
3'{o}7,"
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-module-face 'verilog-ext-font-lock-module-face)
(defface verilog-ext-font-lock-module-face
  '((t (:foreground "green1")))
  "Face for module names."
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-instance-face 'verilog-ext-font-lock-instance-face)
(defface verilog-ext-font-lock-instance-face
  '((t (:foreground "medium spring green")))
  "Face for instance names."
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-time-event-face 'verilog-ext-font-lock-time-event-face)
(defface verilog-ext-font-lock-time-event-face
  '((t (:foreground "deep sky blue" :weight bold)))
  "Face for time-events: @ and #."
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-time-unit-face 'verilog-ext-font-lock-time-unit-face)
(defface verilog-ext-font-lock-time-unit-face
  '((t (:foreground "light steel blue")))
  "Face for time-units: ms, us, ns, ps, fs (delays and timescale/timeprecision)."
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-preprocessor-face 'verilog-ext-font-lock-preprocessor-face)
(defface verilog-ext-font-lock-preprocessor-face
  '((t (:foreground "pale goldenrod")))
  "Face for preprocessor compiler directives (`include, `define, UVM macros...)."
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-modport-face 'verilog-ext-font-lock-modport-face)
(defface verilog-ext-font-lock-modport-face
  '((t (:foreground "light blue")))
  "Face for interface modports."
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-direction-face 'verilog-ext-font-lock-direction-face)
(defface verilog-ext-font-lock-direction-face
  '((t (:foreground "RosyBrown3")))
  "Face for direction of ports/functions/tasks args."
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-typedef-face 'verilog-ext-font-lock-typedef-face)
(defface verilog-ext-font-lock-typedef-face
  '((t (:foreground "light blue")))
  "Face for user defined types."
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-translate-off-face 'verilog-ext-font-lock-translate-off-face)
(defface verilog-ext-font-lock-translate-off-face
  '((t (:background "gray20" :slant italic)))
  "Face for pragmas between comments, e.g:
* translate_off / * translate_on"
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-uvm-classes-face 'verilog-ext-font-lock-uvm-classes-face)
(defface verilog-ext-font-lock-uvm-classes-face
  '((t (:foreground "light blue")))
  "Face for UVM classes."
  :group 'verilog-ext-faces)

(defvar verilog-ext-font-lock-xilinx-attributes-face 'verilog-ext-font-lock-xilinx-attributes-face)
(defface verilog-ext-font-lock-xilinx-attributes-face
  '((t (:foreground "orange1")))
  "Face for Xilinx Vivado RTL synthesis attributes."
  :group 'verilog-ext-faces)


;;;; Regexps
(defconst verilog-ext-font-lock-parenthesis-re "[()]")
(defconst verilog-ext-font-lock-curly-braces-re "[{}]")
(defconst verilog-ext-font-lock-brackets-re "\\(\\[\\|\\]\\)")
(defconst verilog-ext-font-lock-punctuation-re "\\([!,;:?'=<>]\\|\\*\\)")
(defconst verilog-ext-font-lock-punctuation-bold-re "\\([&^~%\+-]\\||\\|\\.\\|\\/\\)")
(defconst verilog-ext-font-lock-system-task-re (concat "\\$" verilog-identifier-re))
(defconst verilog-ext-font-lock-port-connection-re (concat "^[[:blank:]]*\\.\\(" verilog-identifier-re "\\)"))
(defconst verilog-ext-font-lock-dot-name-re (concat "\\(" verilog-identifier-re "\\)\\.\\(" verilog-identifier-re "\\)"))
(defconst verilog-ext-font-lock-braces-content-re "\\[\\(?1:[ +'\*/()$0-9a-zA-Z:_-]*\\)\\]")
(defconst verilog-ext-font-lock-width-signal-re "\\(?1:[0-9]*\\)'[sS]?\\(?2:[hHdDxXbBoO]\\)\\(?3:[0-9a-fA-F_xzXZ]+\\)")
(defconst verilog-ext-font-lock-time-event-re "\\([@#]\\)")
(defconst verilog-ext-font-lock-time-unit-re "[0-9]+\\(\\.[0-9]+\\)?\\(?2:[umnpf]s\\)")
(defconst verilog-ext-font-lock-interface-modport-re (concat "\\(?1:^\\s-*\\(?2:" verilog-identifier-re "\\)\\.\\(?3:" verilog-identifier-re "\\)\\s-+\\)"))
(defconst verilog-ext-font-lock-typedef-struct-re "^\\s-*\\(typedef\\s-+\\)?\\(struct\\|union\\)\\s-+\\(packed\\|\\(un\\)?signed\\)?")


(defconst verilog-ext-font-lock-type-font-keywords
  (eval-when-compile
    (verilog-regexp-words
     '("and" "buf" "bufif0" "bufif1" "cmos" "defparam" "event" "genvar" "highz0"
       "highz1" "integer" "localparam" "mailbox" "nand" "nmos" "nor" "not" "notif0"
       "notif1" "or" "parameter" "pmos" "pull0" "pull1" "pulldown" "pullup" "rcmos"
       "real" "realtime" "reg" "rnmos" "specparam" "strong0" "strong1" "supply"
       "supply0" "supply1" "time" "tran" "tranif0" "tranif1" "tri" "tri0" "tri1"
       "triand" "trior" "trireg" "unsigned" "uwire" "vectored" "wand" "weak0"
       "weak1" "wire" "wor" "xnor" "xor" "signed"
       ;; 1800-2005
       "bit" "byte" "chandle" "int" "logic" "longint" "packed" "shortint"
       "shortreal" "string" "type" "union" "var"
       ;; 1800-2009
       ;; 1800-2012
       "interconnect" "nettype"))))

(defconst verilog-ext-font-lock-direction-keywords
  (eval-when-compile
    (verilog-regexp-words
     '("inout" "input" "output" "ref"))))

(defconst verilog-ext-font-lock-general-keywords
  (eval-when-compile
    (verilog-regexp-opt
     '("always" "assign" "automatic" "case" "casex" "casez" "cell" "config"
       "deassign" "default" "design" "disable" "edge" "else" "endcase" "endconfig"
       "endfunction" "endgenerate" "endmodule" "endprimitive" "endspecify"
       "endtable" "endtask" "for" "force" "forever" "fork" "function" "generate"
       "if" "ifnone" "incdir" "include" "initial" "instance" "join" "large"
       "liblist" "library" "macromodule" "medium" "module" "negedge"
       "noshowcancelled" "posedge" "primitive" "pulsestyle_ondetect"
       "pulsestyle_onevent" "release" "repeat" "scalared" "showcancelled" "small"
       "specify" "strength" "table" "task" "use" "wait" "while"
       ;; 1800-2005
       "alias" "always_comb" "always_ff" "always_latch" "assert" "assume"
       "analog" "before" "bind" "bins" "binsof" "break" "class" "clocking"
       "constraint" "context" "continue" "cover" "covergroup" "coverpoint"
       "cross" "dist" "do" "endclass" "endclocking" "endgroup" "endinterface"
       "endpackage" "endprogram" "endproperty" "endsequence" "expect" "export"
       "extends" "extern" "final" "first_match" "foreach" "forkjoin" "iff"
       "ignore_bins" "illegal_bins" "import" "inside" "interface" "intersect"
       "join_any" "join_none" "local" "matches" "modport" "new" "null" "package"
       "priority" "program" "property" "protected" "pure" "rand" "randc"
       "randcase" "randsequence" "return" "sequence" "solve" "static" "super"
       "tagged" "this" "throughout" "timeprecision" "timeunit" "typedef"
       "unique" "virtual" "void" "wait_order" "wildcard" "with" "within" "const"
       "enum" "struct"
       ;; 1800-2009
       "accept_on" "checker" "endchecker" "eventually" "global" "implies" "let"
       "nexttime" "reject_on" "restrict" "s_always" "s_eventually" "s_nexttime"
       "s_until" "s_until_with" "strong" "sync_accept_on" "sync_reject_on"
       "unique0" "until" "until_with" "untyped" "weak"
       ;; 1800-2012
       "implements" "soft"))))

(defconst verilog-ext-font-lock-grouping-plus-this-keywords
  (eval-when-compile
    (verilog-regexp-words
     '("begin" "end" "this"))))

;; Once UVM dir has been set, obtained through:
;;   (verilog-ext-typedef-batch-update verilog-ext-align-typedef-uvm-dir)
(defconst verilog-ext-font-lock-uvm-classes
  (eval-when-compile
    (verilog-regexp-words
     '("uvm_tlm_nb_initiator_socket_base" "uvm_tlm_b_initiator_socket_base"
       "uvm_tlm_nb_passthrough_target_socket"
       "uvm_tlm_nb_passthrough_initiator_socket"
       "uvm_tlm_b_passthrough_target_socket"
       "uvm_tlm_b_passthrough_initiator_socket" "uvm_tlm_nb_target_socket"
       "uvm_tlm_nb_initiator_socket" "uvm_tlm_b_target_socket"
       "uvm_tlm_b_initiator_socket" "uvm_tlm_nb_target_socket_base"
       "uvm_tlm_nb_passthrough_target_socket_base"
       "uvm_tlm_nb_passthrough_initiator_socket_base"
       "uvm_tlm_b_target_socket_base" "uvm_tlm_b_passthrough_target_socket_base"
       "uvm_tlm_b_passthrough_initiator_socket_base"
       "uvm_tlm_nb_transport_bw_port" "uvm_tlm_nb_transport_fw_port"
       "uvm_tlm_b_transport_port" "uvm_tlm_nb_transport_bw_imp"
       "uvm_tlm_nb_transport_fw_imp" "uvm_tlm_b_transport_imp" "uvm_time"
       "uvm_tlm_if" "uvm_tlm_time" "uvm_tlm_extension" "uvm_tlm_generic_payload"
       "uvm_tlm_extension_base" "uvm_tlm_response_status_e" "uvm_tlm_command_e"
       "uvm_tlm_nb_transport_bw_export" "uvm_tlm_nb_transport_fw_export"
       "uvm_tlm_b_transport_export" "uvm_tlm_transport_channel"
       "uvm_tlm_req_rsp_channel" "uvm_tlm_event" "uvm_tlm_fifo_base"
       "uvm_sqr_if_base" "uvm_seq_item_pull_export" "uvm_transport_port"
       "uvm_nonblocking_transport_port" "uvm_blocking_transport_port"
       "uvm_slave_port" "uvm_nonblocking_slave_port" "uvm_blocking_slave_port"
       "uvm_master_port" "uvm_nonblocking_master_port" "uvm_blocking_master_port"
       "uvm_get_peek_port" "uvm_nonblocking_get_peek_port"
       "uvm_blocking_get_peek_port" "uvm_peek_port" "uvm_nonblocking_peek_port"
       "uvm_blocking_peek_port" "uvm_get_port" "uvm_nonblocking_get_port"
       "uvm_blocking_get_port" "uvm_put_port" "uvm_nonblocking_put_port"
       "uvm_transport_export" "uvm_nonblocking_transport_export"
       "uvm_blocking_transport_export" "uvm_slave_export"
       "uvm_nonblocking_slave_export" "uvm_blocking_slave_export"
       "uvm_master_export" "uvm_nonblocking_master_export"
       "uvm_blocking_master_export" "uvm_get_peek_export"
       "uvm_nonblocking_get_peek_export" "uvm_blocking_get_peek_export"
       "uvm_peek_export" "uvm_nonblocking_peek_export" "uvm_blocking_peek_export"
       "uvm_get_export" "uvm_nonblocking_get_export" "uvm_blocking_get_export"
       "uvm_put_export" "uvm_nonblocking_put_export" "uvm_blocking_put_export"
       "uvm_tlm_if_base" "rsp_type" "req_type" "uvm_tlm_fifo" "uvm_config_seq"
       "seq_req_t" "m_uvm_sqr_seq_base" "uvm_sequence_process_wrapper"
       "uvm_sequence_request" "uvm_sequencer_analysis_fifo"
       "uvm_virtual_sequencer" "uvm_seq_item_pull_imp" "uvm_sequence_library_cfg"
       "uvm_sequence_library" "uvm_sequence_lib_mode" "sequencer_t"
       "uvm_default_sequencer_param_type" "uvm_default_driver_type"
       "uvm_default_sequencer_type" "uvm_default_sequence_type"
       "uvm_sequencer_param_base" "uvm_sequence" "uvm_push_sequencer"
       "uvm_vreg_field_cb" "uvm_vreg_field_cbs" "uvm_vreg_cb" "uvm_vreg_cbs"
       "uvm_vreg_field_cb_iter" "uvm_vreg_cb_iter" "seq_parent_e" "uvm_sequencer"
       "uvm_reg_predictor" "uvm_predict_s" "uvm_reg_cvr_rsrc_db"
       "uvm_reg_sequence" "bit_q_t" "uvm_reg_data_logic_t" "uvm_reg_seq_base"
       "uvm_reg_transaction_order_policy" "uvm_reg_map_addr_range" "uvm_access_e"
       "uvm_elem_kind_e" "uvm_reg_indirect_data" "uvm_reg_indirect_ftdr_seq"
       "uvm_reg_fifo" "uvm_reg_byte_en_t" "uvm_reg_field_cb" "uvm_mem_cb"
       "uvm_reg_bd_cb_iter" "uvm_reg_bd_cb" "uvm_reg_cb" "uvm_predict_e"
       "uvm_reg_write_only_cbs" "uvm_reg_read_only_cbs" "uvm_hier_e"
       "uvm_reg_tlm_adapter" "uvm_reg_adapter" "uvm_reg_bus_op" "uvm_tlm_gp"
       "uvm_reg_cbs" "uvm_reg_field_cb_iter" "uvm_reg_cb_iter" "uvm_reg_file"
       "locality_e" "alloc_mode_e" "uvm_mem_region" "uvm_mem_mam_policy"
       "uvm_reg_cvr_t" "uvm_hdl_path_slice" "uvm_door_e" "uvm_endianness_e"
       "uvm_reg_frontdoor" "uvm_mem_cb_iter" "uvm_reg_item" "uvm_reg_addr_t"
       "uvm_vreg_field" "uvm_vreg" "uvm_reg_map_info" "uvm_mem_mam_cfg"
       "uvm_mem_mam" "uvm_reg_backdoor" "uvm_mem_shared_access_seq"
       "uvm_reg_shared_access_seq" "uvm_reg_mem_hdl_paths_seq"
       "uvm_hdl_path_concat" "uvm_reg_mem_built_in_seq"
       "uvm_reg_mem_shared_access_seq" "uvm_reg_hw_reset_seq" "uvm_check_e"
       "uvm_reg_bit_bash_seq" "uvm_reg_single_bit_bash_seq"
       "uvm_reg_mem_access_seq" "uvm_reg_access_seq" "uvm_reg_single_access_seq"
       "uvm_reg_field" "uvm_reg" "uvm_mem_walk_seq" "uvm_mem_single_walk_seq"
       "uvm_mem_access_seq" "uvm_reg_data_t" "uvm_reg_block"
       "uvm_mem_single_access_seq" "uvm_status_e" "uvm_reg_map" "uvm_reg_randval"
       "uvm_mem" "this_rsp_type" "this_req_type" "this_imp_type"
       "uvm_transport_imp" "uvm_nonblocking_transport_imp"
       "uvm_blocking_transport_imp" "uvm_slave_imp" "uvm_nonblocking_slave_imp"
       "uvm_blocking_slave_imp" "uvm_master_imp" "uvm_nonblocking_master_imp"
       "uvm_blocking_master_imp" "uvm_get_peek_imp" "uvm_nonblocking_get_peek_imp"
       "uvm_blocking_get_peek_imp" "uvm_peek_imp" "uvm_nonblocking_peek_imp"
       "uvm_blocking_peek_imp" "uvm_get_imp" "uvm_nonblocking_get_imp"
       "uvm_blocking_get_imp" "uvm_put_imp" "uvm_nonblocking_put_imp"
       "uvm_blocking_put_imp" "__tmp_int_t__" "_phase" "uvm_hdl_data_t"
       "__local_type__" "uvm_set_get_dap_base" "uvm_get_to_lock_dap" "uvm_test"
       "uvm_subscriber" "uvm_scoreboard" "uvm_blocking_put_port"
       "uvm_random_stimulus" "uvm_push_driver" "uvm_class_clone"
       "uvm_class_converter" "uvm_class_comp" "uvm_built_in_clone"
       "uvm_built_in_converter" "uvm_built_in_comp" "uvm_built_in_pair"
       "uvm_class_pair" "uvm_monitor" "uvm_in_order_built_in_comparator"
       "pair_type" "uvm_tlm_analysis_fifo" "uvm_in_order_comparator" "uvm_driver"
       "uvm_analysis_port" "uvm_seq_item_pull_port"
       "uvm_in_order_class_comparator" "uvm_analysis_export" "uvm_analysis_imp"
       "uvm_algorithmic_comparator" "uvm_agent" "uvm_active_passive_enum"
       "uvm_by_level_visitor_adapter" "uvm_bottom_up_visitor_adapter"
       "uvm_visitor_adapter" "uvm_structure_proxy#(STRUCTURE)" "uvm_transaction"
       "m_uvm_tr_stream_cfg" "uvm_topdown_phase" "uvm_simple_lock_dap" "tab_t"
       "uvm_spell_chkr" "uvm_run_test_callback" "uvm_top_down_visitor_adapter"
       "uvm_component_proxy" "uvm_byte_rsrc" "uvm_bit_rsrc" "uvm_obj_rsrc"
       "uvm_string_rsrc" "uvm_int_rsrc" "this_subtype" "uvm_resource_db_options"
       "uvm_resource_db" "rsrc_t" "override_t" "uvm_resource_options"
       "uvm_resource_types" "access_t" "get_t" "rsrc_info_t" "uvm_env"
       "queue_of_element" "uvm_report_message_element_container"
       "uvm_report_message_element_base" "uvm_report_message_object_element"
       "uvm_report_message_string_element" "uvm_report_message_int_element"
       "uvm_id_file_array" "uvm_sev_override_array" "uvm_id_actions_array"
       "uvm_id_verbosities_array" "uvm_report_cb" "sev_id_struct" "action_e"
       "uvm_report_cb_iter" "uvm_report_catcher" "uvm_report_handler"
       "uvm_registry_object_creator" "uvm_registry_component_creator" "Tregistry"
       "uvm_abstract_object_registry" "common_type" "uvm_registry_common"
       "uvm_component_registry" "uvm_text_recorder" "uvm_text_tr_stream"
       "uvm_set_before_get_dap" "uvm_structure_proxy" "uvm_printer_element_proxy"
       "uvm_line_printer" "uvm_tree_printer" "uvm_printer_element"
       "m_uvm_printer_knobs" "uvm_port_list" "uvm_port_type_e"
       "uvm_port_component" "uvm_port_base" "uvm_port_component_base"
       "uvm_barrier_pool" "uvm_object_string_pool" "uvm_pool" "uvm_phase_cb_pool"
       "uvm_sequencer_base" "uvm_phase_cb" "uvm_wait_op" "uvm_phase_state_change"
       "uvm_task_phase" "uvm_phase_type" "uvm_pack_bitstream_t"
       "uvm_callbacks_objection" "uvm_objection_cbs_t" "uvm_objection_event"
       "uvm_object_registry" "uvm_objection_context_object" "uvm_objection_events"
       "uvm_sequence_state_enum" "uvm_core_state" "uvm_sequence_state"
       "uvm_sequencer_arb_mode" "m_uvm_config_obj_misc" "process_container_c"
       "uvm_void" "uvm_seed_map" "uvm_related_link" "uvm_cause_effect_link"
       "uvm_parent_child_link" "uvm_link_base" "uvm_heartbeat_cbs_t"
       "uvm_objection_callback" "uvm_heartbeat" "uvm_event#(uvm_object)"
       "uvm_heartbeat_modes" "uvm_heartbeat_callback" "uvm_report_message"
       "uvm_enum_wrapper" "uvm_field_flag_t" "uvm_policy"
       "uvm_factory_queue_class" "m_inst_typename_alias_t"
       "m_uvm_factory_type_pair_t" "uvm_factory_override" "uvm_event#(T)"
       "cbs_type" "cb_type" "uvm_event_callback" "uvm_event_base"
       "uvm_post_shutdown_phase" "uvm_shutdown_phase" "uvm_pre_shutdown_phase"
       "uvm_post_main_phase" "uvm_main_phase" "uvm_pre_main_phase"
       "uvm_post_configure_phase" "uvm_configure_phase" "uvm_pre_configure_phase"
       "uvm_post_reset_phase" "uvm_reset_phase" "uvm_pre_reset_phase"
       "uvm_table_printer" "uvm_default_coreservice_t"
       "uvm_visitor#(uvm_component)" "uvm_packer"
       "uvm_component_name_check_visitor" "uvm_visitor"
       "uvm_default_report_server" "uvm_report_server" "uvm_text_tr_database"
       "uvm_default_factory" "uvm_copier" "uvm_config_wrapper" "uvm_config_object"
       "uvm_config_string" "uvm_config_int" "uvm_config_db_options"
       "uvm_config_db" "m_uvm_waiter" "rsrc_q_t" "uvm_resource" "type_id"
       "uvm_object_wrapper" "uvm_objection" "uvm_resource_pool"
       "uvm_sequence_base" "uvm_sequence_item" "uvm_factory" "uvm_resource_base"
       "uvm_event_pool" "uvm_abstract_component_registry" "uvm_recorder"
       "uvm_tr_stream" "uvm_tr_database" "uvm_integral_t" "uvm_radix_enum"
       "uvm_comparer" "uvm_field_op" "uvm_bitstream_t" "uvm_recursion_policy_enum"
       "state_info_t" "recursion_state_e" "uvm_final_phase" "uvm_report_phase"
       "uvm_check_phase" "uvm_extract_phase" "uvm_run_phase"
       "uvm_start_of_simulation_phase" "uvm_end_of_elaboration_phase"
       "uvm_connect_phase" "uvm_build_phase" "uvm_cmdline_setting_base"
       "uvm_cmdline_set_severity" "uvm_cmdline_set_action" "uvm_action"
       "uvm_severity" "uvm_cmdline_set_verbosity" "uvm_cmdline_verbosity"
       "uvm_cmd_line_verb" "uvm_verbosity" "uvm_callback_iter"
       "uvm_queue#(uvm_callback)" "uvm_apprepend" "this_super_type"
       "this_user_type" "uvm_derived_callbacks" "uvm_coreservice_t" "uvm_root"
       "uvm_report_object" "uvm_callbacks" "uvm_callback" "super_type"
       "uvm_typed_callbacks" "uvm_queue" "this_type" "uvm_typeid"
       "uvm_typeid_base" "uvm_callbacks_base" "uvm_bottomup_phase"
       "uvm_phase_state" "uvm_component" "process" "uvm_phase" "uvm_domain"
       "uvm_cmdline_processor" "uvm_object" "uvm_printer" "uvm_barrier"
       "uvm_event"))))


(defconst verilog-ext-font-lock-pragma-keywords
  (eval-when-compile
    (verilog-regexp-words
     '("surefire" "0in" "auto" "leda" "rtl_synthesis" "verilint"
       ;; Recognized by Vivado (check Xilinx attribute 'translate_off/translate_on'):
       "synthesis" "synopsys" "pragma"))))

;;   Xilinx attributes extracted from UG901:
;; - https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_3/ug901-vivado-synthesis.pdf
;; - Chapter 2 (some of them are also supported at XDC).
(defconst verilog-ext-font-lock-xilinx-attributes
  (eval-when-compile
    (verilog-regexp-words
     '("async_reg" "black_box" "cascade_height" "clock_buffer_type"
       "direct_enable" "direct_reset" "dont_touch" "extract_enable"
       "extract_reset" "fsm_encoding" "fsm_safe_state" "full_case" "gated_clock"
       "iob" "io_buffer_type" "keep" "keep_hierarchy" "mark_debug" "max_fanout"
       "parallel_case" "ram_decomp" "ram_style" "retiming_backward"
       "retiming_forward" "rom_style" "shreg_extract" "srl_style" "translate_off"
       "translate_on" "use_dsp"
       ;; uppercase "async_reg" "BLACK_BOX"
       "CASCADE_HEIGHT" "CLOCK_BUFFER_TYPE" "DIRECT_ENABLE" "DIRECT_RESET"
       "DONT_TOUCH" "EXTRACT_ENABLE" "EXTRACT_RESET" "FSM_ENCODING"
       "FSM_SAFE_STATE" "FULL_CASE" "GATED_CLOCK" "IOB" "IO_BUFFER_TYPE" "KEEP"
       "KEEP_HIERARCHY" "MARK_DEBUG" "MAX_FANOUT" "PARALLEL_CASE" "RAM_DECOMP"
       "RAM_STYLE" "RETIMING_BACKWARD" "RETIMING_FORWARD" "ROM_STYLE"
       "SHREG_EXTRACT" "SRL_STYLE" "TRANSLATE_OFF" "TRANSLATE_ON" "USE_DSP"))))


;;;; Functions
(defun verilog-ext-font-lock-module-instance-fontify (limit)
  "Search based fontification function of Verilog modules/instances.
Bound search by LIMIT."
  (let (start-line-pos end-line-pos)
    (when (verilog-ext-find-module-instance-fwd limit)
      (setq start-line-pos (save-excursion
                             (goto-char (match-beginning 1))
                             (line-beginning-position)))
      (setq end-line-pos (save-excursion
                           (goto-char (match-end 2))
                           (line-end-position)))
      (unless (get-text-property (point) 'font-lock-multiline)
        (put-text-property start-line-pos end-line-pos 'font-lock-multiline t))
      (point))))

(defun verilog-ext-font-lock-task-function-fontify (limit)
  "Search based fontification function of Verilog tasks/function.
Bound search by LIMIT."
  (when (verilog-ext-find-function-task-fwd limit)
    (unless (get-text-property (point) 'font-lock-multiline)
      (put-text-property (match-beginning 0) (match-end 0) 'font-lock-multiline t))
    (point)))

(defun verilog-ext-font-lock-modport-fontify (limit)
  "Fontify interface modport declarations.
Bound search by LIMIT."
  (let (if-start if-end mp-start mp-end var-start var-end)
    (when (and (verilog-re-search-forward verilog-ext-font-lock-interface-modport-re limit t)
               (verilog-in-parenthesis-p))
      (setq if-start (match-beginning 2))
      (setq if-end (match-end 2))
      (setq mp-start (match-beginning 3))
      (setq mp-end (match-end 3))
      ;; Calculate variable pos at the end since `thing-at-point' changes match-data
      (setq var-start (car (bounds-of-thing-at-point 'symbol)))
      (setq var-end (cdr (bounds-of-thing-at-point 'symbol)))
      (set-match-data (list if-start if-end mp-start mp-end var-start var-end))
      (point))))

(defun verilog-ext-font-lock-var-decl-typedef-fontify (limit)
  "Fontify variable declarations of user defined types.
Bound search by LIMIT."
  (let ((decl-typedef-re (verilog-get-declaration-typedef-re))
        start end found)
    (when (verilog-align-typedef-enabled-p)
      (while (and (not found)
                  (verilog-re-search-forward decl-typedef-re limit t))
        (when (save-excursion
                (beginning-of-line)
                (looking-at decl-typedef-re))
          (setq found t)))
      (when found
        (setq start (match-beginning 5))
        (setq end (match-end 5))
        (set-match-data (list start end))
        (point)))))

(defun verilog-ext-font-lock-enum-fontify (limit)
  "Fontify (typedef) enum declarations.
Bound search by LIMIT."
  (let (start-line-pos end-line-pos)
    (when (and (verilog-re-search-forward verilog-typedef-enum-re limit t)
               (setq start-line-pos (line-beginning-position))
               (verilog-ext-forward-syntactic-ws)
               (looking-at "{")
               (verilog-ext-forward-sexp)
               (eq (preceding-char) ?})
               (verilog-ext-forward-syntactic-ws)
               (looking-at verilog-identifier-sym-re))
      (setq end-line-pos (line-end-position))
      (unless (get-text-property (point) 'font-lock-multiline)
        (put-text-property start-line-pos end-line-pos 'font-lock-multiline t))
      (point))))

(defun verilog-ext-font-lock-struct-fontify (limit)
  "Fontify (typedef) struct declarations.
Bound search by LIMIT."
  (let (start-line-pos end-line-pos)
    (when (and (verilog-re-search-forward verilog-ext-font-lock-typedef-struct-re limit t)
               (setq start-line-pos (line-beginning-position))
               (verilog-re-search-forward "{" limit t)
               (verilog-ext-backward-char)
               (verilog-ext-forward-sexp)
               (eq (preceding-char) ?})
               (verilog-ext-forward-syntactic-ws)
               (looking-at verilog-identifier-sym-re))
      (setq end-line-pos (line-end-position))
      (unless (get-text-property (point) 'font-lock-multiline)
        (put-text-property start-line-pos end-line-pos 'font-lock-multiline t))
      (point))))

(defun verilog-ext-font-lock-match-translate-off-fontify (limit)
  "Match a translate-off block, setting `match-data' and returning t, else nil.
Bound search by LIMIT.

Similar to `verilog-match-translate-off' but including
`font-lock-multiline' property."
  (when (< (point) limit)
    (let ((start (or (verilog-within-translate-off)
                     (verilog-start-translate-off limit)))
          (case-fold-search t))
      (when start
        (let ((end (or (verilog-end-translate-off limit) limit)))
          (put-text-property start end 'font-lock-multiline t)
          (set-match-data (list start end))
          (goto-char end))))))


;;;; Font-lock keywords
(defvar verilog-ext-font-lock-keywords
  (list
   ;; Preprocessor macros and compiler directives (place at the top to preserve precendence in `else or `include macros over keywords)
   (cons (concat "`" verilog-identifier-re) 'verilog-ext-font-lock-preprocessor-face)
   ;; Grouping keywords
   (cons (concat "\\<\\(" verilog-ext-font-lock-grouping-plus-this-keywords "\\)\\>") 'verilog-ext-font-lock-grouping-keywords-face)
   ;; Builtin keywords
   (concat "\\<\\(" verilog-ext-font-lock-general-keywords "\\)\\>") ; Default 'font-lock-keyword-face
   ;; User/System tasks and functions
   (cons (concat "\\<\\(" verilog-ext-font-lock-system-task-re "\\)\\>") 'font-lock-builtin-face)
   ;; Types & directions
   (cons (concat "\\<\\(" verilog-ext-font-lock-type-font-keywords "\\)\\>") 'font-lock-type-face)
   (cons (concat "\\<\\(" verilog-ext-font-lock-direction-keywords "\\)\\>") 'verilog-ext-font-lock-direction-face)
   ;; Punctuation
   (list verilog-ext-font-lock-time-unit-re          2 verilog-ext-font-lock-time-unit-face)
   (list verilog-ext-font-lock-time-event-re         0 verilog-ext-font-lock-time-event-face)
   (list verilog-ext-font-lock-port-connection-re    1 verilog-ext-font-lock-port-connection-face)
   (list verilog-ext-font-lock-dot-name-re           1 verilog-ext-font-lock-dot-name-face)
   (list verilog-ext-font-lock-braces-content-re     1 verilog-ext-font-lock-braces-content-face)
   (list verilog-ext-font-lock-punctuation-re        0 verilog-ext-font-lock-punctuation-face)
   (list verilog-ext-font-lock-punctuation-bold-re   0 verilog-ext-font-lock-punctuation-bold-face)
   (list verilog-ext-font-lock-brackets-re           0 verilog-ext-font-lock-brackets-face)
   (list verilog-ext-font-lock-parenthesis-re        0 verilog-ext-font-lock-parenthesis-face)
   (list verilog-ext-font-lock-curly-braces-re       0 verilog-ext-font-lock-curly-braces-face)
   (list verilog-ext-font-lock-width-signal-re
         '(1 verilog-ext-font-lock-width-num-face)
         '(2 verilog-ext-font-lock-width-type-face))))

(defvar verilog-ext-font-lock-keywords-1
  (append
   verilog-ext-font-lock-keywords
   (list
    ;; Top level definitions (except classes)
    (list "\\<\\(?1:\\(macro\\|connect\\)?module\\|primitive\\|program\\|interface\\|package\\)\\>\\s-*\\(automatic\\s-+\\)?\\(?3:\\sw+\\)\\s-*\\(?4:#?\\)"
          '(1 font-lock-keyword-face)
          '(3 font-lock-function-name-face))
    ;; Class names and parent
    '(verilog-ext-find-class-fwd
      (1 'font-lock-function-name-face)
      (2 'verilog-ext-font-lock-typedef-face nil t)) ; Parent class, if any
    ;; Functions/tasks
    '(verilog-ext-font-lock-task-function-fontify
      (1 'font-lock-function-name-face)
      (2 'verilog-ext-font-lock-dot-name-face nil t) ; Class name if defined externally
      (3 'font-lock-type-face nil t))                ; Function return type
    ;; Modport interfaces in port lists
    '(verilog-ext-font-lock-modport-fontify
      (0 'verilog-ext-font-lock-dot-name-face)
      (1 'verilog-ext-font-lock-modport-face))
    ;; Modules/instances
    '(verilog-ext-font-lock-module-instance-fontify
      (1 'verilog-ext-font-lock-module-face)
      (2 'verilog-ext-font-lock-instance-face))
    ;; Variable declarations of user defined types
    '(verilog-ext-font-lock-var-decl-typedef-fontify
      (0 'font-lock-type-face))
    ;; (Typedef) enums
    '(verilog-ext-font-lock-enum-fontify
      (0 'verilog-ext-font-lock-typedef-face))
    ;; (Typedef) structs
    '(verilog-ext-font-lock-struct-fontify
      (0 'verilog-ext-font-lock-typedef-face))
    ;; Typedef declarations
    (list verilog-ext-typedef-class-re
          '(2 font-lock-function-name-face))
    (list verilog-ext-typedef-generic-re
          '(2 font-lock-type-face))
    ;; Fallback to `verilog-ext-font-lock-var-decl-typedef-fontify'.
    ;; Try to fontify with a similar font those variable declarations whose regexps have not
    ;; been added to `verilog-align-typedef-regexp' (it won't be possible to align those)
    ;; To do so, check `verilog-ext-typedef-project-update'.
    (list verilog-ext-typedef-var-decl-single-re
          '(1 verilog-ext-font-lock-typedef-face))
    (list verilog-ext-typedef-var-decl-multiple-re
          '(1 verilog-ext-font-lock-typedef-face)))))

(defvar verilog-ext-font-lock-keywords-2
  (append
   verilog-ext-font-lock-keywords-1
   (list
    ;; Pragmas
    (list (concat "\\(//\\s-*\\(" verilog-ext-font-lock-pragma-keywords " \\).*\\)")
          '(0 'verilog-ext-font-lock-translate-off-face prepend)
          '(2 'verilog-ext-font-lock-preprocessor-face prepend))
    ;; Escaped names
    '("\\(\\\\\\S-*\\s-\\)"  0 font-lock-function-name-face)
    ;; Delays/numbers
    '("\\s-*#\\s-*\\(?1:\\([0-9_.]+\\([munpf]s\\)?\\('s?[hdxbo][0-9a-fA-F_xz]*\\)?\\)\\|\\(([^(),.=]+)\\|\\sw+\\)\\)" 1 font-lock-type-face)
    ;; Fontify property/sequence cycle delays - these start with '##'
    '("##\\(?1:\\sw+\\|\\[[^]]+\\]\\)" 1 font-lock-type-face))))

(defvar verilog-ext-font-lock-keywords-3
  (append
   verilog-ext-font-lock-keywords-2
   (list
    ;; UVM constructs
    (cons (concat "\\(" verilog-ext-font-lock-uvm-classes "\\)") 'verilog-ext-font-lock-uvm-classes-face)
    ;; Xilinx attributes
    (list (concat "(\\*\\s-+" "\\<\\(?1:" verilog-ext-font-lock-xilinx-attributes "\\)\\>" "\\s-+\\*)") 1 verilog-ext-font-lock-xilinx-attributes-face)
    ;; *_translate off regions
    '(verilog-ext-font-lock-match-translate-off-fontify
      (0 'verilog-ext-font-lock-translate-off-face prepend)))))


;;; Hierarchy
;; - Extract hierarchy of current file with `verilog-ext-vhier-current-file'
;; - Visualize and navigate it with `verilog-ext-vhier-mode'
;;  Requires `outshine' and `ggtags'.

;;;; Navigation
(define-minor-mode verilog-ext-vhier-mode
  "Instance navigation frontend for Verilog-Perl `vhier'.
Makes use of processed output under `outline-minor-mode' and `outshine'."
  :lighter " vH"
  :keymap
  '(;; Hide/Show
    ("a"       . outline-show-all)
    ("i"       . outline-show-children)
    ("h"       . outline-show-children)
    ("l"       . vhier-hide-sublevels)
    ("I"       . outline-show-branches)
    (";"       . outline-hide-other)
    ;; Movement
    ("u"       . vhier-up-heading)
    ("C-c C-u" . vhier-up-heading)
    ("n"       . vhier-next-visible-heading)
    ("j"       . vhier-next-visible-heading)
    ("p"       . vhier-previous-visible-heading)
    ("k"       . vhier-previous-visible-heading)
    ("C-c C-n" . vhier-forward-same-level)
    ("C-c C-p" . vhier-backward-same-level)
    ;; Jump
    ("o"       . verilog-ext-vhier-outline-jump-to-file)
    ("RET"     . verilog-ext-vhier-outline-jump-to-file)
    ("C-j"     . verilog-ext-vhier-outline-jump-to-file))
  ;; Enable outshine
  (outshine-mode 1)
  (setq buffer-read-only t)
  (view-mode -1))

(defmacro verilog-ext-vhier-outline-nav (vhier-func outline-func)
  "Define function VHIER-FUNC to call OUTLINE-FUNC in a vhier buffer.
Move through headings and point at the beginning of the tag."
  (declare (indent 0) (debug t))
  `(defun ,vhier-func ()
     (interactive)
     (beginning-of-line) ; Required for `outline-hide-sublevels'
     (call-interactively ,outline-func)
     (skip-chars-forward (car (car outshine-promotion-headings)))))

(verilog-ext-vhier-outline-nav vhier-previous-visible-heading #'outline-previous-visible-heading)
(verilog-ext-vhier-outline-nav vhier-next-visible-heading     #'outline-next-visible-heading)
(verilog-ext-vhier-outline-nav vhier-up-heading               #'outline-up-heading)
(verilog-ext-vhier-outline-nav vhier-forward-same-level       #'outline-forward-same-level)
(verilog-ext-vhier-outline-nav vhier-backward-same-level      #'outline-backward-same-level)
(verilog-ext-vhier-outline-nav vhier-hide-sublevels           #'outline-hide-sublevels)

(defun verilog-ext-vhier-outline-jump-to-file ()
  "Jump to file at cursor on Verilog-Perl hierarchy file."
  (interactive)
  (unless verilog-ext-vhier-mode
    (error "Vhier mode not enabled on current buffer"))
  (unless (executable-find "global")
    (error "Vhier mode requires global to work"))
  (unless (featurep 'ggtags)
    (error "Ggtags not available, required for jumping to a file"))
  (unless (ggtags-find-project)
    (error "Associated GTAGS file not found.  Make sure hierarchy file is in the same folder as its matching GTAGS file"))
  (delete-other-windows)
  (split-window-right)
  (shrink-window-horizontally 40)
  (other-window 1)
  (end-of-line)
  (xref-find-definitions (thing-at-point 'symbol t)))


;;;; Extraction
(defvar verilog-ext-vhier-buffer-name "*Verilog-Perl*"
  "Buffer name to use for the hierarchy file.")
(defvar verilog-ext-vhier-shell-cmds-buffer-name "*Verilog-Perl-Shell*"
  "Buffer name to use for the output of the shell commands vppreproc and vhier.")
(defvar verilog-ext-vhier-vhier-args '("--cells"
                                       "--no-missing"
                                       "--missing-modules"))

(defun verilog-ext-vhier-format-hierarchy-write-file (output-file)
  "Process Verilog-Perl buffer and write it to OUTPUT-FILE hierarchy file.
Make an outline/outshine tree-view buffer.  Save as .v extension to allow
compatibility with outshine comments and Gtags/Xref."
  (with-current-buffer (get-buffer verilog-ext-vhier-buffer-name)
    (goto-char (point-min))
    (verilog-ext-replace-regexp-whole-buffer "  " "*")
    (verilog-ext-replace-regexp-whole-buffer "*\\([a-zA-Z0-9_-]\\)" "* \\1")
    (verilog-ext-replace-regexp-whole-buffer "^*" "// *")
    ;; Parse not-used/not-found modules/files
    (goto-char (point-min))
    (re-search-forward "// \\* ")
    (when (re-search-forward "// \\* " nil t)
      (beginning-of-line)
      (open-line 3)
      (forward-line 2)
      (insert "// * Not found module references")
      (verilog-ext-replace-string "// * " "// ** " (point) nil))
    ;; Insert local variables at the end of the file
    (goto-char (point-max))
    (newline 1)
    (insert "\n// * Buffer local variables\n// Local Variables:\n// eval: (verilog-ext-vhier-mode 1)\n// End:\n")
    ;; Insert header to get some info of the file
    (goto-char (point-min))
    (open-line 1)
    (insert (concat "// Hierarchy generated by `verilog-ext' at " (format-time-string "%d-%m-%Y, %H:%M:%S") "\n"))
    (write-file output-file)
    (verilog-ext-vhier-mode)))

(defun verilog-ext-vhier-current-file ()
  "Extract hierarchy of current file module using Verilog-Perl backend."
  (interactive)
  (unless (executable-find "vhier")
    (error "Executable vhier not found"))
  (let* ((library-args (verilog-expand-command "__FLAGS__"))
         (vhier-args (mapconcat #'identity verilog-ext-vhier-vhier-args " "))
         (top-module (verilog-ext-select-file-module buffer-file-name))
         (file-path (or verilog-ext-vhier-output-file
                        (concat (verilog-ext-path-join default-directory "vhier/") top-module ".v")))
         (buf verilog-ext-vhier-buffer-name)
         (buf-err verilog-ext-vhier-shell-cmds-buffer-name)
         (err-msg (format "vhier returned with errors\nCheck %s buffer" buf-err))
         (cmd (concat "vhier "
                      library-args " "
                      vhier-args " "
                      "--top-module " top-module " "
                      (when verilog-ext-vhier-command-file
                        (concat "-f " verilog-ext-vhier-command-file " "))
                      buffer-file-name)))
    (make-directory (file-name-directory file-path) t)
    (unless (= 0 (shell-command cmd buf buf-err))
      (pop-to-buffer buf-err)
      (error err-msg))
    (verilog-ext-vhier-format-hierarchy-write-file file-path)
    (pop-to-buffer (get-file-buffer file-path))))

;;; Flycheck
;; Add support for the following linters in `flycheck':
;;  - verilator (overrides default parameters)
;;  - iverilog
;;  - verible
;;  - slang
;;  - svlint
;;  - Cadence HAL
(defvar verilog-ext-flycheck-linter 'verilog-verilator
  "Verilog-ext flycheck linter.")

(defvar verilog-ext-flycheck-linters '(verilog-verible
                                       verilog-verilator
                                       verilog-slang
                                       verilog-iverilog
                                       verilog-cadence-hal
                                       verilog-svlint)
  "List of supported linters.")


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
  (setq verilog-ext-flycheck-linter linter) ; Save state for reporting
  ;; Set it at the head of the list
  (delete linter flycheck-checkers)
  (add-to-list 'flycheck-checkers linter)
  (verilog-ext-flycheck-setup-linter linter)
  ;; Refresh linter if in a verilog buffer
  (when (string= major-mode "verilog-mode")
    (flycheck-select-checker linter))
  (message "Linter set to: %s " linter))

(defun verilog-ext-flycheck-setup ()
  "Add available linters from `verilog-ext-flycheck-linters' and set default one."
  (interactive)
  (dolist (checker verilog-ext-flycheck-linters)
    (add-to-list 'flycheck-checkers checker))
  (verilog-ext-flycheck-set-linter verilog-ext-flycheck-linter))

(defun verilog-ext-flycheck-mode-toggle (&optional uarg)
  "`flycheck-mode' Verilog wrapper function.
If called with UARG select among available linters and enable flycheck.

Disable function `eldoc-mode' if flycheck is enabled
to avoid minibuffer collisions."
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
      (message "Flycheck disabled"))
    (when verilog-ext-flycheck-eldoc-toggle
      (if flycheck-mode
          (eldoc-mode -1)
        (eldoc-mode 1)))))


;;;; Verilator
(defvar verilog-ext-flycheck-verilator-include-path nil)

(flycheck-define-checker verilog-verilator
  "A Verilog syntax checker using the Verilator Verilog HDL simulator.

See URL `https://www.veripool.org/wiki/verilator'."
  ;; https://verilator.org/guide/latest/exe_verilator.html
  ;;   The three flags -y, +incdir+<dir> and -I<dir> have similar effect;
  ;;   +incdir+<dir> and -y are fairly standard across Verilog tools while -I<dir> is used by many C++ compilers.
  :command ("verilator" "--lint-only" "-Wall" "-Wno-fatal"
            "--bbox-unsup" ; Blackbox unsupported language features to avoid errors on verification sources
            "--bbox-sys"  ;  Blackbox unknown $system calls
            (option-list "-I" verilog-ext-flycheck-verilator-include-path concat)
            source)
  :error-patterns
  ((warning line-start "%Warning-" (zero-or-more not-newline) ": " (file-name) ":" line ":" column ": " (message) line-end)
   (error   line-start "%Error: "                                  (file-name) ":" line ":" column ": " (message) line-end)
   (error   line-start "%Error-"   (zero-or-more not-newline) ": " (file-name) ":" line ":" column ": " (message) line-end))
  :modes (verilog-mode verilog-ts-mode))


;;;; Iverilog
(flycheck-define-checker verilog-iverilog
  "A Verilog syntax checker using Icarus Verilog.

See URL `http://iverilog.icarus.com/'"
  ;; Limitations found:
  ;;   - The command line -y flag will not search for .sv extensions, even though the -g2012 flag is set.
  ;;   - The +libext+.sv will only work with command files (equivalent to -f in xrun), not with command line arguments.
  ;;      - That means that a file that specifies the libraries/plusargs should be used with the -c <COMMAND_FILE> command line argument.
  :command ("iverilog" "-g2012" "-Wall" "-gassertions" "-t" "null" "-i" ; -i ignores missing modules
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
(flycheck-define-checker verilog-slang
  "SystemVerilog Language Services.

slang is the fastest and most compliant SystemVerilog frontend (according to the
open source chipsalliance test suite).

See URL `https://github.com/MikePopoloski/slang'."
  :command ("slang"
            "--lint-only"
            "--ignore-unknown-modules"
            source)
  :error-patterns
  ((error   (file-name) ":" line ":" column ": error: "   (message))
   (warning (file-name) ":" line ":" column ": warning: " (message)))
  :modes (verilog-mode verilog-ts-mode))


;;;; Svlint
(defvar verilog-ext-flycheck-svlint-include-path nil)

(flycheck-define-checker verilog-svlint
  "A Verilog syntax checker using svlint.

See URL `https://github.com/dalance/svlint'"
  :command ("svlint"
            "-1" ; one-line output
            "--ignore-include"
            (option-list "-i" verilog-ext-flycheck-svlint-include-path)
            source)
  :error-patterns
  ((warning line-start "Fail"  (zero-or-more blank) (file-name) ":" line ":" column (zero-or-more blank) (zero-or-more not-newline) "hint: " (message) line-end)
   (error   line-start "Error" (zero-or-more blank) (file-name) ":" line ":" column (zero-or-more blank) (zero-or-more not-newline) "hint: " (message) line-end))
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
  (let* ((log-path (verilog-ext-path-join verilog-ext-flycheck-hal-directory verilog-ext-flycheck-hal-log-name))
         (script-path (verilog-ext-path-join verilog-ext-flycheck-hal-directory verilog-ext-flycheck-hal-script-name))
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


;;; LSP
;; Support for various SystemVerilog language servers
;;  - Builtin:
;;     - hdl_checker: https://github.com/suoto/hdl_checker
;;     - svlangserver: https://github.com/imc-trading/svlangserver
;;  - Additional:
;;     - verible: https://github.com/chipsalliance/verible/tree/master/verilog/tools/ls
;;     - svls: https://github.com/dalance/svls
;;     - veridian: https://github.com/vivekmalneedi/veridian
(defconst verilog-ext-lsp-available-servers
  '((ve-hdl-checker  . ("hdl_checker" "--lsp"))
    (ve-svlangserver . "svlangserver")
    (ve-verible-ls   . "verible-verilog-ls")
    (ve-svls         . "svls")
    (ve-veridian     . "veridian"))
  "Verilog-ext available LSP servers.")

(defconst verilog-ext-lsp-server-ids
  (mapcar #'car verilog-ext-lsp-available-servers))

;;;; lsp-mode
(defvar verilog-ext-lsp-mode-default-server 've-svlangserver)

(defun verilog-ext-lsp-setup ()
  "Configure Verilog for `lsp-mode'.
Register additional clients."
  (interactive)
  (let (server-id server-bin)
    ;; Add `verilog-ts-mode' to the list of existing lsp ids
    (unless (alist-get 'verilog-ts-mode lsp-language-id-configuration)
      (push (cons 'verilog-ts-mode "verilog") lsp-language-id-configuration))
    ;; Register clients
    (dolist (server verilog-ext-lsp-available-servers)
      (setq server-id (car server))
      (setq server-bin (cdr server))
      (cond ((eq server-id 've-svlangserver)
             (lsp-register-client
              (make-lsp-client :new-connection (lsp-stdio-connection 'lsp-clients-svlangserver-command)
                               :major-modes '(verilog-mode verilog-ts-mode)
                               :library-folders-fn 'lsp-clients-svlangserver-get-workspace-additional-dirs
                               :server-id server-id)))
            (t
             (lsp-register-client
              (make-lsp-client :new-connection (lsp-stdio-connection server-bin)
                               :major-modes '(verilog-mode verilog-ts-mode)
                               :server-id server-id))))
      (message "Registered lsp-client: %s" server-id))))

(defun verilog-ext-lsp-set-server (server-id)
  "Set language server defined by SERVER-ID.
Disable the rest to avoid handling priorities.
Override any previous configuration for `verilog-mode' and `verilog-ts-mode'."
  (interactive (list (intern (completing-read "Server-id: " verilog-ext-lsp-server-ids nil t))))
  (let ((cmd (cdr (assoc server-id verilog-ext-lsp-available-servers))))
    (if (not (executable-find (if (listp cmd)
                                  (car cmd)
                                cmd)))
        (message "%s not in $PATH, skipping config..." server-id)
      ;; Else configure available server
      (dolist (mode '(verilog-mode verilog-ts-mode))
        (setq lsp-disabled-clients (assq-delete-all mode lsp-disabled-clients))
        (push (cons mode (remove server-id verilog-ext-lsp-server-ids)) lsp-disabled-clients))
      (message "[Verilog LSP]: %s" server-id))))


;;;; eglot
(defvar verilog-ext-eglot-default-server 've-svlangserver)

(defun verilog-ext-eglot-svlangserver-configuration ()
  "Configure settings for svlangserver with `eglot'.
For the time being, reuse `lsp-clients-svlangserver' variables from
`lsp-verilog'."
  (setq eglot-workspace-configuration
        `((:systemverilog
           (:includeIndexing ,lsp-clients-svlangserver-includeIndexing)
           (:excludeIndexing ,lsp-clients-svlangserver-excludeIndexing)
           (:defines ,lsp-clients-svlangserver-defines)
           (:launchConfiguration ,lsp-clients-svlangserver-launchConfiguration)
           (:lintOnUnsaved ,lsp-clients-svlangserver-lintOnUnsaved)
           (:formatCommand ,lsp-clients-svlangserver-formatCommand)
           (:disableCompletionProvider ,lsp-clients-svlangserver-disableCompletionProvider)
           (:disableHoverProvider ,lsp-clients-svlangserver-disableHoverProvider)
           (:disableSignatureHelpProvider ,lsp-clients-svlangserver-disableSignatureHelpProvider)
           (:disableLinting ,lsp-clients-svlangserver-disableLinting)))))

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

(defun verilog-ext-eglot-set-server (server-id)
  "Configure Verilog for `eglot' with SERVER-ID server.
Override any previous configuration for `verilog-mode' and `verilog-ts-mode'."
  (interactive (list (intern (completing-read "Server-id: " verilog-ext-lsp-server-ids nil t))))
  (let ((cmd (alist-get server-id verilog-ext-lsp-available-servers)))
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
            (push (append (list mode) cmd) eglot-server-programs)
          (push (list mode cmd) eglot-server-programs)))
      ;; Additional settings depending on chosen server-id
      (when (equal server-id 've-svlangserver)
        (dolist (hook '(verilog-mode-hook verilog-ts-mode-hook))
          (add-hook hook #'verilog-ext-eglot-svlangserver-configuration)))
      ;; Some reporting
      (message "Set eglot SV server: %s" server-id))))


;;; Major-mode
(defvar verilog-ext-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "TAB") 'verilog-ext-tab)
    (define-key map (kbd "M-d") 'verilog-ext-kill-word)
    (define-key map (kbd "M-f") 'verilog-ext-forward-word)
    (define-key map (kbd "M-b") 'verilog-ext-backward-word)
    (define-key map (kbd "C-<backspace>") 'verilog-ext-backward-kill-word)
    ;; Features
    (define-key map (kbd "M-i") 'verilog-ext-imenu-list)
    (define-key map (kbd "C-c C-p") 'verilog-ext-preprocess)
    (define-key map (kbd "C-c C-f") 'verilog-ext-flycheck-mode-toggle)
    (define-key map (kbd "C-c C-t") 'verilog-ext-hydra/body)
    (define-key map (kbd "C-c C-v") 'verilog-ext-vhier-current-file)
    ;; Code beautifying
    (define-key map (kbd "C-M-i") 'verilog-ext-indent-block-at-point)
    (define-key map (kbd "C-c C-b") 'verilog-ext-module-at-point-beautify)
    ;; Dwim navigation
    (define-key map (kbd "C-M-a") 'verilog-ext-nav-beg-of-defun-dwim)
    (define-key map (kbd "C-M-e") 'verilog-ext-nav-end-of-defun-dwim)
    (define-key map (kbd "C-M-d") 'verilog-ext-nav-down-dwim)
    (define-key map (kbd "C-M-u") 'verilog-ext-nav-up-dwim)
    (define-key map (kbd "C-M-p") 'verilog-ext-nav-prev-dwim)
    (define-key map (kbd "C-M-n") 'verilog-ext-nav-next-dwim)
    ;; Jump to parent module
    (define-key map (kbd "C-M-.") 'verilog-ext-jump-to-parent-module)
    ;; Port connections
    (define-key map (kbd "C-c C-c") 'verilog-ext-toggle-connect-port)
    (define-key map (kbd "C-c C-l") 'verilog-ext-connect-ports-recursively)
    map)
  "Key map for the `verilog-ext'.")


;;;###autoload
(defun verilog-ext-mode-setup ()
  "Setup `verilog-ext-mode' depending on enabled features."
  (interactive)
  ;; Jump to parent module ag/ripgrep hooks
  (add-hook 'ag-search-finished-hook #'verilog-ext-navigation-ag-rg-hook)
  (add-hook 'ripgrep-search-finished-hook #'verilog-ext-navigation-ag-rg-hook)
  ;; Flycheck
  (verilog-ext-flycheck-setup)
  ;; Lsp
  (verilog-ext-lsp-setup)
  (verilog-ext-lsp-set-server verilog-ext-lsp-mode-default-server)
  (verilog-ext-eglot-set-server verilog-ext-eglot-default-server))

;;;###autoload
(define-minor-mode verilog-ext-mode
  "Minor mode for editing SystemVerilog files.

\\{verilog-ext-mode-map}"
  :lighter " vX"
  :global nil
  ;; Update list of open buffers/directories (Verilog AUTO, flycheck)
  (if verilog-ext-mode
      (progn
        (verilog-ext-scan-buffer-modules)
        (verilog-ext-update-buffer-and-dir-list)
        (setq verilog-library-directories verilog-ext-dir-list)
        (setq verilog-ext-flycheck-verilator-include-path verilog-ext-dir-list)
        (add-hook 'kill-buffer-hook #'verilog-ext-kill-buffer-hook nil :local)
        (verilog-ext-block-end-comments-to-names-mode)
        (verilog-ext-time-stamp-mode)
        ;; `verilog-mode'-only customization (exclude `verilog-ts-mode')
        (when (string= major-mode "verilog-mode")
          ;; Imenu
          (setq-local imenu-create-index-function #'verilog-ext-imenu-index)
          ;; Font-lock
          ;;   It's not possible to add font-lock keywords to minor-modes.
          ;;   The workaround consists in add/remove keywords to the major mode when
          ;;   the minor mode is loaded/unloaded.
          ;;   https://emacs.stackexchange.com/questions/60198/font-lock-add-keywords-is-not-working
          (font-lock-add-keywords nil (append verilog-ext-font-lock-keywords
                                              verilog-ext-font-lock-keywords-1
                                              verilog-ext-font-lock-keywords-2
                                              verilog-ext-font-lock-keywords-3) 'set)
          (font-lock-flush)
          (setq-local font-lock-multiline nil)
          ;; Syntax table overriding:
          ;; Avoid considering tick as part of a symbol on preprocessor directives while
          ;; isearching.  Works in conjunction with `verilog-ext-tab'
          ;; and `verilog-ext-indent-region' to get back standard table to avoid
          ;; indentation issues with compiler directives.
          (modify-syntax-entry ?` ".")))
    ;; Cleanup
    (remove-hook 'kill-buffer-hook #'verilog-ext-kill-buffer-hook :local)
    (verilog-ext-block-end-comments-to-names-mode -1)
    (verilog-ext-time-stamp-mode -1)))


;;; Provide
(provide 'verilog-ext)

;;; verilog-ext.el ends here

;; Silence all the hydra docstring byte-compiler warnings:
;;
;; Local Variables:
;; byte-compile-warnings: (not docstrings)
;; End:
