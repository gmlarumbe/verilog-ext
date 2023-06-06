;;; verilog-ext-utils.el --- Verilog-ext Utils  -*- lexical-binding: t -*-

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

;; Utils

;;; Code:

(require 'verilog-mode)
(require 'xref)
(require 'ag)
(require 'ripgrep)
(require 'company-keywords)

;;;; Custom
(defcustom verilog-ext-file-extension-re "\\.s?vh?$"
  "(SystemVerilog) file extensions.
Defaults to .v, .vh, .sv and .svh."
  :type 'string
  :group 'verilog-ext)


;;;; Consts/Vars
(defconst verilog-ext-keywords-re
  (eval-when-compile
    (regexp-opt verilog-keywords 'symbols)))

(defconst verilog-ext-top-instantiable-re
  (concat "\\<\\(?1:module\\|interface\\)\\>\\(\\s-+\\<automatic\\>\\)?\\s-+\\(?3:" verilog-identifier-sym-re "\\)"))
(defconst verilog-ext-task-re
  (concat "\\(?1:\\(?:\\(?:static\\|pure\\|virtual\\|local\\|protected\\)\\s-+\\)*task\\)\\s-+\\(?:\\(?:static\\|automatic\\)\\s-+\\)?"
          "\\(?:\\(?2:" verilog-identifier-sym-re "\\)::\\)?"
          "\\(?3:" verilog-identifier-sym-re "\\)"))
(defconst verilog-ext-function-re
  (concat "\\(?1:\\(?:\\(?:static\\|pure\\|virtual\\|local\\|protected\\)\\s-+\\)*function\\)\\s-+\\(?:\\(?:static\\|automatic\\)\\s-+\\)?"
          "\\(?:" verilog-identifier-sym-re "\\s-+\\)?\\(?:\\(?:un\\)signed\\s-+\\)?" ; Optional Return type
          "\\(?:\\(?2:" verilog-identifier-sym-re "\\)::\\)?"
          "\\(?3:" verilog-identifier-sym-re "\\)"))
(defconst verilog-ext-class-re (concat "\\(?1:\\<class\\>\\)\\s-+\\(?3:" verilog-identifier-sym-re "\\)"))
(defconst verilog-ext-top-re (concat "\\<\\(?1:package\\|program\\|module\\|interface\\)\\>\\(\\s-+\\<automatic\\>\\)?\\s-+\\(?3:" verilog-identifier-sym-re "\\)"))

(defvar verilog-ext-buffer-list nil)
(defvar verilog-ext-dir-list nil)
(defvar verilog-ext-file-list nil)
(defvar-local verilog-ext-file-allows-instances nil
  "Non nil if current file includes a module or interface block.")

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


(defconst verilog-ext-server-lsp-list
  '((ve-hdl-checker  . ("hdl_checker" "--lsp"))
    (ve-svlangserver . "svlangserver")
    (ve-verible-ls   . "verible-verilog-ls")
    (ve-svls         . "svls")
    (ve-veridian     . "veridian"))
  "Verilog-ext available LSP servers.")

(defconst verilog-ext-server-lsp-ids
  (mapcar #'car verilog-ext-server-lsp-list))

(defconst verilog-ext-async-inject-variables-re "\\`\\(load-path\\|buffer-file-name\\|verilog-ext-workspace-\\|verilog-align-typedef-\\)")


;;;; Wrappers
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
  "Wrap `verilog-backward-sexp', ignore errors and return point."
  (ignore-errors
    (verilog-backward-sexp)
    (point)))

(defun verilog-ext-pos-at-forward-sexp ()
  "Return pos of point afer `verilog-ext-forward-sexp'."
  (save-match-data
    (save-excursion
      (verilog-ext-forward-sexp))))

(defun verilog-ext-pos-at-backward-sexp ()
  "Return pos of point afer `verilog-ext-backward-sexp'."
  (save-match-data
    (save-excursion
      (verilog-ext-backward-sexp))))

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

;;;; String/regexp
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

;;;; Dirs
(defun verilog-ext-dir-files (dir &optional follow-symlinks ignore-dirs)
  "Find SystemVerilog files recursively on DIR.

Follow symlinks if optional argument FOLLOW-SYMLINKS is non-nil.

Discard non-regular files (e.g. Emacs temporary non-saved buffer files like
symlink #.test.sv).

Optional arg IGNORE-DIRS specifies which directories should be excluded from
search."
  (let* ((files (directory-files-recursively dir
                                             verilog-ext-file-extension-re
                                             nil nil follow-symlinks))
         (files-after-ignored (seq-filter (lambda (file)
                                            ;; Each file checks if it has its prefix in the list of ignored directories
                                            (let (ignore-file)
                                              (dolist (dir ignore-dirs)
                                                (when (string-prefix-p (expand-file-name dir) (expand-file-name file))
                                                  (setq ignore-file t)))
                                              (not ignore-file)))
                                          files))
         (files-regular (seq-filter #'file-regular-p files-after-ignored)))
    files-regular))

(defun verilog-ext-dirs-files (dirs &optional follow-symlinks ignore-dirs)
  "Find SystemVerilog files recursively on DIRS.
DIRS is a list of directory strings.

Follow symlinks if optional argument FOLLOW-SYMLINKS is non-nil.

Optional arg IGNORE-DIRS specifies which directories should be excluded from
search."
  (let (files)
    (dolist (dir dirs)
      (push (verilog-ext-dir-files dir follow-symlinks ignore-dirs) files))
    (when files
      (flatten-tree files))))


;;;; File modules
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


;;;; Block at point / point inside block
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

(defun verilog-ext-point-inside-extern-tf-definition ()
  "Return function/task classifier name if point is in an extern definition."
  (save-excursion
    (and (verilog-re-search-backward "\\<\\(function\\|task\\)\\>" nil :no-error)
         (or (looking-at verilog-ext-function-re)
             (looking-at verilog-ext-task-re))
         (match-string-no-properties 2)))) ; Match 2 corresponds to class name classifier

(defun verilog-ext-point-inside-multiline-define ()
  "Return non-nil if point is inside a multilin define.
Check `verilog-indent-ignore-p'."
  (save-match-data
    (or (save-excursion
          (verilog-re-search-forward ".*\\\\\\s-*$" (line-end-position) t))
        (save-excursion  ; Last line after multiline define
          (verilog-backward-syntactic-ws)
          (unless (bobp)
            (backward-char))
          (looking-at "\\\\")))))

(defun verilog-ext-get-block-boundaries (block)
  "Get boundaries of BLOCK.
Assumes that point is looking at a BLOCK type."
  (let ((start-pos (point))
        beg end)
    (save-excursion
      (cond (;; Classes/functions/tasks and tops
             (member block '(class function task module interface package program))
             (verilog-re-search-forward ";" nil t)
             (setq beg (point))
             (goto-char start-pos)
             (verilog-ext-forward-sexp)
             (backward-word)
             (setq end (point)))
            ;; Procedural
            ((member block '(always initial final))
             (verilog-ext-skip-identifier-forward)
             (verilog-ext-forward-syntactic-ws)
             (setq beg (point))
             (verilog-re-search-forward "begin" (line-end-position) t)
             (verilog-ext-forward-sexp)
             (backward-word)
             (setq end (point)))
            ;; Generate
            ((equal block 'generate)
             (verilog-ext-skip-identifier-forward)
             (setq beg (point))
             (verilog-ext-forward-sexp)
             (backward-word)
             (setq end (point)))
            ;; Begin-end
            ((equal block 'begin-end)
             (setq beg (point))
             (verilog-ext-forward-sexp)
             (backward-word)
             (looking-at "\\<end\\>")
             (setq end (match-end 0)))
            ;; Default invalid condition
            (t
             (error "Invalid condition")))
      (cons beg end))))

(defun verilog-ext-point-inside-block (block)
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
        block-boundaries block-beg-point block-end-point block-type block-name)
    (save-match-data
      (save-excursion
        (when (and (verilog-re-search-backward re nil t)
                   (cond (;; Classes
                          (equal block 'class)
                          (if (verilog-ext-class-declaration-is-typedef-p)
                              ;; Try again if looking at a typedef class declaration
                              (verilog-ext-point-inside-block 'class)
                            ;; Else do the same as for function/tasks and top blocks
                            (setq block-type (match-string-no-properties 1))
                            (looking-at verilog-ext-class-re)
                            (setq block-name (match-string-no-properties 3))))
                         ;; Function/tasks and top blocks
                         ((member block '(function task module interface package program))
                          (and (save-excursion ; Exclude external func/tasks declarations
                                 (save-match-data
                                   (verilog-beg-of-statement)
                                   (not (looking-at "\\<extern\\>"))))
                               (setq block-type (match-string-no-properties 1))
                               (or (looking-at verilog-ext-function-re)
                                   (looking-at verilog-ext-task-re)
                                   (looking-at verilog-ext-top-re))
                               (setq block-name (match-string-no-properties 3))))
                         ;; Procedural: always, initial and final
                         ((member block '(always initial final))
                          (if (equal block 'always)
                              (setq block-type "always")
                            (setq block-type (match-string-no-properties 1)))
                          (save-excursion ; Get block name
                            (verilog-ext-skip-identifier-forward)
                            (verilog-ext-forward-syntactic-ws)
                            (setq block-name (buffer-substring-no-properties (point) (line-end-position)))))
                         ;; Generate
                         ((equal block 'generate)
                          (and (setq block-type (match-string-no-properties 1))
                               (save-excursion ; Get block name
                                 (verilog-ext-skip-identifier-forward)
                                 (verilog-ext-forward-syntactic-ws)
                                 (setq block-name (buffer-substring-no-properties (point) (line-end-position))))))
                         ;; Procedural block (begin-end)
                         ((equal block 'begin-end)
                          (verilog-ext-while-t (string= (match-string-no-properties 0) "end")
                            (verilog-ext-backward-sexp)
                            (verilog-re-search-backward re nil t))
                          (setq block-type "begin-end")
                          (setq block-name "")) ; Return non-nil for and condition
                         ;; Default invalid condition
                         (t
                          (error "Invalid condition"))))
          ;; Set boundaries and return value
          (setq block-boundaries (verilog-ext-get-block-boundaries block))
          (setq block-beg-point (car block-boundaries))
          (setq block-end-point (cdr block-boundaries)))
        (when (and block-beg-point block-end-point
                   (>= pos block-beg-point)
                   (< pos block-end-point))
          `((type      . ,block-type)
            (name      . ,block-name)
            (beg-point . ,block-beg-point)
            (end-point . ,block-end-point)))))))

(defconst verilog-ext-block-at-point-all-re
  (regexp-opt
   '("function" "endfunction" "task" "endtask" "class" "endclass"
     "generate" "endgenerate" "module" "endmodule" "interface"
     "endinterface" "program" "endprogram" "package" "endpackage"
     "always" "initial" "final")
   'symbols))

(defconst verilog-ext-block-at-point-top-and-class-re
  (regexp-opt
   '("class" "package" "module" "interface" "program")
   'symbols))

(defconst verilog-ext-block-at-point-top-re
  (regexp-opt
   '("package" "module" "interface" "program")
   'symbols))

(defun verilog-ext-block-at-point (&optional return-pos)
  "Return current block type and name at point.
If RETURN-POS is non-nil, return also the begin and end positions for the block
at point.
Do not reuse `verilog-ext-point-inside-block' implementation to improve
efficiency and be able to use it for features such as `which-func'."
  (let ((start-pos (point))
        block block-type block-name block-boundaries block-beg-point block-end-point)
    (save-match-data
      (save-excursion
        (when (verilog-re-search-backward verilog-ext-block-at-point-all-re nil :no-error)
          (setq block (match-string-no-properties 0))
          ;; Try to set block-type and block-name depending on the context
          (cond (;; Class/top block containing task/function
                 (string-match "\\<end\\(function\\|task\\)\\>" block)
                 (when (and (not (verilog-ext-point-inside-extern-tf-definition)) ; Extern method definition...
                            (verilog-re-search-backward verilog-ext-block-at-point-top-and-class-re nil :no-error)) ; ... will be inside a class/module/program/interface
                   (setq block-type (match-string-no-properties 0))
                   (or (looking-at verilog-ext-class-re)
                       (looking-at verilog-ext-top-re))
                   (setq block-name (match-string-no-properties 3))))
                ;; Defun
                ((string-match "\\<end\\(class\\|generate\\)\\>" block)
                 (when (and (verilog-re-search-backward verilog-ext-block-at-point-top-re nil :no-error)
                            (setq block (match-string-no-properties 0))
                            (string-match verilog-ext-block-at-point-top-re block))
                   (setq block-type block)
                   (looking-at verilog-ext-top-re)
                   (setq block-name (match-string-no-properties 3))))
                ;; Function/task
                ((string-match "\\<\\(function\\|task\\)\\>" block)
                 (if (save-excursion (verilog-re-search-backward "\\<extern\\>" (line-beginning-position) :no-error))
                     (progn ; If extern it must be a class method
                       (verilog-re-search-backward "\\<class\\>" nil :no-error)
                       (when (verilog-ext-looking-at-class-declaration)
                         (setq block-type "class")
                         (setq block-name (match-string-no-properties 3))))
                   ;; Else, non-extern function/task
                   (or (looking-at verilog-ext-function-re)
                       (looking-at verilog-ext-task-re))
                   (setq block-type block)
                   (setq block-name (match-string-no-properties 3))))
                ;; Class
                ((string= block "class")
                 (unless (verilog-ext-class-declaration-is-typedef-p)
                   (setq block-type block)
                   (looking-at verilog-ext-class-re)
                   (setq block-name (match-string-no-properties 3))))
                ;; Package/module/interface/program
                ((string-match verilog-ext-block-at-point-top-re block)
                 (setq block-type block)
                 (looking-at verilog-ext-top-re)
                 (setq block-name (match-string-no-properties 3)))
                ;; Generate/always/initial/final
                ((string-match "\\<\\(generate\\|always\\|initial\\|final\\)\\>" block)
                 (let (temp-pos)
                   (setq block-type block)
                   (save-excursion
                     (verilog-re-search-forward "begin" nil :no-error)
                     (if (looking-at (concat "\\s-*:\\s-*\\(?1:" verilog-identifier-re "\\)"))
                         (setq block-name (match-string-no-properties 1))
                       (setq block-name "unnamed"))
                     (when (string-match "\\<\\(always\\|initial\\|final\\)\\>" block) ; Handle subcase for always/initial/final
                       (verilog-ext-forward-sexp)
                       (when (and (>= start-pos (point)) ; If not inside the procedural block...
                                  ;; ... it's assumed that these will be inside a module/interface/program block
                                  (verilog-re-search-backward verilog-ext-block-at-point-top-re nil :no-error))
                         (setq block-type (match-string-no-properties 0))
                         (looking-at verilog-ext-top-re)
                         (setq block-name (match-string-no-properties 3))
                         (setq temp-pos (point)))))
                   ;; If it was first detected as a procedural/generate but it turned out to be a top/defun block...
                   (when (string-match verilog-ext-block-at-point-top-re block-type)
                     (goto-char temp-pos))))
                ;; Top blocks (might have found "endmodule/endinterface/endprogram/endpackage" or nothing)
                (t
                 (setq block-type nil)
                 (setq block-name nil))))
        ;; Return values and boundaries
        (when (and block-type block-name)
          (when return-pos
            (setq block (intern block-type))
            (setq block-boundaries (verilog-ext-get-block-boundaries block))
            (setq block-beg-point (car block-boundaries))
            (setq block-end-point (cdr block-boundaries)))
          `((type      . ,block-type)
            (name      . ,block-name)
            (beg-point . ,block-beg-point)
            (end-point . ,block-end-point)))))))

;;;; Buffers/hooks
(defun verilog-ext-update-buffer-file-and-dir-list ()
  "Update `verilog-mode' list of open buffers, files, and dir lists."
  (let (verilog-buffers verilog-dirs verilog-files)
    (dolist (buf (buffer-list (current-buffer)))
      (with-current-buffer buf
        (when (or (eq major-mode 'verilog-mode)
                  (eq major-mode 'verilog-ts-mode))
          (push buf verilog-buffers)
          (unless (member default-directory verilog-dirs)
            (push default-directory verilog-dirs))
          (when (and buffer-file-name
                     (string-match verilog-ext-file-extension-re (concat "." (file-name-extension buffer-file-name))))
            (push buffer-file-name verilog-files)))))
    (setq verilog-ext-buffer-list verilog-buffers)
    (setq verilog-ext-dir-list verilog-dirs)
    (setq verilog-ext-file-list verilog-files)))

(defun verilog-ext-kill-buffer-hook ()
  "Verilog hook to run when killing a buffer."
  (setq verilog-ext-buffer-list (remove (current-buffer) verilog-ext-buffer-list)))


;;;; Editing
(defun verilog-ext-kill-word (&optional arg)
  "Make verilog `kill-word' command stop at underscores.
Optional ARG sets number of words to kill."
  (interactive "p")
  (cond ((eq major-mode 'verilog-mode)
         (let ((table (make-syntax-table verilog-mode-syntax-table)))
           (modify-syntax-entry ?_ "_" table)
           (with-syntax-table table
             (kill-word arg))))
        ((eq major-mode 'verilog-ts-mode)
         (kill-word arg))
        (t
         (error "Wrong major-mode to run `verilog-ext-kill-word'"))))

(defun verilog-ext-backward-kill-word (&optional arg)
  "Make verilog `backward-kill-word' command stop at underscores.
Optional ARG sets number of words to kill."
  (interactive "p")
  (cond ((eq major-mode 'verilog-mode)
         (let ((table (make-syntax-table verilog-mode-syntax-table)))
           (modify-syntax-entry ?_ "_" table)
           (with-syntax-table table
             (backward-kill-word arg))))
        ((eq major-mode 'verilog-ts-mode)
         (backward-kill-word arg))
        (t
         (error "Wrong major-mode to run `verilog-ext-backward-kill-word'"))))

(defun verilog-ext-indent-region (start end &optional column)
  "Wrapper for `indent-region'.
Prevents indentation issues with compiler directives with a modified syntax
table.
Pass the args START, END and optional COLUMN to `indent-region'."
  (cond ((eq major-mode 'verilog-mode)
         (let ((table (make-syntax-table verilog-mode-syntax-table)))
           (modify-syntax-entry ?` "w" table)
           (with-syntax-table table
             (indent-region start end column))))
        ((eq major-mode 'verilog-ts-mode)
         (indent-region start end column))
        (t
         (error "Wrong major-mode to run `verilog-ext-backward-kill-word'"))))

(defun verilog-ext-tab (&optional arg)
  "Run corresponding TAB function depending on `major-mode'.
If on a `verilog-mode' buffer, run `electric-verilog-tab' with original
`verilog-mode' syntax table.  Prevents indentation issues with compiler
directives with a modified syntax table.
If on a `verilog-ts-mode' buffer, run `indent-for-tab-command' with ARG."
  (interactive "P")
  (cond ((eq major-mode 'verilog-mode)
         (let ((table (make-syntax-table verilog-mode-syntax-table)))
           (modify-syntax-entry ?` "w" table)
           (with-syntax-table table
             (electric-verilog-tab))))
        ((eq major-mode 'verilog-ts-mode)
         (indent-for-tab-command arg))
        (t
         (error "Wrong major-mode to run `verilog-ext-tab'"))))

;;;; Misc
(defun verilog-ext-company-keywords-add ()
  "Add `verilog-keywords' to `company-keywords' backend."
  (dolist (mode '(verilog-mode verilog-ts-mode))
    (add-to-list 'company-keywords-alist (append `(,mode) verilog-keywords))))

(provide 'verilog-ext-utils)

;;; verilog-ext-utils.el ends here
