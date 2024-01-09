;;; verilog-ext-utils.el --- Verilog-ext Utils  -*- lexical-binding: t -*-

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

;; Common utils used in different features.

;;; Code:

(require 'verilog-mode)

;;;; Custom
(defcustom verilog-ext-file-extension-re "\\.s?vh?\\'"
  "(System)Verilog file extension regexp.
Defaults to .v, .vh, .sv and .svh."
  :type 'string
  :group 'verilog-ext)

(defcustom verilog-ext-cache-enable t
  "If set to non-nil enable use of cache files."
  :type 'boolean
  :group 'verilog-ext)

(defcustom verilog-ext-cache-do-compression nil
  "If set to non-nil compress cache files.

Requires having \"gzip\" and \"gunzip\" in the $PATH.

If set to non-nil increases loading time of `verilog-ext' package but cache
files take up much less disk space."
  :type 'boolean
  :group 'verilog-ext)

(defcustom verilog-ext-project-alist nil
  "`verilog-ext' project alist.

Used for per-project functionality in `verilog-ext'.

Its elements have the following structure: their car is a string with the name
of the project and their cdr a property list with the following properties:
 - :root - base directory of the project (mandatory)
 - :dirs - directories to search for project files (list of strings)
 - :ignore-dirs - directories to ignore (list of strings)
 - :files - files to be used for the project, keep in order for vhier
            hierarchy extraction (list of strings)
 - :ignore-files - files to be ignored for project (list of strings)

Compilation:
 - :compile-cmd - command used to compile current project (string)

Vhier:
 - :command-file - vhier command file
 - :lib-search-path - list of dirs to look for include directories or libraries."
  :type '(repeat
          (list (string :tag "Project")
                (plist :tag "Properties"
                       :options ((:root string)
                                 (:dirs (repeat directory))
                                 (:ignore-dirs (repeat directory))
                                 (:files (repeat file))
                                 (:ignore-files (repeat file))
                                 (:compile-cmd string)
                                 (:command-file file)
                                 (:lib-search-path (repeat directory))))))
  :group 'verilog-ext)



;;;; Consts/Vars
;;;;; Regexps
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
;;;;; LSP
(defconst verilog-ext-lsp-available-servers
  '((ve-hdl-checker  . ("hdl_checker" "--lsp"))
    (ve-svlangserver . "svlangserver")
    (ve-verible-ls   . "verible-verilog-ls")
    (ve-svls         . "svls")
    (ve-veridian     . "veridian"))
  "Verilog-ext available LSP servers.")
(defconst verilog-ext-lsp-server-ids (mapcar #'car verilog-ext-lsp-available-servers))

;;;;; Misc
(defvar verilog-ext-buffer-list nil)
(defvar verilog-ext-dir-list nil)
(defvar verilog-ext-file-list nil)
(defvar-local verilog-ext-file-allows-instances nil
  "Non nil if current file includes a module or interface block.")

(defconst verilog-ext-cache-dir (file-name-concat user-emacs-directory "verilog-ext")
  "The directory where verilog-ext cache files will be placed at.")

(defconst verilog-ext-compiler-directives
  (eval-when-compile
    (mapcar (lambda (directive)
              (substring directive 1 nil))
            verilog-compiler-directives))
  "List of Verilog compiler directives, without the tick.")

;;;; Macros
(defmacro verilog-ext-with-no-hooks (&rest body)
  "Execute BODY without running any additional Verilog hooks."
  (declare (indent 0) (debug t))
  `(let ((prog-mode-hook nil)
         (verilog-mode-hook '(verilog-ext-mode))
         (verilog-ts-mode-hook nil))
     ,@body))

(defmacro verilog-ext-proj-setcdr (proj alist value)
  "Set cdr of ALIST for current PROJ to VALUE.

If current VALUE is nil remove its key from ALIST.

ALIST keys are strings that define projects in `verilog-ext-project-alist'."
  (declare (indent 0) (debug t))
  `(setf (alist-get ,proj ,alist nil 'remove 'string=) ,value))


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
  "Return non-nil if point skipped backwards Verilog identifier chars."
  (< (skip-chars-backward "a-zA-Z0-9_") 0))

(defun verilog-ext-skip-identifier-forward ()
  "Return non-nil if point skipped forward Verilog identifier chars."
  (> (skip-chars-forward "a-zA-Z0-9_") 0))

(defmacro verilog-ext-when-t (cond &rest body)
  "Execute BODY when COND is non-nil.
Same function `when' from subr.el but returning t if COND is nil."
  (declare (indent 1) (debug t))
  (list 'if cond (cons 'progn body) t))

(defmacro verilog-ext-while-t (cond &rest body)
  "Execute BODY while COND is non-nil.
Same function `while' but returning t after last condition."
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


;;;; Dirs/files
(defun verilog-ext-dir-files (dir &optional recursive follow-symlinks ignore-dirs)
  "Find SystemVerilog files on DIR.

If RECURSIVE is non-nil find files recursively.

Follow symlinks if optional argument FOLLOW-SYMLINKS is non-nil.

Discard non-regular files (e.g. Emacs temporary non-saved buffer files like
symlink #.test.sv).

Optional arg IGNORE-DIRS specifies which directories should be excluded from
search."
  (let* ((files (if recursive
                    (directory-files-recursively dir verilog-ext-file-extension-re nil nil follow-symlinks)
                  (directory-files dir t verilog-ext-file-extension-re)))
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

(defun verilog-ext-filelist-from-file (file)
  "Return filelist from FILE as a list of strings."
  (with-temp-buffer
    (insert-file-contents file)
    (delete "" (split-string (buffer-substring-no-properties (point-min) (point-max)) "\n"))))

(defun verilog-ext-file-from-filefile (filelist out-file)
  "Write FILELIST to OUT-FILE as one line per file."
  (with-temp-file out-file
    (insert (mapconcat #'identity filelist "\n"))))

(defun verilog-ext-expand-file-list (file-list &optional rel-dir)
  "Expand files in FILE-LIST.

Expand with respect to REL-DIR if non-nil."
  (mapcar (lambda (file)
            (expand-file-name file rel-dir))
          file-list))

;;;; File modules
(defun verilog-ext-scan-buffer-modules ()
  "Find modules in current buffer.

Return list with found modules and their start and end positions, or nil if no
module was found.

Update the value of buffer-local variable `verilog-ext-file-allows-instances' to
be used in optimization of font-lock and imenu."
  (if (eq major-mode 'verilog-ts-mode)
      ;; `verilog-ts-mode'
      (mapcar (lambda (node)
                `(,(verilog-ts--node-identifier-name node)
                  ,(treesit-node-start node)
                  ,(treesit-node-end node)))
              (verilog-ts-module-declarations-nodes-current-buffer))
    ;; `verilog-mode'
    (let (modules)
      (save-excursion
        (goto-char (point-min))
        (while (verilog-re-search-forward verilog-ext-top-instantiable-re nil t)
          (push `(,(match-string-no-properties 3) ; Name
                  ,(match-beginning 1)            ; Start pos
                  ,(save-excursion                ; End pos
                     (goto-char (match-beginning 1))
                     (verilog-ext-pos-at-forward-sexp)))
                modules)))
      (if modules
          (setq verilog-ext-file-allows-instances t)
        (setq verilog-ext-file-allows-instances nil))
      (nreverse (delete-dups modules)))))

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
        (verilog-ext-with-no-hooks
          (verilog-mode))
        (verilog-ext-scan-buffer-modules)))))

(defun verilog-ext-select-file-module (&optional file)
  "Select file module from FILE.
If only one module was found return it as a string.
If more than one module was found, select between available ones.
Return nil if no module was found."
  (let ((modules (mapcar #'car (verilog-ext-read-file-modules file))))
    (if (cdr modules)
        (completing-read "Select module: " modules)
      (car modules))))


;;;; Block at point / point inside block
(defun verilog-ext-class-declaration-is-typedef-p ()
  "Return non-nil if point is at a typedef class declaration."
  (save-excursion
    (save-match-data
      (and (looking-at verilog-ext-class-re)
           (verilog-ext-backward-syntactic-ws)
           (backward-word)
           (looking-at "typedef")))))

(defun verilog-ext-looking-at-class-declaration ()
  "Return non-nil if point is at a class declaration (i.e. not a typedef).
Updates `match-data' with matches of `verilog-ext-class-re'."
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
  "Return non-nil if point is inside a multiline define.
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
  (eval-when-compile
    (regexp-opt
     '("function" "endfunction" "task" "endtask" "class" "endclass"
       "generate" "endgenerate" "module" "endmodule" "interface"
       "endinterface" "program" "endprogram" "package" "endpackage"
       "always" "initial" "final")
     'symbols)))

(defconst verilog-ext-block-at-point-top-and-class-re
  (eval-when-compile
    (regexp-opt
     '("class" "package" "module" "interface" "program")
     'symbols)))

(defconst verilog-ext-block-at-point-top-re
  (eval-when-compile
    (regexp-opt
     '("package" "module" "interface" "program")
     'symbols)))

(defun verilog-ext-block-at-point (&optional return-pos)
  "Return current block type and name at point.

If RETURN-POS is non-nil, return also the begin and end positions for the block
at point.

Do not reuse `verilog-ext-point-inside-block' implementation to improve
efficiency and be able to use it for features such as `which-func'."
  (if (eq major-mode 'verilog-ts-mode)
      ;; `verilog-ts-mode'
      (let ((node (verilog-ts-block-at-point)))
        (when node
          `((type      . ,(verilog-ts--node-identifier-type node))
            (name      . ,(verilog-ts--node-identifier-name node))
            (beg-point . ,(treesit-node-start node))
            (end-point . ,(treesit-node-end node)))))
    ;; `verilog-mode'
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
              (end-point . ,block-end-point))))))))

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


;;;; Project
(defun verilog-ext-aget (alist key)
  "Return the value in ALIST that is associated with KEY.
If KEY is not found return nil."
  (cdr (assoc key alist)))

(defun verilog-ext-buffer-proj ()
  "Return current buffer project if it belongs to `verilog-ext-project-alist'."
  (catch 'project
    (when (and buffer-file-name verilog-ext-project-alist)
      (dolist (proj verilog-ext-project-alist)
        (when (string-prefix-p (expand-file-name (plist-get (cdr proj) :root))
                               (expand-file-name buffer-file-name))
          (throw 'project (car proj)))))))

(defun verilog-ext-buffer-proj-root (&optional project)
  "Return current buffer PROJECT root if it belongs to `verilog-ext-project-alist'."
  (let ((proj (or project (verilog-ext-buffer-proj))))
    (when proj
      (expand-file-name (plist-get (verilog-ext-aget verilog-ext-project-alist proj) :root)))))

(defun verilog-ext-proj-compile-cmd (&optional project)
  "Return current PROJECT compile-cmd from `verilog-ext-project-alist'."
  (let ((proj (or project (verilog-ext-buffer-proj))))
    (when proj
      (plist-get (verilog-ext-aget verilog-ext-project-alist proj) :compile-cmd))))

(defun verilog-ext-proj-command-file (&optional project)
  "Return current PROJECT vhier command-file from `verilog-ext-project-alist'."
  (let* ((proj (or project (verilog-ext-buffer-proj)))
         (root (verilog-ext-buffer-proj-root proj))
         (cmd-file (plist-get (verilog-ext-aget verilog-ext-project-alist proj) :command-file)))
    (when (and root cmd-file)
      (expand-file-name cmd-file root))))

(defun verilog-ext-proj-lib-search-path (&optional project)
  "Return current PROJECT vhier lib search path."
  (let ((proj (or project (verilog-ext-buffer-proj))))
    (when proj
      (plist-get (verilog-ext-aget verilog-ext-project-alist proj) :lib-search-path))))

(defun verilog-ext-proj-files (&optional project)
  "Return list of files for PROJECT.

These depend on the value of property list of `verilog-ext-project-alist'.
 :dirs - list of strings with optional \"-r\" to find files recursively
 :ignore-dirs - list of strings of dirs to be ignored
 :files - list of strings with the files
 :ignore-files - list of strings of ignored files"
  (let* ((proj (or project (verilog-ext-buffer-proj)))
         (proj-plist (verilog-ext-aget verilog-ext-project-alist proj))
         (proj-root (when proj-plist (expand-file-name (plist-get proj-plist :root))))
         (proj-dirs (plist-get proj-plist :dirs))
         (proj-ignore-dirs (plist-get proj-plist :ignore-dirs))
         (proj-files (plist-get proj-plist :files))
         (proj-ignore-files (plist-get proj-plist :ignore-files))
         files-dirs files-all)
    ;; Basic checks
    (unless proj
      (user-error "Not in a Verilog project buffer, check `verilog-ext-project-alist'"))
    (unless proj-root
      (user-error "Project root not set for project %s" proj))
    ;; Expand filenames (except for proj-dirs since they need to parse the -r recursive flag)
    (when proj-ignore-dirs
      (setq proj-ignore-dirs (verilog-ext-expand-file-list proj-ignore-dirs proj-root)))
    (when proj-files
      (setq proj-files (verilog-ext-expand-file-list proj-files proj-root)))
    (when proj-ignore-files
      (setq proj-ignore-files (verilog-ext-expand-file-list proj-ignore-files proj-root)))
    ;; Analyze directories
    (when proj-dirs
      (mapc (lambda (dir)
              (if (string= "-r" (car (split-string dir)))
                  (setq files-dirs (append files-dirs (verilog-ext-dir-files (expand-file-name (cadr (split-string dir)) proj-root) :recursive :follow-symlinks proj-ignore-dirs)))
                (setq files-dirs (append files-dirs (verilog-ext-dir-files (expand-file-name dir proj-root) nil :follow-symlinks proj-ignore-dirs)))))
            proj-dirs))
    ;; If no dirs or files are specified get recursively all files in root
    (if (and (not proj-files)
             (not proj-dirs))
        (setq files-all (verilog-ext-dir-files proj-root :recursive :follow-symlinks proj-ignore-dirs))
      (setq files-dirs (delete-dups files-dirs))
      (setq files-all (append files-dirs proj-files)))
    ;; Merge and filter
    (seq-filter (lambda (file)
                  (not (member file proj-ignore-files)))
                files-all)))

;;;; Cache
(defun verilog-ext-serialize (data filename)
  "Serialize DATA to FILENAME.

Compress cache files if gzip is available."
  (let ((dir (file-name-directory filename))
        (gzip-buf "*verilog-ext-serialize-compress*"))
    (unless (file-exists-p dir)
      (make-directory dir :parents))
    (if (not (file-writable-p filename))
        (message "Verilog-ext cache '%s' not writeable" filename)
      (with-temp-file filename
        (insert (let (print-length) (prin1-to-string data))))
      (when (and verilog-ext-cache-do-compression
                 (executable-find "gzip"))
        ;; Synchronous processing, as it might be run just before exiting Emacs
        (unless (eq 0 (call-process-shell-command (format "gzip -9f %s" filename) nil gzip-buf t))
          (error "Error compressing %s" filename))))))

(defun verilog-ext-unserialize (filename)
  "Read data serialized by `verilog-ext-serialize' from FILENAME."
  (let* ((compressed-filename (concat filename ".gz"))
         (temp-filename (make-temp-file (concat (file-name-nondirectory filename) "-")))
         (gzip-buf "*verilog-ext-serialize-decompress*")
         (decompress-cmd (format "gunzip -c %s > %s" compressed-filename temp-filename))) ; Keep original compressed file
    (with-demoted-errors
        "Error during file deserialization: %S"
      ;; INFO: Tried using zlib with `zlib-available-p' and
      ;; `zlib-decompress-region', which are faster.  However, these require the
      ;; buffer to be unibyte (i.e. have only ASCII characters). That could not
      ;; be the case for paths with non-latin characters
      ;; https://www.gnu.org/software/emacs/manual/html_node/elisp/Disabling-Multibyte.html
      (if (and verilog-ext-cache-do-compression
               (executable-find "gunzip")
               (file-exists-p compressed-filename))
          (progn
            ;; External gunzip program: This doesn't need to be asynchronous as it will only be done during initial setup
            (unless (eq 0 (call-process-shell-command decompress-cmd nil gzip-buf t))
              (error "Error decompressing %s" compressed-filename))
            (with-temp-buffer
              (insert-file-contents temp-filename)
              (delete-file temp-filename)
              (read (buffer-string))))
        ;; Do not decompress
        (when (file-exists-p filename)
          (with-temp-buffer
            (insert-file-contents filename)
            (read (buffer-string))))))))


(provide 'verilog-ext-utils)

;;; verilog-ext-utils.el ends here
