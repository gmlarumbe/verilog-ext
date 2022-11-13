;;; verilog-utils.el --- Verilog Utils  -*- lexical-binding: t -*-

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
;; Utility functions called from different features.
;;
;;; Code:


(require 'verilog-mode)
(require 'projectile)
(require 'ggtags)


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


;;;; Utility
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
  "Same function `when' from subr.el but returning t if COND is nil."
  (declare (indent 1) (debug t))
  (list 'if cond (cons 'progn body) t))

(defmacro verilog-ext-while-t (cond &rest body)
  "Same function `while' but returning t after last condition for use in ands."
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
Return list with found modules or nil if not found."
  (let (modules)
    (save-excursion
      (goto-char (point-min))
      (while (verilog-re-search-forward verilog-ext-top-instantiable-re nil t)
        (push (match-string-no-properties 3) modules)))
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
  (or (when (featurep 'projectile)
        (projectile-project-root))
      (when (featurep 'project)
        (project-root (project-current)))
      (when (featurep 'ggtags)
        ggtags-project-root)
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
        (when (string-equal major-mode "verilog-mode")
          (push buf verilog-buffers)
          (unless (member default-directory verilog-dirs)
            (push default-directory verilog-dirs)))))
    (setq verilog-ext-buffer-list verilog-buffers)
    (setq verilog-ext-dir-list verilog-dirs)))


;;;; Hooks
(defun verilog-ext-open-buffer-hook ()
  "Verilog hook to run when opening a file."
  (verilog-ext-update-buffer-and-dir-list)
  (setq verilog-library-directories verilog-ext-dir-list)
  (setq verilog-ext-flycheck-verilator-include-path verilog-ext-dir-list))

(defun verilog-ext-kill-buffer-hook ()
  "Verilog hook to run when killing a buffer."
  (setq verilog-ext-buffer-list (remove (current-buffer) verilog-ext-buffer-list)))

(add-hook 'verilog-mode-hook #'verilog-ext-open-buffer-hook)
(add-hook 'kill-buffer-hook #'verilog-ext-kill-buffer-hook nil :local)


(provide 'verilog-utils)

;;; verilog-utils.el ends here
