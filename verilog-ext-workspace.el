;;; verilog-ext-workspace.el --- Verilog-ext Workspace  -*- lexical-binding: t -*-

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

;; Workspace
;; Also gather typedefs: For more info, see: https://github.com/gmlarumbe/verilog-ext/wiki/Typedefs

;;; Code:

(require 'make-mode)
(require 'async)
(require 'verilog-ext-tags)
(require 'verilog-ext-template)

(defgroup verilog-ext-workspace nil
  "Verilog-ext workspace."
  :group 'verilog-ext)

(defcustom verilog-ext-workspace-root-dir nil
  "Workspace root directory for file indexing.
Detected automatically if set to nil."
  :type 'directory
  :group 'verilog-ext-workspace)

(defcustom verilog-ext-workspace-dirs nil
  "List of current workspace directories for indexing.
If set to nil default to search for current project files."
  :type '(repeat directory)
  :group 'verilog-ext-workspace)

(defcustom verilog-ext-workspace-extra-files nil
  "List of files besides the ones searched for in `verilog-ext-workspace-dirs'."
  :type '(repeat file)
  :group 'verilog-ext-workspace)

(defcustom verilog-ext-workspace-ignore-dirs nil
  "List of current workspace directories to be ignored."
  :type '(repeat directory)
  :group 'verilog-ext-workspace)

(defcustom verilog-ext-workspace-ignore-files nil
  "List of current workspace files to be ignored."
  :type '(repeat file)
  :group 'verilog-ext-workspace)


(defun verilog-ext-workspace-root ()
  "Return directory of current workspace root."
  (or verilog-ext-workspace-root-dir
      (and (project-current)
           (project-root (project-current)))
      default-directory))

(defun verilog-ext-workspace-files (&optional follow-symlinks)
  "Return list of current workspace files.

Follow symlinks if optional argument FOLLOW-SYMLINKS is non-nil."
  (let* ((files (if verilog-ext-workspace-dirs
                    (verilog-ext-dirs-files verilog-ext-workspace-dirs
                                            follow-symlinks
                                            verilog-ext-workspace-ignore-dirs)
                  (verilog-ext-dir-files (verilog-ext-workspace-root)
                                         follow-symlinks
                                         verilog-ext-workspace-ignore-dirs)))
         (files-all (append files verilog-ext-workspace-extra-files))
         (files-after-ignored (seq-filter (lambda (file)
                                            (not (member file verilog-ext-workspace-ignore-files)))
                                          files-all)))
    files-after-ignored))

;;;; Tags
(defvar verilog-ext-workspace-tags-defs-table (make-hash-table :test #'equal))
(defvar verilog-ext-workspace-tags-refs-table (make-hash-table :test #'equal))
(defvar verilog-ext-workspace-tags-current-file nil)

(defun verilog-ext-workspace-get-tags ()
  "Get tags of current workspace."
  (let* ((files (verilog-ext-workspace-files))
         (num-files (length files))
         (num-files-processed 0)
         (table (make-hash-table :test #'equal))
         progress)
    ;; Definitions
    (dolist (file files)
      (setq verilog-ext-workspace-tags-current-file file)
      (with-temp-buffer
        (setq progress (/ (* num-files-processed 100) num-files))
        (message "(%0d%%) [Tags collection] Processing %s" progress file)
        (insert-file-contents file)
        (verilog-mode)
        (cond (;; Top-block based-file (module/interface/package/program)
               (save-excursion (verilog-re-search-forward verilog-ext-top-re nil :no-error))
               (verilog-ext-tags-table-push-definitions 'top-items table file))
              ;; No top-blocks class-based file
              ((save-excursion (verilog-ext-find-class-fwd))
               (verilog-ext-tags-table-push-definitions 'classes table file))
              ;; Default,
              (t (dolist (defs '(declarations tf structs))
                   (verilog-ext-tags-table-push-definitions defs table file))))
        (setq num-files-processed (1+ num-files-processed))))
    (setq verilog-ext-workspace-tags-defs-table table)
    ;; References
    (setq table (make-hash-table :test #'equal)) ; Clean table
    (setq num-files-processed 0)
    (dolist (file files)
      (setq verilog-ext-workspace-tags-current-file file)
      (with-temp-buffer
        (setq progress (/ (* num-files-processed 100) num-files))
        (message "(%0d%%) [References collection] Processing %s" progress file)
        (insert-file-contents file)
        (verilog-mode)
        (verilog-ext-tags-table-push-references table verilog-ext-workspace-tags-defs-table file)
        (setq verilog-ext-workspace-tags-refs-table table))
      (setq num-files-processed (1+ num-files-processed)))
    ;; Return value for async processing
    (list verilog-ext-workspace-tags-defs-table verilog-ext-workspace-tags-refs-table)))

(defun verilog-ext-workspace-get-tags-async ()
  "Create tags table asynchronously."
  (let ((parent-load-path load-path))
    (async-start
     (lambda ()
       (setq load-path parent-load-path)
       (require 'verilog-ext)
       (verilog-ext-workspace-get-tags))
     (lambda (result)
       (message "Finished collection tags!")
       (setq verilog-ext-workspace-tags-defs-table (car result))
       (setq verilog-ext-workspace-tags-refs-table (cadr result))))))


;;; Typedefs
(defvar verilog-ext-workspace-align-typedef-words nil)
(defvar verilog-ext-workspace-align-typedef-words-re nil)

(defun verilog-ext-workspace-typedef--var-find (regex &optional limit)
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

(defun verilog-ext-workspace-typedef--var-buffer-update (regex)
  "Scan REGEX on current buffer and update list of user typedefs.
See `verilog-ext-workspace-align-typedef-words'.
Used for fontification and alignment."
  (let (type)
    (save-excursion
      (goto-char (point-min))
      (while (setq type (verilog-ext-workspace-typedef--var-find regex))
        (unless (member type verilog-ext-workspace-align-typedef-words)
          (push type verilog-ext-workspace-align-typedef-words))))))

(defun verilog-ext-workspace-typedef--tf-args-buffer-update ()
  "Scan functions/tasks arguments on current buffer to update user typedefs list.
See `verilog-ext-workspace-align-typedef-words'.
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
              (unless (member arg-proc verilog-ext-workspace-align-typedef-words)
                (push arg-proc verilog-ext-workspace-align-typedef-words)))))))))

(defun verilog-ext-workspace-typedef--class-buffer-update ()
  "Scan class declarations on current buffer to update user typedef list."
  (let (word)
    (save-excursion
      (goto-char (point-min))
      (while (setq word (alist-get 'name (verilog-ext-find-class-fwd)))
        (unless (member word verilog-ext-workspace-align-typedef-words)
          (push word verilog-ext-workspace-align-typedef-words))))))

(defun verilog-ext-workspace-typedef--typedef-buffer-update (regex)
  "Scan REGEX typedef declarations on current buffer to update user typedef list."
  (let (word)
    (save-excursion
      (goto-char (point-min))
      (while (verilog-re-search-forward regex nil t)
        (setq word (match-string-no-properties 2))
        (unless (member word verilog-ext-workspace-align-typedef-words)
          (push word verilog-ext-workspace-align-typedef-words))))))

(defun verilog-ext-workspace-typedef--var-decl-update ()
  "Scan and update Verilog buffers and `verilog-ext-workspace-align-typedef-words'."
  (verilog-ext-workspace-typedef--var-buffer-update verilog-ext-typedef-var-decl-single-re)
  (verilog-ext-workspace-typedef--var-buffer-update verilog-ext-typedef-var-decl-multiple-re)
  (verilog-ext-workspace-typedef--tf-args-buffer-update)
  (verilog-ext-workspace-typedef--class-buffer-update)
  (verilog-ext-workspace-typedef--typedef-buffer-update verilog-ext-typedef-class-re)
  (verilog-ext-workspace-typedef--typedef-buffer-update verilog-ext-typedef-generic-re))

(defun verilog-ext-workspace-typedef-batch-update (files)
  "Scan all (System)Verilog FILES and udpate typedef list.

It will return the updated value of `verilog-ext-workspace-align-typedef-words',
which can be used later along with `verilog-regexp-words' to update the variable
`verilog-align-typedef-regexp'.  This enables the fontification and alignment of
user typedefs."
  (let ((num-files (length files))
        (num-files-processed 0)
        progress)
    (setq verilog-ext-workspace-align-typedef-words nil) ; Reset value
    (dolist (file files)
      (setq progress (/ (* num-files-processed 100) num-files))
      (message "(%0d%%) [Typedef collection] Processing %s" progress file)
      (with-temp-buffer
        (insert-file-contents file)
        (verilog-mode)
        (verilog-ext-workspace-typedef--var-decl-update))
      (setq num-files-processed (1+ num-files-processed)))
    ;; Postprocess obtained results (remove keywords and generic types that were uppercase)
    (mapc (lambda (elm)
            (when (member elm verilog-keywords)
              (delete elm verilog-ext-workspace-align-typedef-words)))
          verilog-ext-workspace-align-typedef-words)
    (let ((case-fold-search nil))
      (setq verilog-ext-workspace-align-typedef-words (seq-remove (lambda (s)
                                                          (not (string-match-p "[[:lower:]]" s)))
                                                        verilog-ext-workspace-align-typedef-words)))
    ;; Store results
    (when verilog-ext-workspace-align-typedef-words
      (setq verilog-ext-workspace-align-typedef-words-re (verilog-regexp-words verilog-ext-workspace-align-typedef-words))
      (setq verilog-align-typedef-regexp verilog-ext-workspace-align-typedef-words-re))))

(defun verilog-ext-workspace-typedef-update ()
  "Update typedef list of current workspace."
  (interactive)
  (verilog-ext-workspace-typedef-batch-update (verilog-ext-workspace-files)))


;;;; Index
(defun verilog-ext-workspace-index-update ()
  "Update workspace index.
Update list of typedefs/classes and populate tags tables."
  (interactive)
  (verilog-ext-workspace-typedef-update)
  (verilog-ext-workspace-get-tags))


;;;; Completion-at-point
(defun verilog-ext-workspace-capf-annotation-function (cand)
  "Completion annotation function for candidate CAND."
  (let ((type (plist-get (car (plist-get (gethash cand verilog-ext-workspace-tags-defs-table) :locs)) :type)))
    (pcase type
      ("function" "<f>")
      ("task"     "<t>")
      (_ type))))

(defun verilog-ext-workspace-capf ()
  "Verilog-ext `completion-at-point' function.
Complete with identifiers of current workspace."
  (interactive)
  (let* ((table verilog-ext-workspace-tags-defs-table)
         start end completions)
    (cond (;; Dot completion for object methods/attributes and hierarchical references
           (eq (preceding-char) ?.)
           (setq start (point))
           (setq end (point))
           (let (table-entry-value block-type)
             (save-excursion
               (backward-char)
               (while (eq (preceding-char) ?\])
                 (verilog-ext-backward-sexp))
               (setq table-entry-value (gethash (thing-at-point 'symbol :no-props) table))
               (when table-entry-value
                 (setq block-type (plist-get (car (plist-get table-entry-value :locs)) :type)) ; TODO: Only using type of first occurence
                 (setq completions (plist-get (gethash block-type table) :items))))))
          ((save-excursion
             (backward-word)
             (setq start (point))
             (eq (preceding-char) ?.))
           (setq end (point))
           (let (table-entry-value block-type)
             (save-excursion
               (goto-char start)
               (backward-char)
               (while (eq (preceding-char) ?\])
                 (verilog-ext-backward-sexp))
               (setq table-entry-value (gethash (thing-at-point 'symbol :no-props) table))
               (when table-entry-value
                 (setq block-type (plist-get (car (plist-get table-entry-value :locs)) :type)) ; TODO: Only using type of first occurence?
                 (setq completions (plist-get (gethash block-type table) :items))))))
          ;; Class static methods/members and package items
          ((looking-back "::" (- (point) 2))
           (setq start (point))
           (setq end (point))
           (save-excursion
             (backward-char 2)
             (while (eq (preceding-char) ?\])
               (verilog-ext-backward-sexp))
             (setq completions (plist-get (gethash (thing-at-point 'symbol :no-props) table) :items))))
          ;; Class static methods/members and package items if not at the beginning
          ((save-excursion
             (backward-word)
             (setq start (point))
             (looking-back "::" (- (point) 2)))
           (setq end (point))
           (save-excursion
             (goto-char start)
             (backward-char 2)
             (while (eq (preceding-char) ?\])
               (verilog-ext-backward-sexp))
             (setq completions (plist-get (gethash (thing-at-point 'symbol :no-props) table) :items))))
          ;; Fallback, all project completions
          (t
           (let ((bds (bounds-of-thing-at-point 'symbol)))
             (setq start (car bds))
             (setq end (cdr bds))
             (setq completions table))))
    ;; Completion
    (list start end completions
          :annotation-function #'verilog-ext-workspace-capf-annotation-function
          :company-docsig #'identity)))

(defun verilog-ext-workspace-capf-set (&optional disable)
  "Enable or DISABLE builtin capf function."
  (if disable
      (remove-hook 'completion-at-point-functions #'verilog-ext-workspace-capf :local)
    (add-hook 'completion-at-point-functions #'verilog-ext-workspace-capf nil :local)))

;;;; Makefile
(defun verilog-ext-workspace-makefile-create ()
  "Create Iverilog/verilator Yasnippet based Makefile.
Create it only if in a project and the Makefile does not already exist."
  (interactive)
  (let ((project-root (verilog-ext-workspace-root))
        file)
    (if project-root
        (if (file-exists-p (setq file (verilog-ext-path-join project-root "Makefile")))
            (error "File %s already exists!" file)
          (find-file file)
          (verilog-ext-template-insert-yasnippet "verilog"))
      (error "Not in a project!"))))

(defun verilog-ext-workspace-makefile-compile ()
  "Prompt to available Makefile targets and compile.
Compiles them with various verilog regexps."
  (interactive)
  (let ((makefile (verilog-ext-path-join (verilog-ext-workspace-root) "Makefile"))
        (makefile-need-target-pickup t) ; Force refresh of makefile targets
        target cmd)
    (unless (file-exists-p makefile)
      (error "%s does not exist!" makefile))
    (with-temp-buffer
      (insert-file-contents makefile)
      (makefile-pickup-targets)
      (setq target (completing-read "Target: " makefile-target-table)))
    (setq cmd (concat "cd " (verilog-ext-workspace-root) " && make " target))
    (compile cmd)))


;;;; Jump-to-parent module
(defun verilog-ext-workspace-jump-to-parent-module ()
  "Find current module/interface instantiations via `ag'/`rg' in current workspace."
  (interactive)
  (verilog-ext-jump-to-parent-module (verilog-ext-workspace-root)))


(provide 'verilog-ext-workspace)

;;; verilog-ext-workspace.el ends here
