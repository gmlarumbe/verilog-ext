;;; verilog-ext-workspace.el --- Verilog-ext Workspace  -*- lexical-binding: t -*-

;; Copyright (C) 2022-2023 Gonzalo Larumbe

;; Author: Gonzalo Larumbe <gonzalomlarumbe@gmail.com>
;; URL: https://github.com/gmlarumbe/verilog-ext
;; Version: 0.2.0
;; Package-Requires: ((emacs "28.1") (verilog-mode "2023.6.6.141322628"))

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

;; Workspace utils

;;; Code:

(require 'make-mode)
(require 'async)
(require 'verilog-ext-tags)
(require 'verilog-ext-capf)
(require 'verilog-ext-typedef)
(require 'verilog-ext-hierarchy)
(require 'verilog-ext-template)
(require 'verilog-ext-compile)

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

(defcustom verilog-ext-workspace-compile-cmd nil
  "The command used to perform compilation on the workspace."
  :group 'verilog-ext-workspace
  :type 'string)


(defvar verilog-ext-workspace-tags-defs-table (make-hash-table :test #'equal))
(defvar verilog-ext-workspace-tags-refs-table (make-hash-table :test #'equal))
(defvar verilog-ext-workspace-tags-inst-table (make-hash-table :test #'equal))

(defconst verilog-ext-workspace-cache-dir (file-name-concat user-emacs-directory "verilog-ext")
  "The directory where Verilog-ext cache files will be placed at.")

(defvar verilog-ext-workspace-cache-typedefs nil)
(defvar verilog-ext-workspace-cache-tags-defs nil)
(defvar verilog-ext-workspace-cache-tags-refs nil)
(defvar verilog-ext-workspace-cache-tags-inst nil)
(defvar verilog-ext-workspace-cache-hierarchy nil)


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


;;;; Cache
(defun verilog-ext-workspace-serialize (data filename)
  "Serialize DATA to FILENAME.

The saved data can be restored with `verilog-ext-workspace-unserialize'."
  (let ((dir (file-name-directory filename)))
    (unless (file-exists-p dir)
      (make-directory dir :parents))
    (if (file-writable-p filename)
        (with-temp-file filename
          (insert (let (print-length) (prin1-to-string data))))
      (message "Verilog-ext cache '%s' not writeable" filename))))

(defun verilog-ext-workspace-unserialize (filename)
  "Read data serialized by `verilog-ext-workspace-serialize' from FILENAME."
  (with-demoted-errors
      "Error during file deserialization: %S"
    (when (file-exists-p filename)
      (with-temp-buffer
        (insert-file-contents filename)
        ;; this will blow up if the contents of the file aren't
        ;; lisp data structures
        (read (buffer-string))))))

(defun verilog-ext-workspace-serialize-cache (&optional type)
  "Serializes the memory cache to the hard drive.
If optional TYPE arg is passed, only serialize that TYPE."
  (pcase type
    ('typedefs  (verilog-ext-workspace-serialize verilog-ext-workspace-cache-typedefs  (file-name-concat verilog-ext-workspace-cache-dir "typedefs")))
    ('tags-defs (verilog-ext-workspace-serialize verilog-ext-workspace-cache-tags-defs (file-name-concat verilog-ext-workspace-cache-dir "tags-defs")))
    ('tags-refs (verilog-ext-workspace-serialize verilog-ext-workspace-cache-tags-refs (file-name-concat verilog-ext-workspace-cache-dir "tags-refs")))
    ('tags-inst (verilog-ext-workspace-serialize verilog-ext-workspace-cache-tags-inst (file-name-concat verilog-ext-workspace-cache-dir "tags-inst")))
    ('hierarchy (verilog-ext-workspace-serialize verilog-ext-workspace-cache-hierarchy (file-name-concat verilog-ext-workspace-cache-dir "hierarchy")))
    (_ (verilog-ext-workspace-serialize verilog-ext-workspace-cache-typedefs  (file-name-concat verilog-ext-workspace-cache-dir "typedefs"))
       (verilog-ext-workspace-serialize verilog-ext-workspace-cache-tags-defs (file-name-concat verilog-ext-workspace-cache-dir "tags-defs"))
       (verilog-ext-workspace-serialize verilog-ext-workspace-cache-tags-refs (file-name-concat verilog-ext-workspace-cache-dir "tags-refs"))
       (verilog-ext-workspace-serialize verilog-ext-workspace-cache-tags-inst (file-name-concat verilog-ext-workspace-cache-dir "tags-inst"))
       (verilog-ext-workspace-serialize verilog-ext-workspace-cache-hierarchy (file-name-concat verilog-ext-workspace-cache-dir "hierarchy")))))

(defun verilog-ext-workspace-unserialize-cache (&optional type)
  "Unserializes the hard drive data to the memory cache.
If optional TYPE arg is passed, only deserialize that TYPE."
  (pcase type
    ('typedefs  (setq verilog-ext-workspace-cache-typedefs  (verilog-ext-workspace-unserialize (file-name-concat verilog-ext-workspace-cache-dir "typedefs"))))
    ('tags-defs (setq verilog-ext-workspace-cache-tags-defs (verilog-ext-workspace-unserialize (file-name-concat verilog-ext-workspace-cache-dir "tags-defs"))))
    ('tags-refs (setq verilog-ext-workspace-cache-tags-refs (verilog-ext-workspace-unserialize (file-name-concat verilog-ext-workspace-cache-dir "tags-refs"))))
    ('tags-inst (setq verilog-ext-workspace-cache-tags-inst (verilog-ext-workspace-unserialize (file-name-concat verilog-ext-workspace-cache-dir "tags-inst"))))
    ('hierarchy (setq verilog-ext-workspace-cache-hierarchy (verilog-ext-workspace-unserialize (file-name-concat verilog-ext-workspace-cache-dir "hierarchy"))))
    (_ (setq verilog-ext-workspace-cache-typedefs  (verilog-ext-workspace-unserialize (file-name-concat verilog-ext-workspace-cache-dir "typedefs")))
       (setq verilog-ext-workspace-cache-tags-defs (verilog-ext-workspace-unserialize (file-name-concat verilog-ext-workspace-cache-dir "tags-defs")))
       (setq verilog-ext-workspace-cache-tags-refs (verilog-ext-workspace-unserialize (file-name-concat verilog-ext-workspace-cache-dir "tags-refs")))
       (setq verilog-ext-workspace-cache-tags-inst (verilog-ext-workspace-unserialize (file-name-concat verilog-ext-workspace-cache-dir "tags-inst")))
       (setq verilog-ext-workspace-cache-hierarchy (verilog-ext-workspace-unserialize (file-name-concat verilog-ext-workspace-cache-dir "hierarchy"))))))

(defun verilog-ext-workspace-clear-cache (&optional type)
  "Clears the hard drive and the memory cache.
If optional TYPE arg is passed, only clear that TYPE."
  (interactive)
  (pcase type
    ('typedefs  (setq verilog-ext-workspace-cache-typedefs  nil)
                (setq verilog-ext-typedef-align-words-re nil)
                (setq verilog-align-typedef-regexp nil))
    ('tags-defs (setq verilog-ext-workspace-cache-tags-defs nil)
                (setq verilog-ext-workspace-tags-defs-table nil))
    ('tags-refs (setq verilog-ext-workspace-cache-tags-refs nil)
                (setq verilog-ext-workspace-tags-refs-table nil))
    ('tags-inst (setq verilog-ext-workspace-cache-tags-inst nil)
                (setq verilog-ext-workspace-tags-inst-table nil))
    ('hierarchy (setq verilog-ext-workspace-cache-hierarchy nil)
                (setq verilog-ext-hierarchy-current-flat-hierarchy nil))
    (_ (setq verilog-ext-workspace-cache-typedefs  nil)
       (setq verilog-ext-workspace-cache-tags-defs nil)
       (setq verilog-ext-workspace-cache-tags-refs nil)
       (setq verilog-ext-workspace-cache-tags-inst nil)
       (setq verilog-ext-workspace-cache-hierarchy nil)
       (setq verilog-ext-typedef-align-words-re nil)
       (setq verilog-align-typedef-regexp nil)
       (setq verilog-ext-workspace-tags-defs-table nil)
       (setq verilog-ext-workspace-tags-refs-table nil)
       (setq verilog-ext-workspace-tags-inst-table nil)
       (setq verilog-ext-hierarchy-current-flat-hierarchy nil)))
  (verilog-ext-workspace-serialize-cache type)
  (message "Cleared cache!"))


;;;; Hierarchy
(defun verilog-ext-workspace-hierarchy-parse (&optional verbose)
  "Return flat hierarchy of modules and instances of current workspace files.

Populates `verilog-ext-hierarchy-current-flat-hierarchy' for subsequent
hierarchy extraction and display.

With current-prefix or VERBOSE, dump output log."
  (interactive "P")
  (let* ((files (if verilog-ext-hierarchy-builtin-dirs
                    (verilog-ext-dirs-files verilog-ext-hierarchy-builtin-dirs :follow-symlinks)
                  (verilog-ext-workspace-files :follow-symlinks)))
         (num-files (length files))
         (num-files-processed 0)
         (log-file (file-name-concat verilog-ext-workspace-cache-dir "hierarchy.log"))
         msg progress flat-hierarchy data)
    (when verbose
      (delete-file log-file))
    (dolist (file files)
      (setq progress (/ (* num-files-processed 100) num-files))
      (setq msg (format "(%0d%%) [Hierarchy parsing] Processing %s" progress file))
      (when verbose
        (append-to-file (concat msg "\n") nil log-file))
      (message "%s" msg)
      (setq data (cond ((eq verilog-ext-hierarchy-backend 'tree-sitter)
                        (verilog-ext-hierarchy-tree-sitter-parse-file file))
                       ((eq verilog-ext-hierarchy-backend 'builtin)
                        (verilog-ext-hierarchy-builtin-parse-file file))
                       (t
                        (error "Wrong backend selected!"))))
      (when data
        (dolist (entry data)
          (push entry flat-hierarchy)))
      (setq num-files-processed (1+ num-files-processed)))
    ;; Update cache
    (setq verilog-ext-workspace-cache-hierarchy verilog-ext-hierarchy-current-flat-hierarchy)
    (verilog-ext-workspace-serialize-cache 'hierarchy)
    ;; Return value for async related function
    (setq verilog-ext-hierarchy-current-flat-hierarchy flat-hierarchy)))

(defun verilog-ext-workspace-hierarchy-parse-async (&optional verbose)
  "Return flat hierarchy of modules and instances of workspace asynchronously.

Populates `verilog-ext-hierarchy-current-flat-hierarchy' for subsequent
hierarchy extraction and display.

With current-prefix or VERBOSE, dump output log."
  (interactive "P")
  (message "Starting hierarchy parsing for %s" (verilog-ext-workspace-root))
  (async-start
   `(lambda ()
      ,(async-inject-variables verilog-ext-async-inject-variables-re)
      (require 'verilog-ext)
      (when (eq verilog-ext-hierarchy-backend 'tree-sitter)
        (require 'verilog-ts-mode))
      (verilog-ext-workspace-hierarchy-parse ,verbose))
   (lambda (result)
     (message "Finished analyzing hierarchy!")
     (setq verilog-ext-hierarchy-current-flat-hierarchy result)
     (setq verilog-ext-workspace-cache-hierarchy verilog-ext-hierarchy-current-flat-hierarchy)
     (verilog-ext-workspace-serialize-cache 'hierarchy))))


;;;; Tags
(defvar verilog-ext-workspace-tags-current-file nil)

(defun verilog-ext-workspace-get-tags (&optional verbose)
  "Get tags of current workspace.
With current-prefix or VERBOSE, dump output log."
  (interactive "P")
  (let* ((files (verilog-ext-workspace-files :follow-symlinks))
         (num-files (length files))
         (num-files-processed 0)
         (table (make-hash-table :test #'equal))
         (inst-table (make-hash-table :test #'equal))
         (log-file (file-name-concat verilog-ext-workspace-cache-dir "tags.log"))
         msg progress)
    (when verbose
      (delete-file log-file))
    ;; Definitions
    (dolist (file files)
      (setq verilog-ext-workspace-tags-current-file file)
      (with-temp-buffer
        (setq progress (/ (* num-files-processed 100) num-files))
        (setq msg (format "(%0d%%) [Tags collection] Processing %s" progress file))
        (when verbose
          (append-to-file (concat msg "\n") nil log-file))
        (message "%s" msg)
        (insert-file-contents file)
        (cond (;; Tree-sitter
               (eq verilog-ext-tags-backend 'tree-sitter)
               (verilog-ts-mode)
               (verilog-ext-tags-table-push-defs-ts :table table :inst-table inst-table :file file))
              (;; Builtin
               (eq verilog-ext-tags-backend 'builtin)
               (verilog-mode)
               (cond (;; Top-block based-file (module/interface/package/program)
                      (save-excursion (verilog-re-search-forward verilog-ext-top-re nil :no-error))
                      (verilog-ext-tags-table-push-defs :tag-type 'top-items :table table :file file :inst-table inst-table))
                     ;; No top-blocks class-based file
                     ((save-excursion (verilog-ext-find-class-fwd))
                      (verilog-ext-tags-table-push-defs :tag-type 'classes :table table :file file))
                     ;; Default,
                     (t (dolist (defs '(declarations tf structs))
                          (verilog-ext-tags-table-push-defs :tag-type defs :table table :file file)))))
              (t ; Fallback error
               (error "Wrong backend for `verilog-ext-tags-backend'")))
        (setq num-files-processed (1+ num-files-processed))))
    (setq verilog-ext-workspace-tags-defs-table table)
    (setq verilog-ext-workspace-tags-inst-table inst-table)
    (setq verilog-ext-workspace-cache-tags-defs table) ; Update cache
    (setq verilog-ext-workspace-cache-tags-inst inst-table)
    (verilog-ext-workspace-serialize-cache 'tags-defs)
    (verilog-ext-workspace-serialize-cache 'tags-inst)
    ;; References
    (setq table (make-hash-table :test #'equal)) ; Clean table
    (setq num-files-processed 0)
    (dolist (file files)
      (setq verilog-ext-workspace-tags-current-file file)
      (with-temp-buffer
        (setq progress (/ (* num-files-processed 100) num-files))
        (setq msg (format "(%0d%%) [References collection] Processing %s" progress file))
        (when verbose
          (append-to-file (concat msg "\n") nil log-file))
        (message "%s" msg)
        (insert-file-contents file)
        (cond (;; Tree-sitter
               (eq verilog-ext-tags-backend 'tree-sitter)
               (verilog-ts-mode)
               (verilog-ext-tags-table-push-refs-ts :table table :defs-table verilog-ext-workspace-tags-defs-table :file file))
              (;; Builtin
               (eq verilog-ext-tags-backend 'builtin)
               (verilog-mode)
               (verilog-ext-tags-table-push-refs :table table :defs-table verilog-ext-workspace-tags-defs-table :file file))
              (t
               (error "Wrong backend for `verilog-ext-tags-backend'")))
        (setq verilog-ext-workspace-tags-refs-table table))
      (setq num-files-processed (1+ num-files-processed)))
    (setq verilog-ext-workspace-cache-tags-refs table) ; Update cache
    (verilog-ext-workspace-serialize-cache 'tags-refs)
    ;; Return value for async processing
    (list verilog-ext-workspace-tags-defs-table verilog-ext-workspace-tags-inst-table verilog-ext-workspace-tags-refs-table)))

(defun verilog-ext-workspace-get-tags-async (&optional verbose)
  "Create tags table asynchronously.
With current-prefix or VERBOSE, dump output log."
  (interactive "P")
  (message "Starting tag collection for %s" (verilog-ext-workspace-root))
  (async-start
   `(lambda ()
      ,(async-inject-variables verilog-ext-async-inject-variables-re)
      (require 'verilog-ext)
      (when (eq verilog-ext-tags-backend 'tree-sitter)
        (require 'verilog-ts-mode))
      (verilog-ext-workspace-get-tags ,verbose))
   (lambda (result)
     (message "Finished collection tags!")
     ;; Tags definitions
     (setq verilog-ext-workspace-tags-defs-table (car result))
     (setq verilog-ext-workspace-cache-tags-defs (car result))
     (setq verilog-ext-workspace-tags-inst-table (cadr result))
     (setq verilog-ext-workspace-cache-tags-inst (cadr result))
     (verilog-ext-workspace-serialize-cache 'tags-defs)
     (verilog-ext-workspace-serialize-cache 'tags-inst)
     ;; Tags references
     (setq verilog-ext-workspace-tags-refs-table (cddr result))
     (setq verilog-ext-workspace-cache-tags-refs (cddr result))
     (verilog-ext-workspace-serialize-cache 'tags-refs))))

;;;; Typedefs
(defun verilog-ext-workspace-typedef-batch-update (files &optional verbose)
  "Scan all (System)Verilog FILES and udpate typedef list.

It will return the updated value of `verilog-ext-typedef-align-words',
which can be used later along with `verilog-regexp-words' to update the variable
`verilog-align-typedef-regexp'.  This enables the fontification and alignment of
user typedefs.

If optional arg VERBOSE is enabled, dump output to a logfile for potential debug
in corresponding async function."
  (let ((num-files (length files))
        (num-files-processed 0)
        (log-file (file-name-concat verilog-ext-workspace-cache-dir "typedefs.log"))
        msg progress)
    (setq verilog-ext-typedef-align-words nil) ; Reset value
    (when verbose
      (delete-file log-file))
    (dolist (file files)
      (setq progress (/ (* num-files-processed 100) num-files))
      (setq msg (format "(%0d%%) [Typedef collection] Processing %s" progress file))
      (when verbose
        (append-to-file (concat msg "\n") nil log-file))
      (message "%s" msg)
      (with-temp-buffer
        (insert-file-contents file)
        (verilog-mode)
        (verilog-ext-typedef--var-decl-update))
      (setq num-files-processed (1+ num-files-processed)))
    ;; Postprocess obtained results (remove keywords and generic types that were uppercase)
    (mapc (lambda (elm)
            (when (member elm verilog-keywords)
              (delete elm verilog-ext-typedef-align-words)))
          verilog-ext-typedef-align-words)
    (let ((case-fold-search nil))
      (setq verilog-ext-typedef-align-words (seq-remove (lambda (s)
                                                          (not (string-match-p "[[:lower:]]" s)))
                                                        verilog-ext-typedef-align-words)))
    ;; Store results
    (when verilog-ext-typedef-align-words
      (setq verilog-ext-typedef-align-words-re (verilog-regexp-words verilog-ext-typedef-align-words))
      (setq verilog-align-typedef-regexp verilog-ext-typedef-align-words-re))
    ;; Update cache
    (setq verilog-ext-workspace-cache-typedefs verilog-ext-typedef-align-words-re)
    (verilog-ext-workspace-serialize-cache 'typedefs)
    ;; Return value for async processing
    verilog-ext-typedef-align-words-re))

(defun verilog-ext-workspace-typedef-update (&optional verbose)
  "Update typedef list of current workspace.
With current-prefix or VERBOSE, dump output log."
  (interactive "P")
  (verilog-ext-workspace-typedef-batch-update (verilog-ext-workspace-files :follow-symlinks) verbose))

(defun verilog-ext-workspace-typedef-update-async (&optional verbose)
  "Update typedef list of current workspace asynchronously.
With current-prefix or VERBOSE, dump output log."
  (interactive "P")
  (message "Starting typedef collection for %s" (verilog-ext-workspace-root))
  (async-start
   `(lambda ()
      ,(async-inject-variables verilog-ext-async-inject-variables-re)
      (require 'verilog-ext)
      (verilog-ext-workspace-typedef-batch-update (verilog-ext-workspace-files :follow-symlinks) ,verbose))
   (lambda (result)
     (message "Finished collection of typedefs!")
     (setq verilog-ext-typedef-align-words-re result)
     (setq verilog-align-typedef-regexp verilog-ext-typedef-align-words-re)
     (setq verilog-ext-workspace-cache-typedefs verilog-ext-typedef-align-words-re)
     (verilog-ext-workspace-serialize-cache 'typedefs))))


;;;; Completion-at-point
(defun verilog-ext-workspace-capf-annotation-function (cand)
  "Workspace completion annotation function for candidate CAND."
  (verilog-ext-capf-annotation-function cand
                                        verilog-ext-workspace-tags-defs-table
                                        verilog-ext-workspace-tags-inst-table))

(defun verilog-ext-workspace-capf ()
  "Verilog-ext `completion-at-point' function.
Complete with identifiers of current workspace."
  (interactive)
  (verilog-ext-capf :defs-table verilog-ext-workspace-tags-defs-table
                    :inst-table verilog-ext-workspace-tags-inst-table
                    :refs-table verilog-ext-workspace-tags-refs-table
                    :annotation-fn #'verilog-ext-workspace-capf-annotation-function))

(defun verilog-ext-workspace-capf-set (&optional disable)
  "Enable or DISABLE builtin capf function.
Replace already existing `verilog-mode' `verilog-completion-at-point'."
  (if disable
      (progn
        (remove-hook 'completion-at-point-functions #'verilog-ext-workspace-capf :local)
        (add-hook 'completion-at-point-functions #'verilog-completion-at-point :local))
    ;; Else
    (add-hook 'completion-at-point-functions #'verilog-ext-workspace-capf nil :local)
    (remove-hook 'completion-at-point-functions #'verilog-completion-at-point :local)))


;;;; Makefile
(defun verilog-ext-workspace-makefile-create ()
  "Create Iverilog/verilator Yasnippet based Makefile.
Create it only if in a project and the Makefile does not already exist."
  (interactive)
  (let ((project-root (verilog-ext-workspace-root))
        file)
    (if project-root
        (if (file-exists-p (setq file (file-name-concat project-root "Makefile")))
            (error "File %s already exists!" file)
          (find-file file)
          (verilog-ext-template-insert-yasnippet "verilog"))
      (error "Not in a project!"))))

(defun verilog-ext-workspace-makefile-compile ()
  "Prompt to available Makefile targets and compile.
Compiles them with various verilog regexps."
  (interactive)
  (let ((makefile (file-name-concat (verilog-ext-workspace-root) "Makefile"))
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


;;;; Compilation
;;;###autoload
(defun verilog-ext-workspace-compile ()
  "Compile using command of `verilog-ext-workspace-compile-cmd'.
Depending on the command, different syntax highlight will be applied.
The function will detect any of the supported compilation error parsers
and will set the appropriate mode."
  (interactive)
  (unless verilog-ext-workspace-compile-cmd
    (error "You first need to set `verilog-ext-workspace-compile-cmd'"))
  (let* ((cmd-list (split-string verilog-ext-workspace-compile-cmd))
         (cmd-args (cdr cmd-list))
         (cmd-bin (car cmd-list))
         (fn (pcase cmd-bin
               ("verilator" #'verilog-ext-compile-verilator)
               ("iverilog" #'verilog-ext-compile-iverilog)
               ("slang" #'verilog-ext-compile-slang)
               ("svlint" #'verilog-ext-compile-svlint)
               ("surelog" #'verilog-ext-compile-surelog)
               ("verible-verilog-lint" #'verilog-ext-compile-verible)
               (_ #'compile)))
         (cmd-processed (cond (;; For svlint, make sure the -1 arg is present
                               (string= cmd-bin "svlint")
                               (if (member "-1" cmd-args)
                                   verilog-ext-workspace-compile-cmd
                                 (mapconcat #'identity `(,cmd-bin "-1" ,@cmd-args) " ")))
                              ;; For slang make sure that there is no colored output
                              ((string= cmd-bin "slang")
                               (if (member "--color-diagnostics=false" cmd-args)
                                   verilog-ext-workspace-compile-cmd
                                 (mapconcat #'identity `(,cmd-bin "--color-diagnostics=false" ,@cmd-args) " ")))
                              ;; For the rest use the provided command
                              (t
                               verilog-ext-workspace-compile-cmd)))
         (cmd (concat "cd " (verilog-ext-workspace-root) " && " cmd-processed)))
    (funcall fn cmd)))

;;;; Jump-to-parent module
(defun verilog-ext-workspace-jump-to-parent-module ()
  "Find current module/interface instantiations via `ag'/`rg' in current workspace."
  (interactive)
  (verilog-ext-jump-to-parent-module (verilog-ext-workspace-root)))


;;;; Setup
(defun verilog-ext-workspace-hierarchy-setup ()
  "Setup workspace builtin hierarchy analysis."
  (verilog-ext-workspace-unserialize-cache 'hierarchy)
  (setq verilog-ext-hierarchy-current-flat-hierarchy verilog-ext-workspace-cache-hierarchy))

(defun verilog-ext-workspace-tags-table-setup ()
  "Setup workspace tags table feature for `xref' and `capf'."
  (verilog-ext-workspace-unserialize-cache 'tags-defs)
  (verilog-ext-workspace-unserialize-cache 'tags-refs)
  (verilog-ext-workspace-unserialize-cache 'tags-inst)
  (setq verilog-ext-workspace-tags-defs-table verilog-ext-workspace-cache-tags-defs)
  (setq verilog-ext-workspace-tags-inst-table verilog-ext-workspace-cache-tags-inst)
  (setq verilog-ext-workspace-tags-refs-table verilog-ext-workspace-cache-tags-refs))

(defun verilog-ext-workspace-typedefs-setup ()
  "Setup workspace typedef feature.
INFO: Enabling this feature will override the value of
`verilog-align-typedef-regexp'."
  (verilog-ext-workspace-unserialize-cache 'typedefs)
  (setq verilog-ext-typedef-align-words-re verilog-ext-workspace-cache-typedefs)
  (setq verilog-align-typedef-regexp verilog-ext-workspace-cache-typedefs))



(provide 'verilog-ext-workspace)

;;; verilog-ext-workspace.el ends here
