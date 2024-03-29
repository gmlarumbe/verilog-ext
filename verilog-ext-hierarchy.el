;;; verilog-ext-hierarchy.el --- Verilog-ext Hierarchy  -*- lexical-binding: t -*-

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

;; Utils for hierarchy extraction and navigation

;;; Code:

(require 'outshine)
(require 'hierarchy)
(require 'tree-widget)
(require 'async)
(require 'verilog-ext-nav)
(require 'verilog-ts-mode)

(defgroup verilog-ext-hierarchy nil
  "Verilog-ext hierarchy."
  :group 'verilog-ext)

(defcustom verilog-ext-hierarchy-backend (if (and (treesit-available-p) (treesit-language-available-p 'verilog))
                                             'tree-sitter
                                           'builtin)
  "Verilog-ext hierarchy extraction backend."
  :type '(choice (const :tag "Verilog-Perl vhier" vhier)
                 (const :tag "Tree-sitter"        tree-sitter)
                 (const :tag "Built-in"           builtin))
  :group 'verilog-ext-hierarchy)

(defcustom verilog-ext-hierarchy-frontend 'hierarchy
  "Verilog-ext hierarchy display and navigation frontend."
  :type '(choice (const :tag "Outshine"  outshine)
                 (const :tag "Hierarchy" hierarchy))
  :group 'verilog-ext-hierarchy)

(defcustom verilog-ext-hierarchy-twidget-init-expand nil
  "Set to non-nil to initially expand the hierarchy using hierarchy.el frontend."
  :group 'verilog-ext-hierarchy
  :type 'boolean)

(defcustom verilog-ext-hierarchy-vhier-use-open-buffers nil
  "Set to non-nil to use list of open Verilog files/dirs with vhier backend."
  :type 'boolean
  :group 'verilog-ext-hierarchy)


;;;; Utils
(defvar verilog-ext-hierarchy-module-alist nil
  "Per project module alist.")

(defconst verilog-ext-hierarchy-async-inject-variables-re
  (eval-when-compile
    (regexp-opt '("load-path"
                  "buffer-file-name"
                  "default-directory"
                  "verilog-ext-feature-list"
                  "verilog-ext-project-alist"
                  "verilog-ext-hierarchy-backend")
                'symbols)))

;;;;; hierarchy.el
(defconst verilog-ext-hierarchy-module-cache-file (file-name-concat verilog-ext-cache-dir "module")
  "The file where Verilog-ext modules will be written to.
Used to navigate definitions with `verilog-ext-hierarchy-twidget-nav-open'.")
(defconst verilog-ext-hierarchy-internal-cache-file (file-name-concat verilog-ext-cache-dir "hierarchy-builtin")
  "The file where Verilog-ext builtin/tree-sitter hierarchies will be written to.")

(defvar verilog-ext-hierarchy-internal-alist nil
  "Per project flat hierarchy alist.
Used by builtin and tree-sitter backends.")

(defvar verilog-ext-hierarchy-current-flat-hier nil
  "Current flat hierarchy.

Used by `verilog-ext-hierarchy-extract--internal',
`verilog-ext-hierarchy-vhier-extract' and their subroutines.
Needed since `verilog-ext-hierarchy-extract--childrenfn' can only
have one argument (item).")


(defun verilog-ext-hierarchy--get-node-leaf (node)
  "Return leaf name of hierarchical reference NODE.
E.g: return \"leaf\" for \"top.block.subblock.leaf\"."
  (car (last (split-string node "\\."))))

(defun verilog-ext-hierarchy--get-node-prefix (node)
  "Return prefix name of hierarchical reference NODE.
E.g: return \"top.block.subblock\" for \"top.block.subblock.leaf\"."
  (let ((prefix (string-join (butlast (split-string node "\\.")) ".")))
    (unless (string= prefix "")
      prefix)))

(defun verilog-ext-hierarchy-extract--childrenfn (item)
  "Childrenfn for `hierarchy'.
Arg ITEM are hierarchy nodes."
  (let* ((prefix (verilog-ext-hierarchy--get-node-prefix item))
         (leaf (verilog-ext-hierarchy--get-node-leaf item))
         (children (cdr (assoc (car (split-string leaf ":")) verilog-ext-hierarchy-current-flat-hier))))
    (mapcar (lambda (child) (concat (when prefix (concat prefix ".")) leaf "." child)) children)))

(defun verilog-ext-hierarchy-extract--construct-node (node hierarchy)
  "Recursively build HIERARCHY for NODE using childrenfn."
  (let ((children (mapcar (lambda (child)
                            (concat node "." child))
                          (cdr (assoc (verilog-ext-hierarchy--get-node-leaf node) verilog-ext-hierarchy-current-flat-hier)))))
    (when children
      (hierarchy-add-tree hierarchy node nil #'verilog-ext-hierarchy-extract--childrenfn)
      (dolist (child children)
        (verilog-ext-hierarchy-extract--construct-node child hierarchy)))
    hierarchy))

(defun verilog-ext-hierarchy-extract--internal (module)
  "Construct hierarchy struct for MODULE.

Modules and instances will be analyzed from corresponding entry in
`verilog-ext-hierarchy-current-flat-hier'.  These entries will have an
associated project present `verilog-ext-project-alist' and will be of the form:
\(module instance1:NAME1 instance2:NAME2 ...\).

With current prefix, force refreshing of hierarchy database for active project.

Return populated `hierarchy' struct."
  (let* ((proj (verilog-ext-buffer-proj))
         (hierarchy-alist (if current-prefix-arg
                              nil
                            (verilog-ext-aget verilog-ext-hierarchy-internal-alist proj))))
    ;; Error checking
    (unless hierarchy-alist
      (cond (current-prefix-arg
             (message "Forcing refresh of hierarchy database for [%s]" proj)
             (verilog-ext-hierarchy-parse)
             (setq hierarchy-alist (verilog-ext-aget verilog-ext-hierarchy-internal-alist proj)))
            ((y-or-n-p (format "Empty hierarchy database for [%s].  Run `verilog-ext-hierarchy-parse'?" proj))
             (verilog-ext-hierarchy-parse)
             (setq hierarchy-alist (verilog-ext-aget verilog-ext-hierarchy-internal-alist proj)))
            (t
             (user-error "Aborting"))))
    (unless (assoc module hierarchy-alist)
      (user-error "Could not find %s in the flat-hierarchy for project [%s]" module proj))
    (unless (cdr (assoc module hierarchy-alist))
      (user-error "Current module has no instances"))
    ;; Extract hierarchy
    (setq verilog-ext-hierarchy-current-flat-hier hierarchy-alist)
    (verilog-ext-hierarchy-extract--construct-node module (hierarchy-new))))


;;;;; Frontend format conversion
(defun verilog-ext-hierarchy--convert-struct-to-string (hierarchy-struct)
  "Convert HIERARCHY-STRUCT to a string.
Used to convert hierarchy formats for displaying on different frontends."
  (let ((offset-blank-spaces 2) ; Intended to be used by outshine, which assumes that...
        (unicode-spc 32)        ; ... vhier output adds two offset indent spaces
        (debug nil))
    (unless (hierarchy-p hierarchy-struct)
      (error "Wrong type for hierarchy-struct"))
    (with-temp-buffer
      (when debug
        (clone-indirect-buffer-other-window "*debug*" t))
      (hierarchy-print hierarchy-struct (lambda (node) (verilog-ext-hierarchy--get-node-leaf node)))
      (save-excursion
        (goto-char (point-min))
        (while (not (eobp))
          (insert-char unicode-spc offset-blank-spaces)
          (forward-line)))
      (buffer-substring-no-properties (point-min) (point-max)))))

(defun verilog-ext-hierarchy--convert-string-to-alist (hierarchy-string)
  "Convert HIERARCHY-STRING to an alist.
Used to convert hierarchy formats for displaying on different frontends.
Alist will be of the form (module instance1:NAME1 instance2:NAME2 ...)."
  (let ((offset-blank-spaces 2) ; Intended to be used by outshine, which assumes that...
        (debug nil)             ; ... vhier output adds two offset indent spaces
        flat-hierarchy current-line parent current-indent cell hierarchy-alist)
    (unless (stringp hierarchy-string)
      (error "Wrong type for hierarchy-string"))
    (with-temp-buffer
      (when debug
        (clone-indirect-buffer-other-window "*debug*" t))
      (insert hierarchy-string)
      (untabify (point-min) (point-max))
      (delete-trailing-whitespace)
      (goto-char (point-min))
      ;; Delete blank initial spaces created by vhier output before processing
      (save-excursion
        (while (not (eobp))
          (delete-char offset-blank-spaces)
          (forward-line)))
      ;; Iterate over different nodes (1 node/line), add them to the flat
      ;; hierarchy and update their children by checking what is their parent on
      ;; an indented string.
      (while (not (eobp))
        (back-to-indentation)
        (setq current-line (buffer-substring-no-properties (point) (line-end-position)))
        (push (cons current-line nil) flat-hierarchy)
        (setq parent nil) ; Clean value before loop start
        (setq parent (save-excursion ; Find parent on an indented string
                       (back-to-indentation)
                       (setq current-indent (current-column))
                       (while (and (not (bobp))
                                   (not parent))
                         (forward-line -1)
                         (back-to-indentation)
                         (when (< (current-column) current-indent)
                           (setq parent (buffer-substring-no-properties (point) (line-end-position)))))
                       parent))
        (when parent
          (setq cell (assoc parent flat-hierarchy))
          (if (cdr cell)
              (setcdr cell (append (cdr cell) (list current-line)))
            (setcdr cell (list current-line))))
        (forward-line)))
    ;; Format elements of flat hierarchy: from "INST module" to "module:INST"
    (dolist (module-and-instances flat-hierarchy)
      (push (mapcar (lambda (module)
                      (if (string-match (concat "\\(?1:" verilog-identifier-sym-re "\\) \\(?2:" verilog-identifier-sym-re "\\)") module)
                          (concat (match-string-no-properties 2 module) ":" (match-string-no-properties 1 module))
                        module))
                    module-and-instances)
            hierarchy-alist))
    ;; Remove instance name from modules (car of each element)
    (dolist (module-and-instances hierarchy-alist)
      (setcar module-and-instances (car (split-string (car module-and-instances) ":"))))
    ;; Return value
    hierarchy-alist))

;;;;; Module-alist
(defun verilog-ext-hierarchy-build-module-alist (files proj)
  "Build alist of modules for FILES in project PROJ.

Used for hierarchy.el frontend to visit file of module at point."
  (let (module-alist)
    (dolist (file files)
      (cond (;; Builtin or vhier without tree-sitter support
             (or (eq verilog-ext-hierarchy-backend 'builtin)
                 (and (eq verilog-ext-hierarchy-backend 'vhier)
                      (not (treesit-language-available-p 'verilog))))
             (with-temp-buffer
               (insert-file-contents file)
               (verilog-ext-with-no-hooks
                 (verilog-mode))
               (dolist (module-and-pos (verilog-ext-scan-buffer-modules))
                 (push `(,(car module-and-pos)
                         ,file
                         ,(cadr module-and-pos))
                       module-alist))))
            (;; Tree-sitter or vhier with tree-sitter support
             (or (eq verilog-ext-hierarchy-backend 'tree-sitter)
                 (and (eq verilog-ext-hierarchy-backend 'vhier)
                      (treesit-language-available-p 'verilog)))
             (with-temp-buffer
               (insert-file-contents file)
               (treesit-parser-create 'verilog)
               (dolist (module-node (verilog-ts-nodes "\\<module_declaration\\>"))
                 (push `(,(verilog-ts--node-identifier-name module-node)
                         ,file
                         ,(line-number-at-pos (treesit-node-start module-node)))
                       module-alist))))
            ;; Default, wrong backend
            (t
             (error "Wrong backend selected"))))
    (setf (alist-get proj verilog-ext-hierarchy-module-alist nil 'remove 'string=) module-alist)))


;;;; Backends/extraction
;;;;; Vhier
(defconst verilog-ext-hierarchy-vhier-buffer-name "*Verilog-Perl*"
  "Buffer name to use for the hierarchy file.")
(defconst verilog-ext-hierarchy-vhier-shell-cmds-buffer-name "*Verilog-Perl-Shell*"
  "Buffer name to use for the output of the shell commands vppreproc and vhier.")
(defconst verilog-ext-hierarchy-vhier-bin-args '("--cells"
                                                 "--instance"
                                                 "--no-missing"
                                                 "--missing-modules"))
(defvar verilog-ext-hierarchy-vhier-open-dirs nil "List of open dirs for `verilog-ext-hierarchy-vhier-extract'.")
(defvar verilog-ext-hierarchy-vhier-open-files nil "List of open files for `verilog-ext-hierarchy-vhier-extract'.")

(defconst verilog-ext-hierarchy-vhier-cache-file (file-name-concat verilog-ext-cache-dir "hierarchy-vhier")
  "The file where Verilog-ext Vhier hierarchy will be written to.")

(defvar verilog-ext-hierarchy-vhier-alist nil)

(defun verilog-ext-hierarchy-vhier-extract (module)
  "Extract hierarchy of MODULE using Verilog-Perl vhier as a backend.

With current prefix, force refreshing of hierarchy database for active project.

Return populated `hierarchy' struct."
  (unless (executable-find "vhier")
    (error "Executable vhier not found"))
  (let* ((proj (verilog-ext-buffer-proj))
         (proj-files `(,@(verilog-ext-proj-files proj) ,@verilog-ext-hierarchy-vhier-open-files))
         (proj-lib-search-path (verilog-ext-proj-lib-search-path proj))
         (cached-hierarchy-alist (if current-prefix-arg
                                     nil
                                   (verilog-ext-aget verilog-ext-hierarchy-vhier-alist proj)))
         (vhier-args (mapconcat #'identity verilog-ext-hierarchy-vhier-bin-args " "))
         (library-args (concat "+libext+" (mapconcat #'concat verilog-library-extensions "+") " "
                               (mapconcat (lambda (dir)
                                            (concat "-y " dir))
                                          `(,@proj-lib-search-path ,@verilog-ext-hierarchy-vhier-open-dirs)
                                          " ")))
         (input-files (mapconcat #'identity proj-files " "))
         (command-file (verilog-ext-proj-command-file proj))
         (buf verilog-ext-hierarchy-vhier-buffer-name)
         (buf-err verilog-ext-hierarchy-vhier-shell-cmds-buffer-name)
         (err-msg (format "vhier returned with errors\nCheck %s buffer" buf-err))
         (cmd (mapconcat #'identity
                         `("vhier" ,vhier-args ,library-args
                           ,(when command-file (mapconcat #'identity `("-f " ,command-file)))
                           ,input-files ,buffer-file-name
                           "--top-module" ,module)
                         " "))
         hierarchy-string hierarchy-alist)
    ;; Basic checks
    (unless proj
      (user-error "Not in a Verilog project buffer, check `verilog-ext-project-alist'"))
    ;; Use cache if already available instead of running vhier command
    (if cached-hierarchy-alist
        (setq verilog-ext-hierarchy-current-flat-hier cached-hierarchy-alist)
      ;; Otherwise run vhier command to extract project hierarchy
      (unless (= 0 (shell-command cmd buf buf-err))
        (pop-to-buffer buf-err)
        (error err-msg))
      (with-current-buffer buf
        ;; Perform a bit of postprocessing to get the format module:INSTANCE
        (verilog-ext-replace-regexp-whole-buffer (concat "\\(?1:" verilog-identifier-sym-re "\\) \\(?2:" verilog-identifier-sym-re "\\)") "\\2:\\1")
        (setq hierarchy-string (buffer-substring-no-properties (point-min) (point-max))))
      ;; Convert indented string to alist for caching and default hierarchy.el displaying
      (setq hierarchy-alist (verilog-ext-hierarchy--convert-string-to-alist hierarchy-string))
      ;; Update variables and cache
      (verilog-ext-proj-setcdr proj verilog-ext-hierarchy-vhier-alist hierarchy-alist)
      (verilog-ext-hierarchy-build-module-alist proj-files proj)
      (setq verilog-ext-hierarchy-current-flat-hier hierarchy-alist)
      (when verilog-ext-cache-enable
        (verilog-ext-serialize verilog-ext-hierarchy-vhier-alist verilog-ext-hierarchy-vhier-cache-file)
        (verilog-ext-serialize verilog-ext-hierarchy-module-alist verilog-ext-hierarchy-module-cache-file)))
    ;; Construct hierarchy struct after setting `verilog-ext-hierarchy-current-flat-hier'
    (unless (assoc module verilog-ext-hierarchy-current-flat-hier)
      (user-error "Could not find %s in the flat-hierarchy for project [%s].\nTry running `verilog-ext-hierarchy-current-buffer' with prefix arg on current buffer" module proj))
    (unless (cdr (assoc module verilog-ext-hierarchy-current-flat-hier))
      (user-error "Current module has no instances"))
    (verilog-ext-hierarchy-extract--construct-node module (hierarchy-new))))


;;;;; Tree-sitter
(defun verilog-ext-hierarchy-tree-sitter-parse-file (file)
  "Return alist with modules and instances from FILE.

Each alist element car is a found module in the file.
These elements cdr are the list of that module's instances.

Instances have module:INST format to make them unique for `hierarchy'
displaying.  Modules have no instance name since they are parsed on its
declaration."
  (let (module-nodes instances module-instances-alist)
    (with-temp-buffer
      (insert-file-contents file)
      (treesit-parser-create 'verilog)
      (setq module-nodes (verilog-ts-module-declarations-nodes-current-buffer))
      (dolist (module-node module-nodes module-instances-alist)
        (setq instances nil)
        (push `(,(verilog-ts--node-identifier-name module-node)
                ,@(dolist (inst-node (verilog-ts-module-instances-nodes module-node) (nreverse instances))
                    (push (concat (verilog-ts--node-identifier-name inst-node) ":" (verilog-ts--node-instance-name inst-node)) instances)))
              module-instances-alist)))))

(defun verilog-ext-hierarchy-tree-sitter-extract (module)
  "Extract hierarchy of MODULE using tree-sitter as a backend.

Populate `verilog-ext-hierarchy-current-flat-hier' with alist of modules
and instances."
  (unless (eq verilog-ext-hierarchy-backend 'tree-sitter)
    (error "Wrong backend!"))
  (verilog-ext-hierarchy-extract--internal module))


;;;;; Builtin
(defun verilog-ext-hierarchy-builtin-parse-file (file)
  "Return alist with modules and instances from FILE.

Each alist element car is a found module in the file.
These elements cdr are the list of that module's instances.

Instances have module:INST format to make them unique for `hierarchy'
displaying.  Modules have no instance name since they are parsed on its
declaration."
  (let (modules instances module-instances-alist)
    (with-temp-buffer
      (insert-file-contents file)
      (verilog-ext-with-no-hooks
        (verilog-mode))
      (setq modules (verilog-ext-scan-buffer-modules))
      (dolist (module modules module-instances-alist)
        (setq instances nil)
        (goto-char (cadr module))
        (while (verilog-ext-find-module-instance-fwd (caddr module))
          (push (concat (match-string-no-properties 1) ":" (match-string-no-properties 2)) instances))
        (push `(,(car module) ,@(nreverse instances)) module-instances-alist)))))

(defun verilog-ext-hierarchy-builtin-extract (module)
  "Extract hierarchy of MODULE using builtin Elisp backend.

Populate `verilog-ext-hierarchy-current-flat-hier' with alist of modules
and instances."
  (unless (eq verilog-ext-hierarchy-backend 'builtin)
    (error "Wrong backend!"))
  (verilog-ext-hierarchy-extract--internal module))


;;;; Frontends/navigation
;;;;; hierarchy.el
(defun verilog-ext-hierarchy-twidget-buf--name ()
  "Return buffer name for twidget hierarchy buffer."
  (concat "*" (verilog-ext-buffer-proj) "*"))

(defun verilog-ext-hierarchy-twidget--buf-project ()
  "Return current project from twidget buffer name.

Assumes that hierarchy buffer name is `verilog-ext-buffer-proj' with stars.
See `verilog-ext-hierarchy-twidget-buf--name'."
  (string-remove-prefix "*" (string-remove-suffix "*" (buffer-name))))

(defun verilog-ext-hierarchy-twidget-nav-open (&optional other-window)
  "Find definition of node/module at point.

Looks at value of `verilog-ext-hierarchy-module-alist' to check definition place
of modules.

If optional arg OTHER-WINDOW is non-nil find definition in other window."
  (interactive)
  (let ((module (save-excursion
                  (widget-end-of-line)
                  (backward-sexp)
                  (thing-at-point 'symbol :no-props)))
        modules-files file line)
    (when module
      (setq modules-files (verilog-ext-aget verilog-ext-hierarchy-module-alist (verilog-ext-hierarchy-twidget--buf-project)))
      (setq file (nth 1 (assoc module modules-files)))
      (setq line (nth 2 (assoc module modules-files)))
      (if (and file line)
          (progn
            (if other-window
                (find-file-other-window file)
              (find-file file))
            (goto-char (point-min))
            (forward-line (1- line))
            (recenter '(4) t))
        (user-error "Could not find %s in `verilog-ext-hierarchy-module-alist'" module)))))

(defun verilog-ext-hierarchy-twidget-nav-open-other-window ()
  "Find definition of node/module at point in other window."
  (interactive)
  (verilog-ext-hierarchy-twidget-nav-open :other-window))

(defun verilog-ext-hierarchy-twidget-nav-init-expand ()
  "Init `tree-widget' expanding hierarchy.

INFO: Could do the same if adding the key argument :open t to `widget-create' in
`hierarchy' function `hierarchy-tree-display'.
INFO: Assumes it's initially collapsed, which is the case by default."
  (save-excursion
    (goto-char (point-min))
    (call-interactively #'widget-button-press)
    (call-interactively #'widget-forward)
    (while (not (bobp))
      (call-interactively #'widget-button-press)
      (call-interactively #'widget-forward))))

(defvar verilog-ext-hierarchy-twidget-nav-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map widget-keymap)
    (define-key map (kbd "SPC") 'widget-button-press)
    (define-key map (kbd "C-n") 'widget-forward)
    (define-key map (kbd "n")   'widget-forward)
    (define-key map (kbd "j")   'widget-forward)
    (define-key map (kbd "C-p") 'widget-backward)
    (define-key map (kbd "p")   'widget-backward)
    (define-key map (kbd "k")   'widget-backward)
    (define-key map (kbd "o")   'verilog-ext-hierarchy-twidget-nav-open-other-window)
    (define-key map (kbd "C-o") 'verilog-ext-hierarchy-twidget-nav-open-other-window)
    (define-key map (kbd "C-j") 'verilog-ext-hierarchy-twidget-nav-open)
    map))

(define-minor-mode verilog-ext-hierarchy-twidget-nav-mode
  "Instance navigation frontend for `tree-widget'."
  :lighter " vH"
  (message "Navigating hierarchy..."))

(defun verilog-ext-hierarchy-twidget-display (hierarchy)
  "Display HIERARCHY using builtin `hierarchy' and `tree-widget' packages.

Show only module name, discard instance name after colon (mod:INST)."
  (unless (hierarchy-p hierarchy)
    (error "Hierarchy must be of hierarchy struct type"))
  (pop-to-buffer
   (hierarchy-tree-display
    hierarchy
    (lambda (item _) (insert (car (split-string (verilog-ext-hierarchy--get-node-leaf item) ":"))))
    (get-buffer-create (verilog-ext-hierarchy-twidget-buf--name))))
  ;; Navigation mode and initial expansion
  (verilog-ext-hierarchy-twidget-nav-mode)
  (when verilog-ext-hierarchy-twidget-init-expand
    (verilog-ext-hierarchy-twidget-nav-init-expand)))

;;;;; outshine
(defmacro verilog-ext-hierarchy-outshine-nav (verilog-ext-func outshine-func)
  "Define function VERILOG-EXT-FUNC to call OUTSHINE-FUNC.
Called in a buffer with `verilog-ext-hierarchy-outshine-nav-mode' enabled.
Move through headings and point at the beginning of the tag."
  (declare (indent 0) (debug t))
  `(defun ,verilog-ext-func ()
     (interactive)
     (beginning-of-line) ; Required for `outline-hide-sublevels'
     (call-interactively ,outshine-func)
     (skip-chars-forward (car (car outshine-promotion-headings)))))

(verilog-ext-hierarchy-outshine-nav verilog-ext-hierarchy-outshine-nav-previous-visible-heading #'outline-previous-visible-heading)
(verilog-ext-hierarchy-outshine-nav verilog-ext-hierarchy-outshine-nav-next-visible-heading     #'outline-next-visible-heading)
(verilog-ext-hierarchy-outshine-nav verilog-ext-hierarchy-outshine-nav-up-heading               #'outline-up-heading)
(verilog-ext-hierarchy-outshine-nav verilog-ext-hierarchy-outshine-nav-forward-same-level       #'outline-forward-same-level)
(verilog-ext-hierarchy-outshine-nav verilog-ext-hierarchy-outshine-nav-backward-same-level      #'outline-backward-same-level)
(verilog-ext-hierarchy-outshine-nav verilog-ext-hierarchy-outshine-nav-hide-sublevels           #'outline-hide-sublevels)

(defun verilog-ext-hierarchy-outshine-jump-to-file (&optional other-window)
  "Jump to module definition at point on navigation hierarchy file.
If OTHER-WINDOW is non-nil, open definition in other window."
  (interactive)
  (if other-window
      (xref-find-definitions-other-window (thing-at-point 'symbol t))
    (xref-find-definitions (thing-at-point 'symbol t))))

(defun verilog-ext-hierarchy-outshine-jump-to-file-other-window ()
  "Jump to module definition at point on navigation hierarchy file."
  (interactive)
  (verilog-ext-hierarchy-outshine-jump-to-file :other-window))

(define-minor-mode verilog-ext-hierarchy-outshine-nav-mode
  "Instance navigation frontend with `outshine'.
Makes use of processed output under `outline-minor-mode' and `outshine'."
  :lighter " vH"
  :keymap
  '(;; Hide/Show
    ("a"       . outline-show-all)
    ("i"       . outline-show-children)
    ("h"       . outline-show-children)
    ("l"       . verilog-ext-hierarchy-outshine-nav-hide-sublevels)
    ("I"       . outline-show-branches)
    (";"       . outline-hide-other)
    ;; Movement
    ("u"       . verilog-ext-hierarchy-outshine-nav-up-heading)
    ("C-c C-u" . verilog-ext-hierarchy-outshine-nav-up-heading)
    ("n"       . verilog-ext-hierarchy-outshine-nav-next-visible-heading)
    ("j"       . verilog-ext-hierarchy-outshine-nav-next-visible-heading)
    ("p"       . verilog-ext-hierarchy-outshine-nav-previous-visible-heading)
    ("k"       . verilog-ext-hierarchy-outshine-nav-previous-visible-heading)
    ("C-c C-n" . verilog-ext-hierarchy-outshine-nav-forward-same-level)
    ("C-c C-p" . verilog-ext-hierarchy-outshine-nav-backward-same-level)
    ;; Jump
    ("o"       . verilog-ext-hierarchy-outshine-jump-to-file-other-window)
    ("C-o"     . verilog-ext-hierarchy-outshine-jump-to-file-other-window)
    ("RET"     . verilog-ext-hierarchy-outshine-jump-to-file)
    ("C-j"     . verilog-ext-hierarchy-outshine-jump-to-file))
  ;; Minor-mode code
  (outshine-mode 1)
  (setq buffer-read-only t)
  (view-mode -1))

(defun verilog-ext-hierarchy-outshine-display (hierarchy)
  "Display HIERARCHY using `outshine'.
Expects HIERARCHY to be a indented string."
  (let ((buf "*Verilog-outshine*"))
    (with-current-buffer (get-buffer-create buf)
      (setq buffer-read-only nil)
      (erase-buffer)
      (insert hierarchy)
      (verilog-ext-replace-regexp-whole-buffer (concat "\\(?1:" verilog-identifier-sym-re "\\):\\(?2:" verilog-identifier-sym-re "\\)") "\\1")
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
      (insert "\n// * Buffer local variables\n// Local Variables:\n// eval: (verilog-ext-hierarchy-outshine-nav-mode)\n// End:\n")
      ;; Insert header to get some info of the file
      (goto-char (point-min))
      (open-line 1)
      (insert "// Hierarchy generated by `verilog-ext'\n")
      (verilog-ext-with-no-hooks
        (verilog-mode))
      (verilog-ext-hierarchy-outshine-nav-mode))
    (pop-to-buffer buf)))

;;;; Core
(defun verilog-ext-hierarchy-serialize ()
  "Write variables to their cache files."
  (verilog-ext-serialize verilog-ext-hierarchy-internal-alist verilog-ext-hierarchy-internal-cache-file)
  (verilog-ext-serialize verilog-ext-hierarchy-vhier-alist verilog-ext-hierarchy-vhier-cache-file)
  (verilog-ext-serialize verilog-ext-hierarchy-module-alist verilog-ext-hierarchy-module-cache-file))

(defun verilog-ext-hierarchy-unserialize ()
  "Read cache files into their corresponding variables."
  (setq verilog-ext-hierarchy-internal-alist (verilog-ext-unserialize verilog-ext-hierarchy-internal-cache-file))
  (setq verilog-ext-hierarchy-vhier-alist (verilog-ext-unserialize verilog-ext-hierarchy-vhier-cache-file))
  (setq verilog-ext-hierarchy-module-alist (verilog-ext-unserialize verilog-ext-hierarchy-module-cache-file)))

(defun verilog-ext-hierarchy-setup ()
  "Setup hierarchy feature.
Read hierarchy cache if enabled."
  (when verilog-ext-cache-enable
    (verilog-ext-hierarchy-unserialize)))

(defun verilog-ext-hierarchy-clear-cache (&optional all)
  "Clear hierarchy cache files for current project.

With prefix arg, clear cache for ALL projects."
  (interactive "P")
  (if (not all)
      (let ((proj (verilog-ext-buffer-proj)))
        (unless proj
          (user-error "Not in a Verilog project buffer"))
        (verilog-ext-proj-setcdr proj verilog-ext-hierarchy-internal-alist nil)
        (verilog-ext-proj-setcdr proj verilog-ext-hierarchy-vhier-alist nil)
        (verilog-ext-proj-setcdr proj verilog-ext-hierarchy-module-alist nil)
        (verilog-ext-hierarchy-serialize)
        (message "[%s] Cleared hierarchy cache!" proj))
    (setq verilog-ext-hierarchy-internal-alist nil)
    (setq verilog-ext-hierarchy-vhier-alist nil)
    (setq verilog-ext-hierarchy-module-alist nil)
    (verilog-ext-hierarchy-serialize)
    (message "Cleared hierarchy cache!")))

(defun verilog-ext-hierarchy-extract (module)
  "Construct hierarchy for MODULE depending on selected backend."
  (cond (;; Verilog-Perl vhier
         (eq verilog-ext-hierarchy-backend 'vhier)
         (verilog-ext-hierarchy-vhier-extract module))
        (;; Tree-sitter
         (eq verilog-ext-hierarchy-backend 'tree-sitter)
         (verilog-ext-hierarchy-tree-sitter-extract module))
        (;; Built-in
         (eq verilog-ext-hierarchy-backend 'builtin)
         (verilog-ext-hierarchy-builtin-extract module))
        ;; Fallback
        (t (error "Must set a proper extraction backend in `verilog-ext-hierarchy-backend'"))))

(defun verilog-ext-hierarchy-display (hierarchy)
  "Display HIERARCHY depending on selected frontend.

Handle conversion (if needed) of input extracted data depending on output
frontend.

E.g.: If extracted with vhier and displayed with hierarchy it is needed to
convert between an indented string and a populated hierarchy struct."
  (let ((display-hierarchy hierarchy))
    (cond (;; Outshine
           (eq verilog-ext-hierarchy-frontend 'outshine)
           (when (hierarchy-p hierarchy)
             (setq display-hierarchy (verilog-ext-hierarchy--convert-struct-to-string hierarchy)))
           (verilog-ext-hierarchy-outshine-display display-hierarchy))
          ;; Hierarchy
          ((eq verilog-ext-hierarchy-frontend 'hierarchy)
           (setq display-hierarchy hierarchy)
           (verilog-ext-hierarchy-twidget-display display-hierarchy))
          ;; Fallback
          (t (error "Must set a proper display frontend in `verilog-ext-hierarchy-frontend'")))))

(defun verilog-ext-hierarchy-parse (&optional verbose)
  "Return flat hierarchy of modules and instances of project.

Populates `verilog-ext-hierarchy-internal-alist' for subsequent hierarchy
extraction and display.

With current-prefix or VERBOSE, dump output log."
  (interactive "P")
  (let* ((proj (verilog-ext-buffer-proj))
         (files (verilog-ext-proj-files proj))
         (num-files (length files))
         (num-files-processed 0)
         (log-file (concat verilog-ext-hierarchy-internal-cache-file ".log"))
         (hier-progress-reporter (make-progress-reporter "[Hierarchy parsing]: " 0 num-files))
         flat-hierarchy data)
    (unless files
      (error "No files found for current buffer project.  Set `verilog-ext-project-alist' accordingly?"))
    (when verbose
      (delete-file log-file))
    (dolist (file files)
      (when verbose
        (append-to-file (format "(%0d%%) [Hierarchy parsing] Processing %s\n" (/ (* num-files-processed 100) num-files) file) nil log-file))
      (progress-reporter-update hier-progress-reporter num-files-processed (format "[%s]" file))
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
    ;; Update hierarchy and module alists and cache
    (verilog-ext-proj-setcdr proj verilog-ext-hierarchy-internal-alist flat-hierarchy)
    (verilog-ext-hierarchy-build-module-alist files proj)
    (when verilog-ext-cache-enable
      (verilog-ext-serialize verilog-ext-hierarchy-internal-alist verilog-ext-hierarchy-internal-cache-file)
      (verilog-ext-serialize verilog-ext-hierarchy-module-alist verilog-ext-hierarchy-module-cache-file)) ; Updated after initial call to `verilog-ext-proj-files'
    ;; Return value for async related function
    (message "Finished analyzing hierarchy!")
    (list verilog-ext-hierarchy-internal-alist verilog-ext-hierarchy-module-alist)))

(defun verilog-ext-hierarchy-parse-async (&optional verbose)
  "Return flat hierarchy of modules and instances of project asynchronously.

Populates `verilog-ext-hierarchy-internal-alist' for subsequent hierarchy
extraction and display.

With current-prefix or VERBOSE, dump output log."
  (interactive "P")
  (message "Starting hierarchy parsing for %s" (verilog-ext-buffer-proj))
  (async-start
   `(lambda ()
      ,(async-inject-variables verilog-ext-hierarchy-async-inject-variables-re)
      (require 'verilog-ext)
      ;; Preserve cache on child Emacs process
      (setq verilog-ext-hierarchy-internal-alist (verilog-ext-unserialize verilog-ext-hierarchy-internal-cache-file))
      (setq verilog-ext-hierarchy-module-alist (verilog-ext-unserialize verilog-ext-hierarchy-module-cache-file))
      (verilog-ext-hierarchy-parse ,@verbose))
   (lambda (result)
     (message "Finished analyzing hierarchy!")
     (setq verilog-ext-hierarchy-internal-alist (car result))
     (setq verilog-ext-hierarchy-module-alist (cadr result)))))

(defun verilog-ext-hierarchy-current-buffer ()
  "Extract and display hierarchy for module of `current-buffer'."
  (interactive)
  (let* ((module (verilog-ext-select-file-module))
         (hierarchy (verilog-ext-hierarchy-extract module)))
    (verilog-ext-hierarchy-display hierarchy)))


(provide 'verilog-ext-hierarchy)

;;; verilog-ext-hierarchy.el ends here
