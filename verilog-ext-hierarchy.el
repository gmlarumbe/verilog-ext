;;; verilog-ext-hierarchy.el --- Verilog-ext Hierarchy  -*- lexical-binding: t -*-

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

(defcustom verilog-ext-hierarchy-backend nil
  "Verilog-ext hierarchy extraction backend."
  :type '(choice (const :tag "Verilog-Perl vhier" vhier)
                 (const :tag "Tree-sitter"        tree-sitter)
                 (const :tag "Built-in"           builtin))
  :group 'verilog-ext-hierarchy)

(defcustom verilog-ext-hierarchy-frontend nil
  "Verilog-ext hierarchy display and navigation frontend."
  :type '(choice (const :tag "Outshine"  outshine)
                 (const :tag "Hierarchy" hierarchy))
  :group 'verilog-ext-hierarchy)

(defcustom verilog-ext-hierarchy-vhier-use-open-buffers t
  "Set to non-nil to use list of open Verilog files/dirs with vhier backend."
  :type 'boolean
  :group 'verilog-ext-hierarchy)

(defcustom verilog-ext-hierarchy-vhier-dirs nil
  "List of library directories to search for with vhier backend."
  :type '(repeat directory)
  :group 'verilog-ext-hierarchy)

(defcustom verilog-ext-hierarchy-vhier-files nil
  "List of additional files to parse before `current-buffer' with vhier backend.
They will be parsed in the order they are included in the list."
  :type '(repeat file)
  :group 'verilog-ext-hierarchy)

(defcustom verilog-ext-hierarchy-vhier-command-file nil
  "Verilog-ext vhier command file."
  :type 'string
  :group 'verilog-ext-hierarchy)

(defcustom verilog-ext-hierarchy-builtin-dirs nil
  "Verilog-ext list of directories for builtin hierarchy extraction.

If set to nil default to search for current workspace files.

It is a list of strings containing directories that will be searched for Verilog
files to obtain a flat hierarchy used for hierarchy extraction with the builtin
backend."
  :type '(repeat directory)
  :group 'verilog-ext-hierarchy)

(defcustom verilog-ext-hierarchy-twidget-init-expand nil
  "Set to non-nil to initially expand the hierarchy using hierarchy.el frontend."
  :group 'verilog-ext-hierarchy
  :type 'boolean)


;;;; Utils
;;;;; hierarchy.el
(defvar verilog-ext-hierarchy-current-flat-hierarchy nil
  "Current flat hierarchy.

Used by `verilog-ext-hierarchy-extract--internal' and its subroutines.

Needed since `verilog-ext-hierarchy-extract--childrenfn' can only have one
argument (item).")

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
         (children (cdr (assoc (car (split-string leaf ":")) verilog-ext-hierarchy-current-flat-hierarchy))))
    (mapcar (lambda (child) (concat (when prefix (concat prefix ".")) leaf "." child)) children)))

(defun verilog-ext-hierarchy-extract--construct-node (node hierarchy)
  "Recursively build HIERARCHY for NODE using childrenfn."
  (let ((children (mapcar (lambda (child)
                            (concat node "." child))
                          (cdr (assoc (verilog-ext-hierarchy--get-node-leaf node) verilog-ext-hierarchy-current-flat-hierarchy)))))
    (when children
      (hierarchy-add-tree hierarchy node nil #'verilog-ext-hierarchy-extract--childrenfn)
      (dolist (child children)
        (verilog-ext-hierarchy-extract--construct-node child hierarchy)))
    hierarchy))

(defun verilog-ext-hierarchy-extract--internal (module)
  "Construct hierarchy struct for MODULE.

Modules and instances will be analyzed from the value of
`verilog-ext-hierarchy-current-flat-hierarchy'.
This alist must be populated before calling the function!

`verilog-ext-hierarchy-current-flat-hierarchy' is an alist of the form:
 ((moduleA instanceA1:NAME_A1 instanceA2:NAME_A2 ...)
  (moduleB instanceB1:NAME_B1 instanceB2:NAME_B2 ...)
  ..)

Return populated `hierarchy' struct."
  ;; Some checks
  (unless verilog-ext-hierarchy-current-flat-hierarchy
    (user-error "Empty hierarchy database, maybe run first `verilog-ext-workspace-hierarchy-parse'?"))
  (unless (assoc module verilog-ext-hierarchy-current-flat-hierarchy)
    (user-error "Could not find %s in the flat-hierarchy" module))
  (if (not (cdr (assoc module verilog-ext-hierarchy-current-flat-hierarchy)))
      (user-error "Current module has no instances")
    ;; Construct node
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

(defun verilog-ext-hierarchy-vhier-extract (module)
  "Extract hierarchy of MODULE using Verilog-Perl vhier as a backend.
Return hierarchy as an indented string."
  (unless (executable-find "vhier")
    (error "Executable vhier not found"))
  (let* ((vhier-args (mapconcat #'identity verilog-ext-hierarchy-vhier-bin-args " "))
         (library-args (concat "+libext+" (mapconcat #'concat verilog-library-extensions "+") " "
                               (mapconcat (lambda (dir)
                                            (concat "-y " dir))
                                          `(,@verilog-ext-hierarchy-vhier-dirs ,@verilog-ext-hierarchy-vhier-open-dirs)
                                          " ")))
         (input-files (mapconcat #'identity
                                 `(,@verilog-ext-hierarchy-vhier-files ,@verilog-ext-hierarchy-vhier-open-files)
                                 " "))
         (buf verilog-ext-hierarchy-vhier-buffer-name)
         (buf-err verilog-ext-hierarchy-vhier-shell-cmds-buffer-name)
         (err-msg (format "vhier returned with errors\nCheck %s buffer" buf-err))
         (cmd (mapconcat #'identity
                         `("vhier" ,vhier-args ,library-args
                           ,(when verilog-ext-hierarchy-vhier-command-file
                              (mapconcat #'identity `("-f " ,verilog-ext-hierarchy-vhier-command-file)))
                           ,input-files ,buffer-file-name "--top-module" ,module)
                         " ")))
    (unless (= 0 (shell-command cmd buf buf-err))
      (pop-to-buffer buf-err)
      (error err-msg))
    (with-current-buffer buf
      ;; Perform a bit of postprocessing to get the format module:INSTANCE
      (verilog-ext-replace-regexp-whole-buffer (concat "\\(?1:" verilog-identifier-sym-re "\\) \\(?2:" verilog-identifier-sym-re "\\)") "\\2:\\1")
      (buffer-substring-no-properties (point-min) (point-max)))))


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
      (verilog-ts-mode)
      (setq module-nodes (verilog-ts-module-declarations-nodes-current-buffer))
      (dolist (module-node module-nodes module-instances-alist)
        (setq instances nil)
        (push `(,(verilog-ts--node-identifier-name module-node)
                ,@(dolist (inst-node (verilog-ts-module-instances-nodes module-node) (nreverse instances))
                    (push (concat (verilog-ts--node-identifier-name inst-node) ":" (verilog-ts--node-instance-name inst-node)) instances)))
              module-instances-alist)))))

(defun verilog-ext-hierarchy-tree-sitter-extract (module)
  "Extract hierarchy of MODULE using tree-sitter as a backend.

Populate `verilog-ext-hierarchy-current-flat-hierarchy' with alist of modules
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
      (verilog-mode)
      (setq modules (verilog-ext-scan-buffer-modules))
      (dolist (module modules module-instances-alist)
        (setq instances nil)
        (goto-char (cadr module))
        (while (verilog-ext-find-module-instance-fwd (caddr module))
          (push (concat (match-string-no-properties 1) ":" (match-string-no-properties 2)) instances))
        (push `(,(car module) ,@(nreverse instances)) module-instances-alist)))))

(defun verilog-ext-hierarchy-builtin-extract (module)
  "Extract hierarchy of MODULE using builtin Elisp backend.

Populate `verilog-ext-hierarchy-current-flat-hierarchy' with alist of modules
and instances."
  (unless (eq verilog-ext-hierarchy-backend 'builtin)
    (error "Wrong backend!"))
  (verilog-ext-hierarchy-extract--internal module))


;;;; Frontends/navigation
;;;;; hierarchy.el
(defun verilog-ext-hierarchy-twidget-nav-open (&optional other-window)
  "Find definition of node/module at point.
Requires having active some backend on `xref-backend-functions',
e.g. lsp/eglot/ggtags.

If optional arg OTHER-WINDOW is non-nil find definition in other window."
  (interactive)
  (let ((module (save-excursion
                  (widget-end-of-line)
                  (backward-sexp)
                  (thing-at-point 'symbol :no-props))))
    (when module
      (widget-end-of-line)
      (backward-sexp)
      (if other-window
          (xref-find-definitions-other-window module)
        (xref-find-definitions module)))))

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

(defun verilog-ext-hierarchy-twidget-display (hierarchy &optional module)
  "Display HIERARCHY using builtin `hierarchy' and `tree-widget' packages.

Show only module name, discard instance name after colon (mod:INST).

Optional arg MODULE will set the name of the display buffer, if provided."
  (unless (hierarchy-p hierarchy)
    (error "Hierarchy must be of hierarchy struct type"))
  (pop-to-buffer
   (hierarchy-tree-display
    hierarchy
    (lambda (item _) (insert (car (split-string (verilog-ext-hierarchy--get-node-leaf item) ":"))))
    (get-buffer-create (concat "*" module "*"))))
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
  "Instance navigation frontend for Verilog-Perl `vhier'.
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

(defun verilog-ext-hierarchy-outshine-display (hierarchy &optional module)
  "Display HIERARCHY using `outshine'.
Expects HIERARCHY to be a indented string.
Optional arg MODULE will set the name of the display buffer, if provided."
  (let ((buf (or (concat "*" module "*")
                 "*Verilog-outshine*")))
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
      (verilog-mode)
      (verilog-ext-hierarchy-outshine-nav-mode))
    (pop-to-buffer buf)))

;;;; Common
(defun verilog-ext-hierarchy-setup ()
  "Setup hierarchy backend/frontend depending on available binaries/packages.
If these have been set before, keep their values."
  (let ((backend (or verilog-ext-hierarchy-backend
                     (cond ((executable-find "vhier")
                            'vhier)
                           ((and (treesit-available-p)
                                 (treesit-language-available-p 'verilog))
                            'tree-sitter)
                           (t
                            'builtin))))
        (frontend (or verilog-ext-hierarchy-frontend
                      'hierarchy)))
    (setq verilog-ext-hierarchy-backend backend)
    (setq verilog-ext-hierarchy-frontend frontend)))

(defun verilog-ext-hierarchy-extract (module)
  "Construct hierarchy for MODULE depending on selected backend."
  (cond (;; Verilog-Perl vhier
         (eq verilog-ext-hierarchy-backend 'vhier)
         (verilog-ext-hierarchy-vhier-extract module)) ; Returns indented string
        (;; Tree-sitter
         (eq verilog-ext-hierarchy-backend 'tree-sitter)
         (verilog-ext-hierarchy-tree-sitter-extract module)) ; Returns populated hierarchy struct
        (;; Built-in
         (eq verilog-ext-hierarchy-backend 'builtin)
         (verilog-ext-hierarchy-builtin-extract module)) ; Returns populated hierarchy struct
        ;; Fallback
        (t (error "Must set a proper extraction backend in `verilog-ext-hierarchy-backend'"))))

(defun verilog-ext-hierarchy-display (hierarchy &optional module)
  "Display HIERARCHY depending on selected frontend.

Handle conversion (if needed) of input extracted data depending on output
frontend.

E.g.: If extracted with vhier and displayed with hierarchy it is needed to
convert between an indented string and a populated hierarchy struct.

Optional arg MODULE will set the name of the display buffer, if provided."
  (let ((display-hierarchy hierarchy))
    (cond (;; Outshine
           (eq verilog-ext-hierarchy-frontend 'outshine)
           (when (hierarchy-p hierarchy)
             (setq display-hierarchy (verilog-ext-hierarchy--convert-struct-to-string hierarchy)))
           (verilog-ext-hierarchy-outshine-display display-hierarchy module))
          ;; Hierarchy
          ((eq verilog-ext-hierarchy-frontend 'hierarchy)
           (when (stringp hierarchy)
             (let ((top-module (string-trim-left (car (split-string (car (split-string hierarchy "\n")) ":")))) ; First line of the string, as parsed by vhier
                   (hierarchy-alist (verilog-ext-hierarchy--convert-string-to-alist hierarchy)))
               (setq verilog-ext-hierarchy-current-flat-hierarchy hierarchy-alist)
               (setq display-hierarchy (verilog-ext-hierarchy-extract--internal top-module))))
           (verilog-ext-hierarchy-twidget-display display-hierarchy module))
          ;; Fallback
          (t (error "Must set a proper display frontend in `verilog-ext-hierarchy-frontend'")))))

(defun verilog-ext-hierarchy-current-buffer ()
  "Extract and display hierarchy for module of `current-buffer'."
  (interactive)
  (let* ((module (verilog-ext-select-file-module))
         (hierarchy (verilog-ext-hierarchy-extract module)))
    (verilog-ext-hierarchy-display hierarchy module)))



(provide 'verilog-ext-hierarchy)

;;; verilog-ext-hierarchy.el ends here
