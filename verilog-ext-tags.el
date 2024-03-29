;;; verilog-ext-tags.el --- Verilog-ext Tags  -*- lexical-binding: t -*-

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
;;
;; Tag collection for jump to definition/reference and semantic completion.
;;
;; `verilog-ext-tags-get-async' relies on emacs-async: https://github.com/jwiegley/emacs-async:
;;
;; - Limitations with async tag collection:
;;
;;   - The `async' library has limitations with hash-tables:
;;      - async-start returns hash tables as lists: https://github.com/jwiegley/emacs-async/issues/164
;;      - Since the # is stripped (https://github.com/jwiegley/emacs-async/issues/145) and it's needed to
;;        properly represent hash-tables, the result is that this implementation requires a workaround
;;      - Solution:
;;        - Reading/writing to/from stored cached files
;;
;;   - Injecting the environment with the value of large hash tables (e.g. `verilog-ext-tags-defs-table') in
;;   `async-start' via `async-inject-variables' takes a long time in the parent process
;;      - Solution:
;;        - Reading environment from stored cached files
;;
;;; Code:

(require 'async)
(require 'map)
(require 'verilog-ext-nav)
(require 'verilog-ts-mode)


(defgroup verilog-ext-tags nil
  "Verilog-ext tags."
  :group 'verilog-ext)

(defcustom verilog-ext-tags-backend (if (and (treesit-available-p) (treesit-language-available-p 'verilog))
                                        'tree-sitter
                                      'builtin)
  "Verilog-ext tags extraction backend."
  :type '(choice (const :tag "Tree-sitter" tree-sitter)
                 (const :tag "Built-in"    builtin))
  :group 'verilog-ext-tags)

(defcustom verilog-ext-tags-fontify-matches t
  "Set to non-nil to fontify matches for xref.

This setting slightly increases processing time of `verilog-ext-tags-get'."
  :type 'boolean
  :group 'verilog-ext-tags)


(defvar verilog-ext-tags-file-hashes nil)

(defvar verilog-ext-tags-defs-table nil)
(defvar verilog-ext-tags-refs-table nil)
(defvar verilog-ext-tags-inst-table nil)

(defvar verilog-ext-tags-defs-file-tables nil)
(defvar verilog-ext-tags-inst-file-tables nil)
(defvar verilog-ext-tags-refs-file-tables nil)

(defvar verilog-ext-tags-defs-current-file nil)
(defvar verilog-ext-tags-inst-current-file nil)
(defvar verilog-ext-tags-refs-current-file nil)

(defconst verilog-ext-tags-defs-file-tables-cache-file (file-name-concat verilog-ext-cache-dir "defs-file-tables")
  "The file where `verilog-ext' defs-file-tables will be written to.")
(defconst verilog-ext-tags-refs-file-tables-cache-file (file-name-concat verilog-ext-cache-dir "refs-file-tables")
  "The file where `verilog-ext' refs-file-tables will be written to.")
(defconst verilog-ext-tags-inst-file-tables-cache-file (file-name-concat verilog-ext-cache-dir "inst-file-tables")
  "The file where `verilog-ext' inst-file-tables will be written to.")

(defconst verilog-ext-tags-defs-table-cache-file (file-name-concat verilog-ext-cache-dir "defs-table")
  "The file where `verilog-ext' defs-table will be written to.")
(defconst verilog-ext-tags-refs-table-cache-file (file-name-concat verilog-ext-cache-dir "refs-table")
  "The file where `verilog-ext' refs-table will be written to.")
(defconst verilog-ext-tags-inst-table-cache-file (file-name-concat verilog-ext-cache-dir "inst-table")
  "The file where `verilog-ext' inst-table will be written to.")

(defconst verilog-ext-tags-file-hashes-cache-file (file-name-concat verilog-ext-cache-dir "file-hashes")
  "The file where `verilog-ext' file-hashes will be written to.")

(defconst verilog-ext-tags-cache-log-file (file-name-concat verilog-ext-cache-dir "tags.log"))

(defconst verilog-ext-tags-async-inject-variables-re
  (eval-when-compile
    (regexp-opt '("load-path"
                  "buffer-file-name"
                  "default-directory"
                  "verilog-ext-feature-list"
                  "verilog-ext-project-alist"
                  "verilog-ext-tags-backend")
                'symbols)))

(defvar verilog-ext-tags-have-been-updated nil
  "Determines whether or not tags have been updated.
Used to conditionally serialize tags cache.")


;;;; Common
(defsubst verilog-ext-tags-locs-props (type desc file line col)
  "Return :locs properties for current tag.

These include tag TYPE, description DESC, the FILE, current LINE and COL."
  `(:type ,type
    :desc ,desc
    :file ,file
    :line ,line
    :col ,col))

(defsubst verilog-ext-tags-desc ()
  "Return string description for tag at point.

The description determines what `xref' will show when a match is found."
  (buffer-substring (line-beginning-position) (line-end-position)))

(cl-defsubst verilog-ext-tags-table-push (&key table tag type desc file line col parent)
  "Add entry for TAG in hash-table TABLE.

It is needed to provide TYPE, description DESC, FILE, LINE and COL properties to
add the entry in the table.

Optional arg PARENT is the module where TAG is defined/instantiated for dot
completion.

If there is no entry in the table for TAG add one.  Otherwise update the
existing one with current location properties."
  (let ((tag-value (gethash tag table))
        locs-plist loc-new parent-value parent-items)
    ;; First add parent and populate its items if it was provided. Create if it did not exist.
    (when parent
      (setq parent-value (or (gethash parent table)
                             (puthash parent (list :items nil :locs nil) table)))
      (setq parent-items (plist-get parent-value :items))
      (unless (member tag parent-items)
        (plist-put parent-value :items `(,@parent-items ,tag))
        (puthash parent parent-value table)))
    ;; Next add the tag if it was not present in the table or update existing tag properties if it was present.
    (if (not tag-value)
        (puthash tag `(:items nil :locs (,(verilog-ext-tags-locs-props type desc file line col))) table)
      (setq locs-plist (plist-get tag-value :locs))
      (setq loc-new (verilog-ext-tags-locs-props type desc file line col))
      (unless (member loc-new locs-plist)
        (push loc-new locs-plist)
        (plist-put tag-value :locs locs-plist)
        (puthash tag `(:items ,(plist-get tag-value :items) :locs ,locs-plist) table)))))

(defun verilog-ext-tags-table-remove-file-locs (file file-tables table)
  "Remove FILE tag locations in TABLE.

FILE-TABLES is the intermediate variable with a per-file hash table for current
project."
  (when (and file-tables
             (gethash file file-tables)
             table)
    (let ((file-tag-locs-table (gethash file file-tables))
          items-and-locs locs tag-loc)
      (maphash (lambda (key value)
                 (setq items-and-locs (gethash (car key) table))
                 (setq locs (plist-get items-and-locs :locs))
                 (setq tag-loc (verilog-ext-tags-locs-props (plist-get value :type)
                                                            (plist-get value :desc)
                                                            (plist-get (cdr key) :file)
                                                            (plist-get (cdr key) :line)
                                                            (plist-get value :col)))
                 (when (member tag-loc locs)
                   (setf (cl-getf items-and-locs :locs) (remove tag-loc locs)))
                 (when (not (plist-get items-and-locs :locs))
                   (remhash (car key) table)))
               file-tag-locs-table))))

(defun verilog-ext-tags-add-file-locs (file file-tables table)
  "Add FILE tag locations in TABLE.

FILE-TABLES is the intermediate variable with a per-file hash table for current
project."
  (let ((file-table (gethash file file-tables)))
    (maphash (lambda (key value)
               (verilog-ext-tags-table-push :table table
                                            :tag (car key)
                                            :type (plist-get value :type)
                                            :desc (plist-get value :desc)
                                            :file (plist-get (cdr key) :file)
                                            :line (plist-get (cdr key) :line)
                                            :col (plist-get value :col)
                                            :parent (plist-get value :parent)))
             file-table)))


;;;; Builtin
(cl-defun verilog-ext-tags-table-push-defs (&key tag-type file start limit parent)
  "Push definitions of TAG-TYPE inside tags hash table.

FILE might be specified for the cases when a temp-buffer without an associated
file is being parsed.

Limit search between START and LIMIT if provided, otherwise search the whole
buffer.

PARENT is the module where TAG is defined/instantiated for dot completion."
  (let ((ignore-paren-decl (eq tag-type 'declarations-no-parens))
        tag type data inner-start inner-limit)
    (unless start (setq start (point-min)))
    (unless limit (setq limit (point-max)))
    (when (eq tag-type 'declarations-no-parens)
      (setq tag-type 'declarations))
    (save-match-data
      (save-excursion
        (goto-char start)
        (pcase tag-type
          ('declarations (while (verilog-re-search-forward (verilog-get-declaration-re) limit :no-error)
                           (setq type (string-trim (match-string-no-properties 0)))
                           (setq tag (thing-at-point 'symbol :no-props))
                           (unless (or (member tag verilog-keywords)
                                       (when ignore-paren-decl
                                         (verilog-in-parenthesis-p))
                                       (not tag))
                             (puthash `(,tag
                                        :file ,file
                                        :line ,(line-number-at-pos))
                                      `(:type ,type
                                        :desc ,(verilog-ext-tags-desc)
                                        :col ,(current-column)
                                        :parent ,parent)
                                      verilog-ext-tags-defs-current-file))))
          ('tf (while (setq data (verilog-ext-find-function-task-fwd limit))
                 (setq tag (match-string-no-properties 1))
                 (puthash `(,tag
                            :file ,file
                            :line ,(line-number-at-pos))
                          `(:type ,(alist-get 'type data)
                            :desc ,(verilog-ext-tags-desc)
                            :col ,(current-column)
                            :parent ,parent)
                          verilog-ext-tags-defs-current-file)
                 (save-excursion ; Get tasks and function declarations
                   (when (< (setq inner-start (alist-get 'pos data))
                            (setq inner-limit (save-excursion
                                                (verilog-re-search-backward "\\<\\(function\\|task\\)\\>" (line-beginning-position) :no-error)
                                                (verilog-ext-pos-at-forward-sexp))))
                     (verilog-ext-tags-table-push-defs :tag-type 'declarations-no-parens
                                                       :file file
                                                       :start inner-start
                                                       :limit inner-limit
                                                       :parent tag)))))
          ('instances (while (verilog-ext-find-module-instance-fwd limit)
                        (puthash `(,(match-string-no-properties 2)
                                   :file ,file
                                   :line ,(line-number-at-pos))
                                 `(:type ,(match-string-no-properties 1)
                                   :desc ,(verilog-ext-tags-desc)
                                   :col ,(current-column)
                                   :parent ,parent)
                                 verilog-ext-tags-inst-current-file)))
          ('structs (while (setq data (verilog-ext-find-struct))
                      (setq tag (alist-get 'name data))
                      (puthash `(,tag
                                 :file ,file
                                 :line ,(line-number-at-pos))
                               `(:type "struct"
                                 :desc ,(verilog-ext-tags-desc)
                                 :col ,(current-column)
                                 :parent ,parent)
                               verilog-ext-tags-defs-current-file)
                      (save-excursion ; Get struct items
                        (verilog-ext-backward-syntactic-ws)
                        (verilog-ext-tags-table-push-defs :tag-type 'declarations
                                                          :file file
                                                          :start (verilog-ext-pos-at-backward-sexp)
                                                          :limit (point)
                                                          :parent tag))))
          ('classes (while (setq data (verilog-ext-find-class-fwd limit))
                      (setq tag (alist-get 'name data))
                      (puthash `(,tag
                                 :file ,file
                                 :line ,(line-number-at-pos))
                               `(:type "class"
                                 :desc ,(verilog-ext-tags-desc)
                                 :col ,(current-column)
                                 :parent ,parent)
                               verilog-ext-tags-defs-current-file)
                      ;; Get class items
                      (save-excursion
                        (verilog-re-search-backward "\\<class\\>" nil :no-error)
                        (setq inner-start (point))
                        (setq inner-limit (verilog-ext-pos-at-forward-sexp)))
                      (dolist (defs '(declarations-no-parens tf structs))
                        (verilog-ext-tags-table-push-defs :tag-type defs
                                                          :file file
                                                          :start inner-start
                                                          :limit inner-limit
                                                          :parent tag))))
          ('top-items (while (verilog-re-search-forward verilog-ext-top-re nil :no-error)
                        (setq tag (match-string-no-properties 3))
                        (setq type (match-string-no-properties 1))
                        (puthash `(,tag
                                   :file ,file
                                   :line ,(line-number-at-pos))
                                 `(:type ,type
                                   :desc ,(verilog-ext-tags-desc)
                                   :col ,(current-column))
                                 verilog-ext-tags-defs-current-file)
                        ;; Get top-block items
                        (setq inner-start (match-beginning 1))
                        (save-excursion
                          (goto-char inner-start)
                          (setq inner-limit (verilog-ext-pos-at-forward-sexp)))
                        (let ((top-items-defs '(declarations tf structs classes)))
                          (when (string-match "\\<\\(module\\|interface\\)\\>" type)
                            (setq top-items-defs `(,@top-items-defs instances)))
                          (dolist (defs top-items-defs)
                            (verilog-ext-tags-table-push-defs :tag-type defs
                                                              :file file
                                                              :start inner-start
                                                              :limit inner-limit
                                                              :parent tag)))))
          (_ (error "Unsupported tag type")))))))

(defun verilog-ext-tags-table-push-refs (file)
  "Push references inside hash table TABLE.

FILE must be provided for the case when references are fetched from a
temp-buffer."
  (let (tag begin line)
    (save-match-data
      (save-excursion
        (goto-char (point-min))
        (while (verilog-re-search-forward verilog-identifier-sym-re nil :no-error)
          (setq begin (match-beginning 0))
          (setq tag (match-string-no-properties 0))
          (setq line (line-number-at-pos begin))
          (unless (or (member tag verilog-keywords) ; Filter verilog keywords
                      (member tag verilog-ext-compiler-directives)
                      (gethash `(,tag :file ,file :line ,line) verilog-ext-tags-defs-current-file) ; Unless it's already a definition
                      (save-excursion ; Filter bit-width expressions
                        (goto-char begin)
                        (eq (preceding-char) ?')))
            (puthash `(,tag ; Key plist
                       :file ,file
                       :line ,(line-number-at-pos))
                     `(:desc ,(verilog-ext-tags-desc) ; Value plist
                       :col ,(current-column))
                     verilog-ext-tags-refs-current-file)))))))


;;;; Tree-sitter
(defconst verilog-ext-tags-definitions-ts-re
  (eval-when-compile
    (regexp-opt
     '(;; Top blocks
       "module_declaration"
       "interface_declaration"
       "program_declaration"
       "package_declaration"
       ;; Classes
       "class_declaration"
       ;; Tasks/functions
       "function_declaration"
       "task_declaration"
       "class_constructor_declaration"
       ;; Method prototypes
       "function_prototype"
       "task_prototype"
       "class_constructor_prototype"
       ;; Coverage
       "covergroup_declaration"
       ;; Constraints
       "constraint_declaration"
       ;; Ports/arguments
       "ansi_port_declaration"
       "tf_port_item1"
       ;; Variable/net/parameter/type declarations
       "variable_decl_assignment"
       "net_decl_assignment"
       "local_parameter_declaration"
       "parameter_declaration"
       "type_declaration"
       ;; Defines
       "text_macro_definition"
       ;; Enum labels
       "enum_name_declaration"
       ;; Instances
       "module_instantiation"
       "interface_instantiation")
     'symbols))
  "Regexp of tree-sitter node types to be used for tags definitions.

Need to be quoted as symbols to avoid bugs: E.g:
\"list_of_variable_decl_assignment\" would also match
\"variable_decl_assignment\".

Even though \"data_declaration\" would match all declarations it cannot be
reliably used since it is too generic.  For example, it would not allow parsing
of multiple variables declarations in one-line.  The same happens with
\"class_property\" which is already handled by \"variable_decl_assignment\" and
\"net_decl_assignment\".

Even though \"module_instantiation\" and \"interface_instantiation\" are not
declarations, these are only included to add items to the defs table for
completion.")

(defconst verilog-ext-tags-method-declaration-ts-re
  (eval-when-compile
    (regexp-opt '("task_declaration" "function_declaration" "class_constructor_declaration") 'symbols)))

(defun verilog-ext-tags-table-push-defs-ts (file)
  "Push current FILE definitions using tree-sitter.

Update hash tables `verilog-ext-tags-defs-current-file' and
`verilog-ext-tags-inst-current-file'."
  (let* ((node (treesit-buffer-root-node 'verilog))
         (tree (treesit-induce-sparse-tree
                node
                verilog-ext-tags-definitions-ts-re
                nil 1000)))
    (verilog-ext-tags-table-push-defs-ts--recurse :node tree
                                                  :parent nil
                                                  :file file)))

(defun verilog-ext-tags-table-push-defs-ts--parent (ts-node ts-type parent-node)
  "Return parent identifier of TS-NODE.

PARENT-NODE is the default parent for TS-NODE.

TS-TYPE is provided to avoid an additional call to `treesit-node-type' since
this function is synctactic sugar for
`verilog-ext-tags-table-push-defs-ts--recurse'."
  (cond (;; Externally defined methods
         (and (string-match verilog-ext-tags-method-declaration-ts-re ts-type)
              (verilog-ts--node-has-child-recursive ts-node "class_type"))
         (verilog-ts--node-identifier-name (verilog-ts--node-has-child-recursive ts-node "class_identifier")))
        (t ;; Default
         (verilog-ts--node-identifier-name parent-node))))

(cl-defun verilog-ext-tags-table-push-defs-ts--recurse (&key node parent file)
  "Push current FILE definitions recursively using tree-sitter.

Traverse the tree starting at NODE.

PARENT is passed as an argument to build the :items prop list of
`verilog-ext-tags-defs-current-file'."
  (let* ((ts-node (car node))
         (children (cdr node))
         (ts-type (treesit-node-type ts-node))
         (is-instance (and ts-type (string-match verilog-ts-instance-re ts-type)))
         (is-typedef-class (verilog-ts--node-is-typedef-class-p ts-node)))
    ;; Iterate over all the nodes of the tree
    (mapc (lambda (child-node)
            (verilog-ext-tags-table-push-defs-ts--recurse :node child-node
                                                          :parent ts-node
                                                          :file file))
          children)
    ;; Push definitions of current node
    (when (and ts-node (not is-typedef-class)) ; root ts-node will be nil
      (goto-char (treesit-node-start ts-node))
      (if is-instance
          (puthash `(,(verilog-ts--node-instance-name ts-node) ; Key plist
                     :file ,file
                     :line ,(line-number-at-pos))
                   `(:type ,(verilog-ts--node-identifier-name ts-node) ; Value plist
                     :col ,(current-column)
                     :parent ,(verilog-ts--node-identifier-name parent))
                   verilog-ext-tags-inst-current-file)
        (puthash `(,(verilog-ts--node-identifier-name ts-node) ; Key plist
                   :file ,file
                   :line ,(line-number-at-pos))
                 `(:type ,(verilog-ts--node-identifier-type ts-node) ; Value plist
                   :desc ,(verilog-ext-tags-desc)
                   :col ,(current-column)
                   :parent ,(verilog-ext-tags-table-push-defs-ts--parent ts-node ts-type parent))
                 verilog-ext-tags-defs-current-file)))))

(defun verilog-ext-tags-table-push-refs-ts (file)
  "Push current FILE references using tree-sitter.

Update hash table `verilog-ext-tags-refs-current-file'."
  (let (tag pos line)
    (dolist (node (verilog-ts-nodes "simple_identifier"))
      (setq tag (treesit-node-text node :no-prop))
      (setq pos (treesit-node-start node))
      (setq line (line-number-at-pos pos))
      (unless (gethash `(,tag :file ,file :line ,line) verilog-ext-tags-defs-current-file) ; Unless it's already a definition
        (goto-char pos)
        (puthash `(,tag ; Key plist
                   :file ,file
                   :line ,(line-number-at-pos))
                 `(:desc ,(verilog-ext-tags-desc) ; Value plist
                   :col ,(current-column))
                 verilog-ext-tags-refs-current-file)))))


;;;; Tags collection and cache
(defun verilog-ext-tags-proj-init (proj)
  "Initialize value of PROJ variables and hash-tables needed for tags collection."
  (dolist (var '(verilog-ext-tags-file-hashes
                 verilog-ext-tags-defs-file-tables
                 verilog-ext-tags-inst-file-tables
                 verilog-ext-tags-refs-file-tables
                 verilog-ext-tags-defs-table
                 verilog-ext-tags-inst-table
                 verilog-ext-tags-refs-table))
    (unless (verilog-ext-aget (eval var) proj)
      (set var (cons (cons proj (make-hash-table :test 'equal)) (symbol-value var))))))

(defun verilog-ext-tags-get--process-file (file proj &optional file-was-removed verbose)
  "Auxiliary function to process FILE tags of project PROJ.

Steps:
 - Initialize tags variables
 - For removed files, remove corresponding file locs from tags tables
   (FILE-WAS-REMOVED should be non-nil)
 - Check current file hash and compare to previous stored ones to check if it
   has changed
 - Consider 3 different scenarios:
    - File did not change: skip that file and check next one
    - File changed: remove previous file locs, collect new file tags and update
      tables and file hashes
    - File is new: collect new file tags and update tables and file hashes (no
      need to remove any file locs).

Optional arg VERBOSE to display extra messages for debugging."
  (let ((proj-file-hashes (verilog-ext-aget verilog-ext-tags-file-hashes proj))
        (proj-defs-file-tables (verilog-ext-aget verilog-ext-tags-defs-file-tables proj))
        (proj-defs-table (verilog-ext-aget verilog-ext-tags-defs-table proj))
        (proj-inst-file-tables (verilog-ext-aget verilog-ext-tags-inst-file-tables proj))
        (proj-inst-table (verilog-ext-aget verilog-ext-tags-inst-table proj))
        (proj-refs-file-tables (verilog-ext-aget verilog-ext-tags-refs-file-tables proj))
        (proj-refs-table (verilog-ext-aget verilog-ext-tags-refs-table proj))
        file-hash-new file-hash-old)
    ;; Reset current file tags
    (setq verilog-ext-tags-defs-current-file (make-hash-table :test 'equal))
    (setq verilog-ext-tags-inst-current-file (make-hash-table :test 'equal))
    (setq verilog-ext-tags-refs-current-file (make-hash-table :test 'equal))
    ;; Process tags
    (if file-was-removed
        (progn ; Remove tags in reverse order: first locs from the table, then from intermediate tables, and finally from file-hashes
          (verilog-ext-tags-table-remove-file-locs file proj-defs-file-tables proj-defs-table)
          (verilog-ext-tags-table-remove-file-locs file proj-inst-file-tables proj-inst-table)
          (verilog-ext-tags-table-remove-file-locs file proj-refs-file-tables proj-refs-table)
          (remhash file proj-defs-file-tables)
          (remhash file proj-inst-file-tables)
          (remhash file proj-refs-file-tables)
          (remhash file proj-file-hashes))
      ;; File not removed: Could be not modified, modified or added
      (with-temp-buffer
        (insert-file-contents file)
        (setq file-hash-new (secure-hash 'md5 (buffer-substring-no-properties (point-min) (point-max))))
        (setq file-hash-old (gethash file proj-file-hashes))
        (if (string= file-hash-new file-hash-old)
            (when verbose (message "Skipping file: %s" file)) ; Not modified
          ;; Modified/added
          (puthash file file-hash-new proj-file-hashes)
          ;; If file has changed remove old tags
          (when file-hash-old
            (verilog-ext-tags-table-remove-file-locs file proj-defs-file-tables proj-defs-table)
            (verilog-ext-tags-table-remove-file-locs file proj-inst-file-tables proj-inst-table)
            (verilog-ext-tags-table-remove-file-locs file proj-refs-file-tables proj-refs-table))
          ;; If file is new or has changed, collect tags
          (cond (;; Tree-sitter
                 (eq verilog-ext-tags-backend 'tree-sitter)
                 (if verilog-ext-tags-fontify-matches
                     (verilog-ext-with-no-hooks ; Avoid spending time on any possible hooks, just on fontifying to get text properties
                       (verilog-ts-mode)
                       (font-lock-ensure))
                   (treesit-parser-create 'verilog)) ; Not running `verilog-ts-mode' avoids unnecessary hooks for this task
                 (verilog-ext-tags-table-push-defs-ts file)  ; Populates `verilog-ext-tags-defs-current-file' and `verilog-ext-tags-inst-current-file'
                 (verilog-ext-tags-table-push-refs-ts file)) ; Populates `verilog-ext-tags-refs-current-file'
                (;; Builtin
                 (eq verilog-ext-tags-backend 'builtin)
                 (verilog-ext-with-no-hooks
                   (verilog-mode))
                 (when verilog-ext-tags-fontify-matches
                   (font-lock-ensure))
                 (cond (;; Top-block based-file (module/interface/package/program)
                        (save-excursion (verilog-re-search-forward verilog-ext-top-re nil :no-error))
                        (verilog-ext-tags-table-push-defs :tag-type 'top-items :file file))
                       ;; No top-blocks class-based file
                       ((save-excursion (verilog-ext-find-class-fwd))
                        (verilog-ext-tags-table-push-defs :tag-type 'classes :file file))
                       ;; Default,
                       (t (dolist (defs '(declarations tf structs))
                            (verilog-ext-tags-table-push-defs :tag-type defs :file file))))
                 (verilog-ext-tags-table-push-refs file))
                (t ; Fallback error
                 (error "Wrong backend for `verilog-ext-tags-backend'")))
          ;; Update file tables
          (puthash file verilog-ext-tags-defs-current-file proj-defs-file-tables)
          (puthash file verilog-ext-tags-inst-current-file proj-inst-file-tables)
          (puthash file verilog-ext-tags-refs-current-file proj-refs-file-tables)
          ;; Update tables
          (verilog-ext-tags-add-file-locs file proj-defs-file-tables proj-defs-table)
          (verilog-ext-tags-add-file-locs file proj-inst-file-tables proj-inst-table)
          (verilog-ext-tags-add-file-locs file proj-refs-file-tables proj-refs-table))))))

(defun verilog-ext-tags-serialize ()
  "Write variables to their cache files."
  (message "Serializing `verilog-ext' tags cache...")
  (dolist (var `((,verilog-ext-tags-defs-file-tables . ,verilog-ext-tags-defs-file-tables-cache-file)
                 (,verilog-ext-tags-refs-file-tables . ,verilog-ext-tags-refs-file-tables-cache-file)
                 (,verilog-ext-tags-inst-file-tables . ,verilog-ext-tags-inst-file-tables-cache-file)
                 (,verilog-ext-tags-defs-table       . ,verilog-ext-tags-defs-table-cache-file)
                 (,verilog-ext-tags-inst-table       . ,verilog-ext-tags-inst-table-cache-file)
                 (,verilog-ext-tags-refs-table       . ,verilog-ext-tags-refs-table-cache-file)
                 (,verilog-ext-tags-file-hashes      . ,verilog-ext-tags-file-hashes-cache-file)))
    (verilog-ext-serialize (car var) (cdr var)))
  (message "Serialized `verilog-ext' tags cache!"))

(defun verilog-ext-tags-unserialize ()
  "Read cache files into their corresponding variables."
  (message "Unserializing `verilog-ext' tags cache...")
  (dolist (var `((verilog-ext-tags-defs-file-tables . ,verilog-ext-tags-defs-file-tables-cache-file)
                 (verilog-ext-tags-refs-file-tables . ,verilog-ext-tags-refs-file-tables-cache-file)
                 (verilog-ext-tags-inst-file-tables . ,verilog-ext-tags-inst-file-tables-cache-file)
                 (verilog-ext-tags-defs-table       . ,verilog-ext-tags-defs-table-cache-file)
                 (verilog-ext-tags-inst-table       . ,verilog-ext-tags-inst-table-cache-file)
                 (verilog-ext-tags-refs-table       . ,verilog-ext-tags-refs-table-cache-file)
                 (verilog-ext-tags-file-hashes      . ,verilog-ext-tags-file-hashes-cache-file)))
    (set (car var) (verilog-ext-unserialize (cdr var))))
  (message "Unserializing `verilog-ext' tags cache... Done"))

(defun verilog-ext-tags-save-cache ()
  "Save tags cache only if tables have been updated.
Removes serializing and compression processing overhead if no change was made."
  (when verilog-ext-tags-have-been-updated
    (verilog-ext-tags-serialize)))

(defun verilog-ext-tags-clear-cache (&optional all)
  "Clear tags cache files for current project.

With prefix arg, clear cache for ALL projects."
  (interactive "P")
  (if (not all)
      (let ((proj (verilog-ext-buffer-proj)))
        (unless proj
          (user-error "Not in a Verilog project buffer"))
        (verilog-ext-proj-setcdr proj verilog-ext-tags-defs-table nil)
        (verilog-ext-proj-setcdr proj verilog-ext-tags-refs-table nil)
        (verilog-ext-proj-setcdr proj verilog-ext-tags-inst-table nil)
        (verilog-ext-proj-setcdr proj verilog-ext-tags-defs-file-tables nil)
        (verilog-ext-proj-setcdr proj verilog-ext-tags-refs-file-tables nil)
        (verilog-ext-proj-setcdr proj verilog-ext-tags-inst-file-tables nil)
        (verilog-ext-proj-setcdr proj verilog-ext-tags-file-hashes nil)
        (verilog-ext-tags-serialize)
        (message "[%s] Cleared tags cache!" proj))
    (setq verilog-ext-tags-defs-table nil)
    (setq verilog-ext-tags-refs-table nil)
    (setq verilog-ext-tags-inst-table nil)
    (setq verilog-ext-tags-defs-file-tables nil)
    (setq verilog-ext-tags-refs-file-tables nil)
    (setq verilog-ext-tags-inst-file-tables nil)
    (setq verilog-ext-tags-file-hashes nil)
    (verilog-ext-tags-serialize)
    (message "Cleared all projects tags cache!")))

(defun verilog-ext-tags-setup ()
  "Setup tags feature: backend, cache read at startup and write before exit."
  (when verilog-ext-cache-enable
    (verilog-ext-tags-unserialize)
    (add-hook 'kill-emacs-hook #'verilog-ext-tags-save-cache)))

(defun verilog-ext-tags-get (&optional verbose)
  "Get tags of current project.
With current-prefix or VERBOSE, dump output log."
  (interactive "P")
  (let* ((proj (verilog-ext-buffer-proj))
         (files (verilog-ext-proj-files proj))
         (files-removed (seq-difference (map-keys (verilog-ext-aget verilog-ext-tags-file-hashes proj)) files))
         (num-files (+ (length files-removed) (length files)))
         (num-files-processed 0)
         (log-file verilog-ext-tags-cache-log-file)
         (tags-progress-reporter (make-progress-reporter "[Tags collection]: " 0 num-files)))
    (verilog-ext-tags-proj-init proj)
    (when verbose
      (delete-file log-file))
    (dolist (file files-removed)
      (progress-reporter-update tags-progress-reporter num-files-processed (format "[%s]" file))
      (verilog-ext-tags-get--process-file file proj :file-was-removed verbose)
      (setq num-files-processed (1+ num-files-processed)))
    (dolist (file files)
      (when verbose
        (append-to-file (format "(%0d%%) [Tags collection] Processing %s\n" (/ (* num-files-processed 100) num-files) file) nil log-file))
      (progress-reporter-update tags-progress-reporter num-files-processed (format "[%s]" file))
      (verilog-ext-tags-get--process-file file proj nil verbose)
      (setq num-files-processed (1+ num-files-processed)))
    (setq verilog-ext-tags-have-been-updated t)
    (message "Finished collection of tags!")))

(defun verilog-ext-tags-get-async (&optional verbose)
  "Create tags table asynchronously.
With current-prefix or VERBOSE, dump output log."
  (interactive "P")
  (let ((proj-root (verilog-ext-buffer-proj-root)))
    (unless proj-root
      (user-error "Not in a Verilog project buffer"))
    (message "Starting tag collection for %s" proj-root)
    (async-start
     `(lambda ()
        ,(async-inject-variables verilog-ext-tags-async-inject-variables-re)
        (require 'verilog-ext)
        (verilog-ext-tags-unserialize)   ; Read environment in child process
        (verilog-ext-tags-get ,@verbose) ; Update variables in child process
        (verilog-ext-tags-serialize))    ; Update cache file in child process
     (lambda (_result)
       (verilog-ext-tags-unserialize)
       (setq verilog-ext-tags-have-been-updated t)
       (message "Finished collection of tags!"))))) ; Update parent process from cache file


(provide 'verilog-ext-tags)

;;; verilog-ext-tags.el ends here
