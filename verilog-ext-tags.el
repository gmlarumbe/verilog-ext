;;; verilog-ext-tags.el --- Verilog-ext Tags  -*- lexical-binding: t -*-

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

;; Tag collection for jump to definition/reference and semantic completion.

;;; Code:

(require 'verilog-ext-nav)
(require 'verilog-ts-mode)


(defgroup verilog-ext-tags nil
  "Verilog-ext tags."
  :group 'verilog-ext)

(defcustom verilog-ext-tags-backend nil
  "Verilog-ext tags extraction backend."
  :type '(choice (const :tag "Tree-sitter" tree-sitter)
                 (const :tag "Built-in"    builtin))
  :group 'verilog-ext-tags)


;;;; Common
(cl-defun verilog-ext-tags-table-push (&key table tag type desc file parent)
  "Add entry for TAG in hash-table TABLE.

It is needed to provide TYPE, description DESC and FILE properties to add the
entry in the table.

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
        (puthash tag `(:items nil :locs (,(verilog-ext-tags-locs-props type desc file))) table)
      (setq locs-plist (plist-get tag-value :locs))
      (setq loc-new (verilog-ext-tags-locs-props type desc file))
      (unless (member loc-new locs-plist)
        (push loc-new locs-plist)
        (plist-put tag-value :locs locs-plist)
        (puthash tag `(:items ,(plist-get tag-value :items) :locs ,locs-plist) table)))))

(defun verilog-ext-tags-locs-props (type desc &optional file)
  "Return :locs properties for current tag.

These include tag TYPE, description DESC, the FILE and current line."
  `(:type ,type
    :desc ,desc
    :file ,(or file buffer-file-name)
    :line ,(line-number-at-pos)))

(defun verilog-ext-tags-desc ()
  "Return string description for tag at point.

The descriptin determines what `xref' will show when a match is found."
  (string-trim (buffer-substring-no-properties (line-beginning-position) (line-end-position))))

(defun verilog-ext-tags-is-def-p (tag defs-table file pos)
  "Return non-nil if TAG is a definition in DEFS-TABLE.

TAG is a definition if:
 1) It is present in DEFS-TABLE
 2) Its entry property list in DEFS-TABLE has the same :file and :line values

Use FILE and POS arguments for comparison."
  (let (existing-def existing-def-props)
    (and defs-table
         (setq existing-def (gethash tag defs-table))
         (setq existing-def-props (plist-get existing-def :locs))
         (progn (catch 'exit
                  (dolist (prop-list existing-def-props)
                    (when (and (eq (plist-get prop-list :file) file)
                               (eq (plist-get prop-list :line) (line-number-at-pos pos)))
                      (throw 'exit t))))))))


;;;; Builtin
(cl-defun verilog-ext-tags-table-push-defs (&key tag-type table file start limit parent inst-table)
  "Push definitions of TAG-TYPE inside hash table TABLE.

FILE might be specified for the cases when a temp-buffer without an associated
file is being parsed.

Limit search between START and LIMIT if provided, otherwise search the whole
buffer.

PARENT is the module where TAG is defined/instantiated for dot completion.

INST-TABLE is the instances table, needed to separate between tags for
completion and navigation."
  (let ((ignore-paren-decl (eq tag-type 'declarations-no-parens))
        (inst-table (or inst-table (make-hash-table :test #'equal)))
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
                             (verilog-ext-tags-table-push :table table
                                                          :tag tag
                                                          :type type
                                                          :desc (verilog-ext-tags-desc)
                                                          :file file
                                                          :parent parent))))
          ('tf (while (setq data (verilog-ext-find-function-task-fwd limit))
                 (setq tag (match-string-no-properties 1))
                 (verilog-ext-tags-table-push :table table
                                              :tag tag
                                              :type (alist-get 'type data)
                                              :desc (verilog-ext-tags-desc)
                                              :file file
                                              :parent parent)
                 (save-excursion ; Get tasks and function declarations
                   (when (< (setq inner-start (alist-get 'pos data))
                            (setq inner-limit (save-excursion
                                                (verilog-re-search-backward "\\<\\(function\\|task\\)\\>" (line-beginning-position) :no-error)
                                                (verilog-ext-pos-at-forward-sexp))))
                     (verilog-ext-tags-table-push-defs :tag-type 'declarations-no-parens
                                                       :table table
                                                       :file file
                                                       :start inner-start
                                                       :limit inner-limit
                                                       :parent tag)))))
          ('instances (while (verilog-ext-find-module-instance-fwd limit)
                        (verilog-ext-tags-table-push :table inst-table
                                                     :tag (match-string-no-properties 2)
                                                     :type (match-string-no-properties 1)
                                                     :desc (verilog-ext-tags-desc)
                                                     :file file
                                                     :parent parent)))
          ('structs (while (setq data (verilog-ext-find-struct))
                      (setq tag (alist-get 'name data))
                      (verilog-ext-tags-table-push :table table
                                                   :tag tag
                                                   :type "struct"
                                                   :desc (verilog-ext-tags-desc)
                                                   :file file
                                                   :parent parent)
                      (save-excursion ; Get struct items
                        (verilog-ext-backward-syntactic-ws)
                        (verilog-ext-tags-table-push-defs :tag-type 'declarations
                                                          :table table
                                                          :file file
                                                          :start (verilog-ext-pos-at-backward-sexp)
                                                          :limit (point)
                                                          :parent tag))))
          ('classes (while (setq data (verilog-ext-find-class-fwd limit))
                      (setq tag (alist-get 'name data))
                      (verilog-ext-tags-table-push :table table
                                                   :tag tag
                                                   :type "class"
                                                   :desc (verilog-ext-tags-desc)
                                                   :file file
                                                   :parent parent)
                      ;; Get class items
                      (save-excursion
                        (verilog-re-search-backward "\\<class\\>" nil :no-error)
                        (setq inner-start (point))
                        (setq inner-limit (verilog-ext-pos-at-forward-sexp)))
                      (dolist (defs '(declarations-no-parens tf structs))
                        (verilog-ext-tags-table-push-defs :tag-type defs
                                                          :table table
                                                          :file file
                                                          :start inner-start
                                                          :limit inner-limit
                                                          :parent tag))))
          ('top-items (while (verilog-re-search-forward verilog-ext-top-re nil :no-error)
                        (setq tag (match-string-no-properties 3))
                        (setq type (match-string-no-properties 1))
                        (verilog-ext-tags-table-push :table table
                                                     :tag tag
                                                     :type type
                                                     :desc (verilog-ext-tags-desc)
                                                     :file file)
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
                                                              :table table
                                                              :file file
                                                              :start inner-start
                                                              :limit inner-limit
                                                              :parent tag
                                                              :inst-table inst-table)))))
          (_ (error "Unsupported tag type")))))))

(cl-defun verilog-ext-tags-table-push-refs (&key table defs-table file start limit)
  "Push references inside hash table TABLE.

Table DEFS-TABLE is used to filter out references that have already been parsed
as definitions.

FILE can be provided for the case when references are fetched from a
temp-buffer.

Limit search between START and LIMIT if provided, otherwise search the whole
buffer."
  (let (tag begin)
    (unless start (setq start (point-min)))
    (unless limit (setq limit (point-max)))
    (save-match-data
      (save-excursion
        (goto-char start)
        (while (verilog-re-search-forward verilog-identifier-sym-re limit :no-error)
          (setq begin (match-beginning 0))
          (setq tag (match-string-no-properties 0))
          (unless (or (member tag verilog-keywords) ; Filter verilog keywords
                      (and defs-table ; Filter existing definitions
                           (verilog-ext-tags-is-def-p tag defs-table file (point)))
                      (save-excursion ; Filter bit-width expressions
                        (goto-char begin)
                        (eq (preceding-char) ?')))
            (verilog-ext-tags-table-push :table table
                                         :tag tag
                                         :desc (verilog-ext-tags-desc)
                                         :file file)))))))


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
       "type_declaration"
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

(cl-defun verilog-ext-tags-table-push-defs-ts (&key table inst-table file)
  "Push definitions inside hash table TABLE using tree-sitter.

FILE might be specified for the cases when a temp-buffer without an associated
file is being parsed.

INST-TABLE is the instances table, needed to separate between tags for
completion and navigation."
  (let* ((node (treesit-buffer-root-node 'verilog))
         (tree (treesit-induce-sparse-tree
                node
                verilog-ext-tags-definitions-ts-re
                nil 1000))
         (inst-table (or inst-table (make-hash-table :test #'equal))))
    (verilog-ext-tags-table-push-defs-ts--recurse :table table
                                                  :inst-table inst-table
                                                  :node tree
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

(cl-defun verilog-ext-tags-table-push-defs-ts--recurse (&key table inst-table node parent file)
  "Push definitions recursively inside hash table TABLE using tree-sitter.

Traverse the tree starting at NODE.

PARENT is passed as an argument to build the :items prop list of TABLE.

FILE might be specified for the cases when a temp-buffer without an associated
file is being parsed.

INST-TABLE is the instances table, needed to separate between tags for
completion and navigation."
  (let* ((ts-node (car node))
         (children (cdr node))
         (ts-type (treesit-node-type ts-node))
         (is-instance (and ts-type (string-match "\\(module\\|interface\\)_instantiation" ts-type))))
    ;; Iterate over all the nodes of the tree
    (mapc (lambda (child-node)
            (verilog-ext-tags-table-push-defs-ts--recurse :table table
                                                          :inst-table inst-table
                                                          :node child-node
                                                          :parent ts-node
                                                          :file file))
          children)
    ;; Push definitions of current node
    (when ts-node ; root ts-node will be nil
      (goto-char (treesit-node-start ts-node))
      (if is-instance
          (verilog-ext-tags-table-push :table inst-table
                                       :tag (verilog-ts--node-instance-name ts-node)
                                       :type (verilog-ts--node-identifier-name ts-node)
                                       :file file
                                       :parent (verilog-ts--node-identifier-name parent))
        (verilog-ext-tags-table-push :table table
                                     :tag (verilog-ts--node-identifier-name ts-node)
                                     :type (verilog-ts--node-identifier-type ts-node)
                                     :desc (verilog-ext-tags-desc)
                                     :file file
                                     :parent (verilog-ext-tags-table-push-defs-ts--parent ts-node ts-type parent))))))

(cl-defun verilog-ext-tags-table-push-refs-ts (&key table defs-table file)
  "Push references inside hash table TABLE using tree-sitter.

Optional definitions table DEFS-TABLE is used to filter out references that have
already been parsed as definitions.

FILE can be provided for the case when references are fetched from a
temp-buffer."
  (let (tag pos)
    (dolist (node (verilog-ts-nodes "simple_identifier"))
      (setq tag (treesit-node-text node :no-prop))
      (setq pos (treesit-node-start node))
      (unless (and defs-table
                   (verilog-ext-tags-is-def-p tag defs-table file pos))
        (goto-char pos)
        (verilog-ext-tags-table-push :table table
                                     :tag tag
                                     :desc (verilog-ext-tags-desc)
                                     :file file)))))

;;;; Setup
(defun verilog-ext-tags-setup ()
  "Setup tags backend depending on tree-sitter availability.
If it has been set before, keep its value."
  (let ((backend (or verilog-ext-tags-backend
                     (if (and (treesit-available-p)
                              (treesit-language-available-p 'verilog))
                         'tree-sitter
                       'builtin))))
    (setq verilog-ext-tags-backend backend)))


(provide 'verilog-ext-tags)

;;; verilog-ext-tags.el ends here
