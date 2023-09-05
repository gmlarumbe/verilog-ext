;;; verilog-ts-mode.el --- Verilog Tree-sitter major mode  -*- lexical-binding: t -*-

;; Copyright (C) 2022-2023 Gonzalo Larumbe

;; Author: Gonzalo Larumbe <gonzalomlarumbe@gmail.com>
;; URL: https://github.com/gmlarumbe/verilog-ext
;; Version: 0.0.0
;; Keywords: Verilog, IDE, Tools
;; Package-Requires: ((emacs "29.1"))

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

;; Major mode to navigate and edit SystemVerilog files with tree-sitter.
;;
;; Provides tree-sitter based implementations for the following features:
;; - Syntax highlighting
;; - Indentation
;; - `imenu'
;; - `'which-func'
;; - Navigation functions
;; - Prettify and beautify
;; - Completion at point
;;
;; Package info:
;;  - https://github.com/gmlarumbe/verilog-ext#tree-sitter
;;
;; Setup instructions:
;;  - https://github.com/gmlarumbe/verilog-ext/wiki/Tree-sitter
;;
;; Contributions:
;;   This major mode is still under active development!
;;   If you wish to contribute, please do so in the following repo:
;;     - https://github.com/gmlarumbe/verilog-ext
;;   Check contributing guidelines:
;;     - https://github.com/gmlarumbe/verilog-ext#contributing

;;; Code:

;;; Requirements

(require 'treesit)
(require 'verilog-mode)

(declare-function treesit-parser-create "treesit.c")
(declare-function treesit-induce-sparse-tree "treesit.c")
(declare-function treesit-node-parent "treesit.c")
(declare-function treesit-node-start "treesit.c")
(declare-function treesit-node-end "treesit.c")
(declare-function treesit-node-child "treesit.c")
(declare-function treesit-node-child-by-field-name "treesit.c")
(declare-function treesit-node-type "treesit.c")


;;; Customization
(defgroup verilog-ts nil
  "SystemVerilog tree-sitter mode."
  :group 'languages)

(defcustom verilog-ts-indent-level 4
  "Tree-sitter indentation of Verilog statements with respect to containing block."
  :group 'verilog-ts
  :type 'integer)

(defcustom verilog-ts-file-extension-re "\\.s?vh?\\'"
  "(SystemVerilog) file extensions.
Defaults to .v, .vh, .sv and .svh."
  :group 'verilog-ts
  :type 'string)


;;; Utils
;;;; Core
(defconst verilog-ts-instance-re "\\(module\\|interface\\)_instantiation")

(defun verilog-ts--node-at-point ()
  "Return tree-sitter node at point."
  (treesit-node-at (point) 'verilog))

(defun verilog-ts--node-has-parent-recursive (node node-type)
  "Return non-nil if NODE is part of NODE-TYPE in the parsed tree."
  (treesit-parent-until
   node
   (lambda (node) ; Third argument must be a function
     (string-match node-type (treesit-node-type node)))))

(defun verilog-ts--node-has-child-recursive (node node-type)
  "Return first node of type NODE-TYPE that is a child of NODE in the parsed tree.
If none is found, return nil."
  (treesit-search-subtree node node-type))

(defun verilog-ts--node-identifier-name (node)
  "Return identifier name of NODE."
  (when node
    (cond ((string-match "class_constructor" (treesit-node-type node))
           "new")
          ((string-match "class_method" (treesit-node-type node))
           (or (treesit-node-text (treesit-search-subtree node "\\(function\\|task\\)_identifier") :no-prop)
               "new"))
          ((string-match "\\(function\\|task\\)_declaration" (treesit-node-type node))
           (treesit-node-text (treesit-search-subtree node "\\(function\\|task\\)_identifier") :no-prop))
          (t
           (treesit-node-text (treesit-search-subtree node "simple_identifier") :no-prop)))))

(defun verilog-ts--node-instance-name (node)
  "Return identifier name of NODE.

Node must be of type `verilog-ts-instance-re' Otherwise return nil."
  (unless (and node (string-match verilog-ts-instance-re (treesit-node-type node)))
    (error "Wrong node type: %s" (treesit-node-type node)))
  (treesit-node-text (treesit-search-subtree node "instance_identifier") :no-prop))

(defun verilog-ts--highest-node-at-pos (pos)
  "Return highest node starting at POS in the parsed tree.

Only might work as expected if point is at the beginning of a symbol.

Snippet fetched from `treesit--indent-1'."
  (let* ((smallest-node (verilog-ts--node-at-point))
         (node (treesit-parent-while
                smallest-node
                (lambda (node)
                  (eq pos (treesit-node-start node))))))
    node))

(defun verilog-ts--highest-node-at-symbol ()
  "Return highest node in the hierarchy for symbol at point.
Check also `treesit-thing-at-point' for similar functionality."
  (verilog-ts--highest-node-at-pos (car (bounds-of-thing-at-point 'symbol))))

(defun verilog-ts--node-at-bol ()
  "Return node at first non-blank character of current line.
Snippet fetched from `treesit--indent-1'."
  (let* ((bol (save-excursion
                (forward-line 0)
                (skip-chars-forward " \t")
                (point)))
         (smallest-node
          (cond ((null (treesit-parser-list)) nil)
                ((eq 1 (length (treesit-parser-list)))
                 (treesit-node-at bol))
                ((treesit-language-at (point))
                 (treesit-node-at bol (treesit-language-at (point))))
                (t (treesit-node-at bol))))
         (node (treesit-parent-while
                smallest-node
                (lambda (node)
                  (eq bol (treesit-node-start node))))))
    node))

(defun verilog-ts-nodes (pred &optional start)
  "Return current buffer NODES that match PRED.

If optional arg START is non-nil, use it as the initial node to search in the
tree."
  (let ((root-node (or start (treesit-buffer-root-node))))
    (mapcar #'car (cdr (treesit-induce-sparse-tree root-node pred)))))

(defun verilog-ts-nodes-props (pred &optional start)
  "Return nodes and properties that satisfy PRED in current buffer.

If optional arg START is non-nil, use it as the initial node to search in the
tree.

Returned properties are a property list that include node name, start position
and end position."
  (mapcar (lambda (node)
            `(,node :name ,(verilog-ts--node-identifier-name node)
                    :start-pos ,(treesit-node-start node)
                    :end-pos ,(treesit-node-end node)))
          (verilog-ts-nodes pred start)))

(defun verilog-ts--inside-module-or-interface-p ()
  "Return non-nil if point is inside a module or interface construct."
  (verilog-ts--node-has-parent-recursive (verilog-ts--node-at-point) "\\(module\\|interface\\)_declaration"))

;;;; Context
(defconst verilog-ts-block-at-point-re
  (eval-when-compile
    (regexp-opt
     '("module_declaration"
       "interface_declaration"
       "program_declaration"
       "package_declaration"
       "class_declaration"
       "function_declaration"
       "task_declaration"
       "class_constructor_declaration"
       "module_instantiation"
       "interface_instantiation"
       "always_construct"
       "initial_construct"
       "final_construct"
       "generate_region"
       "seq_block")
     'symbols)))


(defun verilog-ts-module-at-point ()
  "Return node of module at point."
  (verilog-ts--node-has-parent-recursive (verilog-ts--node-at-point) "module_declaration"))

(defun verilog-ts-instance-at-point ()
  "Return node of instance at point."
  (verilog-ts--node-has-parent-recursive (verilog-ts--node-at-point) verilog-ts-instance-re))

(defun verilog-ts-block-at-point ()
  "Return node of block at point."
  (verilog-ts--node-has-parent-recursive (verilog-ts--node-at-point) verilog-ts-block-at-point-re))

(defun verilog-ts-nodes-block-at-point (pred)
  "Return block at point NODES that match PRED."
  (let ((block (verilog-ts-block-at-point)))
    (when block
      (mapcar #'car (cdr (treesit-induce-sparse-tree block pred))))))

(defun verilog-ts-search-node-block-at-point (pred &optional backward all)
  "Search forward for node matching PRED inside block at point.

By default, only search for named nodes, but if ALL is non-nil, search
for all nodes.  If BACKWARD is non-nil, search backwards."
  (treesit-search-forward (verilog-ts--node-at-point)
                          (lambda (node)
                            (and (string-match pred (treesit-node-type node))
                                 (< (treesit-node-end node) (treesit-node-end (verilog-ts-block-at-point)))))
                          backward
                          all))

;; Some examples using previous API
(defun verilog-ts-module-declarations-nodes-current-buffer ()
  "Return module declaration nodes of current file."
  (verilog-ts-nodes "module_declaration"))

(defun verilog-ts-module-declarations-current-buffer ()
  "Return module declaration names of current file."
  (mapcar (lambda (node-and-props)
            (plist-get (cdr node-and-props) :name))
          (verilog-ts-nodes-props "module_declaration")))

(defun verilog-ts-module-instances-nodes (module-node)
  "Return instance nodes of MODULE-NODE."
  (unless (and module-node (string= "module_declaration" (treesit-node-type module-node)))
    (error "Wrong module-node: %s" module-node))
  (verilog-ts-nodes verilog-ts-instance-re module-node))

(defun verilog-ts-module-instances (module-node)
  "Return instances of MODULE-NODE."
  (unless (and module-node (string= "module_declaration" (treesit-node-type module-node)))
    (error "Wrong module-node: %s" module-node))
  (mapcar (lambda (node-and-props)
            (plist-get (cdr node-and-props) :name))
          (verilog-ts-nodes-props verilog-ts-instance-re module-node)))

(defun verilog-ts-module-always-blocks (module-node)
  "Return always blocks of MODULE-NODE."
  (unless (and module-node (string= "module_declaration" (treesit-node-type module-node)))
    (error "Wrong module-node: %s" module-node))
  (mapcar (lambda (node-and-props)
            (plist-get (cdr node-and-props) :name))
          (verilog-ts-nodes-props "always_keyword" module-node)))

(defun verilog-ts-class-properties (class-node)
  "Return properties of CLASS-NODE."
  (unless (and class-node (string= "class_declaration" (treesit-node-type class-node)))
    (error "Wrong class-node: %s" class-node))
  (mapcar (lambda (node-and-props)
            (plist-get (cdr node-and-props) :name))
          (verilog-ts-nodes-props "class_property" class-node)))

(defun verilog-ts-class-methods (class-node)
  "Return methods of CLASS-NODE."
  (unless (and class-node (string= "class_declaration" (treesit-node-type class-node)))
    (error "Wrong class-node: %s" class-node))
  (mapcar (lambda (node-and-props)
            (plist-get (cdr node-and-props) :name))
          (verilog-ts-nodes-props "class_\\(constructor\\|method\\)" class-node)))

(defun verilog-ts-class-constraints (class-node)
  "Return constraints of CLASS-NODE."
  (unless (and class-node (string= "class_declaration" (treesit-node-type class-node)))
    (error "Wrong class-node: %s" class-node))
  (mapcar (lambda (node-and-props)
            (plist-get (cdr node-and-props) :name))
          (verilog-ts-nodes-props "constraint_declaration" class-node)))



;;;; Navigation
(defun verilog-ts-forward-sexp (&optional arg)
  "Move forward across S-expressions.

With `prefix-arg', move ARG expressions."
  (interactive "p")
  (if (member (following-char) '(?\( ?\{ ?\[))
      (if (and arg (< arg 0))
          (backward-sexp arg)
        (forward-sexp arg))
    (let* ((node (verilog-ts--highest-node-at-symbol))
           (beg (treesit-node-start node))
           (end (treesit-node-end node)))
      (if (and arg (< arg 0))
          (goto-char beg)
        (goto-char end)))))

(defun verilog-ts-backward-sexp (&optional arg)
  "Move backward across S-expressions.

With `prefix-arg', move ARG expressions."
  (interactive "p")
  (if (member (preceding-char) '(?\) ?\} ?\]))
      (if (and arg (< arg 0))
          (forward-sexp arg)
        (backward-sexp arg))
    (let* ((node (treesit-node-parent (verilog-ts--node-at-point)))
           (beg (treesit-node-start node))
           (end (treesit-node-end node)))
      (if (and arg (< arg 0))
          (goto-char end)
        (goto-char beg)))))


;;; Font-lock
;;;; Faces
(defgroup verilog-ts-faces nil
  "Verilog-ts faces."
  :group 'verilog-ts)

(defvar verilog-ts-font-lock-grouping-keywords-face 'verilog-ts-font-lock-grouping-keywords-face)
(defface verilog-ts-font-lock-grouping-keywords-face
  '((t (:inherit font-lock-misc-punctuation-face)))
  "Face for grouping keywords: begin, end."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-punctuation-face 'verilog-ts-font-lock-punctuation-face)
(defface verilog-ts-font-lock-punctuation-face
  '((t (:inherit font-lock-punctuation-face)))
  "Face for punctuation symbols, e.g:
!,;:?'=<>*"
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-operator-face 'verilog-ts-font-lock-operator-face)
(defface verilog-ts-font-lock-operator-face
  '((t (:inherit font-lock-operator-face)))
  "Face for operator symbols, such as &^~+-/|."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-brackets-face 'verilog-ts-font-lock-brackets-face)
(defface verilog-ts-font-lock-brackets-face
  '((t (:inherit font-lock-bracket-face)))
  "Face for brackets []."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-parenthesis-face 'verilog-ts-font-lock-parenthesis-face)
(defface verilog-ts-font-lock-parenthesis-face
  '((t (:inherit font-lock-bracket-face)))
  "Face for parenthesis ()."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-curly-braces-face 'verilog-ts-font-lock-curly-braces-face)
(defface verilog-ts-font-lock-curly-braces-face
  '((t (:inherit font-lock-bracket-face)))
  "Face for curly braces {}."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-port-connection-face 'verilog-ts-font-lock-port-connection-face)
(defface verilog-ts-font-lock-port-connection-face
  '((t (:inherit font-lock-constant-face)))
  "Face for port connections of instances.
.portA (signalA),
.portB (signalB)
);"
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-dot-name-face 'verilog-ts-font-lock-dot-name-face)
(defface verilog-ts-font-lock-dot-name-face
  '((t (:inherit font-lock-property-name-face)))
  "Face for dot-name regexps:
- Interface signals, classes attributes/methods and hierarchical refs.

axi_if.Ready <= 1'b1;
obj.method();"
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-brackets-content-face 'verilog-ts-font-lock-brackets-content-face)
(defface verilog-ts-font-lock-brackets-content-face
  '((t (:inherit font-lock-number-face)))
  "Face for content between brackets: arrays, bit vector width and indexing."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-width-num-face 'verilog-ts-font-lock-width-num-face)
(defface verilog-ts-font-lock-width-num-face
  '((t (:inherit font-lock-number-face)))
  "Face for the bit width number expressions.
{1}'b1,
{4}'hF,
{3}'o7,"
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-width-type-face 'verilog-ts-font-lock-width-type-face)
(defface verilog-ts-font-lock-width-type-face
  '((t (:inherit font-lock-builtin-face)))
  "Face for the bit width type expressions.
1'{b}1,
4'{h}F,
3'{o}7,"
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-module-face 'verilog-ts-font-lock-module-face)
(defface verilog-ts-font-lock-module-face
  '((t (:inherit font-lock-function-call-face)))
  "Face for module names."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-instance-face 'verilog-ts-font-lock-instance-face)
(defface verilog-ts-font-lock-instance-face
  '((t (:inherit font-lock-variable-use-face)))
  "Face for instance names."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-time-event-face 'verilog-ts-font-lock-time-event-face)
(defface verilog-ts-font-lock-time-event-face
  '((t (:inherit font-lock-property-name-face)))
  "Face for time-events: @ and #."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-time-unit-face 'verilog-ts-font-lock-time-unit-face)
(defface verilog-ts-font-lock-time-unit-face
  '((t (:inherit font-lock-property-use-face)))
  "Face for time-units: ms, us, ns, ps, fs (delays and timescale/timeprecision)."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-preprocessor-face 'verilog-ts-font-lock-preprocessor-face)
(defface verilog-ts-font-lock-preprocessor-face
  '((t (:inherit font-lock-preprocessor-face)))
  "Face for preprocessor compiler directives (`include, `define, UVM macros...)."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-modport-face 'verilog-ts-font-lock-modport-face)
(defface verilog-ts-font-lock-modport-face
  '((t (:inherit font-lock-type-face)))
  "Face for interface modports."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-direction-face 'verilog-ts-font-lock-direction-face)
(defface verilog-ts-font-lock-direction-face
  '((t (:inherit font-lock-keyword-face)))
  "Face for direction of ports/functions/tasks args."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-translate-off-face 'verilog-ts-font-lock-translate-off-face)
(defface verilog-ts-font-lock-translate-off-face
  '((t (:slant italic)))
  "Face for pragmas between comments, e.g:
* translate_off / * translate_on"
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-attribute-face 'verilog-ts-font-lock-attribute-face)
(defface verilog-ts-font-lock-attribute-face
  '((t (:inherit font-lock-property-name-face)))
  "Face for RTL attributes."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-error-face 'verilog-ts-font-lock-error-face)
(defface verilog-ts-font-lock-error-face
  '((t (:underline (:style wave :color "Red1"))))
  "Face for tree-sitter parsing errors."
  :group 'verilog-ts-faces)


;;;; Keywords
;; There are some keywords that are not recognized by tree-sitter grammar.
;; For these ones, use regexp matching patterns inside tree-sitter (:match "^foo$")
(defconst verilog-ts-keywords
  '("alias" "and" "assert" "assign" "assume" "before" "binsof" "break" "case"
    "checker" "class" "class" "clocking" "config" "const" "constraint" "cover"
    "covergroup" "coverpoint" "cross" "default" "defparam" "disable" "do" "else"
    "endcase" "endchecker" "endclass" "endclocking" "endconfig" "endfunction"
    "endgenerate" "endgroup" "endinterface" "endmodule" "endpackage"
    "endprogram" "endproperty" "endsequence" "endtask" "enum" "extends" "extern"
    "final" "first_match" "for" "foreach" "forever" "fork" "forkjoin" "function"
    "generate" "genvar" "if" "iff" "illegal_bins" "implements" "import"
    "initial" "inside" "interconnect" "interface" "intersect" "join" "join_any"
    "join_none" "local" "localparam" "modport" "new" "null" "option" "or"
    "package" "packed" "parameter" "program" "property" "pure" "randomize"
    "repeat" "return" "sequence" "showcancelled" "soft" "solve" "struct" "super"
    "tagged" "task" "timeprecision" "timeunit" "type" "typedef" "union" "unique"
    "virtual" "wait" "while" "with"
    (always_keyword)       ; always, always_comb, always_latch, always_ff
    (bins_keyword)         ; bins, illegal_bins, ignore_bins
    (case_keyword)         ; case, casez, casex
    (class_item_qualifier) ; static, protected, local
    (edge_identifier)      ; posedge, negedge, edge
    (lifetime)             ; static, automatic
    (module_keyword)       ; module, macromodule
    (random_qualifier)     ; rand, randc
    (unique_priority)))    ; unique, unique0, priority

(defconst verilog-ts-operators-arithmetic
  '("+" "-" "*" "/" "%" "**"))

(defconst verilog-ts-operators-relational
  '("<" "<=" ">" ">="))

(defconst verilog-ts-operators-equality
  '("===" "!==" "==" "!="))

(defconst verilog-ts-operators-logical
  '("&&" "||" "!"))

(defconst verilog-ts-operators-bitwise
  '("~" "&" "~&" "|" "~|" "^" "~^"))

(defconst verilog-ts-operators-shift
  '("<<" ">>" "<<<" ">>>"))

(defconst verilog-ts-punctuation
  '(";" ":" "," "::"
    "=" "?" "|=" "&=" "^="
    "|->" "|=>" "->"
    (inc_or_dec_operator) ; ++, --
    ":=" ":/" "-:" "+:"))

(defconst verilog-ts-directives
  '("directive_include" "directive_define" "directive_ifdef" "directive_ifndef"
    "directive_timescale" "directive_default_nettype" "directive_elsif"
    "directive_undef" "directive_resetall" "directive_undefineall" "directive_endif"
    "directive_else" "directive_unconnected_drive" "directive_celldefine"
    "directive_endcelldefine" "directive_end_keywords" "directive_unconnected_drive"
    "directive_line" "directive_begin_keywords"))


;;;; Functions
(defun verilog-ts--fontify-width-num (node override start end &rest _)
  "Fontify an identifier node if it is a variable.
Don't fontify if it is a function identifier.  For NODE,
OVERRIDE, START, END, and ARGS, see `treesit-font-lock-rules'."
  (let* ((text (treesit-node-text node))
         (apostrophe-offset (string-match "'" text))
         (type-offset (string-match "[hHdDxXbBoO]" text))
         apostrophe-pos type-pos)
    (when (and apostrophe-offset type-offset)
      (setq apostrophe-pos (+ (treesit-node-start node) apostrophe-offset))
      (setq type-pos (+ (treesit-node-start node) type-offset))
      ;; Width
      (treesit-fontify-with-override
       (treesit-node-start node) apostrophe-pos
       'verilog-ts-font-lock-width-num-face
       override start end)
      ;; Apostrophe
      (treesit-fontify-with-override
       apostrophe-pos (1+ apostrophe-pos)
       'verilog-ts-font-lock-punctuation-face
       override start end)
      ;; Radix
      (treesit-fontify-with-override
       type-pos (1+ type-pos)
       'verilog-ts-font-lock-width-type-face
       override start end))))

;;;; Treesit-settings
(defvar verilog-ts--treesit-settings
  (treesit-font-lock-rules
   :feature 'comment
   :language 'verilog
   '((comment) @font-lock-comment-face)

   :feature 'string
   :language 'verilog
   '((string_literal) @font-lock-string-face
     (double_quoted_string) @font-lock-string-face)

   :feature 'error
   :language 'verilog
   '((ERROR) @verilog-ts-font-lock-error-face)

   :feature 'all
   :language 'verilog
   '(;; Arrays
     ((packed_dimension
       (constant_range) @verilog-ts-font-lock-brackets-content-face))
     ((unpacked_dimension
       (constant_range) @verilog-ts-font-lock-brackets-content-face))
     (select1
      (constant_range) @verilog-ts-font-lock-brackets-content-face)
     ((unpacked_dimension
       (constant_expression) @verilog-ts-font-lock-brackets-content-face))
     (bit_select1
      (expression) @verilog-ts-font-lock-brackets-content-face)
     (constant_select1
      (constant_expression) @verilog-ts-font-lock-brackets-content-face)
     (constant_bit_select1
      (constant_expression) @verilog-ts-font-lock-brackets-content-face)
     (indexed_range
      (expression) @verilog-ts-font-lock-brackets-content-face
      (constant_expression) @verilog-ts-font-lock-brackets-content-face)
     ;; Timeunit
     ((time_unit) @font-lock-constant-face)
     ;; Enum labels
     (enum_name_declaration
      (enum_identifier
       (simple_identifier) @font-lock-constant-face))
     ;; Parameters
     (parameter_value_assignment
      (list_of_parameter_assignments
       (named_parameter_assignment
        (parameter_identifier (simple_identifier) @verilog-ts-font-lock-port-connection-face))))
     (ordered_parameter_assignment ; Ordered parameters (e.g. parameterized class type declaration)
      (_ordered_parameter_assignment
       (data_type (simple_identifier) @verilog-ts-font-lock-port-connection-face)))
     ;; Interface signals (members)
     (expression
      (primary
       (simple_identifier) @verilog-ts-font-lock-dot-name-face
       (select1
        (member_identifier
         (simple_identifier)))))
     ;; Interface signals with index
     (expression
      (primary
       (simple_identifier) @verilog-ts-font-lock-dot-name-face
       (constant_bit_select1)))
     ;; Case item label (not radix)
     (case_item_expression
      (expression
       (primary (simple_identifier) @font-lock-constant-face)))
     ;; Attributes
     (["(*" "*)"] @font-lock-constant-face)
     (attribute_instance
      (attr_spec (simple_identifier) @verilog-ts-font-lock-attribute-face))
     ;; Typedefs
     (type_declaration
      (simple_identifier) @font-lock-constant-face)
     ("typedef" "class" (simple_identifier) @font-lock-constant-face)
     ;; Coverpoint & cross labels
     (cover_point
      (cover_point_identifier (simple_identifier) @font-lock-constant-face))
     (cover_cross
      (cross_identifier (simple_identifier) @font-lock-constant-face))
     ;; Loop variables (foreach[i])
     (loop_variables1
      (index_variable_identifier
       (index_variable_identifier (simple_identifier) @font-lock-constant-face)))
     ;; inside {[min_range:max_range]}
     ((open_value_range
       (value_range
        (expression) @font-lock-constant-face)))
     ;; Bins values
     ((bins_or_options
       (expression
        (primary
         (concatenation
          (expression) @font-lock-constant-face)))))
     ;; Bins ranges
     ((covergroup_value_range
       (expression) @font-lock-constant-face))
     ;; Queue dimension
     (("$") @font-lock-constant-face)
     ;; Numbers with radix (4'hF)
     ((integral_number) @verilog-ts--fontify-width-num))

   :feature 'keyword
   :language 'verilog
   `((["begin" "end" "this"] @verilog-ts-font-lock-grouping-keywords-face)
     ([,@verilog-ts-keywords] @font-lock-keyword-face)
     ;; INFO: Still not well implemented in the grammar (new as a method call without and with arguments)
     (expression ; W/o args
      (primary (simple_identifier) @font-lock-keyword-face)
      (:match "^new$" @font-lock-keyword-face))
     (subroutine_call ; With args
      (tf_call (simple_identifier) @font-lock-keyword-face)
      (:match "^new$" @font-lock-keyword-face))
     (primary
      (let_expression (simple_identifier) @font-lock-keyword-face)
      (:match "^new$" @font-lock-keyword-face)))

   :feature 'operator
   :language 'verilog
   `(;; INFO: Some of these might be redundant
     ([,@verilog-ts-operators-arithmetic] @verilog-ts-font-lock-operator-face)
     ([,@verilog-ts-operators-relational] @verilog-ts-font-lock-punctuation-face)
     ([,@verilog-ts-operators-equality] @verilog-ts-font-lock-punctuation-face)
     ([,@verilog-ts-operators-shift] @verilog-ts-font-lock-punctuation-face)
     ([,@verilog-ts-operators-bitwise] @verilog-ts-font-lock-operator-face)
     ([,@verilog-ts-operators-logical] @verilog-ts-font-lock-operator-face)
     ;; Operators (LRM 11.3):
     ((assignment_operator) @verilog-ts-font-operator-face)
     ((unary_operator) @verilog-ts-font-operator-face)
     ;; ((binary_operator) @verilog-ts-font-operator-face)
     ;; ((inc_or_dec_operator) @verilog-ts-font-operator-face)
     ;; ((stream_operator) @verilog-ts-font-operator-face)
     ((event_trigger) @verilog-ts-font-operator-face))

   :feature 'punctuation
   :language 'verilog
   `(([,@verilog-ts-punctuation] @verilog-ts-font-lock-punctuation-face)
     (["."] @verilog-ts-font-lock-operator-face)
     (["(" ")"] @verilog-ts-font-lock-parenthesis-face)
     (["[" "]"] @verilog-ts-font-lock-brackets-face)
     (["{" "}"] @verilog-ts-font-lock-curly-braces-face)
     (["@" "#" "##" "@*"] @verilog-ts-font-lock-time-event-face))

   :feature 'directives-macros
   :language 'verilog
   `(([,@verilog-ts-directives] @verilog-ts-font-lock-preprocessor-face)
     (text_macro_identifier
      (simple_identifier) @verilog-ts-font-lock-preprocessor-face))

   :feature 'declaration
   :language 'verilog
   '((module_header
      (module_keyword) @font-lock-keyword-face
      (simple_identifier) @font-lock-function-name-face)
     (interface_declaration
      (interface_ansi_header
       (interface_identifier (simple_identifier) @font-lock-function-name-face)))
     (package_declaration
      (package_identifier (simple_identifier) @font-lock-function-name-face))
     (class_declaration
      (class_identifier) @font-lock-function-name-face) ; Class name
     (class_declaration
      (class_type
       (class_identifier (simple_identifier) @font-lock-type-face))) ; Parent class
     ;; Ports
     (["input" "output" "inout" "ref"] @verilog-ts-font-lock-direction-face)
     ;; Ports with user types
     (ansi_port_declaration
      (net_port_header1
       (net_port_type1
        (simple_identifier) @font-lock-type-face)))
     (ansi_port_declaration
      (variable_port_header
       (data_type (simple_identifier) @font-lock-type-face)))
     ;; Interfaces with modports
     (ansi_port_declaration
      (interface_port_header
       (interface_identifier
        (simple_identifier) @verilog-ts-font-lock-dot-name-face)
       (modport_identifier
        (modport_identifier
         (simple_identifier) @verilog-ts-font-lock-modport-face)))))

   :feature 'instance
   :language 'verilog
   '(;; Module names
     (module_instantiation (simple_identifier) @verilog-ts-font-lock-module-face)
     (program_instantiation
      (program_identifier (simple_identifier) @verilog-ts-font-lock-module-face))
     (interface_instantiation
      (interface_identifier (simple_identifier) @verilog-ts-font-lock-module-face))
     (checker_instantiation ; Some module/interface instances might wrongly be detected as checkers
      (checker_identifier (simple_identifier) @verilog-ts-font-lock-module-face))
     (udp_instantiation (simple_identifier) @verilog-ts-font-lock-module-face ; Some module/interface instances might wrongly be detected as UDP
                        (udp_instance
                         (name_of_instance
                          (instance_identifier (simple_identifier) @verilog-ts-font-lock-instance-face))))
     ;; Instance names
     (name_of_instance
      (instance_identifier (simple_identifier) @verilog-ts-font-lock-instance-face))
     ;; Port names
     (named_port_connection ; 'port_identifier standalone also matches port declarations of a module
      (port_identifier (simple_identifier) @verilog-ts-font-lock-port-connection-face))
     (formal_port_identifier (simple_identifier) @verilog-ts-font-lock-port-connection-face))

   :feature 'types
   :language 'verilog
   `(([(integer_vector_type) ; bit, logic, reg
       (integer_atom_type)   ; byte, shortint, int, longint, integer, time
       (non_integer_type)    ; shortreal, real, realtime
       (net_type)]           ; supply0, supply1, tri, triand, trior, trireg, tri0, tri1, uwire, wire, wand, wor
      @font-lock-type-face)
     (["void'" ; void cast of task called as a function
       (data_type_or_void)]
      @font-lock-type-face)
     (data_type_or_implicit1
      (data_type
       (simple_identifier) @font-lock-type-face))
     (data_type
      (class_type
       (class_identifier (simple_identifier) @font-lock-type-face)))
     (type_assignment
      (simple_identifier) @font-lock-type-face)
     ;; User type variable declaration
     (net_declaration
      (simple_identifier) @font-lock-type-face)
     ;; Enum base type
     (enum_base_type) @font-lock-type-face
     ;; Virtual interface handles
     (data_type_or_implicit1
      (data_type
       (interface_identifier (simple_identifier) @font-lock-type-face)))
     ;; Others
     (["string" "event" "signed" "unsigned"] @font-lock-type-face))

   :feature 'definition
   :language 'verilog
   '((function_body_declaration
      (function_identifier
       (function_identifier (simple_identifier) @font-lock-function-name-face)))
     (task_identifier
      (task_identifier (simple_identifier) @font-lock-function-name-face))
     (function_prototype
      (data_type_or_void)
      (function_identifier
       (function_identifier (simple_identifier) @font-lock-function-name-face)))
     (class_scope ; Definition of extern defined methods
      (class_type
       (class_identifier (simple_identifier) @verilog-ts-font-lock-dot-name-face))))

   :feature 'funcall
   :language 'verilog
   '(;; System task/function
     ((system_tf_identifier) @font-lock-builtin-face)
     ;; Method calls (class name)
     (method_call (simple_identifier) @verilog-ts-font-lock-dot-name-face))

   :feature 'extra
   :language 'verilog
   '(;; Method calls (method name)
     (method_call_body
      (method_identifier
       (method_identifier (simple_identifier) @font-lock-doc-face))))))


;;; Indent
;;;; Matchers
(defun verilog-ts--matcher-unit-scope (&rest _)
  "A tree-sitter simple indent matcher.
Matches if point is at $unit scope."
  (let* ((node (verilog-ts--node-at-bol))
         (parent (treesit-node-parent node))
         (root (treesit-buffer-root-node)))
    (or (treesit-node-eq node root)
        (treesit-node-eq parent root))))

(defun verilog-ts--matcher-blank-line (&rest _)
  "A tree-sitter simple indent matcher.
Matches if point is at a blank line."
  (let ((node (verilog-ts--node-at-bol)))
    (unless node
      t)))

(defun verilog-ts--matcher-uvm-field-macro (&rest _)
  "A tree-sitter simple indent matcher.
Matches if point is at uvm_field_* macro.
Snippet fetched from `treesit--indent-1'."
  (let* ((bol (save-excursion
                (forward-line 0)
                (skip-chars-forward " \t")
                (point)))
         (leaf-node (treesit-node-at bol))
         (node (verilog-ts--node-has-parent-recursive leaf-node "text_macro_usage"))
         (node-text (when node
                      (treesit-node-text node :no-props))))
    (when (and node-text
               (or (eq 0 (string-match "`[ou]vm_field_" node-text))))
      node-text)))

(defun verilog-ts--matcher-default-indent (&rest _)
  "A tree-sitter simple indent matcher.
Always return non-nil."
  t)

(defun verilog-ts--matcher-ansi-port-after-paren (&rest _)
  "A tree-sitter simple indent matcher.
Return non-nil if the first ansi-port is in the same line as the opening
parenthesis."
  (let* ((node (verilog-ts--node-at-bol))
         (indent-node (verilog-ts--node-has-parent-recursive node "list_of_port_declarations"))
         (indent-node-line (line-number-at-pos (treesit-node-start indent-node)))
         (first-port-node (treesit-node-child indent-node 1)) ; ansi_port_declaration
         (first-port-node-line (line-number-at-pos (treesit-node-start first-port-node))))
    (eq indent-node-line first-port-node-line)))

(defun verilog-ts--matcher-parameter-port-after-paren (&rest _)
  "A tree-sitter simple indent matcher.
Return non-nil if the first parameter is in the same line as the opening
parenthesis."
  (let* ((node (verilog-ts--node-at-bol))
         (indent-node (verilog-ts--node-has-parent-recursive node "parameter_port_list"))
         (indent-node-line (line-number-at-pos (treesit-node-start indent-node)))
         (first-port-node (treesit-node-child indent-node 2)) ; parameter_port_declaration
         (first-port-node-line (line-number-at-pos (treesit-node-start first-port-node))))
    (eq indent-node-line first-port-node-line)))

(defun verilog-ts--matcher-continued-parameter-port (&rest _)
  "A tree-sitter simple indent matcher.
Return non-nil if matches continued declaration of parameter ports.
parameter A = 0,
          B = 1,
          C = 2"
  (let ((child-node (treesit-node-child (verilog-ts--node-at-bol) 0)))
    (string= (treesit-node-type child-node) "data_type")))

;;;; Anchors
(defun verilog-ts--anchor-end-indent (node parent &rest _)
  "A tree-sitter simple indent anchor for NODE and PARENT.
Handle indentation of block end keywords."
  (save-excursion
    (pcase (treesit-node-text node :no-props)
      ("endtask"
       (goto-char (treesit-node-start (or (verilog-ts--node-has-parent-recursive node "class_method")
                                          (verilog-ts--node-has-parent-recursive node "task_declaration")))))
      ("endfunction"
       (goto-char (treesit-node-start (or (verilog-ts--node-has-parent-recursive node "class_method")
                                          (verilog-ts--node-has-parent-recursive node "function_declaration")
                                          (verilog-ts--node-has-parent-recursive node "class_constructor_declaration")))))
      ;; default is parent-bol 0
      (_
       (goto-char (treesit-node-start parent))
       (back-to-indentation)
       (point)))))

(defun verilog-ts--anchor-expression (node parent &rest _)
  "A tree-sitter simple indent anchor for NODE and PARENT.
Finds the (module_or_generate_item) indentation and return its position."
  (let (indent-node)
    (save-excursion
      (cond ((setq indent-node (verilog-ts--node-has-parent-recursive node "list_of_net_decl_assignments"))
             (goto-char (treesit-node-start indent-node))
             (forward-char verilog-ts-indent-level) ; DANGER: If the line doesn't have the amount of spaces of `verilog-ts-indent-level' it will fail! Use offset instead!!
             (point))
            ;; Default (parent-bol)
            (t
             (goto-char (treesit-node-start parent))
             (back-to-indentation)
             (point))))))

(defun verilog-ts--anchor-grandparent-bol (_node parent &rest _)
  "A tree-sitter simple indent anchor for NODE and PARENT.
Find the beginning of line of node's grandparent.
INFO: Might be present in future Emacs releases.
Check `treesit' and `treesit-simple-indent-presets'."
  (save-excursion
    (goto-char (treesit-node-start (treesit-node-parent parent)))))

(defun verilog-ts--anchor-tf-port-list (node &rest _)
  "A tree-sitter simple indent anchor for NODE.
Indent task/function arguments."
  (let ((indent-node (or (verilog-ts--node-has-parent-recursive node "class_method")
                         (verilog-ts--node-has-parent-recursive node "task_declaration")
                         (verilog-ts--node-has-parent-recursive node "function_declaration"))))
    (save-excursion
      (if indent-node
          (goto-char (treesit-node-start indent-node))
        (point)))))

(defun verilog-ts--anchor-tf-port-item1 (node &rest _)
  "A tree-sitter simple indent anchor for NODE.
Indent task/function arguments."
  (let ((indent-node (verilog-ts--node-has-parent-recursive node "tf_port_list")))
    (save-excursion
      (if indent-node
          (goto-char (treesit-node-start indent-node))
        (point)))))

(defun verilog-ts--anchor-first-ansi-port (node &rest _)
  "A tree-sitter simple indent anchor for NODE.
Indent ansi_ports depending on first port:

 - module foo (input a
    -> Will indent the rest of the ports right below the first one.

 - module foo (
     input a
    -> Will indent the rest of the ports with respect to parent-bol (module)."
  (let ((indent-node (verilog-ts--node-has-parent-recursive node "list_of_port_declarations")))
    (save-excursion
      (goto-char (treesit-node-start indent-node))
      (skip-chars-forward "( \t")
      (point))))

(defun verilog-ts--anchor-ansi-port (node &rest _)
  "A tree-sitter simple indent anchor for NODE.
Indent ansi_ports according to module definition."
  (let ((indent-node (or (verilog-ts--node-has-parent-recursive node "module_declaration")
                         (verilog-ts--node-has-parent-recursive node "interface_declaration"))))
    (when indent-node
      (save-excursion
        (goto-char (treesit-node-start indent-node))
        (point)))))

(defun verilog-ts--anchor-coverpoint-bins (node &rest _)
  "A tree-sitter simple indent anchor for NODE.
Indent bins with respect to label of coverpoint."
  (let ((indent-node (verilog-ts--node-has-parent-recursive node "cover_point")))
    (save-excursion
      (goto-char (treesit-node-start indent-node)))))

(defun verilog-ts--anchor-cross-bins (node &rest _)
  "A tree-sitter simple indent anchor for NODE.
Indent cross bins with respect to label of coverpoint."
  (let ((indent-node (verilog-ts--node-has-parent-recursive node "cover_cross")))
    (save-excursion
      (goto-char (treesit-node-start indent-node)))))

(defun verilog-ts--anchor-continued-parameter (node &rest _)
  "A tree-sitter simple indent anchor for NODE.
Indent continued line parameters in port declarations."
  (let* ((param-decl-node (treesit-search-forward node
                                                  (lambda (node)
                                                    (string= (treesit-node-type node) "parameter_declaration"))
                                                  :backward))
         (param-decl-start-node (treesit-search-subtree param-decl-node
                                                        (lambda (node)
                                                          (string= (treesit-node-type node) "list_of_param_assignments"))))
         (param-decl-start-node (treesit-node-start param-decl-start-node)))
    (when param-decl-start-node
      (save-excursion
        (goto-char param-decl-start-node)))))

(defun verilog-ts--anchor-parameter-port (node &rest _)
  "A tree-sitter simple indent anchor for NODE and PARENT.
Indent parameters depending on first parameter:
 - module foo # (parameter int a = 0
    -> Will indent the rest of the ports right below the first one.
 - module foo #(
     parameter int a = 0,
    -> Will indent the rest of the ports with respect to parent-bol (module)."
  (let ((indent-node (treesit-search-subtree (verilog-ts--node-has-parent-recursive node "parameter_port_list")
                                             (lambda (node)
                                               (string= (treesit-node-type node) "parameter_port_declaration")))))
    (save-excursion
      (goto-char (treesit-node-start indent-node))
      (skip-chars-forward "( \t")
      (point))))

(defun verilog-ts--anchor-point-min (&rest _)
  "A tree-sitter simple indent anchor."
  (save-excursion
    (point-min)))

;;;; Rules
;; INFO: Do not use siblings as anchors, since comments could be wrongly detected as siblings!
(defvar verilog-ts--indent-rules
  `((verilog
     ;; Unit scope
     (verilog-ts--matcher-unit-scope verilog-ts--anchor-point-min 0) ; Place first for highest precedence
     ;; Comments
     ((and (node-is "comment")
           verilog-ts--matcher-unit-scope)
      verilog-ts--anchor-point-min 0)
     ((and (node-is "comment")
           (parent-is "conditional_statement"))
      parent-bol 0)
     ((and (node-is "comment")
           (parent-is "list_of_port_connections"))
      parent-bol 0)
     ((node-is "comment") parent-bol ,verilog-ts-indent-level)
     ;; Procedural
     ((node-is "continuous_assign") parent-bol ,verilog-ts-indent-level)
     ((node-is "always_construct") parent-bol ,verilog-ts-indent-level)
     ((node-is "if_generate_construct") parent-bol ,verilog-ts-indent-level)
     ((node-is "loop_generate_construct") parent-bol ,verilog-ts-indent-level)
     ((node-is "initial_construct") parent-bol ,verilog-ts-indent-level)
     ((node-is "statement_or_null") parent-bol ,verilog-ts-indent-level)
     ((node-is "case_item") parent-bol ,verilog-ts-indent-level)
     ((node-is "block_item_declaration") parent-bol ,verilog-ts-indent-level)     ; Procedural local variables declaration
     ((node-is "tf_item_declaration") parent-bol ,verilog-ts-indent-level)        ; Procedural local variables in tasks declaration
     ((node-is "function_statement_or_null") parent-bol ,verilog-ts-indent-level) ; Procedural statement in a function
     ((node-is "checker_or_generate_item_declaration") parent-bol ,verilog-ts-indent-level) ; default disable iff (!rst_ni);
     ((node-is "concurrent_assertion_item") parent-bol ,verilog-ts-indent-level) ; default disable iff (!rst_ni);
     ((node-is "super") parent-bol ,verilog-ts-indent-level)
     ;; ANSI Port/parameter declaration
     ((and (node-is "ansi_port_declaration")
           verilog-ts--matcher-ansi-port-after-paren)
      verilog-ts--anchor-first-ansi-port 0)
     ((node-is "ansi_port_declaration") verilog-ts--anchor-ansi-port ,verilog-ts-indent-level) ; Fallback of previous rule
     ((node-is "module_or_generate_item") parent-bol ,verilog-ts-indent-level)
     ((node-is "interface_or_generate_item") parent-bol ,verilog-ts-indent-level)
     ((node-is "list_of_param_assignments") parent-bol ,verilog-ts-indent-level) ; First instance parameter (without parameter keyword)
     ((and (node-is "parameter_port_declaration")
           verilog-ts--matcher-continued-parameter-port)
      verilog-ts--anchor-continued-parameter 0)
     ((and (node-is "parameter_port_declaration")
           verilog-ts--matcher-parameter-port-after-paren)
      verilog-ts--anchor-parameter-port 0)
     ((node-is "parameter_port_declaration") parent-bol ,verilog-ts-indent-level) ; First instance parameter (without parameter keyword)
     ;; import packages
     ((and (node-is "package_or_generate_item_declaration")
           (parent-is "package_declaration"))
      parent-bol ,verilog-ts-indent-level)
     ;; Instance port/parameters
     ((node-is "list_of_port_connections") parent-bol ,verilog-ts-indent-level)      ; First port connection
     ((node-is "named_port_connection") parent-bol 0)         ; Rest of ports with respect to first port
     ((node-is "ordered_port_connection") parent-bol 0)         ; Rest of ports with respect to first port
     ((node-is "list_of_parameter_assignments") parent-bol ,verilog-ts-indent-level) ; First instance parameter
     ((node-is "named_parameter_assignment") parent-bol 0)    ; Rest of instance parameters with respect to first parameter
     ;; Block end
     ((node-is "end") verilog-ts--anchor-end-indent 0)
     ;; Closing
     ((or (node-is "else")         ; Parent is 'if
          (node-is "join_keyword") ; Parent is 'fork
          (node-is "}")
          (node-is ")")
          (node-is "]"))
      parent-bol 0)
     ;; Opening.
     ((or (node-is "{")
          (node-is "("))
      parent-bol 0)
     ;; Macros
     ((and (node-is "class_item") ; Place before (node-is "class_item") to match with higher precedence
           verilog-ts--matcher-uvm-field-macro)
      parent-bol 8)
     ;; Others
     ((node-is "class_item") parent-bol ,verilog-ts-indent-level)
     ((node-is "timeunits_declaration") parent-bol ,verilog-ts-indent-level)
     ((node-is "tf_port_list") verilog-ts--anchor-tf-port-list ,verilog-ts-indent-level)              ; Task ports in multiple lines (first line)
     ((node-is "tf_port_item1") verilog-ts--anchor-tf-port-item1 0)       ; Task ports in multiple lines
     ((node-is "constraint_block_item") parent-bol ,verilog-ts-indent-level)
     ((node-is "enum_name_declaration") parent-bol ,verilog-ts-indent-level)
     ((node-is "generate_region") parent-bol ,verilog-ts-indent-level)
     ((node-is "hierarchical_instance") parent-bol 0) ; Instance name in separate line
     ((node-is "constraint_expression") parent-bol ,verilog-ts-indent-level) ; Instance name in separate line
     ((node-is "bins_or_options") verilog-ts--anchor-coverpoint-bins ,verilog-ts-indent-level) ; Instance name in separate line
     ((node-is "cross_body_item") verilog-ts--anchor-cross-bins ,verilog-ts-indent-level) ; Instance name in separate line
     ((node-is "dist_list") parent-bol ,verilog-ts-indent-level) ; Instance name in separate line
     ((node-is "dist_item") verilog-ts--anchor-grandparent-bol ,verilog-ts-indent-level) ; Instance name in separate line
     ;; Continued lines
     ((node-is "expression") verilog-ts--anchor-expression 0)
     ((node-is "constant_expression") parent-bol 0)
     ((node-is "variable_decl_assignment") parent 0)
     ((node-is "param_assignment") parent 0)
     ((node-is "module_ansi_header") parent-bol 0) ; Opening bracket of module ports/parmeters
     ;; Blank lines
     (verilog-ts--matcher-blank-line parent-bol ,verilog-ts-indent-level)
     ;; Default indent
     (verilog-ts--matcher-default-indent parent-bol ,verilog-ts-indent-level))))


;;; Imenu
(defconst verilog-ts-imenu-create-index-re
  (eval-when-compile
    (regexp-opt
     '("module_declaration"
       "interface_declaration"
       "program_declaration"
       "package_declaration"
       "class_declaration"
       "function_declaration"
       "task_declaration"
       "class_constructor_declaration"
       "class_property"
       "module_instantiation"
       "interface_instantiation"
       "always_construct"
       "initial_construct"
       "final_construct"
       "generate_region"))))

(defvar verilog-ts-imenu-format-item-label-function
  'verilog-ts-imenu-format-item-label
  "Imenu function used to format an item label.
It must be a function with two arguments: TYPE and NAME.")

(defvar verilog-ts-imenu-format-parent-item-label-function
  'verilog-ts-imenu-format-parent-item-label
  "Imenu function used to format a parent item label.
It must be a function with two arguments: TYPE and NAME.")

(defvar verilog-ts-imenu-format-parent-item-jump-label-function
  'verilog-ts-imenu-format-parent-item-jump-label
  "Imenu function used to format a parent jump item label.
It must be a function with two arguments: TYPE and NAME.")

(defun verilog-ts-imenu-format-item-label (type name)
  "Return Imenu label for single node using TYPE and NAME."
  (format "%s (%s)" name type))

(defun verilog-ts-imenu-format-parent-item-label (type name)
  "Return Imenu label for parent node using TYPE and NAME."
  (format "%s..." (verilog-ts-imenu-format-item-label type name)))

(defun verilog-ts-imenu-format-parent-item-jump-label (type _name)
  "Return Imenu label for parent node jump using TYPE and NAME."
  (cond ((eq type 'cls)
         "*class definition*")
        ((eq type 'fun)
         "*function definition*")
        ((eq type 'task)
         "*task definition*")
        (t
         (format "%s" type))))

(defun verilog-ts-imenu-treesit-create-index-1 (node)
  "Given a sparse tree, create an imenu alist.

NODE is the root node of the tree returned by
`treesit-induce-sparse-tree' (not a tree-sitter node, its car is
a tree-sitter node).  Walk that tree and return an imenu alist.

Return a list of ENTRY where

ENTRY := (NAME . MARKER)
       | (NAME . ((JUMP-LABEL . MARKER)
                  ENTRY
                  ...)

NAME is the function/class's name, JUMP-LABEL is like \"*function
definition*\".

Copied from Python's `python--imenu-treesit-create-index-1' and adapted to
SystemVerilog parser."
  (let* ((ts-node (car node))
         (children (cdr node))
         (subtrees (mapcan #'verilog-ts-imenu-treesit-create-index-1
                           children))
         (type (pcase (treesit-node-type ts-node)
                 ("module_declaration"            'mod)
                 ("interface_declaration"         'itf)
                 ("program_declaration"           'pgm)
                 ("package_declaration"           'pkg)
                 ("class_declaration"             'cls)
                 ("class_property"                'prop)
                 ("function_declaration"          'fun)
                 ("task_declaration"              'task)
                 ("class_constructor_declaration" 'new)
                 ("module_instantiation"          'inst)
                 ("always_construct"              'always)
                 ("generate_region"               'gen)))
         ;; The root of the tree could have a nil ts-node.
         (name (when ts-node
                 (pcase (treesit-node-type ts-node)
                   ("class_property" (let ((temp-node (treesit-search-subtree ts-node "\\_<variable_decl_assignment\\_>"))
                                           (typedef-node (treesit-search-subtree ts-node "\\_<type_declaration\\_>")))
                                       (cond (temp-node
                                              (if (treesit-search-subtree temp-node "simple_identifier")
                                                  (treesit-node-text (treesit-search-subtree temp-node "simple_identifier") :no-prop)
                                                (treesit-node-text temp-node :no-prop)))
                                             (typedef-node
                                              (treesit-node-text (treesit-node-next-sibling (treesit-node-child typedef-node 1)) :no-prop))
                                             (t
                                              nil))))
                   (_ (verilog-ts--node-identifier-name ts-node)))))
         (marker (when ts-node
                   (set-marker (make-marker)
                               (treesit-node-start ts-node)))))
    (cond
     ((null ts-node)
      subtrees)
     (subtrees
      (let ((parent-label (funcall verilog-ts-imenu-format-parent-item-label-function
                                   type
                                   name))
            (jump-label (funcall verilog-ts-imenu-format-parent-item-jump-label-function
                                 type
                                 name)))
        `((,parent-label
           ,(cons jump-label marker)
           ,@subtrees))))
     (t (let ((label (funcall verilog-ts-imenu-format-item-label-function
                              type
                              name)))
          (list (cons label marker)))))))

(defun verilog-ts-imenu-create-index (&optional node)
  "Imenu index builder function for `verilog-ts-mode'.

NODE is the root node of the subtree you want to build an index
of.  If nil, use the root node of the whole parse tree.

Copied from Python's `python-imenu-treesit-create-index' and adapted
to SystemVerilog parser."
  (let* ((node (or node (treesit-buffer-root-node 'verilog)))
         (tree (treesit-induce-sparse-tree
                node
                verilog-ts-imenu-create-index-re
                nil 1000)))
    (verilog-ts-imenu-treesit-create-index-1 tree)))

(defun verilog-ts--defun-name (node)
  "Return the defun name of NODE.

Return nil if there is no name or if NODE is not a defun node."
  (verilog-ts--node-identifier-name node))


;;; Which-func
(defvar-local verilog-ts-which-func-extra nil
  "Variable to hold extra information for `which-func'.")

(defun verilog-ts-which-func-shorten-block (block-type)
  "Return shortened name of BLOCK-TYPE, if possible."
  (cond ((string= "function_declaration"          block-type) "func")
        ((string= "class_constructor_declaration" block-type) "func")
        ((string= "task_declaration"              block-type) "task")
        ((string= "class_declaration"             block-type) "cls")
        ((string= "module_declaration"            block-type) "mod")
        ((string= "interface_declaration"         block-type) "itf")
        ((string= "package_declaration"           block-type) "pkg")
        ((string= "program_declaration"           block-type) "pgm")
        ((string= "generate_region"               block-type) "gen")
        ((string= "class_property"                block-type) "prop")
        (t block-type)))

(defun verilog-ts-which-func-function ()
  "Retrieve `which-func' candidates."
  (let ((node (verilog-ts--node-has-parent-recursive (verilog-ts--node-at-point) verilog-ts-imenu-create-index-re)))
    (when node
      (setq verilog-ts-which-func-extra (verilog-ts--node-identifier-name node))
      (verilog-ts-which-func-shorten-block (treesit-node-type node)))))

(defun verilog-ts-which-func ()
  "Hook for `verilog-ts-mode' to enable `which-func'."
  (setq-local which-func-functions '(verilog-ts-which-func-function))
  (setq-local which-func-format
              `("["
                (:propertize which-func-current
                 face (which-func :weight bold)
                 mouse-face mode-line-highlight)
                ":"
                (:propertize verilog-ts-which-func-extra
                 face which-func
                 mouse-face mode-line-highlight)
                "]")))


;;; Navigation
(defconst verilog-ts--defun-type-regexp
  (eval-when-compile
    (regexp-opt
     '("module_declaration"
       "interface_declaration"
       "program_declaration"
       "package_declaration"
       "class_declaration"
       "class_method"
       "class_constructor_declaration"
       "function_declaration"
       "task_declaration")
     'symbols)))

(defconst verilog-ts--function-task-regexp
  (eval-when-compile
    (regexp-opt
     '("task_declaration"
       "function_declaration"
       "class_method" ; "class_method" includes constructor and extern prototypes
       "class_constructor_declaration")
     'symbols)))

(defconst verilog-ts--function-task-class-regexp
  (eval-when-compile
    (regexp-opt
     '("class_declaration"
       "task_declaration"
       "function_declaration"
       "class_method"
       "class_constructor_declaration")
     'symbols)))

(defun verilog-ts-find-function-task (&optional bwd)
  "Search for a Verilog function/task declaration or definition.

If optional arg BWD is non-nil, search backwards."
  (treesit-search-forward-goto (verilog-ts--node-at-point) verilog-ts--function-task-regexp t bwd))

(defun verilog-ts-find-function-task-fwd ()
  "Search forward for a Verilog function/task declaration or definition."
  (verilog-ts-find-function-task))

(defun verilog-ts-find-function-task-bwd ()
  "Search backward for a Verilog function/task declaration or definition."
  (verilog-ts-find-function-task :bwd))

(defun verilog-ts-find-class (&optional bwd)
  "Search for a class declaration.

If optional arg BWD is non-nil, search backwards."
  (treesit-search-forward-goto (verilog-ts--node-at-point) "class_declaration" t bwd))

(defun verilog-ts-find-class-fwd ()
  "Search forward for a Verilog class declaration."
  (verilog-ts-find-class))

(defun verilog-ts-find-class-bwd ()
  "Search backward for a Verilog class declaration."
  (verilog-ts-find-class :bwd))

(defun verilog-ts-find-function-task-class (&optional bwd)
  "Find closest declaration of a function/task/class.

If optional arg BWD is non-nil, search backwards."
  (treesit-search-forward-goto (verilog-ts--node-at-point) verilog-ts--function-task-class-regexp t bwd))

(defun verilog-ts-find-function-task-class-fwd ()
  "Search forward for a Verilog function/task/class declaration."
  (verilog-ts-find-function-task-class))

(defun verilog-ts-find-function-task-class-bwd ()
  "Search backward for a Verilog function/task/class declaration."
  (verilog-ts-find-function-task-class :bwd))

(defun verilog-ts-find-block (&optional bwd)
  "Search for a Verilog block regexp.

If optional arg BWD is non-nil, search backwards."
  (treesit-search-forward-goto (verilog-ts--node-at-point) verilog-ts-block-at-point-re t bwd))

(defun verilog-ts-find-block-fwd ()
  "Search forward for a Verilog block regexp."
  (verilog-ts-find-block))

(defun verilog-ts-find-block-bwd ()
  "Search backwards for a Verilog block regexp."
  (verilog-ts-find-block :bwd))

(defun verilog-ts-find-module-instance (&optional bwd)
  "Search for a Verilog module/instance.

If optional arg BWD is non-nil, search backwards."
  (treesit-search-forward-goto (verilog-ts--node-at-point) verilog-ts-instance-re t bwd))

(defun verilog-ts-find-module-instance-fwd ()
  "Search forwards for a Verilog module/instance."
  (verilog-ts-find-module-instance))

(defun verilog-ts-find-module-instance-bwd ()
  "Search backwards for a Verilog module/instance."
  (verilog-ts-find-module-instance :bwd))

(defun verilog-ts-goto-begin-up ()
  "Move point to start position of current begin."
  (let* ((begin-node (verilog-ts--node-has-parent-recursive (verilog-ts--node-at-point) "seq_block"))
         (begin-pos (treesit-node-start begin-node)))
    (when begin-pos
      (goto-char begin-pos))))

(defun verilog-ts-goto-begin-down ()
  "Move point to start position of next nested begin."
  (let* ((begin-node (verilog-ts--node-has-child-recursive (verilog-ts--node-at-point) "seq_block"))
         (begin-pos (treesit-node-start begin-node)))
    (when begin-pos
      (goto-char begin-pos))))

(defun verilog-ts-defun-level-up ()
  "Move up one defun-level."
  (let* ((node (verilog-ts--node-has-parent-recursive (verilog-ts--node-at-point) verilog-ts--defun-type-regexp))
         (pos (treesit-node-start node)))
    (when pos
      (goto-char pos))))

(defun verilog-ts-defun-level-down ()
  "Move down one defun-level."
  (let* ((node (verilog-ts--node-has-child-recursive (verilog-ts--node-at-point) verilog-ts--defun-type-regexp))
         (pos (treesit-node-start node)))
    (when pos
      (goto-char pos))))

(defun verilog-ts-goto-next-error ()
  "Move point to next error in the parse tree."
  (interactive)
  (treesit-search-forward-goto (verilog-ts--node-at-point) "ERROR" t))

(defun verilog-ts-goto-prev-error ()
  "Move point to previous error in the parse tree."
  (interactive)
  (treesit-search-forward-goto (verilog-ts--node-at-point) "ERROR" t :bwd))


;;;; Dwim
(defconst verilog-ts-nav-beg-of-defun-dwim-inside-module-re
  (eval-when-compile
    (regexp-opt
     '("module_declaration"
       "interface_declaration"
       "always_construct"
       "initial_construct"
       "final_construct"
       "generate_region"))))
(defconst verilog-ts-nav-beg-of-defun-dwim-outside-module-re
  (eval-when-compile
    (regexp-opt
     '("function_declaration"
       "task_declaration"
       "class_declaration"
       "package_declaration"
       "program_declaration"))))

(defun verilog-ts-nav-beg-of-defun-dwim ()
  "Context based search upwards.
If in a module/interface look for instantiations.
pOtherwise look for functions/tasks."
  (interactive)
  (if (verilog-ts--inside-module-or-interface-p)
      (treesit-search-forward-goto (verilog-ts--node-at-point) verilog-ts-nav-beg-of-defun-dwim-inside-module-re t :bwd)
    (treesit-search-forward-goto (verilog-ts--node-at-point) verilog-ts-nav-beg-of-defun-dwim-outside-module-re t :bwd)))

(defun verilog-ts-nav-end-of-defun-dwim ()
  "Context based search upwards.
If in a module/interface look for instantiations.
Otherwise look for functions/tasks."
  (interactive)
  (if (verilog-ts--inside-module-or-interface-p)
      (treesit-search-forward-goto (verilog-ts--node-at-point) verilog-ts-nav-beg-of-defun-dwim-inside-module-re t)
    (treesit-search-forward-goto (verilog-ts--node-at-point) verilog-ts-nav-beg-of-defun-dwim-outside-module-re t)))

(defun verilog-ts-nav-down-dwim ()
  "Context based search downwards.
If in a module/interface look for instantiations.
Otherwise look for functions, tasks and classes."
  (interactive)
  (if (verilog-ts--inside-module-or-interface-p)
      (verilog-ts-find-module-instance-fwd)
    (verilog-ts-find-function-task-class-fwd)))

(defun verilog-ts-nav-up-dwim ()
  "Context based search upwards.
If in a module/interface look for instantiations.
Otherwise look for functions, tasks and classes."
  (interactive)
  (if (verilog-ts--inside-module-or-interface-p)
      (verilog-ts-find-module-instance-bwd)
    (verilog-ts-find-function-task-class-bwd)))


;;; Prettify
(defconst verilog-ts-pretty-declarations-node-re "list_of_\\(net\\|variable\\)_decl_assignments")
(defconst verilog-ts-pretty-expr-node-re "\\(non\\)?blocking_assignment")

(defun verilog-ts-pretty-declarations ()
  "Line up declarations around point."
  (interactive)
  (let* ((decl-node-re verilog-ts-pretty-declarations-node-re)
         (nodes (verilog-ts-nodes-block-at-point decl-node-re))
         (indent-levels (mapcar (lambda (node)
                                  (save-excursion
                                    (goto-char (treesit-node-start node))
                                    (skip-chars-backward " \t\n\r")
                                    (forward-char)
                                    (current-column)))
                                nodes))
         (indent-level-max (when indent-levels
                             (apply #'max indent-levels)))
         current-node)
    ;; Start processing
    (when nodes
      (save-excursion
        (goto-char (treesit-node-start (car nodes)))
        (while (setq current-node (verilog-ts-search-node-block-at-point decl-node-re))
          (goto-char (treesit-node-start current-node))
          (just-one-space)
          (indent-to indent-level-max)
          (goto-char (treesit-node-end (verilog-ts-search-node-block-at-point decl-node-re))))))))

(defun verilog-ts-pretty-expr ()
  "Line up expressions around point."
  (interactive)
  (let* ((decl-node-re verilog-ts-pretty-expr-node-re)
         (align-node-re "variable_lvalue")
         (nodes (verilog-ts-nodes-block-at-point decl-node-re))
         (indent-levels (mapcar (lambda (node)
                                  (let ((lhs-node (verilog-ts--node-has-child-recursive node align-node-re)))
                                    (save-excursion
                                      (goto-char (treesit-node-end lhs-node))
                                      (forward-char)
                                      (current-column))))
                                nodes))
         (indent-level-max (when indent-levels
                             (apply #'max indent-levels)))
         current-node)
    ;; Start processing
    (when nodes
      (save-excursion
        (goto-char (treesit-node-start (car nodes)))
        (while (setq current-node (verilog-ts-search-node-block-at-point align-node-re))
          (goto-char (treesit-node-end current-node))
          (just-one-space)
          (indent-to indent-level-max))))))

;;; Beautify
(defun verilog-ts-beautify-block-at-point ()
  "Beautify/indent block at point.

If block is an instance, also align parameters and ports."
  (interactive)
  (let ((node (verilog-ts-block-at-point))
        start end type name)
    (unless node
      (user-error "Not inside a block"))
    (setq start (treesit-node-start node))
    (setq end (treesit-node-end node))
    (setq type (treesit-node-type node))
    (setq name (verilog-ts--node-identifier-name node))
    (indent-region start end)
    ;; Instance: also align ports and params
    (when (string-match verilog-ts-instance-re type)
      (let ((re "\\(\\s-*\\)(")
            params-node ports-node)
        (setq node (verilog-ts-block-at-point)) ; Refresh outdated node after `indent-region'
        (when (setq params-node (verilog-ts--node-has-child-recursive node "list_of_parameter_assignments"))
          (align-regexp (treesit-node-start params-node) (treesit-node-end params-node) re 1 1 nil))
        (when (setq ports-node (verilog-ts--node-has-child-recursive node "list_of_port_connections"))
          (align-regexp (treesit-node-start ports-node) (treesit-node-end ports-node) re 1 1 nil))))
    (message "%s : %s" type name)))

(defun verilog-ts-beautify-current-buffer ()
  "Beautify current buffer:
- Indent whole buffer
- Beautify every instantiated module
- Untabify and delete trailing whitespace"
  (interactive)
  (let (node)
    (indent-region (point-min) (point-max))
    (save-excursion
      (goto-char (point-min))
      (while (setq node (treesit-search-forward (verilog-ts--node-at-point) verilog-ts-instance-re))
        (goto-char (treesit-node-start node))
        (verilog-ts-beautify-block-at-point)
        (setq node (treesit-search-forward (verilog-ts--node-at-point) verilog-ts-instance-re))
        (goto-char (treesit-node-end node))
        (when (not (eobp))
          (forward-char))))
    (untabify (point-min) (point-max))
    (delete-trailing-whitespace (point-min) (point-max))))

(defun verilog-ts-beautify-files (files)
  "Beautify SystemVerilog FILES.
FILES is a list of strings containing the filepaths."
  (dolist (file files)
    (unless (file-exists-p file)
      (error "File %s does not exist! Aborting!" file)))
  (save-window-excursion
    (dolist (file files)
      (with-temp-file file
        (insert-file-contents file)
        (verilog-ts-mode)
        (verilog-ts-beautify-current-buffer)))))

(defun verilog-ts-beautify-dir-files (dir &optional follow-symlinks)
  "Beautify Verilog files on DIR.

If FOLLOW-SYMLINKS is non-nil, symbolic links that point to
directories are followed.  Note that this can lead to infinite
recursion."
  (interactive "DDirectory: ")
  (let ((files (directory-files-recursively dir
                                            verilog-ts-file-extension-re
                                            nil nil
                                            follow-symlinks)))
    (verilog-ts-beautify-files files)))


;;; Completion
(defun verilog-ts-completion-at-point ()
  "Verilog tree-sitter powered completion at point.

Complete with keywords and current buffer identifiers."
  (interactive)
  (let* ((bds (bounds-of-thing-at-point 'symbol))
         (start (car bds))
         (end (cdr bds))
         candidates)
    (setq candidates (remove (thing-at-point 'symbol :no-props)
                             (append (mapcar (lambda (node-and-props)
                                               (plist-get (cdr node-and-props) :name))
                                             (verilog-ts-nodes-props "simple_identifier"))
                                     verilog-keywords)))
    (list start end candidates . nil)))


;;; Major-mode
;;;; Setup
;;;###autoload
(defun verilog-ts-install-grammar ()
  "Install Verilog tree-sitter grammar.

This command requires Git, a C compiler and (sometimes) a C++ compiler,
and the linker to be installed and on PATH."
  (interactive)
  (let ((url "https://github.com/gmlarumbe/tree-sitter-verilog"))
    (add-to-list 'treesit-language-source-alist `(verilog ,url))
    (treesit-install-language-grammar 'verilog)))


;;;; Features
(defvar-keymap verilog-ts-mode-map
  :doc "Keymap for SystemVerilog language with tree-sitter"
  :parent verilog-mode-map
  "TAB"     #'indent-for-tab-command
  "C-M-a"   #'verilog-ts-nav-beg-of-defun-dwim
  "C-M-e"   #'verilog-ts-nav-end-of-defun-dwim
  "C-M-f"   #'verilog-ts-forward-sexp
  "C-M-b"   #'verilog-ts-backward-sexp
  "C-M-d"   #'verilog-ts-nav-down-dwim
  "C-M-u"   #'verilog-ts-nav-up-dwim
  "C-c TAB" #'verilog-ts-pretty-declarations
  "C-c C-o" #'verilog-ts-pretty-expr
  "C-c e n" #'verilog-ts-goto-next-error
  "C-c e p" #'verilog-ts-goto-prev-error)

(defvar verilog-ts-mode-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?\\ "\\"     table)
    (modify-syntax-entry ?+  "."      table)
    (modify-syntax-entry ?-  "."      table)
    (modify-syntax-entry ?=  "."      table)
    (modify-syntax-entry ?%  "."      table)
    (modify-syntax-entry ?<  "."      table)
    (modify-syntax-entry ?>  "."      table)
    (modify-syntax-entry ?&  "."      table)
    (modify-syntax-entry ?|  "."      table)
    (modify-syntax-entry ?`  "."      table)
    (modify-syntax-entry ?_  "_"      table)
    (modify-syntax-entry ?\' "."      table)
    (modify-syntax-entry ?/  ". 124b" table)
    (modify-syntax-entry ?*  ". 23"   table)
    (modify-syntax-entry ?\n "> b"    table)
    table)
  "Syntax table used in Verilog mode buffers.")

;;;###autoload
(define-derived-mode verilog-ts-mode verilog-mode "SystemVerilog"
  "Major mode for editing SystemVerilog files, using tree-sitter library."
  :syntax-table verilog-ts-mode-syntax-table
  ;; Treesit
  (when (treesit-ready-p 'verilog)
    (treesit-parser-create 'verilog)
    ;; Font-lock.
    (setq font-lock-defaults nil) ; Disable `verilog-mode' font-lock/indent config
    (setq-local treesit-font-lock-feature-list
                '((comment string)
                  (keyword operator)
                  (directives-macros types punctuation declaration definition all instance funcall)
                  (error)))
    (setq-local treesit-font-lock-settings verilog-ts--treesit-settings)
    ;; Indent.
    (setq-local indent-line-function nil)
    (setq-local comment-indent-function nil)
    (setq-local treesit-simple-indent-rules verilog-ts--indent-rules)
    ;; Navigation.
    (setq-local treesit-defun-type-regexp verilog-ts--defun-type-regexp)
    ;; Imenu.
    (setq-local imenu-create-index-function #'verilog-ts-imenu-create-index)
    ;; Which-func
    (verilog-ts-which-func)
    ;; Completion
    (add-hook 'completion-at-point-functions #'verilog-ts-completion-at-point nil 'local)
    ;; Setup.
    (treesit-major-mode-setup)))


;;; Provide
(provide 'verilog-ts-mode)

;;; verilog-ts-mode.el ends here

