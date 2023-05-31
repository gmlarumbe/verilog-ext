;;; verilog-ts-mode.el --- Verilog Tree-Sitter Mode  -*- lexical-binding: t -*-

;; Copyright (C) 2022-2023 Gonzalo Larumbe

;; Author: Gonzalo Larumbe <gonzalomlarumbe@gmail.com>
;; URL: https://github.com/gmlarumbe/verilog-ext
;; Version: 0.0.0
;; Keywords: Verilog, IDE, Tools
;; Package-Requires: ((emacs "29") (async "1.9.7"))

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

;; Verilog Tree-sitter Mode

;;; Code:

;;; Requirements

(require 'treesit)
(require 'async)
(require 'project)
(eval-when-compile
  (require 'verilog-mode))

(declare-function treesit-parser-create "treesit.c")
(declare-function treesit-induce-sparse-tree "treesit.c")
(declare-function treesit-node-parent "treesit.c")
(declare-function treesit-node-start "treesit.c")
(declare-function treesit-node-end "treesit.c")
(declare-function treesit-node-child "treesit.c")
(declare-function treesit-node-child-by-field-name "treesit.c")
(declare-function treesit-node-type "treesit.c")


;;; Customization
(defcustom verilog-ts-indent-level 4
  "Tree-sitter indentation of Verilog statements with respect to containing block."
  :group 'verilog-ts
  :type 'integer)
(put 'verilog-ts-indent-level 'safe-local-variable #'integerp)


;;; Utils
;;;; Auxiliary
(defun verilog-ts--node-at-point ()
  "Return tree-sitter node at point."
  (treesit-node-at (point) 'verilog))

(defun verilog-ts--node-has-parent-recursive (node node-type)
  "Return non-nil if NODE is part of NODE-TYPE in the hierarchy."
  (treesit-parent-until
   node
   (lambda (node)
     (string= (treesit-node-type node) node-type))))

(defun verilog-ts--node-identifier-name (node)
  "Return identifier name of NODE."
  (treesit-node-text (treesit-search-subtree node "simple_identifier") :no-prop))

(defun verilog-ts--highest-node-at-pos (pos)
  "Return highest node in the hierarchy that starts at POS.
INFO: Only works if point is at the beginning of a symbol!
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

;;;; Navigation
(defun verilog-ts-forward-sexp ()
  "Move forward across expressions."
  (interactive)
  (if (member (following-char) '(?\( ?\{ ?\[))
      (forward-sexp 1)
    (let* ((node (verilog-ts--highest-node-at-symbol))
           (end (treesit-node-end node)))
      (goto-char end))))

(defun verilog-ts-backward-sexp ()
  "Move backward across expressions."
  (interactive)
  (if (member (preceding-char) '(?\) ?\} ?\]))
      (backward-sexp 1)
    (let* ((node (treesit-node-parent (verilog-ts--node-at-point)))
           (beg (treesit-node-start node)))
      (goto-char beg))))


;;;; Context info
(defun verilog-ts-module-at-point ()
  "Return name of module at point."
  (interactive)
  (let ((node-at-point (treesit-node-at (point)))
        module-node)
    (setq module-node (verilog-ts--node-has-parent-recursive node-at-point "module_instantiation"))
    (when module-node
      (treesit-node-text (treesit-search-subtree module-node "simple_identifier") :no-prop))))

(defun verilog-ts-nodes-current-buffer (pred)
  "Return node names that satisfy PRED in current buffer."
  (interactive)
  (let* ((root-node (treesit-buffer-root-node))
         (pred-nodes (cdr (treesit-induce-sparse-tree root-node pred)))
         names-list)
    (dolist (node pred-nodes)
      (push (verilog-ts--node-identifier-name (car node)) names-list))
    (seq-reverse names-list)))

(defun verilog-ts-class-attributes ()
  "Return class attributes of current file."
  (interactive)
  (verilog-ts-nodes-current-buffer "class_property"))

;; TODO: Still does not work for constructors (new methods)
(defun verilog-ts-class-methods ()
  "Return class methods of current file."
  (interactive)
  (verilog-ts-nodes-current-buffer "class_method"))

(defun verilog-ts-class-constraints ()
  "Return class constraints of current file."
  (interactive)
  (verilog-ts-nodes-current-buffer "constraint_declaration"))

(defun verilog-ts-module-instances ()
  "Return module instances of current file."
  (interactive)
  (verilog-ts-nodes-current-buffer "module_instantiation"))

;; TODO: Does not work since it does not find simple_identifier easily
(defun verilog-ts-always-blocks ()
  "Return always blocks of current file."
  (interactive)
  (verilog-ts-nodes-current-buffer "always_keyword"))



;;; Font-lock
;;;; Faces
(defgroup verilog-ts-faces nil
  "Verilog-ts faces."
  :group 'verilog-ts)

(defvar verilog-ts-font-lock-grouping-keywords-face 'verilog-ts-font-lock-grouping-keywords-face)
(defface verilog-ts-font-lock-grouping-keywords-face
  '((t (:foreground "dark olive green")))
  "Face for grouping keywords: begin, end."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-punctuation-face 'verilog-ts-font-lock-punctuation-face)
(defface verilog-ts-font-lock-punctuation-face
  '((t (:foreground "burlywood")))
  "Face for punctuation symbols, e.g:
!,;:?'=<>*"
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-punctuation-bold-face 'verilog-ts-font-lock-punctuation-bold-face)
(defface verilog-ts-font-lock-punctuation-bold-face
  '((t (:inherit verilog-ts-font-lock-punctuation-face :weight extra-bold)))
  "Face for bold punctuation symbols, such as &^~+-/|."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-brackets-face 'verilog-ts-font-lock-brackets-face)
(defface verilog-ts-font-lock-brackets-face
  '((t (:foreground "goldenrod")))
  "Face for brackets []."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-parenthesis-face 'verilog-ts-font-lock-parenthesis-face)
(defface verilog-ts-font-lock-parenthesis-face
  '((t (:foreground "dark goldenrod")))
  "Face for parenthesis ()."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-curly-braces-face 'verilog-ts-font-lock-curly-braces-face)
(defface verilog-ts-font-lock-curly-braces-face
  '((t (:foreground "DarkGoldenrod2")))
  "Face for curly braces {}."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-port-connection-face 'verilog-ts-font-lock-port-connection-face)
(defface verilog-ts-font-lock-port-connection-face
  '((t (:foreground "bisque2")))
  "Face for port connections of instances.
.portA (signalA),
.portB (signalB)
);"
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-dot-name-face 'verilog-ts-font-lock-dot-name-face)
(defface verilog-ts-font-lock-dot-name-face
  '((t (:foreground "gray70")))
  "Face for dot-name regexps:
- Interface signals, classes attributes/methods and hierarchical refs.

axi_if.Ready <= 1'b1;
obj.method();"
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-braces-content-face 'verilog-ts-font-lock-braces-content-face)
(defface verilog-ts-font-lock-braces-content-face
  '((t (:foreground "yellow green")))
  "Face for content between braces: arrays, bit vector width and indexing."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-width-num-face 'verilog-ts-font-lock-width-num-face)
(defface verilog-ts-font-lock-width-num-face
  '((t (:foreground "chartreuse2")))
  "Face for the bit width number expressions.
{1}'b1,
{4}'hF,
{3}'o7,"
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-width-type-face 'verilog-ts-font-lock-width-type-face)
(defface verilog-ts-font-lock-width-type-face
  '((t (:foreground "sea green" :weight bold)))
  "Face for the bit width type expressions.
1'{b}1,
4'{h}F,
3'{o}7,"
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-module-face 'verilog-ts-font-lock-module-face)
(defface verilog-ts-font-lock-module-face
  '((t (:foreground "green1")))
  "Face for module names."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-instance-face 'verilog-ts-font-lock-instance-face)
(defface verilog-ts-font-lock-instance-face
  '((t (:foreground "medium spring green")))
  "Face for instance names."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-time-event-face 'verilog-ts-font-lock-time-event-face)
(defface verilog-ts-font-lock-time-event-face
  '((t (:foreground "deep sky blue" :weight bold)))
  "Face for time-events: @ and #."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-time-unit-face 'verilog-ts-font-lock-time-unit-face)
(defface verilog-ts-font-lock-time-unit-face
  '((t (:foreground "light steel blue")))
  "Face for time-units: ms, us, ns, ps, fs (delays and timescale/timeprecision)."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-preprocessor-face 'verilog-ts-font-lock-preprocessor-face)
(defface verilog-ts-font-lock-preprocessor-face
  '((t (:foreground "pale goldenrod")))
  "Face for preprocessor compiler directives (`include, `define, UVM macros...)."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-modport-face 'verilog-ts-font-lock-modport-face)
(defface verilog-ts-font-lock-modport-face
  '((t (:foreground "light blue")))
  "Face for interface modports."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-direction-face 'verilog-ts-font-lock-direction-face)
(defface verilog-ts-font-lock-direction-face
  '((t (:foreground "RosyBrown3")))
  "Face for direction of ports/functions/tasks args."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-typedef-face 'verilog-ts-font-lock-typedef-face)
(defface verilog-ts-font-lock-typedef-face
  '((t (:foreground "light blue")))
  "Face for user defined types."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-translate-off-face 'verilog-ts-font-lock-translate-off-face)
(defface verilog-ts-font-lock-translate-off-face
  '((t (:background "gray20" :slant italic)))
  "Face for pragmas between comments, e.g:
* translate_off / * translate_on"
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-uvm-classes-face 'verilog-ts-font-lock-uvm-classes-face)
(defface verilog-ts-font-lock-uvm-classes-face
  '((t (:foreground "light blue")))
  "Face for UVM classes."
  :group 'verilog-ts-faces)

(defvar verilog-ts-font-lock-xilinx-attributes-face 'verilog-ts-font-lock-xilinx-attributes-face)
(defface verilog-ts-font-lock-xilinx-attributes-face
  '((t (:foreground "orange1")))
  "Face for Xilinx Vivado RTL synthesis attributes."
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
(defvar verilog--treesit-settings
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
   ;; :override t
   '((ERROR) @font-lock-warning-face) ; Shows as highlighted red, good for debugging

   :feature 'all
   :language 'verilog
   '(;; Arrays
     ((packed_dimension
       (constant_range) @verilog-ts-font-lock-braces-content-face))
     ((unpacked_dimension
       (constant_range) @verilog-ts-font-lock-braces-content-face))
     (select1
      (constant_range) @verilog-ts-font-lock-braces-content-face)
     ((unpacked_dimension
       (constant_expression) @verilog-ts-font-lock-braces-content-face))
     (bit_select1
      (expression) @verilog-ts-font-lock-braces-content-face)
     (constant_select1
      (constant_expression) @verilog-ts-font-lock-braces-content-face)
     (constant_bit_select1
      (constant_expression) @verilog-ts-font-lock-braces-content-face)
     (indexed_range
      (expression) @verilog-ts-font-lock-braces-content-face
      (constant_expression) @verilog-ts-font-lock-braces-content-face)
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
      (attr_spec (simple_identifier) @verilog-ts-font-lock-xilinx-attributes-face))
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
     ((integral_number) @verilog-ts--fontify-width-num)
     )

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
      (:match "^new$" @font-lock-keyword-face))
     )

   :feature 'operator
   :language 'verilog
   `(;; INFO: Some of these might be redundant
     ([,@verilog-ts-operators-arithmetic] @verilog-ts-font-lock-punctuation-bold-face)
     ([,@verilog-ts-operators-relational] @verilog-ts-font-lock-punctuation-face)
     ([,@verilog-ts-operators-equality] @verilog-ts-font-lock-punctuation-face)
     ([,@verilog-ts-operators-shift] @verilog-ts-font-lock-punctuation-face)
     ([,@verilog-ts-operators-bitwise] @verilog-ts-font-lock-punctuation-bold-face)
     ([,@verilog-ts-operators-logical] @verilog-ts-font-lock-punctuation-bold-face)
     ;; Operators (LRM 11.3):
     ((assignment_operator) @verilog-ts-font-lock-punctuation-face)
     ((unary_operator) @verilog-ts-font-lock-punctuation-face)
     ;; ((binary_operator) @verilog-ts-font-lock-punctuation-face)
     ;; ((inc_or_dec_operator) @verilog-ts-font-lock-punctuation-face)
     ;; ((stream_operator) @verilog-ts-font-lock-punctuation-face)
     ((event_trigger) @verilog-ts-font-lock-punctuation-face)
     )

   :feature 'punctuation
   :language 'verilog
   `(([,@verilog-ts-punctuation] @verilog-ts-font-lock-punctuation-face)
     (["."] @verilog-ts-font-lock-punctuation-bold-face)
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
         (simple_identifier) @verilog-ts-font-lock-modport-face))))
     )

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
     (formal_port_identifier (simple_identifier) @verilog-ts-font-lock-port-connection-face)
     )

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
     (["string" "event" "signed" "unsigned"] @font-lock-type-face)
     )

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
       (class_identifier (simple_identifier) @verilog-ts-font-lock-dot-name-face)))
     )

   :feature 'funcall
   :language 'verilog
   '(;; System task/function
     ((system_tf_identifier) @font-lock-builtin-face)
     ;; Method calls (class name)
     (method_call (simple_identifier) @verilog-ts-font-lock-dot-name-face)
     )

   :feature 'extra
   :language 'verilog
   ;; System task/function
   '(;; Method calls (method name)
     (method_call_body
      (method_identifier
       (method_identifier (simple_identifier) @font-lock-doc-face))))

   ))


;;; Indent
;;;; Matchers
(defun verilog-ts--unit-scope (&rest _)
  "A tree-sitter simple indent matcher.
Matches if point is at $unit scope."
  (let* ((node (verilog-ts--node-at-bol))
         (parent (treesit-node-parent node))
         (root (treesit-buffer-root-node)))
    (or (treesit-node-eq node root)
        (treesit-node-eq parent root))))

(defun verilog-ts--blank-line (&rest _)
  "A tree-sitter simple indent matcher.
Matches if point is at a blank line."
  (let ((node (verilog-ts--node-at-bol)))
    (unless node
      t)))

(defun verilog-ts--uvm-field-macro (&rest _)
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

(defun verilog-ts--default-indent (&rest _)
  "A tree-sitter simple indent matcher.
Always return non-nil."
  t)

(defun verilog-ts--ansi-port-after-paren (&rest _)
  "A tree-sitter simple indent matcher.
Return non-nil if the first ansi-port is in the same line as the opening
parenthesis."
  (let* ((node (verilog-ts--node-at-bol))
         (indent-node (verilog-ts--node-has-parent-recursive node "list_of_port_declarations"))
         (indent-node-line (line-number-at-pos (treesit-node-start indent-node)))
         (first-port-node (treesit-node-child indent-node 1)) ; ansi_port_declaration
         (first-port-node-line (line-number-at-pos (treesit-node-start first-port-node))))
    (eq indent-node-line first-port-node-line)))

(defun verilog-ts--parameter-port-after-paren (&rest _)
  "A tree-sitter simple indent matcher.
Return non-nil if the first parameter is in the same line as the opening
parenthesis."
  (let* ((node (verilog-ts--node-at-bol))
         (indent-node (verilog-ts--node-has-parent-recursive node "parameter_port_list"))
         (indent-node-line (line-number-at-pos (treesit-node-start indent-node)))
         (first-port-node (treesit-node-child indent-node 2)) ; parameter_port_declaration
         (first-port-node-line (line-number-at-pos (treesit-node-start first-port-node))))
    (eq indent-node-line first-port-node-line)))

(defun verilog-ts--continued-parameter-port (&rest _)
  "A tree-sitter simple indent matcher.
Return non-nil if matches continued declaration of parameter ports.
parameter A = 0,
          B = 1,
          C = 2"
  (let ((child-node (treesit-node-child (verilog-ts--node-at-bol) 0)))
    (string= (treesit-node-type child-node) "data_type")))

;;;; Anchors
(defun verilog-ts--end-indent-anchor (node parent &rest _)
  "A tree-sitter simple indent anchor.
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

(defun verilog-ts--expression-anchor (node parent &rest _)
  "A tree-sitter simple indent anchor.
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

(defun verilog-ts--grandparent-bol-indent-anchor (node parent &rest _)
  "A tree-sitter simple indent anchor.
Find the beginning of line of node's grandparent.
INFO: Might be present in future Emacs releases.
Check `treesit' and `treesit-simple-indent-presets'."
  (save-excursion
    (goto-char (treesit-node-start (treesit-node-parent parent)))))

(defun verilog-ts--tf-port-list-anchor (node parent &rest _)
  "A tree-sitter simple indent anchor.
Indent task/function arguments."
  (let ((indent-node (or (verilog-ts--node-has-parent-recursive node "class_method")
                         (verilog-ts--node-has-parent-recursive node "task_declaration")
                         (verilog-ts--node-has-parent-recursive node "function_declaration"))))
    (save-excursion
      (if indent-node
          (goto-char (treesit-node-start indent-node))
        (point)))))

(defun verilog-ts--tf-port-item1-anchor (node parent &rest _)
  "A tree-sitter simple indent anchor.
Indent task/function arguments."
  (let ((indent-node (verilog-ts--node-has-parent-recursive node "tf_port_list")))
    (save-excursion
      (if indent-node
          (goto-char (treesit-node-start indent-node))
        (point)))))

(defun verilog-ts--ansi-port-anchor (node parent &rest _)
  "A tree-sitter simple indent anchor.
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

(defun verilog-ts--ansi-port (node parent &rest _)
  "A tree-sitter simple indent anchor.
Indent ansi_ports according to module definition."
  (let ((indent-node (or (verilog-ts--node-has-parent-recursive node "module_declaration")
                         (verilog-ts--node-has-parent-recursive node "interface_declaration"))))
    (when indent-node
      (save-excursion
        (goto-char (treesit-node-start indent-node))
        (point)))))

(defun verilog-ts--coverpoint-bins-anchor (node parent &rest _)
  "A tree-sitter simple indent anchor.
Indent bins with respect to label of coverpoint."
  (let ((indent-node (verilog-ts--node-has-parent-recursive node "cover_point")))
    (save-excursion
      (goto-char (treesit-node-start indent-node)))))

(defun verilog-ts--cross-bins-anchor (node parent &rest _)
  "A tree-sitter simple indent anchor.
Indent cross bins with respect to label of coverpoint."
  (let ((indent-node (verilog-ts--node-has-parent-recursive node "cover_cross")))
    (save-excursion
      (goto-char (treesit-node-start indent-node)))))

(defun verilog-ts--continued-parameter-anchor (node parent &rest _)
  "A tree-sitter simple indent anchor.
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

(defun verilog-ts--parameter-port-anchor (node parent &rest _)
  "A tree-sitter simple indent anchor.
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

(defun verilog-ts--point-min-anchor (node parent &rest _)
  "A tree-sitter simple indent anchor."
  (save-excursion
    (point-min)))


(defvar verilog-ts--indent-rules
  `((verilog
     ;; Unit scope
     (verilog-ts--unit-scope verilog-ts--point-min-anchor 0) ; Place first for highest precedence
     ;; Comments
     ((and (node-is "comment")
           verilog-ts--unit-scope)
      verilog-ts--point-min-anchor 0)
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
           verilog-ts--ansi-port-after-paren)
      verilog-ts--ansi-port-anchor 0)
     ((node-is "ansi_port_declaration") verilog-ts--ansi-port ,verilog-ts-indent-level) ; Fallback of previous rule
     ((node-is "module_or_generate_item") parent-bol ,verilog-ts-indent-level)
     ((node-is "interface_or_generate_item") parent-bol ,verilog-ts-indent-level)
     ((node-is "list_of_param_assignments") parent-bol ,verilog-ts-indent-level) ; First instance parameter (without parameter keyword)
     ((and (node-is "parameter_port_declaration")
           verilog-ts--continued-parameter-port)
      verilog-ts--continued-parameter-anchor 0)
     ((and (node-is "parameter_port_declaration")
           verilog-ts--parameter-port-after-paren)
      verilog-ts--parameter-port-anchor 0)
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
     ((node-is "end") verilog-ts--end-indent-anchor 0)
     ;; Closing
     ((or (node-is "else")         ; Parent is 'if
          (node-is "join_keyword") ; Parent is 'fork
          (node-is "}")
          (node-is ")")
          (node-is "]"))
      parent-bol 0)
     ;; Opening. TODO: I think these are never hit?
     ((or (node-is "{")
          (node-is "("))
      parent-bol 0)
     ;; Macros
     ((and (node-is "class_item") ; Place before (node-is "class_item") to match with higher precedence
           verilog-ts--uvm-field-macro)
      parent-bol 8)
     ;; Others
     ((node-is "class_item") parent-bol ,verilog-ts-indent-level)
     ((node-is "timeunits_declaration") parent-bol ,verilog-ts-indent-level)
     ((node-is "tf_port_list") verilog-ts--tf-port-list-anchor ,verilog-ts-indent-level)              ; Task ports in multiple lines (first line)
     ((node-is "tf_port_item1") verilog-ts--tf-port-item1-anchor 0)       ; Task ports in multiple lines
     ((node-is "constraint_block_item") parent-bol ,verilog-ts-indent-level)
     ((node-is "enum_name_declaration") parent-bol ,verilog-ts-indent-level)
     ((node-is "generate_region") parent-bol ,verilog-ts-indent-level)
     ((node-is "hierarchical_instance") parent-bol 0) ; Instance name in separate line
     ((node-is "constraint_expression") parent-bol ,verilog-ts-indent-level) ; Instance name in separate line
     ((node-is "bins_or_options") verilog-ts--coverpoint-bins-anchor ,verilog-ts-indent-level) ; Instance name in separate line
     ((node-is "cross_body_item") verilog-ts--cross-bins-anchor ,verilog-ts-indent-level) ; Instance name in separate line
     ((node-is "dist_list") parent-bol ,verilog-ts-indent-level) ; Instance name in separate line
     ((node-is "dist_item") verilog-ts--grandparent-bol-indent-anchor ,verilog-ts-indent-level) ; Instance name in separate line
     ;; Continued lines
     ((node-is "expression") verilog-ts--expression-anchor 0)
     ((node-is "constant_expression") parent-bol 0)
     ((node-is "variable_decl_assignment") parent 0)
     ((node-is "param_assignment") parent 0)
     ((node-is "module_ansi_header") parent-bol 0) ; Opening bracket of module ports/parmeters
     ;; Blank lines
     (verilog-ts--blank-line parent-bol ,verilog-ts-indent-level)
     ;; Default indent
     (verilog-ts--default-indent parent-bol ,verilog-ts-indent-level)
     )))


;;; Imenu
(defun verilog-ts--defun-name (node)
  "Return the defun name of NODE.
Return nil if there is no name or if NODE is not a defun node."
  (verilog-ts--node-identifier-name node))


;;; Navigation
(defconst verilog-ts--defun-type-regexp
  (regexp-opt '("module_declaration"
                "interface_ansi_header"
                "class_declaration"
                "function_declaration"
                "task_declaration"
                "class_method")))

;;; Completion
(defvar verilog-ts-capf-table nil)
(defconst verilog-ts-async-inject-variables-re "\\`\\(load-path\\|buffer-file-name\\)")

(defun verilog-ts-capf-create-table ()
  "Verilog tree-sitter create completion at point table synchronously."
  (let (completions)
    (dolist (file (directory-files-recursively (project-root (project-current)) "\\.[s]?v[h]?$"))
      (with-temp-buffer
        (message "Processing %s" file)
        (insert-file-contents file)
        (verilog-ts-mode)
        (setq completions (append (verilog-ts-nodes-current-buffer "simple_identifier") completions))))
    (delete-dups completions)
    (setq verilog-ts-capf-table completions)))

(defun verilog-ts-capf-create-table-async ()
  "Verilog tree-sitter create completion at point table asynchronously."
  (message "Starting tag collection for %s" (project-root (project-current)))
  (async-start
   `(lambda ()
      ,(async-inject-variables verilog-ts-async-inject-variables-re)
      (require 'verilog-mode)
      (require 'verilog-ts-mode)
      (verilog-ts-capf-create-table))
   (lambda (result)
     (message "Finished collection tags!")
     (setq verilog-ts-capf-table result))))

(defun verilog-ts-capf ()
  "Verilog tree-sitter completion at point.
Complete with identifiers of current project."
  (interactive)
  (let* ((bds (bounds-of-thing-at-point 'symbol))
         (start (car bds))
         (end (cdr bds)))
    (list start end verilog-ts-capf-table . nil)))


;;; Major-mode
(defvar-keymap verilog-ts-mode-map
  :doc "Keymap for SystemVerilog language with tree-sitter"
  :parent verilog-mode-map
  "TAB" #'indent-for-tab-command)

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
    (setq-local treesit-font-lock-settings verilog--treesit-settings)
    ;; Indent.
    (setq-local indent-line-function nil)
    (setq-local comment-indent-function nil)
    (setq-local treesit-simple-indent-rules verilog-ts--indent-rules)
    ;; Navigation.
    (setq-local treesit-defun-type-regexp verilog-ts--defun-type-regexp)
    ;; Imenu.
    (setq-local treesit-defun-name-function #'verilog-ts--defun-name)
    (setq-local treesit-simple-imenu-settings
                `(("Class" "\\`class_declaration\\'" nil nil)
                  ("Task" "\\`task_declaration\\'" nil nil)
                  ("Func" "\\`function_declaration\\'" nil nil)))
    ;; Completion
    (add-hook 'completion-at-point-functions 'verilog-ts-capf nil 'local)
    ;; Setup.
    (treesit-major-mode-setup)))


;;; Provide
(provide 'verilog-ts-mode)

;;; verilog-ts-mode.el ends here

