;;; verilog-tree-sitter.el --- Verilog Tree-sitter  -*- lexical-binding: t -*-

;; Copyright (C) 2022 Gonzalo Larumbe

;; Author: Gonzalo Larumbe <gonzalomlarumbe@gmail.com>
;; URL: https://github.com/gmlarumbe/verilog-ext
;; Version: 0.0.0
;; Keywords: Verilog, IDE, Tools
;; Package-Requires: ((emacs "28.1"))

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
;;; Code:


(require 'treesit)

;; TODO: There are some keywords that are not recognized.
;; For these ones, use regexp matching patterns inside tree-sitter
(setq verilog-ts-keywords
      ;; Block delimiters
      '(
        (module_keyword)
        "endmodule"
        "program"
        "endprogram"
        "class"
        "endclass"
        "interface"
        "endinterface"
        "package"
        "endpackage"
        "checker"
        "endchecker"
        "config"
        "endconfig"

        "final"
        "alias"
        "iff"
        "illegal_bins"
        "intersect"
        "module"
        "class"
        "unique"
        "property"
        ;; "after"
        "macromodule"
        ;; "connectmodule"
        "interconnect"
        "showcancelled"
        "soft"
        "forkjoin"
        "or"
        "assume"

        "pure"
        "virtual"
        "extends"
        "implements"
        "super"
        (class_item_qualifier)

        "parameter"
        "localparam"
        "defparam"
        "assign"
        "typedef"
        "modport"
        "fork"
        "join"
        "join_none"
        "join_any"
        "default"
        "break"
        "assert"
        (unique_priority)
        "tagged"
        "extern"


        "function"
        "endfunction"

        "task"
        "endtask"

        "return"

        ;; [
        ;; ] @label
        ;; "begin"
        ;; "end"

        ;; [
        ;; ] @repeat
        (always_keyword)
        "generate"
        "for"
        "foreach"
        "repeat"
        "forever"
        "initial"
        "while"

        ;; [
        ;; ] @conditional
        "if"
        "else"
        (case_keyword)
        "endcase"

        (edge_identifier)
        (net_type)
        "timeprecision"
        "timeunit"
        "import"
        "#"
        "##"
        (lifetime) ; automatic/static?
        "enum"
        "rand"
        "constraint"
        "new"
        ))


(setq verilog-ts-operators
      '(
        "="
        ;; "-"
        ;; "+"
        ;; "/"
        ;; "*"
        ;; "^"
        ;; "&"
        ;; "|"
        ;; "&&"
        ;; "||"
        ":" ; TODO: What about this one? Better to take it out?
        (unary_operator)
        "{"
        "}"
        "'{"
        "<="
        "@"
        "or"
        "and"
        "=="
        "!="
        "==="
        "!=="
        "-:"
        "<"
        ">"
        ">="
        "%"
        ">>"
        "<<"
        "|="
        (inc_or_dec_operator)

        ;; Not sure about this one...
        ;; (cast
        ;;  ["'" "(" ")"] @operator)

        "?"
        ))

(setq verilog-ts-bold-operators
      '(
        ;; "="
        "-"
        "+"
        "/"
        "*"
        "^"
        "&"
        "|"
        "&&"
        "||"
        ;; ":" ; TODO: What about this one? Better to take it out?
        ;; (unary_operator)
        "{"
        "}"
        "'{"
        "<="
        "@"
        "or"
        "and"
        "=="
        "!="
        "==="
        "!=="
        "-:"
        "<"
        ">"
        ">="
        "%"
        ">>"
        "<<"
        "|="
        (inc_or_dec_operator)

        ;; Not sure about this one...
        ;; (cast
        ;;  ["'" "(" ")"] @operator)

        "?"
        ))


(setq verilog-ts-punctuation
      '(
        "["
        "]"
        "("
        ")"
        ;; ] @punctuation.delimiter
        ";"
        "::"
        ","
        "."
        ))


(setq verilog--treesit-settings
      (treesit-font-lock-rules
       :feature 'comment
       :language 'verilog
       '((comment) @font-lock-comment-face)

       :feature 'string
       :language 'verilog
       '((string_literal) @font-lock-string-face
         (double_quoted_string) @font-lock-string-face)

       :feature 'keyword
       :language 'verilog
       `([,@verilog-ts-keywords] @font-lock-keyword-face)

       :feature 'misc
       :language 'verilog
       '(;; Ports
         ((port_direction) @verilog-ext-font-lock-direction-face)
         ;; Ports with user types
         (ansi_port_declaration
          (net_port_header1
           (net_port_type1
            (simple_identifier) @font-lock-type-face)))
         ;; Ports in checkers TODO (instances of 1 port wrongly detected as checkers?)
         (formal_port_identifier
          (simple_identifier) @font-lock-constant-face)
         ;; Arrays
         ((packed_dimension
           (constant_range) @verilog-ext-font-lock-braces-content-face))
         ;; ((packed_dimension
         ;;   (constant_expression) @verilog-ext-font-lock-braces-content-face))
         ((unpacked_dimension
           (constant_range) @verilog-ext-font-lock-braces-content-face))
         ((unpacked_dimension
           (constant_expression) @verilog-ext-font-lock-braces-content-face))
         (bit_select1
          (expression) @verilog-ext-font-lock-braces-content-face)
         (constant_select1
          (constant_expression) @verilog-ext-font-lock-braces-content-face)
         ;; Timeunit
         ((time_unit) @font-lock-constant-face)
         ;; Radix
         ;; (expression
         ;;  (primary
         ;;   (primary_literal
         ;;    (integral_number) @font-lock-constant-face)))

         ;; System function
         ((system_tf_call
           (system_tf_identifier) @font-lock-builtin-face))
         ;; Enum labels
         (enum_name_declaration
          (enum_identifier
           (simple_identifier) @font-lock-constant-face))
         ;; Begin-end
         (["begin" "end"] @verilog-ext-font-lock-grouping-keywords-face)
         ;; Package identifiers

         ;; ((:match "\\<package\\>\\s-+\\([a-zA-Z_]+\\)") @font-lock-function-name-face)

         ;; (package_identifier
         ;;  (simple_identifier) @font-lock-function-name-face)

         ;; INFO: It was white before, is this important?
         (parameter_identifier
          (simple_identifier) @font-lock-doc-face)

         )

       :feature 'operator
       :language 'verilog
       `(([,@verilog-ts-operators] @verilog-ext-font-lock-punctuation-face)
         ([,@verilog-ts-bold-operators] @verilog-ext-font-lock-punctuation-bold-face))

       :feature 'punctuation
       :language 'verilog
       `([,@verilog-ts-punctuation] @verilog-ext-font-lock-punctuation-face)

       :feature 'macros
       :language 'verilog
       '((["directive_include"
           "directive_timescale"
           "directive_default_nettype"]
          @verilog-ext-font-lock-preprocessor-face)

         (text_macro_identifier
          (simple_identifier) @verilog-ext-font-lock-preprocessor-face))

       :feature 'module
       :language 'verilog
       '(;; Module declaration
         (module_header
          (module_keyword) @font-lock-keyword-face
          ;; (lifetime) @font-lock-type-face ;; TODO: Don't know how to make it optional.
          (simple_identifier) @font-lock-function-name-face)
         ;; Module instantiation (wihtout parameters)
         (module_instantiation
          (simple_identifier) @verilog-ext-font-lock-module-face
          (hierarchical_instance
           (name_of_instance
            (instance_identifier
             (simple_identifier) @verilog-ext-font-lock-instance-face))
           (list_of_port_connections
            (named_port_connection
             (port_identifier
              (simple_identifier) @verilog-ext-font-lock-port-connection-face)))))
         ;; Module instantiation parameters: INFO: Commented out to make it more general for interfaces/classes parameters
         ;; (module_instantiation
         ;;  (parameter_value_assignment
         ;;   (list_of_parameter_assignments
         ;;    (named_parameter_assignment
         ;;     (parameter_identifier
         ;;      (simple_identifier) @font-lock-doc-face)))))

         ;; TODO: Tried to mix the two above but it didn't work
         ;; (module_instantiation
         ;;  (simple_identifier) @font-lock-function-name-face
         ;;  (parameter_value_assignment
         ;;   (list_of_parameter_assignments
         ;;    (named_parameter_assignment
         ;;     (parameter_identifier
         ;;      (simple_identifier) @font-lock-doc-face))))
         ;;  (hierarchical_instance
         ;;   (name_of_instance
         ;;    (instance_identifier
         ;;     (simple_identifier) @font-lock-preprocessor-face))
         ;;   (list_of_port_connections
         ;;    (named_port_connection
         ;;     (port_identifier
         ;;      (simple_identifier) @font-lock-constant-face)))))

         ;; TODO: Instances of 1 port are detected as checkers? Also happens for interfaces?
         (checker_instantiation
          (checker_identifier
           (simple_identifier) @font-lock-function-name-face)
          (name_of_instance
           (instance_identifier
            (simple_identifier) @font-lock-doc-face)))

         ;; Interfaces
         (interface_declaration
          (interface_ansi_header
           (interface_identifier
            (simple_identifier) @font-lock-function-name-face)))
         )

       :feature 'types
       :language 'verilog
       '((data_type
          (integer_vector_type) @font-lock-type-face)
         (data_type
          (integer_atom_type) @font-lock-type-face)
         ((data_type_or_void
           (data_type) @font-lock-type-face))
         (data_type_or_implicit1
          (data_type
           (simple_identifier) @font-lock-type-face))
         ;; User type variable declaration
         ;; TODO: Commented since this generates problems because of unsupported
         ;; external method body declaration.
         (net_declaration
          (simple_identifier) @font-lock-type-face)
         ;; Enum base type
         (enum_base_type) @font-lock-type-face
         ;; Others
         (["void"] @font-lock-type-face)
         )

       :feature 'definition
       :language 'verilog
       '(

         ;; TODO: Externally defined function/task body. Still doesn't work well in master's grammar
         (class_scope
          (class_type
           (class_identifier
            (simple_identifier) @font-lock-constant-face)))
         ;; End of TODO
         (function_identifier
          (function_identifier
           (simple_identifier) @font-lock-function-name-face))
         (task_identifier
          (task_identifier
           (simple_identifier) @font-lock-function-name-face))
         ;; TODO: Similar to thing in module instances with parameters, tried to make it together but didn't work
         ;; (class_declaration
         ;;  (class_identifier) @font-lock-function-name-face ; class name
         ;;  (class_type
         ;;   (class_identifier
         ;;    (simple_identifier) @font-lock-type-face))) ; parent class
         ;; Class name
         ((class_declaration
           (class_identifier) @font-lock-function-name-face))
         ;; Parent class
         ((class_declaration
           (class_type
            (class_identifier
             (simple_identifier) @font-lock-type-face))))
         ;; Function arguments (more generic capture group in 'types)
         ;; (tf_port_list
         ;;  (tf_port_item1
         ;;   (data_type_or_implicit1
         ;;    (data_type
         ;;     (simple_identifier) @font-lock-type-face))))


         ;;   (function_declaration
         ;;  (function_body_declaration
         ;;   (function_data_type_or_implicit1
         ;;    (data_type_or_void))
         ;;   (function_identifier
         ;;    (function_identifier (simple_identifier)))
         ;; ) ; parent class


         )
       )
      ;; "Tree-sitter font-lock settings."
      )

(define-derived-mode verilog-ts-mode verilog-mode "Verilog"
  "Major mode for editing SystemVerilog files, using tree-sitter library."
  :syntax-table verilog-mode-syntax-table
  (setq font-lock-defaults nil)
  (when (treesit-ready-p 'verilog)
    (treesit-parser-create 'verilog)
    ;; (setq-local treesit-font-lock-feature-list
    ;;             '(( comment definition)
    ;;               ( keyword string type)
    ;;               ( assignment builtin constant decorator
    ;;                 escape-sequence number property string-interpolation )
    ;;               ( bracket delimiter function operator variable)))
    (setq-local treesit-font-lock-feature-list
                '((comment string keyword operator macros types punctuation misc module definition)))
    (setq-local treesit-font-lock-settings verilog--treesit-settings)
    (treesit-major-mode-setup)))



(provide 'verilog-tree-sitter)

;;; verilog-tree-sitter.el ends here





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Function/tasks identifiers


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Method qualifiers (virtual/local/protected/pure)
;; (class_method
;;  (method_qualifier) @function.builtin)

;; Class function prototypes return types
;; (class_item
;;  (class_method
;;   (function_prototype
;;    (data_type_or_void) @type)))

;; Class function declaration return types
;; (function_declaration
;;  (function_body_declaration
;;   (function_data_type_or_implicit1
;;    (data_type_or_void) @type)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; User typedefs

;; Modules/Instances
;; (module_instantiation
;;  (simple_identifier) @verilog-module
;;  (hierarchical_instance
;;   (name_of_instance
;;    (instance_identifier
;;     (simple_identifier) @verilog-instance))))


;; Class types (attributes) - Put before class extensions?
;; (class_item
;;  (class_property
;;   (data_declaration
;;    (data_type_or_implicit1
;;     (data_type
;;      (class_type
;;       (class_identifier
;;        (simple_identifier) @type)))))))

;; (class_item
;;  (class_property
;;   (data_declaration
;;    (data_type_or_implicit1
;;     (data_type
;;      (simple_identifier) @type)))))



;; (package_import_declaration
;;  "import" @include)

;; (package_import_declaration
;;  (package_import_item
;;   (package_identifier
;;    (simple_identifier) @constant)))

;; (package_scope
;;  (package_identifier
;;   (simple_identifier) @constant))

;; (package_declaration
;;  (package_identifier
;;   (simple_identifier) @constant))

;; (parameter_port_list
;;  "#" @constructor)


;; (port_identifier
;;  (simple_identifier) @variable)

;; [
;;   (integer_vector_type)
;;   (integer_atom_type)
;; ] @type.builtin

;; [
;;   "signed"
;;   "unsigned"
;; ] @label

;; (data_type
;;  (simple_identifier) @type)

;; (method_call_body
;;   (method_identifier) @field)

;; (interface_identifier
;;  (simple_identifier) @type)

;; (modport_identifier
;;  (modport_identifier
;;   (simple_identifier) @field))

;; (net_port_type1
;;  (simple_identifier) @type)

;; [
;;   (double_quoted_string)
;;   (string_literal)
;; ] @string


;; ; begin/end label
;; (seq_block
;;  (simple_identifier) @comment)



;; (default_nettype_compiler_directive
;;  (default_nettype_value) @string)

;; (text_macro_identifier
;;  (simple_identifier) @constant)

;; (module_declaration
;;  (module_header
;;   (simple_identifier) @constructor))


;; (parameter_identifier
;;  (simple_identifier) @parameter)

;; [
;;   (integral_number)
;;   (unsigned_number)
;;   (unbased_unsized_literal)
;; ] @number

;; (time_unit) @attribute

;; (checker_instantiation
;;  (checker_identifier
;;   (simple_identifier) @constructor))

;; (module_instantiation
;;  (simple_identifier) @constructor)

;; (name_of_instance
;;  (instance_identifier
;;   (simple_identifier) @variable))

;; (interface_port_declaration
;;  (interface_identifier
;;   (simple_identifier) @type))

;; (lifetime) @label


;; (function_subroutine_call
;;  (subroutine_call
;;   (tf_call
;;    (simple_identifier) @function)))

;; (function_subroutine_call
;;  (subroutine_call
;;   (system_tf_call
;;    (system_tf_identifier) @function.builtin)))


;; ;;TODO: fixme
;; ;(assignment_pattern_expression
;;  ;(assignment_pattern
;;   ;(parameter_identifier) @field))

;; (type_declaration
;;   (data_type ["packed"] @label))

;; (struct_union) @type

;; [
;;   "enum"
;; ] @type

;; (enum_name_declaration
;;  (enum_identifier
;;   (simple_identifier) @constant))


;; [
;;   (integer_atom_type)
;;   (non_integer_type)
;;   "genvar"
;; ] @type.builtin

;; (struct_union_member
;;  (list_of_variable_decl_assignments
;;   (variable_decl_assignment
;;    (simple_identifier) @field)))

;; (member_identifier
;;  (simple_identifier) @field)

;; (struct_union_member
;;  (data_type_or_void
;;   (data_type
;;    (simple_identifier) @type)))

;; (type_declaration
;;  (simple_identifier) @type)

;; (generate_block_identifier) @comment


;; TODO: Tests here
;; (simple_identifier
;;  (.match? @constant "after")) @constant



;; TODO: Still does not support external function declarations
;; (function_body_declaration
;;  (function_identifier
;;   (simple_identifier) @function.builtin)
;;  (ERROR
;;   (class_identifier
;;    (simple_identifier) @function)))


;; ;; Error
;; ;; TODO: Not sure if it's a good idea to highlight this
;; ;; , since not all code is supported:
;; ;;  - e.g.: macros inside ports show as an ERROR
;; ;;  - external function declarations also show as ERROR
;; ;; (ERROR) @error
