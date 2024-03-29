;;; verilog-ext-capf.el --- Verilog-ext Completion at point  -*- lexical-binding: t -*-

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

;; Completion at point utils

;;; Code:

(require 'verilog-ext-tags)

;; Fetched from IEEE 1800-2012
;; https://ece.uah.edu/~gaede/cpe526/2012%20System%20Verilog%20Language%20Reference%20Manual.pdf
(defconst verilog-ext-capf-system-tf
  '(;; Section 18.13: Random number system functions and methods
    "$urandom" "$urandom_range"
    ;; Section 20: Utility system tasks and system functions
    ;; Simulation control tasks (20.2)
    "$finish" "$stop" "$exit"
    ;; Simulation time functions (20.3)
    "$realtime" "$stime" "$time"
    ;; Timescale tasks (20.4)
    "$printtimescale" "$timeformat"
    ;; Conversion functions (20.5)
    "$bitstoreal" "$realtobits" "$bitstoshortreal" "$shortrealtobits" "$itor"
    "$rtoi" "$signed" "$unsigned" "$cast"
    ;; Data query functions (20.6)
    "$bits" "$isunbounded" "$typename"
    ;; Array query functions (20.7)
    "$unpacked_dimensions" "$dimensions" "$left" "$right" "$low" "$high"
    "$increment" "$size"
    ;; Math functions (20.8)
    "$clog2" "$asin" "$ln" "$acos" "$log10" "$atan" "$exp" "$atan2" "$sqrt"
    "$hypot" "$pow" "$sinh" "$floor" "$cosh" "$ceil" "$tanh" "$sin" "$asinh"
    "$cos" "$acosh" "$tan" "$atanh"
    ;; Bit vector system functions (20.9)
    "$countbits" "$countones" "$onehot" "$onehot0" "$isunknown"
    ;; Severity tasks (20.10)
    "$fatal" "$error" "$warning" "$info"
    ;; Elaboration tasks (20.11)
    "$fatal" "$error" "$warning" "$info"
    ;; Assertion control tasks (20.12)
    "$asserton" "$assertoff" "$assertkill" "$assertcontrol" "$assertpasson"
    "$assertpassoff" "$assertfailon" "$assertfailoff" "$assertnonvacuouson"
    "$assertvacuousoff"
    ;; Sampled value system functions (20.13)
    "$sampled" "$rose" "$fell" "$stable" "$changed" "$past" "$past_gclk"
    "$rose_gclk" "$fell_gclk" "$stable_gclk" "$changed_gclk" "$future_gclk"
    "$rising_gclk" "$falling_gclk" "$steady_gclk" "$changing_gclk"
    ;; Coverage control functions (20.14)
    "$coverage_control" "$coverage_get_max" "$coverage_get" "$coverage_merge"
    "$coverage_save" "$get_coverage" "$set_coverage_db_name" "$load_coverage_db"
    ;; Probabilistic distribution functions (20.15)
    "$random" "$dist_chi_square" "$dist_erlang" "$dist_exponential"
    "$dist_normal" "$dist_poisson" "$dist_t" "$dist_uniform"
    ;; Stochastic analysis tasks and functions (20.16)
    "$q_initialize" "$q_add" "$q_remove" "$q_full" "$q_exam"
    ;; PLA modeling tasks (20.17)
    "$async$and$array" "$async$and$plane" "$async$nand$array"
    "$async$nand$plane" "$async$or$array" "$async$or$plane" "$async$nor$array"
    "$async$nor$plane" "$sync$and$array" "$sync$and$plane" "$sync$nand$array"
    "$sync$nand$plane" "$sync$or$array" "$sync$or$plane" "$sync$nor$array"
    "$sync$nor$plane"
    ;; Miscellaneous tasks and functions (20.18)
    "$system"
    ;; Section 21: Input/output system tasks and system function
    ;; Display tasks (21.2)
    "$display" "$write" "$displayb" "$writeb" "$displayh" "$writeh" "$displayo"
    "$writeo" "$strobe" "$monitor" "$strobeb" "$monitorb" "$strobeh" "$monitorh"
    "$strobeo" "$monitoro" "$monitoroff" "$monitoron"
    ;; File I/O tasks and functions (21.3)
    "$fclose" "$fopen" "$fdisplay" "$fwrite" "$fdisplayb" "$fwriteb"
    "$fdisplayh" "$fwriteh" "$fdisplayo" "$fwriteo" "$fstrobe" "$fmonitor"
    "$fstrobeb" "$fmonitorb" "$fstrobeh" "$fmonitorh" "$fstrobeo" "$fmonitoro"
    "$swrite" "$sformat" "$swriteb" "$sformatf" "$swriteh" "$fgetc" "$swriteo"
    "$ungetc" "$fscanf" "$fgets" "$fread" "$sscanf" "$fseek" "$rewind" "$fflush"
    "$ftell" "$feof" "$ferror"
    ;; Memory load tasks (21.4)
    "$readmemb" "$readmemh"
    ;; Memory dump tasks (21.5)
    "$writememb" "$writememh"
    ;; Command line input (21.6)
    "$test$plusargs" "$value$plusargs"
    ;; VCD tasks (21.7)
    "$dumpfile" "$dumpvars" "$dumpoff" "$dumpon" "$dumpall" "$dumplimit"
    "$dumpflush" "$dumpports" "$dumpportsoff" "$dumpportson" "$dumpportsall"
    "$dumpportslimit" "$dumpportsflush"))

(defconst verilog-ext-capf-directives
  '(;; Section 22: Compiler directives
    "`__FILE__" "`__LINE__" "`begin_keywords" "`celldefine" "`default_nettype"
    "`define" "`else" "`elsif" "`end_keywords" "`endcelldefine" "`endif" "`ifdef"
    "`ifndef" "`include" "`line" "`nounconnected_drive" "`pragma" "`resetall"
    "`timescale" "`unconnected_drive" "`undef" "`undefineall"
    ;; Fetched from Accellera UVM Class reference manual:
    ;; https://www.accellera.org/images/downloads/standards/uvm/UVM_Class_Reference_Manual_1.2.pdf
    ;; Section 21.1: Report Macros
    "`uvm_info" "`uvm_warning" "`uvm_error" "`uvm_fatal" "`uvm_info_context"
    "`uvm_warning_context" "`uvm_error_context" "`uvm_fatal_context"
    "`uvm_info_begin" "`uvm_info_end" "`uvm_warning_begin" "`uvm_warning_end"
    "`uvm_error_begin" "`uvm_error_end" "`uvm_fatal_begin" "`uvm_fatal_end"
    "`uvm_info_context_begin" "`uvm_info_context_end"
    "`uvm_warning_context_begin" "`uvm_warning_context_end"
    "`uvm_error_context_begin" "`uvm_error_context_end"
    "`uvm_fatal_context_begin" "`uvm_fatal_context_end" "`uvm_message_add_tag"
    "`uvm_message_add_int" "`uvm_message_add_string" "`uvm_message_add_object"
    ;; Section 21.2: Utility and Field Macros for Components and Objects
    "`uvm_field_utils_begin" "`uvm_field_utils_end" "`uvm_object_utils"
    "`uvm_object_param_utils" "`uvm_object_utils_begin"
    "`uvm_object_param_utils_begin" "`uvm_object_utils_end"
    "`uvm_component_utils" "`uvm_component_param_utils"
    "`uvm_component_utils_begin" "`uvm_component_param_utils_begin"
    "`uvm_component_end" "`uvm_object_registry" "`uvm_component_registry"
    "`uvm_field_int" "`uvm_field_object" "`uvm_field_string" "`uvm_field_enum"
    "`uvm_field_real" "`uvm_field_event" "`uvm_field_sarray_int"
    "`uvm_field_sarray_object" "`uvm_field_sarray_string"
    "`uvm_field_sarray_enum" "`uvm_field_array_int" "`uvm_field_array_object"
    "`uvm_field_array_string" "`uvm_field_array_enum" "`uvm_field_queue_int"
    "`uvm_field_queue_object" "`uvm_field_queue_string" "`uvm_field_queue_enum"
    "`uvm_field_aa_int_string" "`uvm_field_aa_object_string"
    "`uvm_field_aa_string_string" "`uvm_field_aa_object_int"
    "`uvm_field_aa_int_int" "`uvm_field_aa_int_int_unsigned"
    "`uvm_field_aa_int_integer" "`uvm_field_aa_int_integer_unsigned"
    "`uvm_field_aa_int_byte" "`uvm_field_aa_int_byte_unsigned"
    "`uvm_field_aa_int_shortint" "`uvm_field_aa_int_shortint_unsigned"
    "`uvm_field_aa_int_longint" "`uvm_field_aa_int_longint_unsigned"
    "`uvm_field_aa_int_key" "`uvm_field_aa_int_enumkey" "`uvm_record_attribute"
    "`uvm_record_int" "`uvm_record_string" "`uvm_record_time" "`uvm_record_real"
    "`uvm_record_field" "`uvm_pack_intN" "`uvm_pack_enumN" "`uvm_pack_sarrayN"
    "`uvm_pack_arrayN" "`uvm_pack_queueN" "`uvm_pack_int" "`uvm_pack_enum"
    "`uvm_pack_string" "`uvm_pack_real" "`uvm_pack_sarray" "`uvm_pack_array"
    "`uvm_pack_queue" "`uvm_unpack_intN" "`uvm_unpack_enumN"
    "`uvm_unpack_sarrayN" "`uvm_unpack_arrayN" "`uvm_unpack_queueN"
    "`uvm_unpack_int" "`uvm_unpack_enum" "`uvm_unpack_string" "`uvm_unpack_real"
    "`uvm_unpack_sarray" "`uvm_unpack_array" "`uvm_unpack_queue"
    ;; Section 21.3 Sequence-Related Macros
    "`uvm_create" "`uvm_do" "`uvm_do_pri" "`uvm_do_with" "`uvm_do_pri_with"
    "`uvm_create_on" "`uvm_do_on" "`uvm_do_on_pri" "`uvm_do_on_with"
    "`uvm_do_on_pri_with" "`uvm_send" "`uvm_send_pri" "`uvm_rand_send"
    "`uvm_rand_send_pri" "`uvm_rand_send_with" "`uvm_rand_send_pri_with"
    "`uvm_add_to_sequence_library" "`uvm_declare_p_sequencer"
    ;; Section 21.4 Callback Macros
    "`uvm_register_cb" "`uvm_set_super_type" "`uvm_do_callbacks"
    "`uvm_do_obj_callbacks" "`uvm_do_callbacks_exit_on"
    "`uvm_do_obj_callbacks_exit_on"
    ;; Section 21.5 TLM Implementation Port Declaration Macros
    "`uvm_blocking_put_imp_decl" "`uvm_nonblocking_put_imp_decl"
    "`uvm_put_imp_decl" "`uvm_blocking_get_imp_decl" "`uvm_nonblocking_get_imp_decl"
    "`uvm_get_imp_decl" "`uvm_blocking_peek_imp_decl"
    "`uvm_nonblocking_peek_imp_decl" "`uvm_peek_imp_decl"
    "`uvm_blocking_get_peek_imp_decl" "`uvm_nonblocking_get_peek_imp_decl"
    "`uvm_get_peek_imp_decl" "`uvm_blocking_master_imp_decl"
    "`uvm_nonblocking_master_imp_decl" "`uvm_master_imp_decl"
    "`uvm_blocking_slave_imp_decl" "`uvm_nonblocking_slave_imp_decl"
    "`uvm_slave_imp_decl" "`uvm_blocking_transport_imp_decl"
    "`uvm_nonblocking_transport_imp_decl" "`uvm_transport_imp_decl"
    "`uvm_analysis_imp_decl"
    ;; Section 21.6 Register Defines
    "`UVM_REG_ADDR_WIDTH" "`UVM_REG_DATA_WIDTH" "`UVM_REG_BYTENABLE_WIDTH"
    "`UVM_REG_CVR_WIDTH"
    ;; Section 21.7 UVM Version Defines
    "`UVM_MAJOR_REV" "`UVM_MINOR_REV" "`UVM_FIX_REV" "`UVM_NAME"
    "`UVM_VERSION_STRING" "`UVM_MAJOR_REV_1" "`UVM_MINOR_REV_2" "`UVM_VERSION_1_2"
    "`UVM_POST_VERSION_1_1"))

(defun verilog-ext-capf-get-table-entry (table &optional tag)
  "Get symbol at point entry from capf TABLE.

If TAG is nil, search for the entry that corresponds to `symbol-at-point'.
Otherwise search for TAG entry."
  (unless tag
    (setq tag (thing-at-point 'symbol :no-props)))
  (gethash tag table))

(defun verilog-ext-capf-get-entry-items (entry)
  "Get items from tags table ENTRY."
  (plist-get entry :items))

(defun verilog-ext-capf-get-entry-type (entry)
  "Get type from tags table ENTRY.

Only returns the type of the first occurrence in the :locs property of ENTRY."
  (let ((locs (plist-get entry :locs)))
    (plist-get (car locs) :type)))

(defun verilog-ext-capf-get-completions (table &optional tag)
  "Get completion candidates from TABLE.

If optional arg TAG is nil, get completions for symbol at point."
  (verilog-ext-capf-get-entry-items (verilog-ext-capf-get-table-entry table tag)))

(defun verilog-ext-capf--dot-completion-bounds ()
  "Return bounds of dot completion for `completion-at-point'.

Return value is a cons with (start . end) bounds."
  (let (start end)
    (cond ((eq (preceding-char) ?.)
           (setq start (point))
           (setq end (point)))
          ((save-excursion
             (skip-chars-backward verilog-identifier-sym-re)
             (setq start (point))
             (eq (preceding-char) ?.))
           (setq end (point)))
          (t
           nil))
    (when (and start end)
      (cons start end))))

(defun verilog-ext-capf--scope-completion-bounds ()
  "Return bounds of scope completion for `completion-at-point'.

Return value is a cons with (start . end) bounds."
  (let (start end)
    (cond ((looking-back "::" (- (point) 2))
           (setq start (point))
           (setq end (point)))
          ((save-excursion
             (skip-chars-backward verilog-identifier-sym-re)
             (setq start (point))
             (looking-back "::" (- (point) 2)))
           (setq end (point)))
          (t
           nil))
    (when (and start end)
      (cons start end))))

(defun verilog-ext-capf--system-tf-bounds ()
  "Return bounds of system tasks and functions for `completion-at-point'.

Return value is a cons with (start . end) bounds."
  (let (start end)
    (cond ((eq (preceding-char) ?$)
           (setq start (1- (point)))
           (setq end (point)))
          ((save-excursion
             (skip-chars-backward verilog-identifier-sym-re)
             (setq start (1- (point)))
             (eq (preceding-char) ?$))
           (setq end (point)))
          (t
           nil))
    (when (and start end)
      (cons start end))))

(defun verilog-ext-capf--directives-bounds ()
  "Return bounds of directives, if possible, for `completion-at-point'.

Return value is a cons with (start . end) bounds."
  (let (start end)
    (cond ((eq (preceding-char) ?`)
           (setq start (1- (point)))
           (setq end (point)))
          ((save-excursion
             (skip-chars-backward verilog-identifier-sym-re)
             (setq start (1- (point)))
             (eq (preceding-char) ?`))
           (setq end (point)))
          (t
           nil))
    (when (and start end)
      (cons start end))))

(defun verilog-ext-capf-annotation-function (cand)
  "Completion annotation function for candidate CAND.

Get candidate type from `verilog-ext-tags-defs-table' or if not found, from
`verilog-ext-tags-inst-table'.

See available types in `verilog-ext-tags-definitions-ts-re'."
  (let* ((proj (verilog-ext-buffer-proj))
         (defs-table (alist-get proj verilog-ext-tags-defs-table nil nil #'string=))
         (inst-table (alist-get proj verilog-ext-tags-inst-table nil nil #'string=))
         (entry (or (and defs-table (gethash cand defs-table))
                    (and inst-table (gethash cand inst-table))))
         (locs (plist-get entry :locs))
         (type (plist-get (car locs) :type))) ; INFO: Getting the type of the first appearance
    (cond (;; Type
           type
           (pcase type
             ;; Builtin
             ("function" "<f>")
             ("task"     "<t>")
             ;; Tree-sitter
             ("module_declaration"            "<mod>")
             ("interface_declaration"         "<itf>")
             ("program_declaration"           "<pgm>")
             ("package_declaration"           "<pkg>")
             ("class_declaration"             "<cls>")
             ("function_declaration"          "<f>")
             ("task_declaration"              "<t>")
             ("class_constructor_declaration" "<f>")
             ("constraint_declaration"        "<constraint>")
             ("covergroup_declaration"        "<covergroup>")
             (_ type)))
          (;; Keywords
           (member cand verilog-keywords)
           "<kwd>")
          (t ;; Default
           nil))))

(defun verilog-ext-capf ()
  "Complete with identifiers present in various hash tables.

Tables used: `verilog-ext-tags-defs-table', `verilog-ext-tags-inst-table' and
`verilog-ext-tags-refs-table'.

Show annotations using function `verilog-ext-capf-annotation-function'."
  (interactive)
  (let* ((proj (verilog-ext-buffer-proj))
         (defs-table (alist-get proj verilog-ext-tags-defs-table nil 'remove #'string=))
         (refs-table (alist-get proj verilog-ext-tags-refs-table nil 'remove #'string=))
         (inst-table (alist-get proj verilog-ext-tags-inst-table nil 'remove #'string=))
         (annotation-fn #'verilog-ext-capf-annotation-function)
         bounds start end completions)
    (cond (;; Dot completion for object methods/attributes and hierarchical references
           (setq bounds (verilog-ext-capf--dot-completion-bounds))
           (let (table-entry-value block-type)
             (save-excursion
               (goto-char (car bounds))
               (backward-char)
               (while (eq (preceding-char) ?\]) ; Skip array indexes
                 (verilog-ext-backward-sexp))
               (setq table-entry-value (or (verilog-ext-capf-get-table-entry defs-table)
                                           (verilog-ext-capf-get-table-entry inst-table))) ; Search for definitions of objects and instances
               (when table-entry-value
                 (setq block-type (verilog-ext-capf-get-entry-type table-entry-value))
                 (setq completions (append (verilog-ext-capf-get-completions defs-table block-type)
                                           (verilog-ext-capf-get-completions inst-table block-type)))))))
          (;; Class static methods/members and package items
           (setq bounds (verilog-ext-capf--scope-completion-bounds))
           (save-excursion
             (goto-char (car bounds))
             (backward-char 2)
             (while (eq (preceding-char) ?\]) ; Skip array indexes
               (verilog-ext-backward-sexp))
             (setq completions (append (verilog-ext-capf-get-completions defs-table)
                                       (verilog-ext-capf-get-completions inst-table)))))
          (;; System tasks and functions
           (setq bounds (verilog-ext-capf--system-tf-bounds))
           (setq completions verilog-ext-capf-system-tf))
          (;; Compiler directives
           (setq bounds (verilog-ext-capf--directives-bounds))
           (setq completions verilog-ext-capf-directives))
          (t ; Fallback, all project completions and lang keywords
           (setq bounds (bounds-of-thing-at-point 'symbol))
           (dolist (table `(,defs-table ,inst-table ,refs-table))
             (when table
               (maphash (lambda (key _value)
                          (push key completions))
                        table)))
           (delete-dups completions)
           (setq completions `(,@completions ,@verilog-keywords))))
    ;; Return value for `completion-at-point'
    (setq start (car bounds))
    (setq end (cdr bounds))
    (list start end completions
          :annotation-function annotation-fn
          :company-docsig #'identity)))

(defun verilog-ext-capf-set (&optional disable)
  "Enable or DISABLE builtin capf function."
  (if disable
      (remove-hook 'completion-at-point-functions #'verilog-ext-capf :local)
    (add-hook 'completion-at-point-functions #'verilog-ext-capf nil :local)))


(provide 'verilog-ext-capf)

;;; verilog-ext-capf.el ends here


