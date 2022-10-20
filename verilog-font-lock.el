;;; verilog-font-lock.el --- Verilog Custom Font Lock  -*- lexical-binding: t -*-

;; Copyright (C) 2022 Gonzalo Larumbe

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
;; Improved syntax highlighting based on `font-lock' keywords overriding.
;;
;; Multiline Font Locking has reliability limitations in Emacs.
;;  - https://www.gnu.org/software/emacs/manual/html_node/elisp/Multiline-Font-Lock.html
;;  - https://www.gnu.org/software/emacs/manual/html_node/elisp/Font-Lock-Multiline.html
;;
;; One way to ensure reliable rehighlighting of multiline font-lock constructs
;; is by using the `font-lock-multiline' text property.
;; - The `font-lock-multiline' variable might seem to be working but is not reliable.
;; - Using the `font-lock-multiline' property might apply to a few lines (such is the case).
;;   For longer sections it is necessary to create font lock custom functions and gets
;;   more complicated.
;;
;; Search based fontification:
;; - https://www.gnu.org/software/emacs/manual/html_node/elisp/Search_002dbased-Fontification.html
;;
;;; Code:


(require 'verilog-mode)
(require 'verilog-navigation)


;;;; Faces
(defvar verilog-ext-font-lock-grouping-keywords-face 'verilog-ext-font-lock-grouping-keywords-face)
(defface verilog-ext-font-lock-grouping-keywords-face
  '((t (:foreground "dark olive green")))
  "Face for grouping keywords: begin, end."
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-punctuation-face 'verilog-ext-font-lock-punctuation-face)
(defface verilog-ext-font-lock-punctuation-face
  '((t (:foreground "burlywood")))
  "Face for punctuation symbols: !,;:?'=<>*"
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-punctuation-bold-face 'verilog-ext-font-lock-punctuation-bold-face)
(defface verilog-ext-font-lock-punctuation-bold-face
  '((t (:inherit verilog-ext-font-lock-punctuation-face :weight extra-bold)))
  "Face for bold punctuation symbols, such as &^~+-/|."
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-braces-face 'verilog-ext-font-lock-braces-face)
(defface verilog-ext-font-lock-braces-face
  '((t (:foreground "goldenrod")))
  "Face for braces []."
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-brackets-face 'verilog-ext-font-lock-brackets-face)
(defface verilog-ext-font-lock-brackets-face
  '((t (:foreground "dark goldenrod")))
  "Face for brackets ()."
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-curly-brackets-face 'verilog-ext-font-lock-curly-brackets-face)
(defface verilog-ext-font-lock-curly-brackets-face
  '((t (:foreground "DarkGoldenrod2")))
  "Face for curly brackets {}."
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-port-connection-face 'verilog-ext-font-lock-port-connection-face)
(defface verilog-ext-font-lock-port-connection-face
  '((t (:foreground "bisque2")))
  "Face for port connections of instances.
.portA (signalA),
.portB (signalB)
);
"
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-dot-name-face 'verilog-ext-font-lock-dot-name-face)
(defface verilog-ext-font-lock-dot-name-face
  '((t (:foreground "gray70")))
  "Face for dot-name regexps:
- Interface signals, classes attributes/methods and hierarchical refs.

axi_if.Ready <= 1'b1;
obj.method();
"
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-braces-content-face 'verilog-ext-font-lock-braces-content-face)
(defface verilog-ext-font-lock-braces-content-face
  '((t (:foreground "yellow green")))
  "Face for content between braces: arrays, bit vector width and indexing."
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-width-num-face 'verilog-ext-font-lock-width-num-face)
(defface verilog-ext-font-lock-width-num-face
  '((t (:foreground "chartreuse2")))
  "Face for the bit width number expressions.
{1}'b1,
{4}'hF,
{3}'o7,
"
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-width-type-face 'verilog-ext-font-lock-width-type-face)
(defface verilog-ext-font-lock-width-type-face
  '((t (:foreground "sea green" :weight bold)))
  "Face for the bit width type expressions.
1'{b}1,
4'{h}F,
3'{o}7,
"
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-module-face 'verilog-ext-font-lock-module-face)
(defface verilog-ext-font-lock-module-face
  '((t (:foreground "green1")))
  "Face for module names."
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-instance-face 'verilog-ext-font-lock-instance-face)
(defface verilog-ext-font-lock-instance-face
  '((t (:foreground "medium spring green")))
  "Face for instance names."
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-time-event-face 'verilog-ext-font-lock-time-event-face)
(defface verilog-ext-font-lock-time-event-face
  '((t (:foreground "deep sky blue" :weight bold)))
  "Face for time-events: @ and #."
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-time-unit-face 'verilog-ext-font-lock-time-unit-face)
(defface verilog-ext-font-lock-time-unit-face
  '((t (:foreground "light steel blue")))
  "Face for time-units: ms, us, ns, ps, fs (delays and timescale/timeprecision)."
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-preprocessor-face 'verilog-ext-font-lock-preprocessor-face)
(defface verilog-ext-font-lock-preprocessor-face
  '((t (:foreground "pale goldenrod")))
  "Face for preprocessor compiler directives (`include, `define, UVM macros...)."
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-modport-face 'verilog-ext-font-lock-modport-face)
(defface verilog-ext-font-lock-modport-face
  '((t (:foreground "light blue")))
  "Face for interface modports."
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-translate-off-face 'verilog-ext-font-lock-translate-off-face)
(defface verilog-ext-font-lock-translate-off-face
  '((t (:background "gray20" :slant italic)))
  "Face for pragmas between comments: * translate_off / * translate_on"
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-uvm-classes-face 'verilog-ext-font-lock-uvm-classes-face)
(defface verilog-ext-font-lock-uvm-classes-face
  '((t (:foreground "light blue")))
  "Face for UVM classes."
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-xilinx-attributes-face 'verilog-ext-font-lock-xilinx-attributes-face)
(defface verilog-ext-font-lock-xilinx-attributes-face
  '((t (:foreground "orange1")))
  "Face for Xilinx Vivado RTL synthesis attributes."
  :group 'verilog-ext-font-lock-faces)


;;;; Regexps
(defconst verilog-ext-font-lock-brackets-re "[()]")
(defconst verilog-ext-font-lock-curly-brackets-re "[{}]")
(defconst verilog-ext-font-lock-braces-re "\\(\\[\\|\\]\\)")
(defconst verilog-ext-font-lock-punctuation-re "\\([!,;:?'=<>]\\|\\*\\)")
(defconst verilog-ext-font-lock-punctuation-bold-re "\\([&^~+-]\\||\\|\\.\\|\\/\\)")
(defconst verilog-ext-font-lock-system-task-re (concat "\\$" verilog-identifier-re))
(defconst verilog-ext-font-lock-port-connection-re (concat "^[[:blank:]]*\\.\\(" verilog-identifier-re "\\)"))
(defconst verilog-ext-font-lock-dot-name-re (concat "\\(" verilog-identifier-re "\\)\\.\\(" verilog-identifier-re "\\)"))
(defconst verilog-ext-font-lock-braces-content-re "\\[\\(?1:[ +\*/()$0-9a-zA-Z:_-]*\\)\\]")
(defconst verilog-ext-font-lock-width-signal-re "\\(?1:[0-9]*\\)'\\(?2:[hdxbo]\\)\\(?3:[0-9a-fA-F_xzXZ]+\\)")
(defconst verilog-ext-font-lock-time-event-re "\\([@#]\\)")
(defconst verilog-ext-font-lock-time-unit-re "[0-9]+\\(\\.[0-9]+\\)?\\(?2:[umnpf]s\\)")
(defconst verilog-ext-font-lock-interface-modport-re (concat "\\(?1:^\\s-*\\(?2:" verilog-identifier-re "\\)\\.\\(?3:" verilog-identifier-re "\\)\\s-+\\)"))
(defconst verilog-ext-font-lock-typedef-struct-re "^\\s-*\\(typedef\\s-+\\)?\\(struct\\|union\\)\\s-+\\(packed\\|\\(un\\)?signed\\)?")
(defconst verilog-ext-font-lock-range-optional-re "\\s-*\\(\\[[^]]*\\]\\s-*\\)*")

;; Obtained with:
;; (dolist (word (cl-set-difference verilog-keywords verilog-type-keywords :test #'equal))
;;   (insert "\"" word "\" "))
(defconst verilog-ext-font-lock-keywords-no-types
  '("`__FILE__" "`__LINE" "`begin_keywords" "`celldefine" "`default_nettype"
    "`define" "`else" "`elsif" "`end_keywords" "`endcelldefine" "`endif"
    "`ifdef" "`ifndef" "`include" "`line" "`nounconnected_drive" "`pragma"
    "`resetall" "`timescale" "`unconnected_drive" "`undef" "`undefineall"
    "`case" "`default" "`endfor" "`endprotect" "`endswitch" "`endwhile" "`for"
    "`format" "`if" "`let" "`protect" "`switch" "`timescale" "`time_scale"
    "`while" "after" "alias" "always" "always_comb" "always_ff" "always_latch"
    "assert" "assign" "assume" "automatic" "before" "begin" "bind" "bins"
    "binsof" "bit" "break" "byte" "case" "casex" "casez" "cell" "chandle"
    "class" "clocking" "config" "const" "constraint" "context" "continue"
    "cover" "covergroup" "coverpoint" "cross" "deassign" "default" "design"
    "disable" "dist" "do" "edge" "else" "end" "endcase" "endclass" "endclocking"
    "endconfig" "endfunction" "endgenerate" "endgroup" "endinterface"
    "endmodule" "endpackage" "endprimitive" "endprogram" "endproperty"
    "endspecify" "endsequence" "endtable" "endtask" "enum" "event" "expect"
    "export" "extends" "extern" "final" "first_match" "for" "force" "foreach"
    "forever" "fork" "forkjoin" "function" "generate" "genvar" "highz0" "highz1"
    "if" "iff" "ifnone" "ignore_bins" "illegal_bins" "import" "incdir" "include"
    "initial" "inside" "instance" "int" "interface" "intersect" "join"
    "join_any" "join_none" "large" "liblist" "library" "local" "longint"
    "macromodule" "matches" "medium" "modport" "module" "negedge" "new"
    "noshowcancelled" "null" "package" "packed" "posedge" "primitive" "priority"
    "program" "property" "protected" "pulsestyle_onevent" "pulsestyle_ondetect"
    "pure" "rand" "randc" "randcase" "randsequence" "ref" "release" "repeat"
    "return" "scalared" "sequence" "shortint" "shortreal" "showcancelled"
    "signed" "small" "solve" "specify" "specparam" "static" "string" "strong0"
    "strong1" "struct" "super" "supply0" "supply1" "table" "tagged" "task"
    "this" "throughout" "timeprecision" "timeunit" "type" "typedef" "union"
    "unique" "unsigned" "use" "uwire" "var" "vectored" "virtual" "void" "wait"
    "wait_order" "weak0" "weak1" "while" "wildcard" "with" "within" "accept_on"
    "checker" "endchecker" "eventually" "global" "implies" "let" "nexttime"
    "reject_on" "restrict" "s_always" "s_eventually" "s_nexttime" "s_until"
    "s_until_with" "strong" "sync_accept_on" "sync_reject_on" "unique0" "until"
    "until_with" "untyped" "weak" "implements" "interconnect" "nettype" "soft"))
(defconst verilog-ext-font-lock-keywords-no-types-re
  (verilog-regexp-words verilog-ext-font-lock-keywords-no-types))

(defconst verilog-ext-font-lock-type-font-keywords
  (verilog-regexp-words
   '("and" "buf" "bufif0" "bufif1" "cmos" "defparam" "event" "genvar" "highz0"
   "highz1" "inout" "input" "integer" "localparam" "mailbox" "nand" "nmos" "nor"
   "not" "notif0" "notif1" "or" "output" "parameter" "pmos" "pull0" "pull1"
   "pulldown" "pullup" "rcmos" "real" "realtime" "reg" "rnmos" "specparam"
   "strong0" "strong1" "supply" "supply0" "supply1" "time" "tran" "tranif0"
   "tranif1" "tri" "tri0" "tri1" "triand" "trior" "trireg" "unsigned" "uwire"
   "vectored" "wand" "weak0" "weak1" "wire" "wor" "xnor" "xor" "signed"
   ;; 1800-2005
   "bit" "byte" "chandle" "const" "enum" "int" "logic" "longint" "packed" "ref"
   "shortint" "shortreal" "static" "string" "struct" "type" "typedef" "union"
   "var"
   ;; 1800-2009
   ;; 1800-2012
   "interconnect" "nettype"
   )))

(defconst verilog-ext-font-lock-general-keywords
  (verilog-regexp-opt
   '("always" "assign" "automatic" "case" "casex" "casez" "cell" "config"
     "deassign" "default" "design" "disable" "edge" "else" "endcase" "endconfig"
     "endfunction" "endgenerate" "endmodule" "endprimitive" "endspecify"
     "endtable" "endtask" "for" "force" "forever" "fork" "function" "generate"
     "if" "ifnone" "incdir" "include" "initial" "instance" "join" "large"
     "liblist" "library" "macromodule" "medium" "module" "negedge"
     "noshowcancelled" "posedge" "primitive" "pulsestyle_ondetect"
     "pulsestyle_onevent" "release" "repeat" "scalared" "showcancelled" "small"
     "specify" "strength" "table" "task" "use" "wait" "while"
     ;; 1800-2005
     "alias" "always_comb" "always_ff" "always_latch" "assert" "assume" "analog"
     "before" "bind" "bins" "binsof" "break" "class" "clocking" "constraint"
     "context" "continue" "cover" "covergroup" "coverpoint" "cross" "dist" "do"
     "endclass" "endclocking" "endgroup" "endinterface" "endpackage"
     "endprogram" "endproperty" "endsequence" "expect" "export" "extends"
     "extern" "final" "first_match" "foreach" "forkjoin" "iff" "ignore_bins"
     "illegal_bins" "import" "inside" "interface" "intersect" "join_any"
     "join_none" "local" "matches" "modport" "new" "null" "package" "priority"
     "program" "property" "protected" "pure" "rand" "randc" "randcase"
     "randsequence" "return" "sequence" "solve" "super" "tagged" "this"
     "throughout" "timeprecision" "timeunit" "unique" "virtual" "void"
     "wait_order" "wildcard" "with" "within"
     ;; 1800-2009
     "accept_on" "checker" "endchecker" "eventually" "global" "implies" "let"
     "nexttime" "reject_on" "restrict" "s_always" "s_eventually" "s_nexttime"
     "s_until" "s_until_with" "strong" "sync_accept_on" "sync_reject_on"
     "unique0" "until" "until_with" "untyped" "weak"
     ;; 1800-2012
     "implements" "soft")))

(defconst verilog-ext-font-lock-grouping-plus-this-keywords
  (verilog-regexp-words
   '("begin" "end" "this")))

;; Obtained via grep -R of classes starting with uvm_* and some processing.
;; Does not include internal classes (such as m_uvm_*), nor enums, nor non-class
;; typedefs such as vector derived.
(defconst verilog-ext-font-lock-uvm-classes
  (verilog-regexp-words
   '("uvm_agent" "uvm_algorithmic_comparator" "uvm_analysis_export"
     "uvm_analysis_imp" "uvm_analysis_port" "uvm_barrier" "uvm_bit_rsrc"
     "uvm_blocking_get_export" "uvm_blocking_get_imp"
     "uvm_blocking_get_peek_export" "uvm_blocking_get_peek_imp"
     "uvm_blocking_get_peek_port" "uvm_blocking_get_port"
     "uvm_blocking_master_export" "uvm_blocking_master_imp"
     "uvm_blocking_master_port" "uvm_blocking_peek_export"
     "uvm_blocking_peek_imp" "uvm_blocking_peek_port" "uvm_blocking_put_export"
     "uvm_blocking_put_imp" "uvm_blocking_put_port" "uvm_blocking_slave_export"
     "uvm_blocking_slave_imp" "uvm_blocking_slave_port"
     "uvm_blocking_transport_export" "uvm_blocking_transport_imp"
     "uvm_blocking_transport_port" "uvm_bogus_class" "uvm_bottomup_phase"
     "uvm_build_phase" "uvm_built_in_clone" "uvm_built_in_comp"
     "uvm_built_in_converter" "uvm_built_in_pair" "uvm_byte_rsrc" "uvm_callback"
     "uvm_callback_iter" "uvm_callbacks" "uvm_callbacks_base"
     "uvm_callbacks_objection" "uvm_check_phase" "uvm_class_clone"
     "uvm_class_comp" "uvm_class_converter" "uvm_class_pair" "uvm_cmd_line_verb"
     "uvm_cmdline_processor" "uvm_comparer" "uvm_component"
     "uvm_component_registry" "uvm_config_db" "uvm_config_db_options"
     "uvm_config_object_wrapper" "uvm_configure_phase" "uvm_connect_phase"
     "uvm_copy_map" "uvm_derived_callbacks" "uvm_domain" "uvm_driver"
     "uvm_end_of_elaboration_phase" "uvm_env" "uvm_event" "uvm_event_callback"
     "uvm_event_pool" "uvm_exhaustive_sequence" "uvm_external_connector"
     "uvm_extract_phase" "uvm_factory" "uvm_factory_override"
     "uvm_factory_queue_class" "uvm_final_phase" "uvm_get_export" "uvm_get_imp"
     "uvm_get_peek_export" "uvm_get_peek_imp" "uvm_get_peek_port" "uvm_get_port"
     "uvm_hdl_path_concat" "uvm_heartbeat" "uvm_heartbeat_callback"
     "uvm_if_base_abstract" "uvm_in_order_built_in_comparator"
     "uvm_in_order_class_comparator" "uvm_in_order_comparator" "uvm_int_rsrc"
     "uvm_line_printer" "uvm_main_phase" "uvm_master_export" "uvm_master_imp"
     "uvm_master_port" "uvm_mem" "uvm_mem_access_seq" "uvm_mem_mam"
     "uvm_mem_mam_cfg" "uvm_mem_mam_policy" "uvm_mem_region"
     "uvm_mem_shared_access_seq" "uvm_mem_single_access_seq"
     "uvm_mem_single_walk_seq" "uvm_mem_walk_seq" "uvm_monitor"
     "uvm_nonblocking_get_export" "uvm_nonblocking_get_imp"
     "uvm_nonblocking_get_peek_export" "uvm_nonblocking_get_peek_imp"
     "uvm_nonblocking_get_peek_port" "uvm_nonblocking_get_port"
     "uvm_nonblocking_master_export" "uvm_nonblocking_master_imp"
     "uvm_nonblocking_master_port" "uvm_nonblocking_peek_export"
     "uvm_nonblocking_peek_imp" "uvm_nonblocking_peek_port"
     "uvm_nonblocking_put_export" "uvm_nonblocking_put_imp"
     "uvm_nonblocking_put_port" "uvm_nonblocking_slave_export"
     "uvm_nonblocking_slave_imp" "uvm_nonblocking_slave_port"
     "uvm_nonblocking_transport_export" "uvm_nonblocking_transport_imp"
     "uvm_nonblocking_transport_port" "uvm_obj_rsrc" "uvm_object"
     "uvm_object_registry" "uvm_object_string_pool" "uvm_object_wrapper"
     "uvm_objection" "uvm_objection_callback" "uvm_objection_context_object"
     "uvm_objection_events" "uvm_packer" "uvm_peek_export" "uvm_peek_imp"
     "uvm_peek_port" "uvm_phase" "uvm_pool" "uvm_port_base" "uvm_port_component"
     "uvm_port_component_base" "uvm_post_configure_phase" "uvm_post_main_phase"
     "uvm_post_reset_phase" "uvm_post_shutdown_phase" "uvm_pre_configure_phase"
     "uvm_pre_main_phase" "uvm_pre_reset_phase" "uvm_pre_shutdown_phase"
     "uvm_predict_s" "uvm_printer" "uvm_printer_knobs" "uvm_push_driver"
     "uvm_push_sequencer" "uvm_put_export" "uvm_put_imp" "uvm_put_port"
     "uvm_queue" "uvm_random_sequence" "uvm_random_stimulus" "uvm_recorder"
     "uvm_reg" "uvm_reg_access_seq" "uvm_reg_adapter" "uvm_reg_backdoor"
     "uvm_reg_bit_bash_seq" "uvm_reg_block" "uvm_reg_cbs" "uvm_reg_field"
     "uvm_reg_fifo" "uvm_reg_file" "uvm_reg_frontdoor" "uvm_reg_hw_reset_seq"
     "uvm_reg_indirect_data" "uvm_reg_indirect_ftdr_seq" "uvm_reg_item"
     "uvm_reg_map" "uvm_reg_map_info" "uvm_reg_mem_access_seq"
     "uvm_reg_mem_built_in_seq" "uvm_reg_mem_hdl_paths_seq"
     "uvm_reg_mem_shared_access_seq" "uvm_reg_predictor" "uvm_reg_read_only_cbs"
     "uvm_reg_sequence" "uvm_reg_shared_access_seq" "uvm_reg_single_access_seq"
     "uvm_reg_single_bit_bash_seq" "uvm_reg_tlm_adapter"
     "uvm_reg_write_only_cbs" "uvm_report_catcher" "uvm_report_global_server"
     "uvm_report_handler" "uvm_report_object" "uvm_report_phase"
     "uvm_report_server" "uvm_reset_phase" "uvm_resource" "uvm_resource_base"
     "uvm_resource_db" "uvm_resource_db_options" "uvm_resource_options"
     "uvm_resource_pool" "uvm_resource_types" "uvm_root"
     "uvm_root_report_handler" "uvm_run_phase" "uvm_scope_stack"
     "uvm_scoreboard" "uvm_seed_map" "uvm_seq_item_pull_export"
     "uvm_seq_item_pull_imp" "uvm_seq_item_pull_port" "uvm_sequence"
     "uvm_sequence_base" "uvm_sequence_item" "uvm_sequence_library"
     "uvm_sequence_library_cfg" "uvm_sequence_request" "uvm_sequencer"
     "uvm_sequencer_analysis_fifo" "uvm_sequencer_base"
     "uvm_sequencer_param_base" "uvm_shutdown_phase" "uvm_simple_sequence"
     "uvm_slave_export" "uvm_slave_imp" "uvm_slave_port" "uvm_spell_chkr"
     "uvm_sqr_if_base" "uvm_start_of_simulation_phase" "uvm_status_container"
     "uvm_string_rsrc" "uvm_subscriber" "uvm_table_printer" "uvm_task_phase"
     "uvm_test" "uvm_test_done_objection" "uvm_tlm_analysis_fifo"
     "uvm_tlm_b_initiator_socket" "uvm_tlm_b_initiator_socket_base"
     "uvm_tlm_b_passthrough_initiator_socket"
     "uvm_tlm_b_passthrough_initiator_socket_base"
     "uvm_tlm_b_passthrough_target_socket"
     "uvm_tlm_b_passthrough_target_socket_base" "uvm_tlm_b_target_socket"
     "uvm_tlm_b_target_socket_base" "uvm_tlm_b_transport_export"
     "uvm_tlm_b_transport_imp" "uvm_tlm_b_transport_port" "uvm_tlm_event"
     "uvm_tlm_extension" "uvm_tlm_extension_base" "uvm_tlm_fifo"
     "uvm_tlm_fifo_base" "uvm_tlm_generic_payload" "uvm_tlm_if"
     "uvm_tlm_if_base" "uvm_tlm_nb_initiator_socket"
     "uvm_tlm_nb_initiator_socket_base"
     "uvm_tlm_nb_passthrough_initiator_socket"
     "uvm_tlm_nb_passthrough_initiator_socket_base"
     "uvm_tlm_nb_passthrough_target_socket"
     "uvm_tlm_nb_passthrough_target_socket_base" "uvm_tlm_nb_target_socket"
     "uvm_tlm_nb_target_socket_base" "uvm_tlm_nb_transport_bw_export"
     "uvm_tlm_nb_transport_bw_imp" "uvm_tlm_nb_transport_bw_port"
     "uvm_tlm_nb_transport_fw_export" "uvm_tlm_nb_transport_fw_imp"
     "uvm_tlm_nb_transport_fw_port" "uvm_tlm_req_rsp_channel" "uvm_tlm_time"
     "uvm_tlm_transport_channel" "uvm_topdown_phase" "uvm_transaction"
     "uvm_transport_export" "uvm_transport_imp" "uvm_transport_port"
     "uvm_tree_printer" "uvm_typed_callbacks" "uvm_typeid" "uvm_typeid_base"
     "uvm_utils" "uvm_void" "uvm_vreg" "uvm_vreg_cbs" "uvm_vreg_field"
     "uvm_vreg_field_cbs")))

(defconst verilog-ext-font-lock-pragma-keywords
  (verilog-regexp-words
   '("surefire" "0in" "auto" "leda" "rtl_synthesis" "verilint"
     ;; Recognized by Vivado (check Xilinx attribute 'translate_off/translate_on'):
     "synthesis" "synopsys" "pragma")))

;;   Xilinx attributes extracted from UG901:
;; - https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_3/ug901-vivado-synthesis.pdf
;; - Chapter 2 (some of them are also supported at XDC).
(defconst verilog-ext-font-lock-xilinx-attributes
  (verilog-regexp-words
   '("async_reg" "black_box" "cascade_height" "clock_buffer_type"
     "direct_enable" "direct_reset" "dont_touch" "extract_enable"
     "extract_reset" "fsm_encoding" "fsm_safe_state" "full_case" "gated_clock"
     "iob" "io_buffer_type" "keep" "keep_hierarchy" "mark_debug" "max_fanout"
     "parallel_case" "ram_decomp" "ram_style" "retiming_backward"
     "retiming_forward" "rom_style" "shreg_extract" "srl_style" "translate_off"
     "translate_on" "use_dsp"
     ;; uppercase "async_reg" "BLACK_BOX"
     "CASCADE_HEIGHT" "CLOCK_BUFFER_TYPE" "DIRECT_ENABLE" "DIRECT_RESET"
     "DONT_TOUCH" "EXTRACT_ENABLE" "EXTRACT_RESET" "FSM_ENCODING"
     "FSM_SAFE_STATE" "FULL_CASE" "GATED_CLOCK" "IOB" "IO_BUFFER_TYPE" "KEEP"
     "KEEP_HIERARCHY" "MARK_DEBUG" "MAX_FANOUT" "PARALLEL_CASE" "RAM_DECOMP"
     "RAM_STYLE" "RETIMING_BACKWARD" "RETIMING_FORWARD" "ROM_STYLE"
     "SHREG_EXTRACT" "SRL_STYLE" "TRANSLATE_OFF" "TRANSLATE_ON" "USE_DSP")))


;;;; Functions
(defun verilog-ext-font-lock-module-instance-fontify (limit)
  "Search based fontification function of Verilog modules/instances.
Bound search by LIMIT."
  (let (start-line end-line)
    (when (verilog-ext-find-module-instance-fwd limit)
      (setq start-line (save-excursion
                         (goto-char (match-beginning 1))
                         (point-at-bol)))
      (setq end-line (save-excursion
                       (goto-char (match-end 2))
                       (point-at-eol)))
      (unless (get-text-property (point) 'font-lock-multiline)
        (put-text-property start-line end-line 'font-lock-multiline t))
      (point))))

(defun verilog-ext-font-lock-modport-fontify (limit)
  "Fontify interface modport declarations.
Bound search by LIMIT."
  (let (if-start if-end mp-start mp-end var-start var-end)
    (when (and (verilog-re-search-forward verilog-ext-font-lock-interface-modport-re limit t)
               (verilog-in-parenthesis-p))
      (setq if-start (match-beginning 2))
      (setq if-end (match-end 2))
      (setq mp-start (match-beginning 3))
      (setq mp-end (match-end 3))
      ;; Calculate variable pos at the end since `thing-at-point' changes match-data
      (setq var-start (car (bounds-of-thing-at-point 'symbol)))
      (setq var-end (cdr (bounds-of-thing-at-point 'symbol)))
      (set-match-data (list if-start if-end mp-start mp-end var-start var-end))
      (point))))


(defun verilog-ext-font-lock-match-translate-off-fontify (limit)
  "Match a translate-off block, setting `match-data' and returning t, else nil.
Bound search by LIMIT.

Similar to `verilog-match-translate-off' but including
`font-lock-multiline' property."
  (when (< (point) limit)
    (let ((start (or (verilog-within-translate-off)
                     (verilog-start-translate-off limit)))
          (case-fold-search t))
      (when start
        (let ((end (or (verilog-end-translate-off limit) limit)))
          (put-text-property start end 'font-lock-multiline t)
          (set-match-data (list start end))
          (goto-char end))))))



;;;; Font-lock keywords
(defvar verilog-ext-font-lock-keywords
  (list
   ;; Preprocessor macros and compiler directives (place at the top to preserve precendence in `else or `include macros over keywords)
   (cons (concat "`" verilog-identifier-re) 'verilog-ext-font-lock-preprocessor-face)
   ;; UVM constructs
   (cons (concat "\\(" verilog-ext-font-lock-uvm-classes "\\)") 'verilog-ext-font-lock-uvm-classes-face)
   ;; Grouping keywords
   (cons (concat "\\<\\(" verilog-ext-font-lock-grouping-plus-this-keywords "\\)\\>") 'verilog-ext-font-lock-grouping-keywords-face)
   ;; Builtin keywords
   (concat "\\<\\(" verilog-ext-font-lock-general-keywords "\\)\\>") ; Default 'font-lock-keyword-face
   ;; User/System tasks and functions
   (cons (concat "\\<\\(" verilog-ext-font-lock-system-task-re "\\)\\>") 'font-lock-builtin-face)
   ;; Types
   (cons (concat "\\<\\(" verilog-ext-font-lock-type-font-keywords "\\)\\>") 'font-lock-type-face)
   ))

(defvar verilog-ext-font-lock-keywords-1
  (append
   verilog-ext-font-lock-keywords
   (list
    ;; Function/task extern definitions: Must be placed before module/function definitions to override font-locking
    (list "\\(?1:\\<function\\>\\|\\<task\\>\\)\\s-+\\(?2:\\automatic\\s-+\\)?\\(?3:\\(?4:\\sw+\\)\\s-+\\)?\\(?5:\\sw+\\)\\s-*::\\s-*\\(?6:\\sw+\\)"
          '(5 verilog-ext-font-lock-dot-name-face)
          '(6 font-lock-function-name-face)) ; Match 4 is return type (might be void), Match 5 is class name, Match 6 is func/task name
    ;; Module definitions
    (list "\\<\\(?1:\\(macro\\|connect\\)?module\\|primitive\\|class\\|program\\|interface\\|package\\|task\\)\\>\\s-*\\(automatic\\s-+\\)?\\(?3:\\sw+\\)\\s-*\\(?4:#?\\)"
          '(1 font-lock-keyword-face)
          '(3 font-lock-function-name-face))
    ;; Function definitions
    (list "\\<function\\>\\s-+\\(?1:\\automatic\\s-+\\)?\\(?2:\\(?3:\\sw+\\)\\s-+\\)?\\(?4:\\sw+\\)"
          '(4 font-lock-function-name-face)) ; Match 3 is return type (might be void)
    ;; Modport interfaces in port lists
    '(verilog-ext-font-lock-modport-fontify
      (0 'verilog-ext-font-lock-modport-face)
      (1 'verilog-ext-font-lock-dot-name-face))
    ;; Modules/instances
    '(verilog-ext-font-lock-module-instance-fontify (1 'verilog-ext-font-lock-module-face))
    '(verilog-ext-font-lock-module-instance-fontify (2 'verilog-ext-font-lock-instance-face))
    )))

(defvar verilog-ext-font-lock-keywords-2
  (append
   verilog-ext-font-lock-keywords-1
   (list
    ;; Pragmas
    (list (concat "\\(//\\s-*\\(" verilog-ext-font-lock-pragma-keywords " \\).*\\)")
          '(0 'verilog-ext-font-lock-translate-off-face prepend)
          '(2 'verilog-ext-font-lock-preprocessor-face prepend))
    ;; Escaped names
    '("\\(\\\\\\S-*\\s-\\)"  0 font-lock-function-name-face)
    ;; Delays/numbers
    '("\\s-*#\\s-*\\(?1:\\([0-9_.]+\\([munpf]s\\)?\\('s?[hdxbo][0-9a-fA-F_xz]*\\)?\\)\\|\\(([^(),.=]+)\\|\\sw+\\)\\)" 1 font-lock-type-face append)
    ;; Fontify property/sequence cycle delays - these start with '##'
    '("##\\(?1:\\sw+\\|\\[[^]]+\\]\\)" 1 font-lock-type-face append)
    )))

(defvar verilog-ext-font-lock-keywords-3
  (append
   verilog-ext-font-lock-keywords-2
   (list
    ;; Verilog-ext font-lock extra re
    (list verilog-ext-font-lock-time-unit-re          2 verilog-ext-font-lock-time-unit-face)
    (list verilog-ext-font-lock-time-event-re         0 verilog-ext-font-lock-time-event-face)
    (list verilog-ext-font-lock-port-connection-re    1 verilog-ext-font-lock-port-connection-face)
    (list verilog-ext-font-lock-dot-name-re           1 verilog-ext-font-lock-dot-name-face)
    (list verilog-ext-font-lock-braces-content-re     1 verilog-ext-font-lock-braces-content-face)
    (list verilog-ext-font-lock-punctuation-re        0 verilog-ext-font-lock-punctuation-face)
    (list verilog-ext-font-lock-punctuation-bold-re   0 verilog-ext-font-lock-punctuation-bold-face)
    (list verilog-ext-font-lock-braces-re             0 verilog-ext-font-lock-braces-face)
    (list verilog-ext-font-lock-brackets-re           0 verilog-ext-font-lock-brackets-face)
    (list verilog-ext-font-lock-curly-brackets-re     0 verilog-ext-font-lock-curly-brackets-face)
    (list verilog-ext-font-lock-width-signal-re
          '(1 verilog-ext-font-lock-width-num-face)
          '(2 verilog-ext-font-lock-width-type-face))
    ;; Xilinx attributes
    (list (concat "(\\*\\s-+" "\\<\\(?1:" verilog-ext-font-lock-xilinx-attributes "\\)\\>" "\\s-+\\*)") 1 verilog-ext-font-lock-xilinx-attributes-face)
    ;; *_translate off regions
    '(verilog-ext-font-lock-match-translate-off-fontify
      (0 'verilog-ext-font-lock-translate-off-face prepend)) ; 3rd parameter (prepend or t) overrides previous fontlocking
    )))


;;;; Config
(font-lock-add-keywords 'verilog-mode (append verilog-ext-font-lock-keywords
                                              verilog-ext-font-lock-keywords-1
                                              verilog-ext-font-lock-keywords-2
                                              verilog-ext-font-lock-keywords-3) 'set)
(add-hook 'verilog-mode-hook (lambda () (setq font-lock-multiline nil)))


(provide 'verilog-font-lock)

;;; verilog-font-lock.el ends here
