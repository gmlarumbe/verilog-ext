;;; verilog-ext-tests-tags.el --- Verilog-Ext ERT tags tests  -*- lexical-binding: t -*-

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
;;
;; ERT Tags Tests
;;
;;; Code:


;; https://stackoverflow.com/questions/18180393/compare-hash-table-in-emacs-lisp
;; Using `ht' could be an alternative, but let's try to reduce the amount of dependencies
(defun hash-equal (hash1 hash2)
  "Compare two hash tables to see whether they are equal."
  (and (= (hash-table-count hash1)
          (hash-table-count hash2))
       (catch 'flag (maphash (lambda (x y)
                               (or (equal (gethash x hash2) y)
                                   ;; (message "Error with %s and %s" (gethash x hash2) y)
                                   (throw 'flag nil)))
                             hash1)
              (throw 'flag t))))

(defun hash-not-equal (hash1 hash2)
  "Compare two hash tables to see whether they are different.
Return differences get a better explanation of the errors in ERT testsuites."
  (and (= (hash-table-count hash1)
          (hash-table-count hash2))
       (catch 'flag (maphash (lambda (x y)
                               (or (equal (gethash x hash2) y)
                                   (throw 'flag (list (format "%s" y) (format "%s" (gethash x hash2))))))
                             hash1)
              (throw 'flag nil))))

(defmacro verilog-ext-test-tags-defs-file (file tag-type)
  (declare (indent 1) (debug t))
  `(let ((table (make-hash-table :test #'equal)))
     (with-temp-buffer
       (insert-file-contents (file-name-concat verilog-ext-tests-common-dir ,file))
       (verilog-mode)
       ;; Avoid errors in desc when there are tabs and trailing whitespaces
       (untabify (point-min) (point-max))
       (delete-trailing-whitespace (point-min) (point-max))
       ;; Get definitions
       (verilog-ext-tags-get-definitions ,tag-type table ,file))))

(defmacro verilog-ext-test-tags-refs-file (file)
  (declare (indent 1) (debug t))
  `(let ((table (make-hash-table :test #'equal)))
     (with-temp-buffer
       (insert-file-contents (file-name-concat verilog-ext-tests-common-dir ,file))
       (verilog-mode)
       ;; Avoid errors in desc when there are tabs and trailing whitespaces
       (untabify (point-min) (point-max))
       (delete-trailing-whitespace (point-min) (point-max))
       ;; Get references
       (verilog-ext-tags-get-references table nil ,file))))

(defvar verilog-ext-test-tags-defs-table-alist
  '(;; DANGER: Happens if setting `verilog-align-typedef-regexp' to nil:
    ;;    For some reason the instances.sv test works fine in an interactive Emacs `ert' session but fails in the terminal with a new Emacs process.
    ;;    Tried replacing defmacro with defun, both here in the test file and in verilog-ext and didn't change anything.
    ;;    Also tried with (setq value (plist-put value :locs locs-plist)) instead of just (plist-put value), as suggested by the docstring, but nothing changed.
    (("instances.sv" top-items) #s(hash-table size 65 test equal rehash-size 1.5 rehash-threshold 0.8125 data
                                              ("instances"
                                               (:items
                                                ;; DANGER: First line should be the correct one, but for some reason I_TEST_IF was detected before I_BLOCK_0 with Emacs in batch mode.
                                                ;; The interactive one matches the result if running (verilog-ext-test-tags-defs-file "instances.sv" 'top-items) in an Eshell.
                                                ;; ("i" "I_BLOCK0" "I_BLOCK1" "I_BLOCK2" "I_BLOCK3" "I_BLOCK_GEN" "I_TEST_IF" "ITEST_IF_PARAMS" "ITEST_IF_PARAMS_ARRAY" "I_TEST_IF_PARAMS_EMPTY" "I_BLOCK_WS_0" "I_BLOCK_WS_1")
                                                ;; End of DANGER
                                                ("i" "I_TEST_IF" "I_BLOCK0" "I_BLOCK1" "I_BLOCK2" "I_BLOCK3" "I_BLOCK_GEN" "ITEST_IF_PARAMS" "ITEST_IF_PARAMS_ARRAY" "I_TEST_IF_PARAMS_EMPTY" "I_BLOCK_WS_0" "I_BLOCK_WS_1")
                                                :locs
                                                ((:type "module" :desc "module instances;" :file "instances.sv" :line 20)))
                                               "i"
                                               (:items nil :locs
                                                ((:type "genvar" :desc "for (genvar i=0; i<VALUE; i++) begin : gen_test" :file "instances.sv" :line 60)))
                                               "I_TEST_IF"
                                               (:items nil :locs
                                                ((:type "test_if" :desc "test_if I_TEST_IF (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 77)))
                                               "I_BLOCK0"
                                               (:items nil :locs
                                                ((:type "block0" :desc ");" :file "instances.sv" :line 27)))
                                               "I_BLOCK1"
                                               (:items nil :locs
                                                ((:type "block1" :desc ");" :file "instances.sv" :line 34)))
                                               "I_BLOCK2"
                                               (:items nil :locs
                                                ((:type "block2" :desc ");" :file "instances.sv" :line 45)))
                                               "I_BLOCK3"
                                               (:items nil :locs
                                                ((:type "block3" :desc ");" :file "instances.sv" :line 56)))
                                               "I_BLOCK_GEN"
                                               (:items nil :locs
                                                ((:type "block_gen" :desc ");" :file "instances.sv" :line 70)))
                                               "ITEST_IF_PARAMS"
                                               (:items nil :locs
                                                ((:type "test_if_params" :desc "test_if_params # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 79)))
                                               "ITEST_IF_PARAMS_ARRAY"
                                               (:items nil :locs
                                                ((:type "test_if_params_array" :desc "test_if_params_array # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS_ARRAY[5:0] (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 81)))
                                               "I_TEST_IF_PARAMS_EMPTY"
                                               (:items nil :locs
                                                ((:type "test_if_params_empty" :desc "test_if_params_empty #() I_TEST_IF_PARAMS_EMPTY (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 83)))
                                               "I_BLOCK_WS_0"
                                               (:items nil :locs
                                                ((:type "block_ws_0" :desc ");" :file "instances.sv" :line 92)))
                                               "I_BLOCK_WS_1"
                                               (:items nil :locs
                                                ((:type "block_ws_1" :desc ");" :file "instances.sv" :line 105))))))

    (("tb_program.sv" top-items) #s(hash-table size 65 test equal rehash-size 1.5 rehash-threshold 0.8125 data
                                               ("tb_program"
                                                (:items
                                                 ("Clk" "Rst_n" "RXD" "TXD" "Temp" "Switches" "ROM_Data" "ROM_Addr" "FREQ_CLK" "TX_SPEED" "BIT_CYCLES" "ROM" "Data" "i" "init_rom" "init_values" "reset_system" "serial_rx")
                                                 :locs
                                                 ((:type "module" :desc "module automatic tb_program (" :file "tb_program.sv" :line 23)))
                                                "Clk"
                                                (:items nil :locs
                                                 ((:type "input logic" :desc "input logic         Clk," :file "tb_program.sv" :line 24)))
                                                "Rst_n"
                                                (:items nil :locs
                                                 ((:type "output logic" :desc "output logic        Rst_n," :file "tb_program.sv" :line 25)))
                                                "RXD"
                                                (:items nil :locs
                                                 ((:type "output logic" :desc "output logic        RXD," :file "tb_program.sv" :line 26)))
                                                "TXD"
                                                (:items nil :locs
                                                 ((:type "input logic" :desc "input logic         TXD," :file "tb_program.sv" :line 27)))
                                                "Temp"
                                                (:items nil :locs
                                                 ((:type "input logic [7:0]" :desc "input logic [7:0]   Temp," :file "tb_program.sv" :line 28)))
                                                "Switches"
                                                (:items nil :locs
                                                 ((:type "input logic [7:0]" :desc "input logic [7:0]   Switches," :file "tb_program.sv" :line 29)))
                                                "ROM_Data"
                                                (:items nil :locs
                                                 ((:type "output logic [11:0]" :desc "output logic [11:0] ROM_Data," :file "tb_program.sv" :line 30)))
                                                "ROM_Addr"
                                                (:items nil :locs
                                                 ((:type "input logic [11:0]" :desc "input logic [11:0]  ROM_Addr" :file "tb_program.sv" :line 31)))
                                                "FREQ_CLK"
                                                (:items nil :locs
                                                 ((:type "localparam logic [31:0]" :desc "localparam logic [31:0] FREQ_CLK = 100000000;" :file "tb_program.sv" :line 37)))
                                                "TX_SPEED"
                                                (:items nil :locs
                                                 ((:type "localparam logic [31:0]" :desc "localparam logic [31:0] TX_SPEED = 115200;" :file "tb_program.sv" :line 38)))
                                                "BIT_CYCLES"
                                                (:items nil :locs
                                                 ((:type "localparam integer" :desc "localparam integer BIT_CYCLES = FREQ_CLK / TX_SPEED;" :file "tb_program.sv" :line 39)))
                                                "ROM"
                                                (:items nil :locs
                                                 ((:type "logic [11:0]" :desc "logic [11:0] ROM [4096];" :file "tb_program.sv" :line 55)))
                                                "Data"
                                                (:items nil :locs
                                                 ((:type "input logic [7:0]" :desc "task serial_rx (input logic [7:0] Data);" :file "tb_program.sv" :line 115)))
                                                "i"
                                                (:items nil :locs
                                                 ((:type "int" :desc "for (int i=0; i<8; ++i) begin" :file "tb_program.sv" :line 121)))
                                                "init_rom"
                                                (:items nil :locs
                                                 ((:type "task" :desc "task init_rom ();" :file "tb_program.sv" :line 58)))
                                                "init_values"
                                                (:items nil :locs
                                                 ((:type "task" :desc "task init_values;" :file "tb_program.sv" :line 99)))
                                                "reset_system"
                                                (:items nil :locs
                                                 ((:type "task" :desc "task reset_system;" :file "tb_program.sv" :line 104)))
                                                "serial_rx"
                                                (:items nil :locs
                                                 ((:type "task" :desc "task serial_rx (input logic [7:0] Data);" :file "tb_program.sv" :line 115))))))

    (("uvm_component.svh" classes) #s(hash-table size 145 test equal rehash-size 1.5 rehash-threshold 0.8125 data
                                                 ("uvm_component"
                                                  (:items
                                                   ("get_full_name" "get_next_child" "get_first_child" "get_num_children" "has_child" "get_depth" "massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches" "begin_tr" "record_error_tr" "record_event_tr" "print_enabled" "m_build_done" "m_phasing_active" "m_add_child" "m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "new" "get_parent" "get_children" "get_child" "set_name" "lookup" "build_phase" "connect_phase" "end_of_elaboration_phase" "start_of_simulation_phase" "run_phase" "pre_reset_phase" "reset_phase" "post_reset_phase" "pre_configure_phase" "configure_phase" "post_configure_phase" "pre_main_phase" "main_phase" "post_main_phase" "pre_shutdown_phase" "shutdown_phase" "post_shutdown_phase" "extract_phase" "check_phase" "report_phase" "final_phase" "phase_started" "phase_ready_to_end" "phase_ended" "set_domain" "get_domain" "define_domain" "suspend" "resume" "resolve_bindings" "apply_config_settings" "print_config" "print_config_with_audit" "set_print_config_matches" "raised" "dropped" "all_dropped" "create_component" "create_object" "set_type_override_by_type" "set_inst_override_by_type" "set_type_override" "set_inst_override" "print_override_info" "set_report_id_verbosity_hier" "set_report_severity_id_verbosity_hier" "set_report_severity_action_hier" "set_report_id_action_hier" "set_report_severity_id_action_hier" "set_report_default_file_hier" "set_report_severity_file_hier" "set_report_id_file_hier" "set_report_severity_id_file_hier" "set_report_verbosity_level_hier" "pre_abort" "accept_tr" "do_accept_tr" "do_begin_tr" "end_tr" "do_end_tr" "get_tr_stream" "free_tr_stream" "do_execute_op" "get_tr_database" "set_tr_database" "set_local" "m_set_full_name" "do_resolve_bindings" "do_flush" "flush" "m_extract_name" "create" "clone" "set_recording_enabled" "set_recording_enabled_hier" "do_print" "m_set_cl_msg_args" "m_set_cl_verb" "m_set_cl_action" "m_set_cl_sev" "m_apply_verbosity_settings" "m_do_pre_abort" "m_unsupported_set_local")
                                                   :locs
                                                   ((:type "class" :desc "virtual class uvm_component extends uvm_report_object;" :file "uvm_component.svh" :line 49)))
                                                  "get_full_name"
                                                  (:items
                                                   ("get_next_child" "get_first_child" "get_num_children" "has_child" "get_depth" "massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function string get_full_name ();" :file "uvm_component.svh" :line 93)
                                                    (:type "string" :desc "extern virtual function string get_full_name ();" :file "uvm_component.svh" :line 93)))
                                                  "get_next_child"
                                                  (:items
                                                   ("get_first_child" "get_num_children" "has_child" "get_depth" "massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern function int get_next_child (ref string name);" :file "uvm_component.svh" :line 116)
                                                    (:type "int" :desc "extern function int get_next_child (ref string name);" :file "uvm_component.svh" :line 116)))
                                                  "get_first_child"
                                                  (:items
                                                   ("get_num_children" "has_child" "get_depth" "massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern function int get_first_child (ref string name);" :file "uvm_component.svh" :line 133)
                                                    (:type "int" :desc "extern function int get_first_child (ref string name);" :file "uvm_component.svh" :line 133)))
                                                  "get_num_children"
                                                  (:items
                                                   ("has_child" "get_depth" "massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern function int get_num_children ();" :file "uvm_component.svh" :line 141)
                                                    (:type "int" :desc "extern function int get_num_children ();" :file "uvm_component.svh" :line 141)))
                                                  "has_child"
                                                  (:items
                                                   ("get_depth" "massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern function int has_child (string name);" :file "uvm_component.svh" :line 149)
                                                    (:type "int" :desc "extern function int has_child (string name);" :file "uvm_component.svh" :line 149)))
                                                  "get_depth"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern function int unsigned get_depth();" :file "uvm_component.svh" :line 178)
                                                    (:type "int unsigned" :desc "extern function int unsigned get_depth();" :file "uvm_component.svh" :line 178)))
                                                  "massage_scope"
                                                  (:items
                                                   ("use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern function string massage_scope(string scope);" :file "uvm_component.svh" :line 688)
                                                    (:type "string" :desc "extern function string massage_scope(string scope);" :file "uvm_component.svh" :line 688)))
                                                  "use_automatic_config"
                                                  (:items
                                                   ("print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function bit use_automatic_config();" :file "uvm_component.svh" :line 740)
                                                    (:type "bit" :desc "extern virtual function bit use_automatic_config();" :file "uvm_component.svh" :line 740)))
                                                  "print_config_matches"
                                                  (:items nil :locs
                                                   ((:type "bit" :desc "static `ifndef UVM_ENABLE_DEPRECATED_API local `endif bit print_config_matches;" :file "uvm_component.svh" :line 770)))
                                                  "get_print_config_matches"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "static function bit get_print_config_matches() ;" :file "uvm_component.svh" :line 782)
                                                    (:type "bit" :desc "static function bit get_print_config_matches() ;" :file "uvm_component.svh" :line 782)))
                                                  "begin_tr"
                                                  (:items
                                                   ("record_error_tr" "record_event_tr" "print_enabled" "m_build_done" "m_phasing_active" "m_add_child" "m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern function int begin_tr (uvm_transaction tr," :file "uvm_component.svh" :line 1220)
                                                    (:type "int" :desc "extern function int begin_tr (uvm_transaction tr," :file "uvm_component.svh" :line 1220)))
                                                  "record_error_tr"
                                                  (:items
                                                   ("record_event_tr" "print_enabled" "m_build_done" "m_phasing_active" "m_add_child" "m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern function int record_error_tr (string stream_name=\"main\"," :file "uvm_component.svh" :line 1296)
                                                    (:type "int" :desc "extern function int record_error_tr (string stream_name=\"main\"," :file "uvm_component.svh" :line 1296)))
                                                  "record_event_tr"
                                                  (:items
                                                   ("print_enabled" "m_build_done" "m_phasing_active" "m_add_child" "m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern function int record_event_tr (string stream_name=\"main\"," :file "uvm_component.svh" :line 1317)
                                                    (:type "int" :desc "extern function int record_event_tr (string stream_name=\"main\"," :file "uvm_component.svh" :line 1317)))
                                                  "print_enabled"
                                                  (:items nil :locs
                                                   ((:type "bit" :desc "bit print_enabled = 1;" :file "uvm_component.svh" :line 1341)))
                                                  "m_build_done"
                                                  (:items nil :locs
                                                   ((:type "bit" :desc "/*protected*/ bit  m_build_done;" :file "uvm_component.svh" :line 1383)))
                                                  "m_phasing_active"
                                                  (:items nil :locs
                                                   ((:type "int" :desc "/*protected*/ int  m_phasing_active;" :file "uvm_component.svh" :line 1384)))
                                                  "m_add_child"
                                                  (:items
                                                   ("m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern protected virtual function bit  m_add_child(uvm_component child);" :file "uvm_component.svh" :line 1391)
                                                    (:type "bit" :desc "extern protected virtual function bit  m_add_child(uvm_component child);" :file "uvm_component.svh" :line 1391)))
                                                  "m_begin_tr"
                                                  (:items
                                                   ("m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern protected function int m_begin_tr (uvm_transaction tr," :file "uvm_component.svh" :line 1409)
                                                    (:type "int" :desc "extern protected function int m_begin_tr (uvm_transaction tr," :file "uvm_component.svh" :line 1409)))
                                                  "m_name"
                                                  (:items nil :locs
                                                   ((:type "string" :desc "string m_name;" :file "uvm_component.svh" :line 1414)))
                                                  "recording_detail"
                                                  (:items nil :locs
                                                   ((:type "int unsigned" :desc "int unsigned recording_detail = UVM_NONE;" :file "uvm_component.svh" :line 1421)))
                                                  "get_recording_enabled"
                                                  (:items
                                                   ("error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function bit get_recording_enabled();" :file "uvm_component.svh" :line 1424)
                                                    (:type "bit" :desc "extern virtual function bit get_recording_enabled();" :file "uvm_component.svh" :line 1424)))
                                                  "new"
                                                  (:items
                                                   ("get_full_name" "get_next_child" "get_first_child" "get_num_children" "has_child" "get_depth" "massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern function new (string name, uvm_component parent);" :file "uvm_component.svh" :line 66)))
                                                  "get_parent"
                                                  (:items
                                                   ("get_full_name" "get_next_child" "get_first_child" "get_num_children" "has_child" "get_depth" "massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function uvm_component get_parent ();" :file "uvm_component.svh" :line 83)))
                                                  "get_children"
                                                  (:items
                                                   ("get_next_child" "get_first_child" "get_num_children" "has_child" "get_depth" "massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern function void get_children(ref uvm_component children[$]);" :file "uvm_component.svh" :line 107)))
                                                  "get_child"
                                                  (:items
                                                   ("get_next_child" "get_first_child" "get_num_children" "has_child" "get_depth" "massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern function uvm_component get_child (string name);" :file "uvm_component.svh" :line 112)))
                                                  "set_name"
                                                  (:items
                                                   ("get_depth" "massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function void set_name (string name);" :file "uvm_component.svh" :line 157)))
                                                  "lookup"
                                                  (:items
                                                   ("get_depth" "massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern function uvm_component lookup (string name);" :file "uvm_component.svh" :line 169)))
                                                  "build_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function void build_phase(uvm_phase phase);" :file "uvm_component.svh" :line 211)))
                                                  "connect_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function void connect_phase(uvm_phase phase);" :file "uvm_component.svh" :line 220)))
                                                  "end_of_elaboration_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function void end_of_elaboration_phase(uvm_phase phase);" :file "uvm_component.svh" :line 229)))
                                                  "start_of_simulation_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function void start_of_simulation_phase(uvm_phase phase);" :file "uvm_component.svh" :line 238)))
                                                  "run_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "task" :desc "extern virtual task run_phase(uvm_phase phase);" :file "uvm_component.svh" :line 256)))
                                                  "pre_reset_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "task" :desc "extern virtual task pre_reset_phase(uvm_phase phase);" :file "uvm_component.svh" :line 277)))
                                                  "reset_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "task" :desc "extern virtual task reset_phase(uvm_phase phase);" :file "uvm_component.svh" :line 298)))
                                                  "post_reset_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "task" :desc "extern virtual task post_reset_phase(uvm_phase phase);" :file "uvm_component.svh" :line 319)))
                                                  "pre_configure_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "task" :desc "extern virtual task pre_configure_phase(uvm_phase phase);" :file "uvm_component.svh" :line 340)))
                                                  "configure_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "task" :desc "extern virtual task configure_phase(uvm_phase phase);" :file "uvm_component.svh" :line 361)))
                                                  "post_configure_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "task" :desc "extern virtual task post_configure_phase(uvm_phase phase);" :file "uvm_component.svh" :line 382)))
                                                  "pre_main_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "task" :desc "extern virtual task pre_main_phase(uvm_phase phase);" :file "uvm_component.svh" :line 403)))
                                                  "main_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "task" :desc "extern virtual task main_phase(uvm_phase phase);" :file "uvm_component.svh" :line 424)))
                                                  "post_main_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "task" :desc "extern virtual task post_main_phase(uvm_phase phase);" :file "uvm_component.svh" :line 445)))
                                                  "pre_shutdown_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "task" :desc "extern virtual task pre_shutdown_phase(uvm_phase phase);" :file "uvm_component.svh" :line 466)))
                                                  "shutdown_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "task" :desc "extern virtual task shutdown_phase(uvm_phase phase);" :file "uvm_component.svh" :line 487)))
                                                  "post_shutdown_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "task" :desc "extern virtual task post_shutdown_phase(uvm_phase phase);" :file "uvm_component.svh" :line 508)))
                                                  "extract_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function void extract_phase(uvm_phase phase);" :file "uvm_component.svh" :line 517)))
                                                  "check_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function void check_phase(uvm_phase phase);" :file "uvm_component.svh" :line 528)))
                                                  "report_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function void report_phase(uvm_phase phase);" :file "uvm_component.svh" :line 537)))
                                                  "final_phase"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function void final_phase(uvm_phase phase);" :file "uvm_component.svh" :line 546)))
                                                  "phase_started"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function void phase_started (uvm_phase phase);" :file "uvm_component.svh" :line 555)))
                                                  "phase_ready_to_end"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function void phase_ready_to_end (uvm_phase phase);" :file "uvm_component.svh" :line 580)))
                                                  "phase_ended"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function void phase_ended (uvm_phase phase);" :file "uvm_component.svh" :line 590)))
                                                  "set_domain"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern function void set_domain(uvm_domain domain, int hier=1);" :file "uvm_component.svh" :line 608)))
                                                  "get_domain"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern function uvm_domain get_domain();" :file "uvm_component.svh" :line 616)))
                                                  "define_domain"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual protected function void define_domain(uvm_domain domain);" :file "uvm_component.svh" :line 650)))
                                                  "suspend"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "task" :desc "extern virtual task suspend ();" :file "uvm_component.svh" :line 661)))
                                                  "resume"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "task" :desc "extern virtual task resume ();" :file "uvm_component.svh" :line 674)))
                                                  "resolve_bindings"
                                                  (:items
                                                   ("massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function void resolve_bindings ();" :file "uvm_component.svh" :line 686)))
                                                  "apply_config_settings"
                                                  (:items
                                                   ("use_automatic_config" "print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function void apply_config_settings (bit verbose = 0);" :file "uvm_component.svh" :line 732)))
                                                  "print_config"
                                                  (:items
                                                   ("print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern function void print_config(bit recurse = 0, bit audit = 0);" :file "uvm_component.svh" :line 757)))
                                                  "print_config_with_audit"
                                                  (:items
                                                   ("print_config_matches" "get_print_config_matches")
                                                   :locs
                                                   ((:type "function" :desc "extern function void print_config_with_audit(bit recurse = 0);" :file "uvm_component.svh" :line 768)))
                                                  "set_print_config_matches"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "static function void set_print_config_matches(bit val) ;" :file "uvm_component.svh" :line 794)))
                                                  "raised"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "virtual function void raised (uvm_objection objection, uvm_object source_obj," :file "uvm_component.svh" :line 818)))
                                                  "dropped"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "virtual function void dropped (uvm_objection objection, uvm_object source_obj," :file "uvm_component.svh" :line 833)))
                                                  "all_dropped"
                                                  (:items nil :locs
                                                   ((:type "task" :desc "virtual task all_dropped (uvm_objection objection, uvm_object source_obj," :file "uvm_component.svh" :line 848)))
                                                  "create_component"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "extern function uvm_component create_component (string requested_type_name," :file "uvm_component.svh" :line 881)))
                                                  "create_object"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "extern function uvm_object create_object (string requested_type_name," :file "uvm_component.svh" :line 900)))
                                                  "set_type_override_by_type"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "extern static function void set_type_override_by_type" :file "uvm_component.svh" :line 923)))
                                                  "set_inst_override_by_type"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "extern function void set_inst_override_by_type(string relative_inst_path," :file "uvm_component.svh" :line 980)))
                                                  "set_type_override"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "extern static function void set_type_override(string original_type_name," :file "uvm_component.svh" :line 1001)))
                                                  "set_inst_override"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "extern function void set_inst_override(string relative_inst_path," :file "uvm_component.svh" :line 1025)))
                                                  "print_override_info"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "extern function void print_override_info(string requested_type_name," :file "uvm_component.svh" :line 1037)))
                                                  "set_report_id_verbosity_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "extern function void set_report_id_verbosity_hier (string id," :file "uvm_component.svh" :line 1055)))
                                                  "set_report_severity_id_verbosity_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "extern function void set_report_severity_id_verbosity_hier(uvm_severity severity," :file "uvm_component.svh" :line 1069)))
                                                  "set_report_severity_action_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "extern function void set_report_severity_action_hier (uvm_severity severity," :file "uvm_component.svh" :line 1076)))
                                                  "set_report_id_action_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "extern function void set_report_id_action_hier (string id," :file "uvm_component.svh" :line 1082)))
                                                  "set_report_severity_id_action_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "extern function void set_report_severity_id_action_hier(uvm_severity severity," :file "uvm_component.svh" :line 1096)))
                                                  "set_report_default_file_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "extern function void set_report_default_file_hier (UVM_FILE file);" :file "uvm_component.svh" :line 1104)))
                                                  "set_report_severity_file_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "extern function void set_report_severity_file_hier (uvm_severity severity," :file "uvm_component.svh" :line 1108)))
                                                  "set_report_id_file_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "extern function void set_report_id_file_hier (string id," :file "uvm_component.svh" :line 1113)))
                                                  "set_report_severity_id_file_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "extern function void set_report_severity_id_file_hier(uvm_severity severity," :file "uvm_component.svh" :line 1127)))
                                                  "set_report_verbosity_level_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "extern function void set_report_verbosity_level_hier (int verbosity);" :file "uvm_component.svh" :line 1141)))
                                                  "pre_abort"
                                                  (:items nil :locs
                                                   ((:type "function" :desc "virtual function void pre_abort;" :file "uvm_component.svh" :line 1162)))
                                                  "accept_tr"
                                                  (:items
                                                   ("begin_tr" "record_error_tr" "record_event_tr" "print_enabled" "m_build_done" "m_phasing_active" "m_add_child" "m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern function void accept_tr (uvm_transaction tr, time accept_time = 0);" :file "uvm_component.svh" :line 1191)))
                                                  "error_str"
                                                  (:items nil :locs
                                                   ((:type "string" :desc "string error_str;" :file "uvm_component.svh" :line 1481)))
                                                  "cs"
                                                  (:items nil :locs
                                                   ((:type "uvm_coreservice_t" :desc "uvm_coreservice_t cs;" :file "uvm_component.svh" :line 1483)))
                                                  "do_accept_tr"
                                                  (:items
                                                   ("begin_tr" "record_error_tr" "record_event_tr" "print_enabled" "m_build_done" "m_phasing_active" "m_add_child" "m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual protected function void do_accept_tr (uvm_transaction tr);" :file "uvm_component.svh" :line 1201)))
                                                  "do_begin_tr"
                                                  (:items
                                                   ("record_error_tr" "record_event_tr" "print_enabled" "m_build_done" "m_phasing_active" "m_add_child" "m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "function void do_begin_tr (uvm_transaction tr," :file "uvm_component.svh" :line 1235)))
                                                  "end_tr"
                                                  (:items
                                                   ("record_error_tr" "record_event_tr" "print_enabled" "m_build_done" "m_phasing_active" "m_add_child" "m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern function void end_tr (uvm_transaction tr," :file "uvm_component.svh" :line 1265)))
                                                  "do_end_tr"
                                                  (:items
                                                   ("record_error_tr" "record_event_tr" "print_enabled" "m_build_done" "m_phasing_active" "m_add_child" "m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual protected function void do_end_tr (uvm_transaction tr," :file "uvm_component.svh" :line 1277)))
                                                  "get_tr_stream"
                                                  (:items
                                                   ("print_enabled" "m_build_done" "m_phasing_active" "m_add_child" "m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function uvm_tr_stream get_tr_stream(string name," :file "uvm_component.svh" :line 1326)))
                                                  "free_tr_stream"
                                                  (:items
                                                   ("print_enabled" "m_build_done" "m_phasing_active" "m_add_child" "m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function void free_tr_stream(uvm_tr_stream stream);" :file "uvm_component.svh" :line 1331)))
                                                  "do_execute_op"
                                                  (:items
                                                   ("m_build_done" "m_phasing_active" "m_add_child" "m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function void do_execute_op( uvm_field_op op );" :file "uvm_component.svh" :line 1344)))
                                                  "get_tr_database"
                                                  (:items
                                                   ("m_build_done" "m_phasing_active" "m_add_child" "m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function uvm_tr_database get_tr_database();" :file "uvm_component.svh" :line 1354)))
                                                  "set_tr_database"
                                                  (:items
                                                   ("m_build_done" "m_phasing_active" "m_add_child" "m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function void set_tr_database(uvm_tr_database db);" :file "uvm_component.svh" :line 1357)))
                                                  "set_local"
                                                  (:items
                                                   ("m_add_child" "m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern                   function void set_local(uvm_resource_base rsrc) ;" :file "uvm_component.svh" :line 1386)))
                                                  "m_set_full_name"
                                                  (:items
                                                   ("m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern local     virtual function void m_set_full_name();" :file "uvm_component.svh" :line 1392)))
                                                  "do_resolve_bindings"
                                                  (:items
                                                   ("m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern                   function void do_resolve_bindings();" :file "uvm_component.svh" :line 1394)))
                                                  "do_flush"
                                                  (:items
                                                   ("m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern                   function void do_flush();" :file "uvm_component.svh" :line 1395)))
                                                  "flush"
                                                  (:items
                                                   ("m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual           function void flush ();" :file "uvm_component.svh" :line 1397)))
                                                  "m_extract_name"
                                                  (:items
                                                   ("m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern local             function void m_extract_name(string name ," :file "uvm_component.svh" :line 1399)))
                                                  "create"
                                                  (:items
                                                   ("m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function uvm_object create (string name=\"\");" :file "uvm_component.svh" :line 1404)))
                                                  "clone"
                                                  (:items
                                                   ("m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function uvm_object clone  ();" :file "uvm_component.svh" :line 1405)))
                                                  "set_recording_enabled"
                                                  (:items
                                                   ("error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function void set_recording_enabled(bit enabled);" :file "uvm_component.svh" :line 1437)))
                                                  "set_recording_enabled_hier"
                                                  (:items
                                                   ("error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern virtual function void set_recording_enabled_hier (bit enabled);" :file "uvm_component.svh" :line 1440)))
                                                  "do_print"
                                                  (:items
                                                   ("error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern         function void   do_print(uvm_printer printer);" :file "uvm_component.svh" :line 1442)))
                                                  "m_set_cl_msg_args"
                                                  (:items
                                                   ("error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern function void m_set_cl_msg_args;" :file "uvm_component.svh" :line 1445)))
                                                  "m_set_cl_verb"
                                                  (:items
                                                   ("error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern function void m_set_cl_verb;" :file "uvm_component.svh" :line 1446)))
                                                  "m_set_cl_action"
                                                  (:items
                                                   ("error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern function void m_set_cl_action;" :file "uvm_component.svh" :line 1447)))
                                                  "m_set_cl_sev"
                                                  (:items
                                                   ("error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern function void m_set_cl_sev;" :file "uvm_component.svh" :line 1448)))
                                                  "m_apply_verbosity_settings"
                                                  (:items
                                                   ("error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern function void m_apply_verbosity_settings(uvm_phase phase);" :file "uvm_component.svh" :line 1449)))
                                                  "m_do_pre_abort"
                                                  (:items
                                                   ("error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern /*local*/ function void m_do_pre_abort;" :file "uvm_component.svh" :line 1455)))
                                                  "m_unsupported_set_local"
                                                  (:items
                                                   ("error_str" "cs")
                                                   :locs
                                                   ((:type "function" :desc "extern function void m_unsupported_set_local(uvm_resource_base rsrc);" :file "uvm_component.svh" :line 1459))))))
    ))

(defvar verilog-ext-test-tags-refs-table-alist
  '(("instances.sv" #s(hash-table size 65 test equal rehash-size 1.5 rehash-threshold 0.8125 data
                                  ("instances"
                                   (:items nil :locs
                                    ((:type nil :desc "module instances;" :file "instances.sv" :line 20)))
                                   "block0"
                                   (:items nil :locs
                                    ((:type nil :desc "block0 I_BLOCK0 (" :file "instances.sv" :line 23)))
                                   "I_BLOCK0"
                                   (:items nil :locs
                                    ((:type nil :desc "block0 I_BLOCK0 (" :file "instances.sv" :line 23)))
                                   "Port0"
                                   (:items nil :locs
                                    ((:type nil :desc ".Port0 (Port0)," :file "instances.sv" :line 102)
                                     (:type nil :desc ".Port0 (Port0)," :file "instances.sv" :line 89)
                                     (:type nil :desc ".Port0 (Port0)," :file "instances.sv" :line 67)
                                     (:type nil :desc ".Port0 (Port0)," :file "instances.sv" :line 53)
                                     (:type nil :desc ".Port0 (Port0)," :file "instances.sv" :line 42)
                                     (:type nil :desc ".Port0 (Port0)," :file "instances.sv" :line 31)
                                     (:type nil :desc ".Port0 (Port0)," :file "instances.sv" :line 24)))
                                   "Port1"
                                   (:items nil :locs
                                    ((:type nil :desc ".Port1 (Port1)," :file "instances.sv" :line 103)
                                     (:type nil :desc ".Port1 (Port1)," :file "instances.sv" :line 90)
                                     (:type nil :desc ".Port1 (Port1)," :file "instances.sv" :line 68)
                                     (:type nil :desc ".Port1 (Port1)," :file "instances.sv" :line 54)
                                     (:type nil :desc ".Port1 (Port1)," :file "instances.sv" :line 43)
                                     (:type nil :desc ".Port1 (Port1)," :file "instances.sv" :line 32)
                                     (:type nil :desc ".Port1 (Port1)," :file "instances.sv" :line 25)))
                                   "Port2"
                                   (:items nil :locs
                                    ((:type nil :desc ".Port2 (Port2)" :file "instances.sv" :line 104)
                                     (:type nil :desc ".Port2 (Port2)" :file "instances.sv" :line 91)
                                     (:type nil :desc ".Port2 (Port2)" :file "instances.sv" :line 69)
                                     (:type nil :desc ".Port2 (Port2)" :file "instances.sv" :line 55)
                                     (:type nil :desc ".Port2 (Port2)" :file "instances.sv" :line 44)
                                     (:type nil :desc ".Port2 (Port2)" :file "instances.sv" :line 33)
                                     (:type nil :desc ".Port2 (Port2)" :file "instances.sv" :line 26)))
                                   "block1"
                                   (:items nil :locs
                                    ((:type nil :desc "block1 I_BLOCK1(" :file "instances.sv" :line 30)))
                                   "I_BLOCK1"
                                   (:items nil :locs
                                    ((:type nil :desc "block1 I_BLOCK1(" :file "instances.sv" :line 30)))
                                   "block2"
                                   (:items nil :locs
                                    ((:type nil :desc "block2 #(" :file "instances.sv" :line 37)))
                                   "Param0"
                                   (:items nil :locs
                                    ((:type nil :desc ".Param0 (Param0)," :file "instances.sv" :line 96)
                                     (:type nil :desc ".Param0 (Param0)," :file "instances.sv" :line 63)
                                     (:type nil :desc ".Param0 (Param0)," :file "instances.sv" :line 49)
                                     (:type nil :desc ".Param0 (Param0)," :file "instances.sv" :line 38)))
                                   "Param1"
                                   (:items nil :locs
                                    ((:type nil :desc ".Param1 (Param1)," :file "instances.sv" :line 97)
                                     (:type nil :desc ".Param1 (Param1)," :file "instances.sv" :line 64)
                                     (:type nil :desc ".Param1 (Param1)," :file "instances.sv" :line 50)
                                     (:type nil :desc ".Param1 (Param1)," :file "instances.sv" :line 39)))
                                   "Param2"
                                   (:items nil :locs
                                    ((:type nil :desc ".Param2 (Param2)" :file "instances.sv" :line 98)
                                     (:type nil :desc ".Param2 (Param2)" :file "instances.sv" :line 65)
                                     (:type nil :desc ".Param2 (Param2)" :file "instances.sv" :line 51)
                                     (:type nil :desc ".Param2 (Param2)" :file "instances.sv" :line 40)))
                                   "I_BLOCK2"
                                   (:items nil :locs
                                    ((:type nil :desc ") I_BLOCK2 (" :file "instances.sv" :line 41)))
                                   "block3"
                                   (:items nil :locs
                                    ((:type nil :desc "block3#(" :file "instances.sv" :line 48)))
                                   "I_BLOCK3"
                                   (:items nil :locs
                                    ((:type nil :desc ")I_BLOCK3(" :file "instances.sv" :line 52)))
                                   "i"
                                   (:items nil :locs
                                    ((:type nil :desc "for (genvar i=0; i<VALUE; i++) begin : gen_test" :file "instances.sv" :line 60)))
                                   "VALUE"
                                   (:items nil :locs
                                    ((:type nil :desc "for (genvar i=0; i<VALUE; i++) begin : gen_test" :file "instances.sv" :line 60)))
                                   "gen_test"
                                   (:items nil :locs
                                    ((:type nil :desc "end : gen_test" :file "instances.sv" :line 72)
                                     (:type nil :desc "for (genvar i=0; i<VALUE; i++) begin : gen_test" :file "instances.sv" :line 60)))
                                   "block_gen"
                                   (:items nil :locs
                                    ((:type nil :desc "block_gen #(" :file "instances.sv" :line 62)))
                                   "I_BLOCK_GEN"
                                   (:items nil :locs
                                    ((:type nil :desc ") I_BLOCK_GEN (" :file "instances.sv" :line 66)))
                                   "test_if"
                                   (:items nil :locs
                                    ((:type nil :desc "test_if I_TEST_IF (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 77)))
                                   "I_TEST_IF"
                                   (:items nil :locs
                                    ((:type nil :desc "test_if I_TEST_IF (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 77)))
                                   "clk"
                                   (:items nil :locs
                                    ((:type nil :desc "test_if_params_empty #() I_TEST_IF_PARAMS_EMPTY (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 83)
                                     (:type nil :desc "test_if_params_array # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS_ARRAY[5:0] (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 81)
                                     (:type nil :desc "test_if_params # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 79)
                                     (:type nil :desc "test_if I_TEST_IF (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 77)))
                                   "rst_n"
                                   (:items nil :locs
                                    ((:type nil :desc "test_if_params_empty #() I_TEST_IF_PARAMS_EMPTY (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 83)
                                     (:type nil :desc "test_if_params_array # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS_ARRAY[5:0] (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 81)
                                     (:type nil :desc "test_if_params # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 79)
                                     (:type nil :desc "test_if I_TEST_IF (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 77)))
                                   "test_if_params"
                                   (:items nil :locs
                                    ((:type nil :desc "test_if_params # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 79)))
                                   "param1"
                                   (:items nil :locs
                                    ((:type nil :desc "test_if_params_array # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS_ARRAY[5:0] (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 81)
                                     (:type nil :desc "test_if_params # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 79)))
                                   "param2"
                                   (:items nil :locs
                                    ((:type nil :desc "test_if_params_array # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS_ARRAY[5:0] (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 81)
                                     (:type nil :desc "test_if_params # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 79)))
                                   "ITEST_IF_PARAMS"
                                   (:items nil :locs
                                    ((:type nil :desc "test_if_params # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 79)))
                                   "test_if_params_array"
                                   (:items nil :locs
                                    ((:type nil :desc "test_if_params_array # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS_ARRAY[5:0] (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 81)))
                                   "ITEST_IF_PARAMS_ARRAY"
                                   (:items nil :locs
                                    ((:type nil :desc "test_if_params_array # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS_ARRAY[5:0] (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 81)))
                                   "test_if_params_empty"
                                   (:items nil :locs
                                    ((:type nil :desc "test_if_params_empty #() I_TEST_IF_PARAMS_EMPTY (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 83)))
                                   "I_TEST_IF_PARAMS_EMPTY"
                                   (:items nil :locs
                                    ((:type nil :desc "test_if_params_empty #() I_TEST_IF_PARAMS_EMPTY (.clk(clk), .rst_n(rst_n));" :file "instances.sv" :line 83)))
                                   "block_ws_0"
                                   (:items nil :locs
                                    ((:type nil :desc "block_ws_0" :file "instances.sv" :line 87)))
                                   "I_BLOCK_WS_0"
                                   (:items nil :locs
                                    ((:type nil :desc "I_BLOCK_WS_0 (" :file "instances.sv" :line 88)))
                                   "block_ws_1"
                                   (:items nil :locs
                                    ((:type nil :desc "block_ws_1 // Comment" :file "instances.sv" :line 94)))
                                   "I_BLOCK_WS_1"
                                   (:items nil :locs
                                    ((:type nil :desc "I_BLOCK_WS_1 // More comments here" :file "instances.sv" :line 100))))))

    ("tb_program.sv" #s(hash-table size 65 test equal rehash-size 1.5 rehash-threshold 0.8125 data
                                   ("global_pkg"
                                    (:items nil :locs
                                     ((:type nil :desc "import global_pkg::*;" :file "tb_program.sv" :line 21)))
                                    "tb_program"
                                    (:items nil :locs
                                     ((:type nil :desc "endmodule: tb_program" :file "tb_program.sv" :line 151)
                                      (:type nil :desc "module automatic tb_program (" :file "tb_program.sv" :line 23)))
                                    "Clk"
                                    (:items nil :locs
                                     ((:type nil :desc "repeat (1000) @(posedge Clk);" :file "tb_program.sv" :line 140)
                                      (:type nil :desc "@(posedge Clk); // Resync" :file "tb_program.sv" :line 130)
                                      (:type nil :desc "repeat (BIT_CYCLES) @(posedge Clk);" :file "tb_program.sv" :line 127)
                                      (:type nil :desc "repeat (BIT_CYCLES) @(posedge Clk);" :file "tb_program.sv" :line 123)
                                      (:type nil :desc "repeat (BIT_CYCLES) @(posedge Clk);" :file "tb_program.sv" :line 119)
                                      (:type nil :desc "@(posedge Clk);" :file "tb_program.sv" :line 116)
                                      (:type nil :desc "repeat (10) @(posedge Clk);" :file "tb_program.sv" :line 110)
                                      (:type nil :desc "repeat (10) @(posedge Clk);" :file "tb_program.sv" :line 108)
                                      (:type nil :desc "repeat (10) @(posedge Clk);" :file "tb_program.sv" :line 106)
                                      (:type nil :desc "input logic         Clk," :file "tb_program.sv" :line 24)))
                                    "Rst_n"
                                    (:items nil :locs
                                     ((:type nil :desc "Rst_n <= 1;" :file "tb_program.sv" :line 109)
                                      (:type nil :desc "Rst_n <= 0;" :file "tb_program.sv" :line 107)
                                      (:type nil :desc "output logic        Rst_n," :file "tb_program.sv" :line 25)))
                                    "RXD"
                                    (:items nil :locs
                                     ((:type nil :desc "RXD = 1'b1;" :file "tb_program.sv" :line 126)
                                      (:type nil :desc "RXD = Data[i];" :file "tb_program.sv" :line 122)
                                      (:type nil :desc "RXD = 1'b0;" :file "tb_program.sv" :line 118)
                                      (:type nil :desc "RXD = 1'b1;" :file "tb_program.sv" :line 100)
                                      (:type nil :desc "output logic        RXD," :file "tb_program.sv" :line 26)))
                                    "TXD"
                                    (:items nil :locs
                                     ((:type nil :desc "input logic         TXD," :file "tb_program.sv" :line 27)))
                                    "Temp"
                                    (:items nil :locs
                                     ((:type nil :desc "input logic [7:0]   Temp," :file "tb_program.sv" :line 28)))
                                    "Switches"
                                    (:items nil :locs
                                     ((:type nil :desc "input logic [7:0]   Switches," :file "tb_program.sv" :line 29)))
                                    "ROM_Data"
                                    (:items nil :locs
                                     ((:type nil :desc "assign ROM_Data = ROM[ROM_Addr];" :file "tb_program.sv" :line 56)
                                      (:type nil :desc "output logic [11:0] ROM_Data," :file "tb_program.sv" :line 30)))
                                    "ROM_Addr"
                                    (:items nil :locs
                                     ((:type nil :desc "assign ROM_Data = ROM[ROM_Addr];" :file "tb_program.sv" :line 56)
                                      (:type nil :desc "input logic [11:0]  ROM_Addr" :file "tb_program.sv" :line 31)))
                                    "FREQ_CLK"
                                    (:items nil :locs
                                     ((:type nil :desc "localparam integer BIT_CYCLES = FREQ_CLK / TX_SPEED;" :file "tb_program.sv" :line 39)
                                      (:type nil :desc "localparam logic [31:0] FREQ_CLK = 100000000;" :file "tb_program.sv" :line 37)))
                                    "TX_SPEED"
                                    (:items nil :locs
                                     ((:type nil :desc "localparam integer BIT_CYCLES = FREQ_CLK / TX_SPEED;" :file "tb_program.sv" :line 39)
                                      (:type nil :desc "localparam logic [31:0] TX_SPEED = 115200;" :file "tb_program.sv" :line 38)))
                                    "BIT_CYCLES"
                                    (:items nil :locs
                                     ((:type nil :desc "repeat (BIT_CYCLES) @(posedge Clk);" :file "tb_program.sv" :line 127)
                                      (:type nil :desc "repeat (BIT_CYCLES) @(posedge Clk);" :file "tb_program.sv" :line 123)
                                      (:type nil :desc "repeat (BIT_CYCLES) @(posedge Clk);" :file "tb_program.sv" :line 119)
                                      (:type nil :desc "localparam integer BIT_CYCLES = FREQ_CLK / TX_SPEED;" :file "tb_program.sv" :line 39)))
                                    "tb_top"
                                    (:items nil :locs
                                     ((:type nil :desc "$dumpvars(0, tb_top);     // Module Output file" :file "tb_program.sv" :line 49)))
                                    "ROM"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['h2A] = 8'h20;" :file "tb_program.sv" :line 94)
                                      (:type nil :desc "ROM['h29] = {TYPE_2, JMP_UNCOND};" :file "tb_program.sv" :line 93)
                                      (:type nil :desc "ROM['h28] = {TYPE_4, 6'h0};" :file "tb_program.sv" :line 91)
                                      (:type nil :desc "ROM['h27] = DMA_TX_BUFFER_LSB;" :file "tb_program.sv" :line 89)
                                      (:type nil :desc "ROM['h26] = {TYPE_3, WR_SRC_ACC, DST_MEM};" :file "tb_program.sv" :line 88)
                                      (:type nil :desc "ROM['h25] = 'hCD;" :file "tb_program.sv" :line 87)
                                      (:type nil :desc "ROM['h24] = {TYPE_3, LD_SRC_CONSTANT, DST_ACC}; // for LSB" :file "tb_program.sv" :line 86)
                                      (:type nil :desc "ROM['h23] = DMA_TX_BUFFER_MSB;                  // One for MSB and other" :file "tb_program.sv" :line 85)
                                      (:type nil :desc "ROM['h22] = {TYPE_3, WR_SRC_ACC, DST_MEM};      // from acc to mem." :file "tb_program.sv" :line 84)
                                      (:type nil :desc "ROM['h21] = 'hAB;                               // Requires write to acc and" :file "tb_program.sv" :line 83)
                                      (:type nil :desc "ROM['h20] = {TYPE_3, LD_SRC_CONSTANT, DST_ACC}; // Load DMA TX registers:" :file "tb_program.sv" :line 82)
                                      (:type nil :desc "ROM['hF]  = 8'h20;" :file "tb_program.sv" :line 80)
                                      (:type nil :desc "ROM['hE]  = {TYPE_2, JMP_UNCOND};" :file "tb_program.sv" :line 79)
                                      (:type nil :desc "ROM['hD]  = {TYPE_1, ALU_AND};" :file "tb_program.sv" :line 78)
                                      (:type nil :desc "ROM['hC]  = {TYPE_1, ALU_BIN2ASCII};" :file "tb_program.sv" :line 77)
                                      (:type nil :desc "ROM['hB]  = {TYPE_1, ALU_ASCII2BIN};" :file "tb_program.sv" :line 76)
                                      (:type nil :desc "ROM['hA]  = {TYPE_1, ALU_SHIFTR}; // SHR" :file "tb_program.sv" :line 74)
                                      (:type nil :desc "ROM['h9]  = {TYPE_1, ALU_SHIFTL}; // SHL" :file "tb_program.sv" :line 73)
                                      (:type nil :desc "ROM['h8]  = 8'h40;" :file "tb_program.sv" :line 71)
                                      (:type nil :desc "ROM['h7]  = {TYPE_3, LD_SRC_MEM, DST_A}; // LD  0x40 Ra" :file "tb_program.sv" :line 70)
                                      (:type nil :desc "ROM['h6]  = 8'h40;" :file "tb_program.sv" :line 68)
                                      (:type nil :desc "ROM['h5]  = {TYPE_3, WR_SRC_ACC, DST_MEM}; // MV Acc #40" :file "tb_program.sv" :line 67)
                                      (:type nil :desc "ROM['h4]  = {TYPE_1, ALU_ADD};" :file "tb_program.sv" :line 65)
                                      (:type nil :desc "ROM['h3]  = 8'h3;" :file "tb_program.sv" :line 64)
                                      (:type nil :desc "ROM['h2]  = {TYPE_3, LD_SRC_CONSTANT, DST_B}; // LD #3 Rb" :file "tb_program.sv" :line 63)
                                      (:type nil :desc "ROM['h1]  = 8'h2;" :file "tb_program.sv" :line 62)
                                      (:type nil :desc "ROM['h0]  = {TYPE_3, LD_SRC_CONSTANT, DST_A}; // LD #2 Ra" :file "tb_program.sv" :line 61)
                                      (:type nil :desc "assign ROM_Data = ROM[ROM_Addr];" :file "tb_program.sv" :line 56)
                                      (:type nil :desc "logic [11:0] ROM [4096];" :file "tb_program.sv" :line 55)))
                                    "init_rom"
                                    (:items nil :locs
                                     ((:type nil :desc "init_rom;" :file "tb_program.sv" :line 135)
                                      (:type nil :desc "endtask: init_rom" :file "tb_program.sv" :line 95)
                                      (:type nil :desc "task init_rom ();" :file "tb_program.sv" :line 58)))
                                    "TYPE_3"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['h26] = {TYPE_3, WR_SRC_ACC, DST_MEM};" :file "tb_program.sv" :line 88)
                                      (:type nil :desc "ROM['h24] = {TYPE_3, LD_SRC_CONSTANT, DST_ACC}; // for LSB" :file "tb_program.sv" :line 86)
                                      (:type nil :desc "ROM['h22] = {TYPE_3, WR_SRC_ACC, DST_MEM};      // from acc to mem." :file "tb_program.sv" :line 84)
                                      (:type nil :desc "ROM['h20] = {TYPE_3, LD_SRC_CONSTANT, DST_ACC}; // Load DMA TX registers:" :file "tb_program.sv" :line 82)
                                      (:type nil :desc "ROM['h7]  = {TYPE_3, LD_SRC_MEM, DST_A}; // LD  0x40 Ra" :file "tb_program.sv" :line 70)
                                      (:type nil :desc "ROM['h5]  = {TYPE_3, WR_SRC_ACC, DST_MEM}; // MV Acc #40" :file "tb_program.sv" :line 67)
                                      (:type nil :desc "ROM['h2]  = {TYPE_3, LD_SRC_CONSTANT, DST_B}; // LD #3 Rb" :file "tb_program.sv" :line 63)
                                      (:type nil :desc "ROM['h0]  = {TYPE_3, LD_SRC_CONSTANT, DST_A}; // LD #2 Ra" :file "tb_program.sv" :line 61)))
                                    "LD_SRC_CONSTANT"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['h24] = {TYPE_3, LD_SRC_CONSTANT, DST_ACC}; // for LSB" :file "tb_program.sv" :line 86)
                                      (:type nil :desc "ROM['h20] = {TYPE_3, LD_SRC_CONSTANT, DST_ACC}; // Load DMA TX registers:" :file "tb_program.sv" :line 82)
                                      (:type nil :desc "ROM['h2]  = {TYPE_3, LD_SRC_CONSTANT, DST_B}; // LD #3 Rb" :file "tb_program.sv" :line 63)
                                      (:type nil :desc "ROM['h0]  = {TYPE_3, LD_SRC_CONSTANT, DST_A}; // LD #2 Ra" :file "tb_program.sv" :line 61)))
                                    "DST_A"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['h7]  = {TYPE_3, LD_SRC_MEM, DST_A}; // LD  0x40 Ra" :file "tb_program.sv" :line 70)
                                      (:type nil :desc "ROM['h0]  = {TYPE_3, LD_SRC_CONSTANT, DST_A}; // LD #2 Ra" :file "tb_program.sv" :line 61)))
                                    "DST_B"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['h2]  = {TYPE_3, LD_SRC_CONSTANT, DST_B}; // LD #3 Rb" :file "tb_program.sv" :line 63)))
                                    "TYPE_1"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['hD]  = {TYPE_1, ALU_AND};" :file "tb_program.sv" :line 78)
                                      (:type nil :desc "ROM['hC]  = {TYPE_1, ALU_BIN2ASCII};" :file "tb_program.sv" :line 77)
                                      (:type nil :desc "ROM['hB]  = {TYPE_1, ALU_ASCII2BIN};" :file "tb_program.sv" :line 76)
                                      (:type nil :desc "ROM['hA]  = {TYPE_1, ALU_SHIFTR}; // SHR" :file "tb_program.sv" :line 74)
                                      (:type nil :desc "ROM['h9]  = {TYPE_1, ALU_SHIFTL}; // SHL" :file "tb_program.sv" :line 73)
                                      (:type nil :desc "ROM['h4]  = {TYPE_1, ALU_ADD};" :file "tb_program.sv" :line 65)))
                                    "ALU_ADD"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['h4]  = {TYPE_1, ALU_ADD};" :file "tb_program.sv" :line 65)))
                                    "WR_SRC_ACC"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['h26] = {TYPE_3, WR_SRC_ACC, DST_MEM};" :file "tb_program.sv" :line 88)
                                      (:type nil :desc "ROM['h22] = {TYPE_3, WR_SRC_ACC, DST_MEM};      // from acc to mem." :file "tb_program.sv" :line 84)
                                      (:type nil :desc "ROM['h5]  = {TYPE_3, WR_SRC_ACC, DST_MEM}; // MV Acc #40" :file "tb_program.sv" :line 67)))
                                    "DST_MEM"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['h26] = {TYPE_3, WR_SRC_ACC, DST_MEM};" :file "tb_program.sv" :line 88)
                                      (:type nil :desc "ROM['h22] = {TYPE_3, WR_SRC_ACC, DST_MEM};      // from acc to mem." :file "tb_program.sv" :line 84)
                                      (:type nil :desc "ROM['h5]  = {TYPE_3, WR_SRC_ACC, DST_MEM}; // MV Acc #40" :file "tb_program.sv" :line 67)))
                                    "LD_SRC_MEM"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['h7]  = {TYPE_3, LD_SRC_MEM, DST_A}; // LD  0x40 Ra" :file "tb_program.sv" :line 70)))
                                    "ALU_SHIFTL"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['h9]  = {TYPE_1, ALU_SHIFTL}; // SHL" :file "tb_program.sv" :line 73)))
                                    "ALU_SHIFTR"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['hA]  = {TYPE_1, ALU_SHIFTR}; // SHR" :file "tb_program.sv" :line 74)))
                                    "ALU_ASCII2BIN"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['hB]  = {TYPE_1, ALU_ASCII2BIN};" :file "tb_program.sv" :line 76)))
                                    "ALU_BIN2ASCII"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['hC]  = {TYPE_1, ALU_BIN2ASCII};" :file "tb_program.sv" :line 77)))
                                    "ALU_AND"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['hD]  = {TYPE_1, ALU_AND};" :file "tb_program.sv" :line 78)))
                                    "TYPE_2"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['h29] = {TYPE_2, JMP_UNCOND};" :file "tb_program.sv" :line 93)
                                      (:type nil :desc "ROM['hE]  = {TYPE_2, JMP_UNCOND};" :file "tb_program.sv" :line 79)))
                                    "JMP_UNCOND"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['h29] = {TYPE_2, JMP_UNCOND};" :file "tb_program.sv" :line 93)
                                      (:type nil :desc "ROM['hE]  = {TYPE_2, JMP_UNCOND};" :file "tb_program.sv" :line 79)))
                                    "DST_ACC"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['h24] = {TYPE_3, LD_SRC_CONSTANT, DST_ACC}; // for LSB" :file "tb_program.sv" :line 86)
                                      (:type nil :desc "ROM['h20] = {TYPE_3, LD_SRC_CONSTANT, DST_ACC}; // Load DMA TX registers:" :file "tb_program.sv" :line 82)))
                                    "DMA_TX_BUFFER_MSB"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['h23] = DMA_TX_BUFFER_MSB;                  // One for MSB and other" :file "tb_program.sv" :line 85)))
                                    "DMA_TX_BUFFER_LSB"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['h27] = DMA_TX_BUFFER_LSB;" :file "tb_program.sv" :line 89)))
                                    "TYPE_4"
                                    (:items nil :locs
                                     ((:type nil :desc "ROM['h28] = {TYPE_4, 6'h0};" :file "tb_program.sv" :line 91)))
                                    "init_values"
                                    (:items nil :locs
                                     ((:type nil :desc "init_values;" :file "tb_program.sv" :line 105)
                                      (:type nil :desc "endtask : init_values" :file "tb_program.sv" :line 101)
                                      (:type nil :desc "task init_values;" :file "tb_program.sv" :line 99)))
                                    "reset_system"
                                    (:items nil :locs
                                     ((:type nil :desc "reset_system;" :file "tb_program.sv" :line 136)
                                      (:type nil :desc "endtask : reset_system" :file "tb_program.sv" :line 111)
                                      (:type nil :desc "task reset_system;" :file "tb_program.sv" :line 104)))
                                    "serial_rx"
                                    (:items nil :locs
                                     ((:type nil :desc "serial_rx('hCD);" :file "tb_program.sv" :line 139)
                                      (:type nil :desc "serial_rx('hAB);" :file "tb_program.sv" :line 138)
                                      (:type nil :desc "endtask: serial_rx" :file "tb_program.sv" :line 131)
                                      (:type nil :desc "task serial_rx (input logic [7:0] Data);" :file "tb_program.sv" :line 115)))
                                    "Data"
                                    (:items nil :locs
                                     ((:type nil :desc "RXD = Data[i];" :file "tb_program.sv" :line 122)
                                      (:type nil :desc "task serial_rx (input logic [7:0] Data);" :file "tb_program.sv" :line 115)))
                                    "i"
                                    (:items nil :locs
                                     ((:type nil :desc "RXD = Data[i];" :file "tb_program.sv" :line 122)
                                      (:type nil :desc "for (int i=0; i<8; ++i) begin" :file "tb_program.sv" :line 121))))))

    ("ucontroller.sv" #s(hash-table size 97 test equal rehash-size 1.5 rehash-threshold 0.8125 data
                                    ("ucontroller"
                                     (:items nil :locs
                                      ((:type nil :desc "endmodule: ucontroller" :file "ucontroller.sv" :line 213)
                                       (:type nil :desc "module ucontroller # (" :file "ucontroller.sv" :line 21)))
                                     "FREQ_CLK"
                                     (:items nil :locs
                                      ((:type nil :desc ".FREQ_CLK (FREQ_CLK)," :file "ucontroller.sv" :line 153)
                                       (:type nil :desc "parameter logic [31:0] FREQ_CLK = 100000000," :file "ucontroller.sv" :line 22)))
                                     "TX_SPEED"
                                     (:items nil :locs
                                      ((:type nil :desc ".TX_SPEED (TX_SPEED)" :file "ucontroller.sv" :line 154)
                                       (:type nil :desc "parameter logic [31:0] TX_SPEED = 115200" :file "ucontroller.sv" :line 23)))
                                     "Clk"
                                     (:items nil :locs
                                      ((:type nil :desc ".Clk," :file "ucontroller.sv" :line 198)
                                       (:type nil :desc ".Clk," :file "ucontroller.sv" :line 173)
                                       (:type nil :desc ".Clk," :file "ucontroller.sv" :line 156)
                                       (:type nil :desc ".Clk," :file "ucontroller.sv" :line 126)
                                       (:type nil :desc ".Clk," :file "ucontroller.sv" :line 113)
                                       (:type nil :desc ".Clk," :file "ucontroller.sv" :line 84)
                                       (:type nil :desc "input logic         Clk," :file "ucontroller.sv" :line 25)))
                                     "Rst_n"
                                     (:items nil :locs
                                      ((:type nil :desc ".Rst_n," :file "ucontroller.sv" :line 199)
                                       (:type nil :desc ".Rst_n," :file "ucontroller.sv" :line 174)
                                       (:type nil :desc ".Rst_n," :file "ucontroller.sv" :line 157)
                                       (:type nil :desc ".Rst_n," :file "ucontroller.sv" :line 127)
                                       (:type nil :desc ".Rst_n," :file "ucontroller.sv" :line 114)
                                       (:type nil :desc ".Rst_n," :file "ucontroller.sv" :line 85)
                                       (:type nil :desc "input logic         Rst_n," :file "ucontroller.sv" :line 26)))
                                     "RXD"
                                     (:items nil :locs
                                      ((:type nil :desc ".RXD," :file "ucontroller.sv" :line 166)
                                       (:type nil :desc "input logic         RXD," :file "ucontroller.sv" :line 28)))
                                     "TXD"
                                     (:items nil :locs
                                      ((:type nil :desc ".TXD," :file "ucontroller.sv" :line 162)
                                       (:type nil :desc "output logic        TXD," :file "ucontroller.sv" :line 29)))
                                     "ROM_Data"
                                     (:items nil :locs
                                      ((:type nil :desc ".ROM_Data," :file "ucontroller.sv" :line 87)
                                       (:type nil :desc "input logic [11:0]  ROM_Data," :file "ucontroller.sv" :line 31)))
                                     "ROM_Addr"
                                     (:items nil :locs
                                      ((:type nil :desc ".ROM_Addr," :file "ucontroller.sv" :line 88)
                                       (:type nil :desc "output logic [11:0] ROM_Addr," :file "ucontroller.sv" :line 32)))
                                     "Temp"
                                     (:items nil :locs
                                      ((:type nil :desc ".Temp" :file "ucontroller.sv" :line 207)
                                       (:type nil :desc "output logic [7:0]  Temp," :file "ucontroller.sv" :line 34)))
                                     "Switches"
                                     (:items nil :locs
                                      ((:type nil :desc ".Switches," :file "ucontroller.sv" :line 206)
                                       (:type nil :desc "output logic [7:0]  Switches" :file "ucontroller.sv" :line 35)))
                                     "DMA_Oen"
                                     (:items nil :locs
                                      ((:type nil :desc ".DMA_Oen," :file "ucontroller.sv" :line 188)
                                       (:type nil :desc ".Oen     (DMA_Oen)" :file "ucontroller.sv" :line 148)
                                       (:type nil :desc "logic       DMA_Oen;" :file "ucontroller.sv" :line 40)))
                                     "DMA_Wen"
                                     (:items nil :locs
                                      ((:type nil :desc ".DMA_Wen," :file "ucontroller.sv" :line 191)
                                       (:type nil :desc ".Wen     (DMA_Wen)," :file "ucontroller.sv" :line 147)
                                       (:type nil :desc "logic       DMA_Wen;" :file "ucontroller.sv" :line 41)))
                                     "DMA_Cs"
                                     (:items nil :locs
                                      ((:type nil :desc ".DMA_Cs," :file "ucontroller.sv" :line 185)
                                       (:type nil :desc ".Cs      (DMA_Cs)," :file "ucontroller.sv" :line 146)
                                       (:type nil :desc "logic       DMA_Cs;" :file "ucontroller.sv" :line 42)))
                                     "CPU_Oen"
                                     (:items nil :locs
                                      ((:type nil :desc ".CPU_Oen," :file "ucontroller.sv" :line 187)
                                       (:type nil :desc ".RAM_Oen      (CPU_Oen)," :file "ucontroller.sv" :line 95)
                                       (:type nil :desc "logic       CPU_Oen;" :file "ucontroller.sv" :line 43)))
                                     "CPU_Wen"
                                     (:items nil :locs
                                      ((:type nil :desc ".CPU_Wen," :file "ucontroller.sv" :line 190)
                                       (:type nil :desc ".RAM_Wen      (CPU_Wen)," :file "ucontroller.sv" :line 94)
                                       (:type nil :desc "logic       CPU_Wen;" :file "ucontroller.sv" :line 44)))
                                     "CPU_Cs"
                                     (:items nil :locs
                                      ((:type nil :desc ".CPU_Cs," :file "ucontroller.sv" :line 184)
                                       (:type nil :desc ".RAM_Cs       (CPU_Cs)," :file "ucontroller.sv" :line 93)
                                       (:type nil :desc "logic       CPU_Cs;" :file "ucontroller.sv" :line 45)))
                                     "CPU_Address"
                                     (:items nil :locs
                                      ((:type nil :desc ".CPU_Address," :file "ucontroller.sv" :line 181)
                                       (:type nil :desc ".RAM_Addr     (CPU_Address)," :file "ucontroller.sv" :line 90)
                                       (:type nil :desc "logic [7:0] CPU_Address;" :file "ucontroller.sv" :line 46)))
                                     "DMA_Address"
                                     (:items nil :locs
                                      ((:type nil :desc ".DMA_Address," :file "ucontroller.sv" :line 182)
                                       (:type nil :desc ".Address (DMA_Address)," :file "ucontroller.sv" :line 143)
                                       (:type nil :desc "logic [7:0] DMA_Address;" :file "ucontroller.sv" :line 47)))
                                     "DMA_DataOut"
                                     (:items nil :locs
                                      ((:type nil :desc ".DMA_DataOut," :file "ucontroller.sv" :line 179)
                                       (:type nil :desc ".DataOut (DMA_DataOut)," :file "ucontroller.sv" :line 144)
                                       (:type nil :desc "logic [7:0] DMA_DataOut;" :file "ucontroller.sv" :line 48)))
                                     "CPU_DataOut"
                                     (:items nil :locs
                                      ((:type nil :desc ".CPU_DataOut," :file "ucontroller.sv" :line 178)
                                       (:type nil :desc ".DataOut      (CPU_DataOut)," :file "ucontroller.sv" :line 91)
                                       (:type nil :desc "logic [7:0] CPU_DataOut;" :file "ucontroller.sv" :line 49)))
                                     "Dma_Idle"
                                     (:items nil :locs
                                      ((:type nil :desc ".DMA_Idle      (Dma_Idle)," :file "ucontroller.sv" :line 177)
                                       (:type nil :desc ".Dma_Idle," :file "ucontroller.sv" :line 133)
                                       (:type nil :desc "logic       Dma_Idle;" :file "ucontroller.sv" :line 50)))
                                     "TX_Data"
                                     (:items nil :locs
                                      ((:type nil :desc ".TX_DataIn (TX_Data)," :file "ucontroller.sv" :line 160)
                                       (:type nil :desc ".TX_Data," :file "ucontroller.sv" :line 140)
                                       (:type nil :desc "logic [7:0] TX_Data;" :file "ucontroller.sv" :line 52)))
                                     "TX_Ready"
                                     (:items nil :locs
                                      ((:type nil :desc ".TX_Ready," :file "ucontroller.sv" :line 161)
                                       (:type nil :desc ".TX_Ready," :file "ucontroller.sv" :line 139)
                                       (:type nil :desc "logic       TX_Ready;" :file "ucontroller.sv" :line 53)))
                                     "TX_Valid"
                                     (:items nil :locs
                                      ((:type nil :desc ".TX_Valid," :file "ucontroller.sv" :line 159)
                                       (:type nil :desc ".TX_Valid," :file "ucontroller.sv" :line 141)
                                       (:type nil :desc "logic       TX_Valid;" :file "ucontroller.sv" :line 54)))
                                     "Data_Read"
                                     (:items nil :locs
                                      ((:type nil :desc ".Data_Read," :file "ucontroller.sv" :line 164)
                                       (:type nil :desc ".Data_Read," :file "ucontroller.sv" :line 138)
                                       (:type nil :desc "logic       Data_Read;" :file "ucontroller.sv" :line 55)))
                                     "RX_Data"
                                     (:items nil :locs
                                      ((:type nil :desc ".Data_Out  (RX_Data)," :file "ucontroller.sv" :line 165)
                                       (:type nil :desc ".RX_Data," :file "ucontroller.sv" :line 135)
                                       (:type nil :desc "logic [7:0] RX_Data;" :file "ucontroller.sv" :line 56)))
                                     "RX_Empty"
                                     (:items nil :locs
                                      ((:type nil :desc ".Empty     (RX_Empty)" :file "ucontroller.sv" :line 168)
                                       (:type nil :desc ".RX_Empty," :file "ucontroller.sv" :line 136)
                                       (:type nil :desc "logic       RX_Empty;" :file "ucontroller.sv" :line 57)))
                                     "RX_Full"
                                     (:items nil :locs
                                      ((:type nil :desc ".Full      (RX_Full)," :file "ucontroller.sv" :line 167)
                                       (:type nil :desc ".RX_Full," :file "ucontroller.sv" :line 137)
                                       (:type nil :desc "logic       RX_Full;" :file "ucontroller.sv" :line 58)))
                                     "RAM_DataOut"
                                     (:items nil :locs
                                      ((:type nil :desc ".DataOut (RAM_DataOut)," :file "ucontroller.sv" :line 205)
                                       (:type nil :desc ".DataIn  (RAM_DataOut)," :file "ucontroller.sv" :line 145)
                                       (:type nil :desc ".DataIn       (RAM_DataOut)," :file "ucontroller.sv" :line 92)
                                       (:type nil :desc "logic [7:0] RAM_DataOut;" :file "ucontroller.sv" :line 60)))
                                     "RAM_DataIn"
                                     (:items nil :locs
                                      ((:type nil :desc ".DataIn  (RAM_DataIn)," :file "ucontroller.sv" :line 204)
                                       (:type nil :desc ".RAM_DataIn," :file "ucontroller.sv" :line 180)
                                       (:type nil :desc "logic [7:0] RAM_DataIn;" :file "ucontroller.sv" :line 61)))
                                     "ALU_DataIn"
                                     (:items nil :locs
                                      ((:type nil :desc ".InData  (ALU_DataIn)," :file "ucontroller.sv" :line 115)
                                       (:type nil :desc ".ALU_DataIn," :file "ucontroller.sv" :line 104)
                                       (:type nil :desc "logic [7:0] ALU_DataIn;" :file "ucontroller.sv" :line 63)))
                                     "ALU_DataOut"
                                     (:items nil :locs
                                      ((:type nil :desc ".OutData (ALU_DataOut)," :file "ucontroller.sv" :line 116)
                                       (:type nil :desc ".ALU_DataOut," :file "ucontroller.sv" :line 103)
                                       (:type nil :desc "logic [7:0] ALU_DataOut;" :file "ucontroller.sv" :line 64)))
                                     "alu_op"
                                     (:items nil :locs
                                      ((:type nil :desc "alu_op      ALU_op;" :file "ucontroller.sv" :line 65)))
                                     "ALU_op"
                                     (:items nil :locs
                                      ((:type nil :desc ".ALU_op," :file "ucontroller.sv" :line 117)
                                       (:type nil :desc ".ALU_op," :file "ucontroller.sv" :line 102)
                                       (:type nil :desc "alu_op      ALU_op;" :file "ucontroller.sv" :line 65)))
                                     "FlagE"
                                     (:items nil :locs
                                      ((:type nil :desc ".FlagE" :file "ucontroller.sv" :line 121)
                                       (:type nil :desc ".FlagE" :file "ucontroller.sv" :line 108)
                                       (:type nil :desc "logic       FlagE;" :file "ucontroller.sv" :line 66)))
                                     "FlagN"
                                     (:items nil :locs
                                      ((:type nil :desc ".FlagN," :file "ucontroller.sv" :line 120)
                                       (:type nil :desc ".FlagN," :file "ucontroller.sv" :line 107)
                                       (:type nil :desc "logic       FlagN;" :file "ucontroller.sv" :line 67)))
                                     "FlagC"
                                     (:items nil :locs
                                      ((:type nil :desc ".FlagC," :file "ucontroller.sv" :line 119)
                                       (:type nil :desc ".FlagC," :file "ucontroller.sv" :line 106)
                                       (:type nil :desc "logic       FlagC;" :file "ucontroller.sv" :line 68)))
                                     "FlagZ"
                                     (:items nil :locs
                                      ((:type nil :desc ".FlagZ," :file "ucontroller.sv" :line 118)
                                       (:type nil :desc ".FlagZ," :file "ucontroller.sv" :line 105)
                                       (:type nil :desc "logic       FlagZ;" :file "ucontroller.sv" :line 69)))
                                     "RAM_Address"
                                     (:items nil :locs
                                      ((:type nil :desc ".Address (RAM_Address)," :file "ucontroller.sv" :line 203)
                                       (:type nil :desc ".RAM_Address," :file "ucontroller.sv" :line 183)
                                       (:type nil :desc "logic [7:0] RAM_Address;" :file "ucontroller.sv" :line 71)))
                                     "RAM_Wen"
                                     (:items nil :locs
                                      ((:type nil :desc ".Wen     (RAM_Wen)," :file "ucontroller.sv" :line 201)
                                       (:type nil :desc ".RAM_Wen" :file "ucontroller.sv" :line 192)
                                       (:type nil :desc ".RAM_Wen      (CPU_Wen)," :file "ucontroller.sv" :line 94)
                                       (:type nil :desc "logic       RAM_Wen;" :file "ucontroller.sv" :line 72)))
                                     "RAM_Oen"
                                     (:items nil :locs
                                      ((:type nil :desc ".Oen     (RAM_Oen)," :file "ucontroller.sv" :line 202)
                                       (:type nil :desc ".RAM_Oen," :file "ucontroller.sv" :line 189)
                                       (:type nil :desc ".RAM_Oen      (CPU_Oen)," :file "ucontroller.sv" :line 95)
                                       (:type nil :desc "logic       RAM_Oen;" :file "ucontroller.sv" :line 73)))
                                     "RAM_Cs"
                                     (:items nil :locs
                                      ((:type nil :desc ".Cs      (RAM_Cs)," :file "ucontroller.sv" :line 200)
                                       (:type nil :desc ".RAM_Cs," :file "ucontroller.sv" :line 186)
                                       (:type nil :desc ".RAM_Cs       (CPU_Cs)," :file "ucontroller.sv" :line 93)
                                       (:type nil :desc "logic       RAM_Cs;" :file "ucontroller.sv" :line 74)))
                                     "Bus_grant"
                                     (:items nil :locs
                                      ((:type nil :desc ".DMA_Bus_grant (Bus_grant)," :file "ucontroller.sv" :line 176)
                                       (:type nil :desc ".Bus_grant," :file "ucontroller.sv" :line 129)
                                       (:type nil :desc ".DMA_Ack      (Bus_grant)," :file "ucontroller.sv" :line 98)
                                       (:type nil :desc "logic       Bus_grant;" :file "ucontroller.sv" :line 76)))
                                     "Bus_req"
                                     (:items nil :locs
                                      ((:type nil :desc ".DMA_Bus_req   (Bus_req)," :file "ucontroller.sv" :line 175)
                                       (:type nil :desc ".Bus_req," :file "ucontroller.sv" :line 130)
                                       (:type nil :desc ".DMA_Req      (Bus_req)," :file "ucontroller.sv" :line 97)
                                       (:type nil :desc "logic       Bus_req;" :file "ucontroller.sv" :line 77)))
                                     "Dma_Tx_Ready"
                                     (:items nil :locs
                                      ((:type nil :desc ".Dma_Tx_Ready," :file "ucontroller.sv" :line 132)
                                       (:type nil :desc ".DMA_Ready    (Dma_Tx_Ready)," :file "ucontroller.sv" :line 99)
                                       (:type nil :desc "logic       Dma_Tx_Ready;" :file "ucontroller.sv" :line 78)))
                                     "Dma_Tx_Start"
                                     (:items nil :locs
                                      ((:type nil :desc ".Dma_Tx_Start," :file "ucontroller.sv" :line 131)
                                       (:type nil :desc ".DMA_Tx_Start (Dma_Tx_Start)," :file "ucontroller.sv" :line 100)
                                       (:type nil :desc "logic       Dma_Tx_Start;" :file "ucontroller.sv" :line 79)))
                                     "cpu"
                                     (:items nil :locs
                                      ((:type nil :desc "cpu I_CPU (" :file "ucontroller.sv" :line 83)))
                                     "I_CPU"
                                     (:items nil :locs
                                      ((:type nil :desc "cpu I_CPU (" :file "ucontroller.sv" :line 83)))
                                     "RAM_Addr"
                                     (:items nil :locs
                                      ((:type nil :desc ".RAM_Addr     (CPU_Address)," :file "ucontroller.sv" :line 90)))
                                     "DataOut"
                                     (:items nil :locs
                                      ((:type nil :desc ".DataOut (RAM_DataOut)," :file "ucontroller.sv" :line 205)
                                       (:type nil :desc ".DataOut (DMA_DataOut)," :file "ucontroller.sv" :line 144)
                                       (:type nil :desc ".DataOut      (CPU_DataOut)," :file "ucontroller.sv" :line 91)))
                                     "DataIn"
                                     (:items nil :locs
                                      ((:type nil :desc ".DataIn  (RAM_DataIn)," :file "ucontroller.sv" :line 204)
                                       (:type nil :desc ".DataIn  (RAM_DataOut)," :file "ucontroller.sv" :line 145)
                                       (:type nil :desc ".DataIn       (RAM_DataOut)," :file "ucontroller.sv" :line 92)))
                                     "DMA_Req"
                                     (:items nil :locs
                                      ((:type nil :desc ".DMA_Req      (Bus_req)," :file "ucontroller.sv" :line 97)))
                                     "DMA_Ack"
                                     (:items nil :locs
                                      ((:type nil :desc ".DMA_Ack      (Bus_grant)," :file "ucontroller.sv" :line 98)))
                                     "DMA_Ready"
                                     (:items nil :locs
                                      ((:type nil :desc ".DMA_Ready    (Dma_Tx_Ready)," :file "ucontroller.sv" :line 99)))
                                     "DMA_Tx_Start"
                                     (:items nil :locs
                                      ((:type nil :desc ".DMA_Tx_Start (Dma_Tx_Start)," :file "ucontroller.sv" :line 100)))
                                     "alu"
                                     (:items nil :locs
                                      ((:type nil :desc "alu I_ALU (" :file "ucontroller.sv" :line 112)))
                                     "I_ALU"
                                     (:items nil :locs
                                      ((:type nil :desc "alu I_ALU (" :file "ucontroller.sv" :line 112)))
                                     "InData"
                                     (:items nil :locs
                                      ((:type nil :desc ".InData  (ALU_DataIn)," :file "ucontroller.sv" :line 115)))
                                     "OutData"
                                     (:items nil :locs
                                      ((:type nil :desc ".OutData (ALU_DataOut)," :file "ucontroller.sv" :line 116)))
                                     "dma"
                                     (:items nil :locs
                                      ((:type nil :desc "dma I_DMA (" :file "ucontroller.sv" :line 125)))
                                     "I_DMA"
                                     (:items nil :locs
                                      ((:type nil :desc "dma I_DMA (" :file "ucontroller.sv" :line 125)))
                                     "Address"
                                     (:items nil :locs
                                      ((:type nil :desc ".Address (RAM_Address)," :file "ucontroller.sv" :line 203)
                                       (:type nil :desc ".Address (DMA_Address)," :file "ucontroller.sv" :line 143)))
                                     "Cs"
                                     (:items nil :locs
                                      ((:type nil :desc ".Cs      (RAM_Cs)," :file "ucontroller.sv" :line 200)
                                       (:type nil :desc ".Cs      (DMA_Cs)," :file "ucontroller.sv" :line 146)))
                                     "Wen"
                                     (:items nil :locs
                                      ((:type nil :desc ".Wen     (RAM_Wen)," :file "ucontroller.sv" :line 201)
                                       (:type nil :desc ".Wen     (DMA_Wen)," :file "ucontroller.sv" :line 147)))
                                     "Oen"
                                     (:items nil :locs
                                      ((:type nil :desc ".Oen     (RAM_Oen)," :file "ucontroller.sv" :line 202)
                                       (:type nil :desc ".Oen     (DMA_Oen)" :file "ucontroller.sv" :line 148)))
                                     "uart"
                                     (:items nil :locs
                                      ((:type nil :desc "uart # (" :file "ucontroller.sv" :line 152)))
                                     "I_UART"
                                     (:items nil :locs
                                      ((:type nil :desc ") I_UART (" :file "ucontroller.sv" :line 155)))
                                     "TX_DataIn"
                                     (:items nil :locs
                                      ((:type nil :desc ".TX_DataIn (TX_Data)," :file "ucontroller.sv" :line 160)))
                                     "Data_Out"
                                     (:items nil :locs
                                      ((:type nil :desc ".Data_Out  (RX_Data)," :file "ucontroller.sv" :line 165)))
                                     "Full"
                                     (:items nil :locs
                                      ((:type nil :desc ".Full      (RX_Full)," :file "ucontroller.sv" :line 167)))
                                     "Empty"
                                     (:items nil :locs
                                      ((:type nil :desc ".Empty     (RX_Empty)" :file "ucontroller.sv" :line 168)))
                                     "ram_arbiter"
                                     (:items nil :locs
                                      ((:type nil :desc "ram_arbiter I_RAM_ARBITER (" :file "ucontroller.sv" :line 172)))
                                     "I_RAM_ARBITER"
                                     (:items nil :locs
                                      ((:type nil :desc "ram_arbiter I_RAM_ARBITER (" :file "ucontroller.sv" :line 172)))
                                     "DMA_Bus_req"
                                     (:items nil :locs
                                      ((:type nil :desc ".DMA_Bus_req   (Bus_req)," :file "ucontroller.sv" :line 175)))
                                     "DMA_Bus_grant"
                                     (:items nil :locs
                                      ((:type nil :desc ".DMA_Bus_grant (Bus_grant)," :file "ucontroller.sv" :line 176)))
                                     "DMA_Idle"
                                     (:items nil :locs
                                      ((:type nil :desc ".DMA_Idle      (Dma_Idle)," :file "ucontroller.sv" :line 177)))
                                     "ram"
                                     (:items nil :locs
                                      ((:type nil :desc "ram I_RAM (" :file "ucontroller.sv" :line 197)))
                                     "I_RAM"
                                     (:items nil :locs
                                      ((:type nil :desc "ram I_RAM (" :file "ucontroller.sv" :line 197))))))
    ))


(ert-deftest tags::definitions ()
  (let ((alist verilog-ext-test-tags-defs-table-alist)
        file tag-type defs)
    (dolist (elm alist)
      (setq file (caar elm))
      (setq tag-type (cadar elm))
      (setq defs (cadr elm))
      (should-not (hash-not-equal defs (verilog-ext-test-tags-defs-file file tag-type))))))

(ert-deftest tags::references ()
  (let ((alist verilog-ext-test-tags-refs-table-alist)
        file refs)
    (dolist (elm alist)
      (setq file (car elm))
      (setq refs (cadr elm))
      (should-not (hash-not-equal refs (verilog-ext-test-tags-refs-file file))))))


(provide 'verilog-ext-tests-tags)

;;; verilog-ext-tests-tags.el ends here
