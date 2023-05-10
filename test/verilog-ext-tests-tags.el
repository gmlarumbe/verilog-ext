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
                                                ("i" "I_TEST_IF" "I_BLOCK0" "I_BLOCK1" "I_BLOCK2" "I_BLOCK3" "I_BLOCK_GEN" "ITEST_IF_PARAMS" "ITEST_IF_PARAMS_ARRAY" "I_TEST_IF_PARAMS_EMPTY" "I_BLOCK_WS_0" "I_BLOCK_WS_1")
                                                ;; End of DANGER
                                                :locs
                                                ((:type "module" :desc
                                                  #("module instances;" 7 16
                                                    (face
                                                     (:foreground "goldenrod" :weight bold)))
                                                  :file "instances.sv" :line 20)))
                                               "i"
                                               (:items nil :locs
                                                ((:type "genvar" :desc
                                                  #("for (genvar i=0; i<VALUE; i++) begin : gen_test" 12 13
                                                    (face
                                                     (:foreground "goldenrod" :weight bold))
                                                    17 18
                                                    (face
                                                     (:foreground "goldenrod" :weight bold))
                                                    26 27
                                                    (face
                                                     (:foreground "goldenrod" :weight bold)))
                                                  :file "instances.sv" :line 60)))
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
                                               "I_TEST_IF"
                                               (:items nil :locs
                                                ((:type "test_if" :desc
                                                  #("test_if I_TEST_IF (.clk(clk), .rst_n(rst_n));" 8 17
                                                    (face
                                                     (:foreground "goldenrod" :weight bold)))
                                                  :file "instances.sv" :line 77)))
                                               "ITEST_IF_PARAMS"
                                               (:items nil :locs
                                                ((:type "test_if_params" :desc
                                                  #("test_if_params # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS (.clk(clk), .rst_n(rst_n));" 52 67
                                                    (face
                                                     (:foreground "goldenrod" :weight bold)))
                                                  :file "instances.sv" :line 79)))
                                               "ITEST_IF_PARAMS_ARRAY"
                                               (:items nil :locs
                                                ((:type "test_if_params_array" :desc
                                                  #("test_if_params_array # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS_ARRAY[5:0] (.clk(clk), .rst_n(rst_n));" 58 79
                                                    (face
                                                     (:foreground "goldenrod" :weight bold)))
                                                  :file "instances.sv" :line 81)))
                                               "I_TEST_IF_PARAMS_EMPTY"
                                               (:items nil :locs
                                                ((:type "test_if_params_empty" :desc
                                                  #("test_if_params_empty #() I_TEST_IF_PARAMS_EMPTY (.clk(clk), .rst_n(rst_n));" 25 47
                                                    (face
                                                     (:foreground "goldenrod" :weight bold)))
                                                  :file "instances.sv" :line 83)))
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
                                                 ((:type "module" :desc
                                                   #("module automatic tb_program (" 17 27
                                                     (face
                                                      (:foreground "goldenrod" :weight bold)))
                                                   :file "tb_program.sv" :line 23)))
                                                "Clk"
                                                (:items nil :locs
                                                 ((:type "input logic" :desc
                                                   #("input logic         Clk," 20 23
                                                     (face
                                                      (:foreground "goldenrod" :weight bold)))
                                                   :file "tb_program.sv" :line 24)))
                                                "Rst_n"
                                                (:items nil :locs
                                                 ((:type "output logic" :desc
                                                   #("output logic        Rst_n," 20 25
                                                     (face
                                                      (:foreground "goldenrod" :weight bold)))
                                                   :file "tb_program.sv" :line 25)))
                                                "RXD"
                                                (:items nil :locs
                                                 ((:type "output logic" :desc
                                                   #("output logic        RXD," 20 23
                                                     (face
                                                      (:foreground "goldenrod" :weight bold)))
                                                   :file "tb_program.sv" :line 26)))
                                                "TXD"
                                                (:items nil :locs
                                                 ((:type "input logic" :desc
                                                   #("input logic         TXD," 20 23
                                                     (face
                                                      (:foreground "goldenrod" :weight bold)))
                                                   :file "tb_program.sv" :line 27)))
                                                "Temp"
                                                (:items nil :locs
                                                 ((:type "input logic [7:0]" :desc
                                                   #("input logic [7:0]   Temp," 20 24
                                                     (face
                                                      (:foreground "goldenrod" :weight bold)))
                                                   :file "tb_program.sv" :line 28)))
                                                "Switches"
                                                (:items nil :locs
                                                 ((:type "input logic [7:0]" :desc
                                                   #("input logic [7:0]   Switches," 20 28
                                                     (face
                                                      (:foreground "goldenrod" :weight bold)))
                                                   :file "tb_program.sv" :line 29)))
                                                "ROM_Data"
                                                (:items nil :locs
                                                 ((:type "output logic [11:0]" :desc
                                                   #("output logic [11:0] ROM_Data," 20 28
                                                     (face
                                                      (:foreground "goldenrod" :weight bold)))
                                                   :file "tb_program.sv" :line 30)))
                                                "ROM_Addr"
                                                (:items nil :locs
                                                 ((:type "input logic [11:0]" :desc
                                                   #("input logic [11:0]  ROM_Addr" 20 28
                                                     (face
                                                      (:foreground "goldenrod" :weight bold)))
                                                   :file "tb_program.sv" :line 31)))
                                                "FREQ_CLK"
                                                (:items nil :locs
                                                 ((:type "localparam logic [31:0]" :desc
                                                   #("localparam logic [31:0] FREQ_CLK = 100000000;" 24 32
                                                     (face
                                                      (:foreground "goldenrod" :weight bold)))
                                                   :file "tb_program.sv" :line 37)))
                                                "TX_SPEED"
                                                (:items nil :locs
                                                 ((:type "localparam logic [31:0]" :desc
                                                   #("localparam logic [31:0] TX_SPEED = 115200;" 24 32
                                                     (face
                                                      (:foreground "goldenrod" :weight bold)))
                                                   :file "tb_program.sv" :line 38)))
                                                "BIT_CYCLES"
                                                (:items nil :locs
                                                 ((:type "localparam integer" :desc
                                                   #("localparam integer BIT_CYCLES = FREQ_CLK / TX_SPEED;" 19 29
                                                     (face
                                                      (:foreground "goldenrod" :weight bold)))
                                                   :file "tb_program.sv" :line 39)))
                                                "ROM"
                                                (:items nil :locs
                                                 ((:type "logic [11:0]" :desc
                                                   #("logic [11:0] ROM [4096];" 13 16
                                                     (face
                                                      (:foreground "goldenrod" :weight bold)))
                                                   :file "tb_program.sv" :line 55)))
                                                "Data"
                                                (:items nil :locs
                                                 ((:type "input logic [7:0]" :desc
                                                   #("task serial_rx (input logic [7:0] Data);" 34 38
                                                     (face
                                                      (:foreground "goldenrod" :weight bold)))
                                                   :file "tb_program.sv" :line 115)))
                                                "i"
                                                (:items nil :locs
                                                 ((:type "int" :desc
                                                   #("for (int i=0; i<8; ++i) begin" 9 10
                                                     (face
                                                      (:foreground "goldenrod" :weight bold))
                                                     14 15
                                                     (face
                                                      (:foreground "goldenrod" :weight bold))
                                                     21 22
                                                     (face
                                                      (:foreground "goldenrod" :weight bold)))
                                                   :file "tb_program.sv" :line 121)))
                                                "init_rom"
                                                (:items nil :locs
                                                 ((:type "task" :desc
                                                   #("task init_rom ();" 5 13
                                                     (face
                                                      (:foreground "goldenrod" :weight bold)))
                                                   :file "tb_program.sv" :line 58)))
                                                "init_values"
                                                (:items nil :locs
                                                 ((:type "task" :desc
                                                   #("task init_values;" 5 16
                                                     (face
                                                      (:foreground "goldenrod" :weight bold)))
                                                   :file "tb_program.sv" :line 99)))
                                                "reset_system"
                                                (:items nil :locs
                                                 ((:type "task" :desc
                                                   #("task reset_system;" 5 17
                                                     (face
                                                      (:foreground "goldenrod" :weight bold)))
                                                   :file "tb_program.sv" :line 104)))
                                                "serial_rx"
                                                (:items nil :locs
                                                 ((:type "task" :desc
                                                   #("task serial_rx (input logic [7:0] Data);" 5 14
                                                     (face
                                                      (:foreground "goldenrod" :weight bold)))
                                                   :file "tb_program.sv" :line 115))))))

    (("uvm_component.svh" classes) #s(hash-table size 145 test equal rehash-size 1.5 rehash-threshold 0.8125 data
                                                 ("uvm_component"
                                                  (:items
                                                   ("get_parent" "get_full_name" "get_child" "get_next_child" "get_first_child" "get_num_children" "has_child" "lookup" "get_depth" "massage_scope" "use_automatic_config" "print_config_matches" "get_print_config_matches" "create_component" "create_object" "begin_tr" "record_error_tr" "record_event_tr" "print_enabled" "m_phase_imps" "m_current_phase" "m_build_done" "m_phasing_active" "m_parent" "m_children" "m_children_by_handle" "m_add_child" "create" "clone" "m_tr_h" "m_begin_tr" "m_name" "recording_detail" "get_recording_enabled" "new" "get_children" "set_name" "build_phase" "connect_phase" "end_of_elaboration_phase" "start_of_simulation_phase" "run_phase" "pre_reset_phase" "reset_phase" "post_reset_phase" "pre_configure_phase" "configure_phase" "post_configure_phase" "pre_main_phase" "main_phase" "post_main_phase" "pre_shutdown_phase" "shutdown_phase" "post_shutdown_phase" "extract_phase" "check_phase" "report_phase" "final_phase" "phase_started" "phase_ready_to_end" "phase_ended" "set_domain" "get_domain" "define_domain" "suspend" "resume" "resolve_bindings" "apply_config_settings" "print_config" "print_config_with_audit" "set_print_config_matches" "raised" "dropped" "all_dropped" "set_type_override_by_type" "set_inst_override_by_type" "set_type_override" "set_inst_override" "print_override_info" "set_report_id_verbosity_hier" "set_report_severity_id_verbosity_hier" "set_report_severity_action_hier" "set_report_id_action_hier" "set_report_severity_id_action_hier" "set_report_default_file_hier" "set_report_severity_file_hier" "set_report_id_file_hier" "set_report_severity_id_file_hier" "set_report_verbosity_level_hier" "pre_abort" "accept_tr" "do_accept_tr" "do_begin_tr" "end_tr" "do_end_tr" "get_tr_stream" "free_tr_stream" "do_execute_op" "get_tr_database" "set_tr_database" "set_local" "m_set_full_name" "do_resolve_bindings" "do_flush" "flush" "m_extract_name" "set_recording_enabled" "set_recording_enabled_hier" "do_print" "m_set_cl_msg_args" "m_set_cl_verb" "m_set_cl_action" "m_set_cl_sev" "m_apply_verbosity_settings" "m_do_pre_abort" "m_unsupported_set_local")
                                                   :locs
                                                   ((:type "class" :desc
                                                     #("virtual class uvm_component extends uvm_report_object;" 14 27
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 49)))
                                                  "get_parent"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function uvm_component get_parent ();" 38 48
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 83)
                                                    (:type "uvm_component" :desc
                                                     #("extern virtual function uvm_component get_parent ();" 38 48
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 83)))
                                                  "get_full_name"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function string get_full_name ();" 31 44
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 93)
                                                    (:type "string" :desc
                                                     #("extern virtual function string get_full_name ();" 31 44
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 93)))
                                                  "get_child"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function uvm_component get_child (string name);" 30 39
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 112)
                                                    (:type "uvm_component" :desc
                                                     #("extern function uvm_component get_child (string name);" 30 39
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 112)))
                                                  "get_next_child"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function int get_next_child (ref string name);" 20 34
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 116)
                                                    (:type "int" :desc
                                                     #("extern function int get_next_child (ref string name);" 20 34
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 116)))
                                                  "get_first_child"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function int get_first_child (ref string name);" 20 35
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 133)
                                                    (:type "int" :desc
                                                     #("extern function int get_first_child (ref string name);" 20 35
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 133)))
                                                  "get_num_children"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function int get_num_children ();" 20 36
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 141)
                                                    (:type "int" :desc
                                                     #("extern function int get_num_children ();" 20 36
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 141)))
                                                  "has_child"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function int has_child (string name);" 20 29
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 149)
                                                    (:type "int" :desc
                                                     #("extern function int has_child (string name);" 20 29
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 149)))
                                                  "lookup"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function uvm_component lookup (string name);" 30 36
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 169)
                                                    (:type "uvm_component" :desc
                                                     #("extern function uvm_component lookup (string name);" 30 36
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 169)))
                                                  "get_depth"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function int unsigned get_depth();" 29 38
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 178)
                                                    (:type "int unsigned" :desc
                                                     #("extern function int unsigned get_depth();" 29 38
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 178)))
                                                  "massage_scope"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function string massage_scope(string scope);" 23 36
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 688)
                                                    (:type "string" :desc
                                                     #("extern function string massage_scope(string scope);" 23 36
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 688)))
                                                  "use_automatic_config"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function bit use_automatic_config();" 28 48
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 740)
                                                    (:type "bit" :desc
                                                     #("extern virtual function bit use_automatic_config();" 28 48
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 740)))
                                                  "print_config_matches"
                                                  (:items nil :locs
                                                   ((:type "bit" :desc
                                                     #("static `ifndef UVM_ENABLE_DEPRECATED_API local `endif bit print_config_matches;" 58 78
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 770)))
                                                  "get_print_config_matches"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("static function bit get_print_config_matches() ;" 20 44
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 782)
                                                    (:type "bit" :desc
                                                     #("static function bit get_print_config_matches() ;" 20 44
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 782)))
                                                  "create_component"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function uvm_component create_component (string requested_type_name," 30 46
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 881)
                                                    (:type "uvm_component" :desc
                                                     #("extern function uvm_component create_component (string requested_type_name," 30 46
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 881)))
                                                  "create_object"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function uvm_object create_object (string requested_type_name," 27 40
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 900)
                                                    (:type "uvm_object" :desc
                                                     #("extern function uvm_object create_object (string requested_type_name," 27 40
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 900)))
                                                  "begin_tr"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function int begin_tr (uvm_transaction tr," 20 28
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1220)
                                                    (:type "int" :desc
                                                     #("extern function int begin_tr (uvm_transaction tr," 20 28
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1220)))
                                                  "record_error_tr"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function int record_error_tr (string stream_name=\"main\"," 20 35
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1296)
                                                    (:type "int" :desc
                                                     #("extern function int record_error_tr (string stream_name=\"main\"," 20 35
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1296)))
                                                  "record_event_tr"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function int record_event_tr (string stream_name=\"main\"," 20 35
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1317)
                                                    (:type "int" :desc
                                                     #("extern function int record_event_tr (string stream_name=\"main\"," 20 35
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1317)))
                                                  "print_enabled"
                                                  (:items nil :locs
                                                   ((:type "bit" :desc
                                                     #("bit print_enabled = 1;" 4 17
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1341)))
                                                  "m_phase_imps"
                                                  (:items nil :locs
                                                   ((:type "uvm_phase" :desc
                                                     #("/*protected*/ uvm_phase  m_phase_imps[uvm_phase];    // functors to override ovm_root defaults" 25 37
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1377)))
                                                  "m_current_phase"
                                                  (:items nil :locs
                                                   ((:type "uvm_phase" :desc
                                                     #("uvm_phase            m_current_phase;            // the most recently executed phase" 21 36
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1380)))
                                                  "m_build_done"
                                                  (:items nil :locs
                                                   ((:type "bit" :desc
                                                     #("/*protected*/ bit  m_build_done;" 19 31
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1383)))
                                                  "m_phasing_active"
                                                  (:items nil :locs
                                                   ((:type "int" :desc
                                                     #("/*protected*/ int  m_phasing_active;" 19 35
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1384)))
                                                  "m_parent"
                                                  (:items nil :locs
                                                   ((:type "uvm_component" :desc
                                                     #("/*protected*/ uvm_component m_parent;" 28 36
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1388)))
                                                  "m_children"
                                                  (:items nil :locs
                                                   ((:type "protected     uvm_component" :desc
                                                     #("protected     uvm_component m_children[string];" 28 38
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1389)))
                                                  "m_children_by_handle"
                                                  (:items nil :locs
                                                   ((:type "protected     uvm_component" :desc
                                                     #("protected     uvm_component m_children_by_handle[uvm_component];" 28 48
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1390)))
                                                  "m_add_child"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern protected virtual function bit  m_add_child(uvm_component child);" 39 50
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1391)
                                                    (:type "bit" :desc
                                                     #("extern protected virtual function bit  m_add_child(uvm_component child);" 39 50
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1391)))
                                                  "create"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function uvm_object create (string name=\"\");" 35 41
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1404)
                                                    (:type "uvm_object" :desc
                                                     #("extern virtual function uvm_object create (string name=\"\");" 35 41
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1404)))
                                                  "clone"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function uvm_object clone  ();" 35 40
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1405)
                                                    (:type "uvm_object" :desc
                                                     #("extern virtual function uvm_object clone  ();" 35 40
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1405)))
                                                  "m_tr_h"
                                                  (:items nil :locs
                                                   ((:type "local uvm_recorder" :desc
                                                     #("local uvm_recorder m_tr_h[uvm_transaction];" 19 25
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1408)))
                                                  "m_begin_tr"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern protected function int m_begin_tr (uvm_transaction tr," 30 40
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1409)
                                                    (:type "int" :desc
                                                     #("extern protected function int m_begin_tr (uvm_transaction tr," 30 40
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1409)))
                                                  "m_name"
                                                  (:items nil :locs
                                                   ((:type "string" :desc
                                                     #("string m_name;" 7 13
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1414)))
                                                  "recording_detail"
                                                  (:items nil :locs
                                                   ((:type "int unsigned" :desc
                                                     #("int unsigned recording_detail = UVM_NONE;" 13 29
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1421)))
                                                  "get_recording_enabled"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function bit get_recording_enabled();" 28 49
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1424)
                                                    (:type "bit" :desc
                                                     #("extern virtual function bit get_recording_enabled();" 28 49
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1424)))
                                                  "new"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function new (string name, uvm_component parent);" 16 19
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 66)))
                                                  "get_children"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void get_children(ref uvm_component children[$]);" 21 33
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 107)))
                                                  "set_name"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function void set_name (string name);" 29 37
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 157)))
                                                  "build_phase"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function void build_phase(uvm_phase phase);" 29 40
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 211)))
                                                  "connect_phase"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function void connect_phase(uvm_phase phase);" 29 42
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 220)))
                                                  "end_of_elaboration_phase"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function void end_of_elaboration_phase(uvm_phase phase);" 29 53
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 229)))
                                                  "start_of_simulation_phase"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function void start_of_simulation_phase(uvm_phase phase);" 29 54
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 238)))
                                                  "run_phase"
                                                  (:items nil :locs
                                                   ((:type "task" :desc
                                                     #("extern virtual task run_phase(uvm_phase phase);" 20 29
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 256)))
                                                  "pre_reset_phase"
                                                  (:items nil :locs
                                                   ((:type "task" :desc
                                                     #("extern virtual task pre_reset_phase(uvm_phase phase);" 20 35
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 277)))
                                                  "reset_phase"
                                                  (:items nil :locs
                                                   ((:type "task" :desc
                                                     #("extern virtual task reset_phase(uvm_phase phase);" 20 31
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 298)))
                                                  "post_reset_phase"
                                                  (:items nil :locs
                                                   ((:type "task" :desc
                                                     #("extern virtual task post_reset_phase(uvm_phase phase);" 20 36
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 319)))
                                                  "pre_configure_phase"
                                                  (:items nil :locs
                                                   ((:type "task" :desc
                                                     #("extern virtual task pre_configure_phase(uvm_phase phase);" 20 39
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 340)))
                                                  "configure_phase"
                                                  (:items nil :locs
                                                   ((:type "task" :desc
                                                     #("extern virtual task configure_phase(uvm_phase phase);" 20 35
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 361)))
                                                  "post_configure_phase"
                                                  (:items nil :locs
                                                   ((:type "task" :desc
                                                     #("extern virtual task post_configure_phase(uvm_phase phase);" 20 40
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 382)))
                                                  "pre_main_phase"
                                                  (:items nil :locs
                                                   ((:type "task" :desc
                                                     #("extern virtual task pre_main_phase(uvm_phase phase);" 20 34
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 403)))
                                                  "main_phase"
                                                  (:items nil :locs
                                                   ((:type "task" :desc
                                                     #("extern virtual task main_phase(uvm_phase phase);" 20 30
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 424)))
                                                  "post_main_phase"
                                                  (:items nil :locs
                                                   ((:type "task" :desc
                                                     #("extern virtual task post_main_phase(uvm_phase phase);" 20 35
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 445)))
                                                  "pre_shutdown_phase"
                                                  (:items nil :locs
                                                   ((:type "task" :desc
                                                     #("extern virtual task pre_shutdown_phase(uvm_phase phase);" 20 38
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 466)))
                                                  "shutdown_phase"
                                                  (:items nil :locs
                                                   ((:type "task" :desc
                                                     #("extern virtual task shutdown_phase(uvm_phase phase);" 20 34
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 487)))
                                                  "post_shutdown_phase"
                                                  (:items nil :locs
                                                   ((:type "task" :desc
                                                     #("extern virtual task post_shutdown_phase(uvm_phase phase);" 20 39
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 508)))
                                                  "extract_phase"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function void extract_phase(uvm_phase phase);" 29 42
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 517)))
                                                  "check_phase"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function void check_phase(uvm_phase phase);" 29 40
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 528)))
                                                  "report_phase"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function void report_phase(uvm_phase phase);" 29 41
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 537)))
                                                  "final_phase"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function void final_phase(uvm_phase phase);" 29 40
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 546)))
                                                  "phase_started"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function void phase_started (uvm_phase phase);" 29 42
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 555)))
                                                  "phase_ready_to_end"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function void phase_ready_to_end (uvm_phase phase);" 29 47
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 580)))
                                                  "phase_ended"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function void phase_ended (uvm_phase phase);" 29 40
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 590)))
                                                  "set_domain"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void set_domain(uvm_domain domain, int hier=1);" 21 31
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 608)))
                                                  "get_domain"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function uvm_domain get_domain();" 27 37
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 616)))
                                                  "define_domain"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual protected function void define_domain(uvm_domain domain);" 39 52
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 650)))
                                                  "suspend"
                                                  (:items nil :locs
                                                   ((:type "task" :desc
                                                     #("extern virtual task suspend ();" 20 27
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 661)))
                                                  "resume"
                                                  (:items nil :locs
                                                   ((:type "task" :desc
                                                     #("extern virtual task resume ();" 20 26
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 674)))
                                                  "resolve_bindings"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function void resolve_bindings ();" 29 45
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 686)))
                                                  "apply_config_settings"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function void apply_config_settings (bit verbose = 0);" 29 50
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 732)))
                                                  "print_config"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void print_config(bit recurse = 0, bit audit = 0);" 21 33
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 757)))
                                                  "print_config_with_audit"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void print_config_with_audit(bit recurse = 0);" 21 44
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 768)))
                                                  "set_print_config_matches"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("static function void set_print_config_matches(bit val) ;" 21 45
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 794)))
                                                  "raised"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("virtual function void raised (uvm_objection objection, uvm_object source_obj," 22 28
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 818)))
                                                  "dropped"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("virtual function void dropped (uvm_objection objection, uvm_object source_obj," 22 29
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 833)))
                                                  "all_dropped"
                                                  (:items nil :locs
                                                   ((:type "task" :desc
                                                     #("virtual task all_dropped (uvm_objection objection, uvm_object source_obj," 13 24
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 848)))
                                                  "set_type_override_by_type"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern static function void set_type_override_by_type" 28 53
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 923)))
                                                  "set_inst_override_by_type"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void set_inst_override_by_type(string relative_inst_path," 21 46
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 980)))
                                                  "set_type_override"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern static function void set_type_override(string original_type_name," 28 45
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1001)))
                                                  "set_inst_override"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void set_inst_override(string relative_inst_path," 21 38
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1025)))
                                                  "print_override_info"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void print_override_info(string requested_type_name," 21 40
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1037)))
                                                  "set_report_id_verbosity_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void set_report_id_verbosity_hier (string id," 21 49
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1055)))
                                                  "set_report_severity_id_verbosity_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void set_report_severity_id_verbosity_hier(uvm_severity severity," 21 58
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1069)))
                                                  "set_report_severity_action_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void set_report_severity_action_hier (uvm_severity severity," 21 52
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1076)))
                                                  "set_report_id_action_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void set_report_id_action_hier (string id," 21 46
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1082)))
                                                  "set_report_severity_id_action_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void set_report_severity_id_action_hier(uvm_severity severity," 21 55
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1096)))
                                                  "set_report_default_file_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void set_report_default_file_hier (UVM_FILE file);" 21 49
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1104)))
                                                  "set_report_severity_file_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void set_report_severity_file_hier (uvm_severity severity," 21 50
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1108)))
                                                  "set_report_id_file_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void set_report_id_file_hier (string id," 21 44
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1113)))
                                                  "set_report_severity_id_file_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void set_report_severity_id_file_hier(uvm_severity severity," 21 53
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1127)))
                                                  "set_report_verbosity_level_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void set_report_verbosity_level_hier (int verbosity);" 21 52
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1141)))
                                                  "pre_abort"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("virtual function void pre_abort;" 22 31
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1162)))
                                                  "accept_tr"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void accept_tr (uvm_transaction tr, time accept_time = 0);" 21 30
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1191)))
                                                  "do_accept_tr"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual protected function void do_accept_tr (uvm_transaction tr);" 39 51
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1201)))
                                                  "do_begin_tr"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("function void do_begin_tr (uvm_transaction tr," 14 25
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1235)))
                                                  "end_tr"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void end_tr (uvm_transaction tr," 21 27
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1265)))
                                                  "do_end_tr"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual protected function void do_end_tr (uvm_transaction tr," 39 48
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1277)))
                                                  "get_tr_stream"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function uvm_tr_stream get_tr_stream(string name," 38 51
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1326)))
                                                  "free_tr_stream"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function void free_tr_stream(uvm_tr_stream stream);" 29 43
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1331)))
                                                  "do_execute_op"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function void do_execute_op( uvm_field_op op );" 29 42
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1344)))
                                                  "get_tr_database"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function uvm_tr_database get_tr_database();" 40 55
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1354)))
                                                  "set_tr_database"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function void set_tr_database(uvm_tr_database db);" 29 44
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1357)))
                                                  "set_local"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern                   function void set_local(uvm_resource_base rsrc) ;" 39 48
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1386)))
                                                  "m_set_full_name"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern local     virtual function void m_set_full_name();" 39 54
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1392)))
                                                  "do_resolve_bindings"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern                   function void do_resolve_bindings();" 39 58
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1394)))
                                                  "do_flush"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern                   function void do_flush();" 39 47
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1395)))
                                                  "flush"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual           function void flush ();" 39 44
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1397)))
                                                  "m_extract_name"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern local             function void m_extract_name(string name ," 39 53
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1399)))
                                                  "set_recording_enabled"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function void set_recording_enabled(bit enabled);" 29 50
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1437)))
                                                  "set_recording_enabled_hier"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern virtual function void set_recording_enabled_hier (bit enabled);" 29 55
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1440)))
                                                  "do_print"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern         function void   do_print(uvm_printer printer);" 31 39
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1442)))
                                                  "m_set_cl_msg_args"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void m_set_cl_msg_args;" 21 38
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1445)))
                                                  "m_set_cl_verb"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void m_set_cl_verb;" 21 34
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1446)))
                                                  "m_set_cl_action"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void m_set_cl_action;" 21 36
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1447)))
                                                  "m_set_cl_sev"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void m_set_cl_sev;" 21 33
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1448)))
                                                  "m_apply_verbosity_settings"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void m_apply_verbosity_settings(uvm_phase phase);" 21 47
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1449)))
                                                  "m_do_pre_abort"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern /*local*/ function void m_do_pre_abort;" 31 45
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1455)))
                                                  "m_unsupported_set_local"
                                                  (:items nil :locs
                                                   ((:type "function" :desc
                                                     #("extern function void m_unsupported_set_local(uvm_resource_base rsrc);" 21 44
                                                       (face
                                                        (:foreground "goldenrod" :weight bold)))
                                                     :file "uvm_component.svh" :line 1459))))))
    ))

(defvar verilog-ext-test-tags-refs-table-alist
  '(("instances.sv" #s(hash-table size 65 test equal rehash-size 1.5 rehash-threshold 0.8125 data
                                  ("instances"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("module instances;" 7 16
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 20)))
                                   "block0"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("block0 I_BLOCK0 (" 0 6
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 23)))
                                   "I_BLOCK0"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("block0 I_BLOCK0 (" 7 15
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 23)))
                                   "Port0"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #(".Port0 (Port0)," 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 102)
                                     (:type nil :desc
                                      #(".Port0 (Port0)," 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 89)
                                     (:type nil :desc
                                      #(".Port0 (Port0)," 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 67)
                                     (:type nil :desc
                                      #(".Port0 (Port0)," 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 53)
                                     (:type nil :desc
                                      #(".Port0 (Port0)," 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 42)
                                     (:type nil :desc
                                      #(".Port0 (Port0)," 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 31)
                                     (:type nil :desc
                                      #(".Port0 (Port0)," 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 24)))
                                   "Port1"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #(".Port1 (Port1)," 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 103)
                                     (:type nil :desc
                                      #(".Port1 (Port1)," 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 90)
                                     (:type nil :desc
                                      #(".Port1 (Port1)," 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 68)
                                     (:type nil :desc
                                      #(".Port1 (Port1)," 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 54)
                                     (:type nil :desc
                                      #(".Port1 (Port1)," 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 43)
                                     (:type nil :desc
                                      #(".Port1 (Port1)," 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 32)
                                     (:type nil :desc
                                      #(".Port1 (Port1)," 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 25)))
                                   "Port2"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #(".Port2 (Port2)" 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 104)
                                     (:type nil :desc
                                      #(".Port2 (Port2)" 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 91)
                                     (:type nil :desc
                                      #(".Port2 (Port2)" 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 69)
                                     (:type nil :desc
                                      #(".Port2 (Port2)" 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 55)
                                     (:type nil :desc
                                      #(".Port2 (Port2)" 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 44)
                                     (:type nil :desc
                                      #(".Port2 (Port2)" 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 33)
                                     (:type nil :desc
                                      #(".Port2 (Port2)" 1 6
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        8 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 26)))
                                   "block1"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("block1 I_BLOCK1(" 0 6
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 30)))
                                   "I_BLOCK1"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("block1 I_BLOCK1(" 7 15
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 30)))
                                   "block2"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("block2 #(" 0 6
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 37)))
                                   "Param0"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #(".Param0 (Param0)," 1 7
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        9 15
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 96)
                                     (:type nil :desc
                                      #(".Param0 (Param0)," 1 7
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        9 15
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 63)
                                     (:type nil :desc
                                      #(".Param0 (Param0)," 1 7
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        9 15
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 49)
                                     (:type nil :desc
                                      #(".Param0 (Param0)," 1 7
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        9 15
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 38)))
                                   "Param1"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #(".Param1 (Param1)," 1 7
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        9 15
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 97)
                                     (:type nil :desc
                                      #(".Param1 (Param1)," 1 7
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        9 15
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 64)
                                     (:type nil :desc
                                      #(".Param1 (Param1)," 1 7
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        9 15
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 50)
                                     (:type nil :desc
                                      #(".Param1 (Param1)," 1 7
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        9 15
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 39)))
                                   "Param2"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #(".Param2 (Param2)" 1 7
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        9 15
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 98)
                                     (:type nil :desc
                                      #(".Param2 (Param2)" 1 7
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        9 15
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 65)
                                     (:type nil :desc
                                      #(".Param2 (Param2)" 1 7
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        9 15
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 51)
                                     (:type nil :desc
                                      #(".Param2 (Param2)" 1 7
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        9 15
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 40)))
                                   "I_BLOCK2"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #(") I_BLOCK2 (" 2 10
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 41)))
                                   "block3"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("block3#(" 0 6
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 48)))
                                   "I_BLOCK3"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #(")I_BLOCK3(" 1 9
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 52)))
                                   "i"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("for (genvar i=0; i<VALUE; i++) begin : gen_test" 12 13
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        17 18
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        26 27
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 60)))
                                   "VALUE"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("for (genvar i=0; i<VALUE; i++) begin : gen_test" 19 24
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 60)))
                                   "gen_test"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("end : gen_test" 6 14
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 72)
                                     (:type nil :desc
                                      #("for (genvar i=0; i<VALUE; i++) begin : gen_test" 39 47
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 60)))
                                   "block_gen"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("block_gen #(" 0 9
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 62)))
                                   "I_BLOCK_GEN"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #(") I_BLOCK_GEN (" 2 13
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 66)))
                                   "test_if"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("test_if I_TEST_IF (.clk(clk), .rst_n(rst_n));" 0 7
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 77)))
                                   "I_TEST_IF"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("test_if I_TEST_IF (.clk(clk), .rst_n(rst_n));" 8 17
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 77)))
                                   "clk"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("test_if_params_empty #() I_TEST_IF_PARAMS_EMPTY (.clk(clk), .rst_n(rst_n));" 50 53
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        54 57
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 83)
                                     (:type nil :desc
                                      #("test_if_params_array # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS_ARRAY[5:0] (.clk(clk), .rst_n(rst_n));" 87 90
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        91 94
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 81)
                                     (:type nil :desc
                                      #("test_if_params # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS (.clk(clk), .rst_n(rst_n));" 70 73
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        74 77
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 79)
                                     (:type nil :desc
                                      #("test_if I_TEST_IF (.clk(clk), .rst_n(rst_n));" 20 23
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        24 27
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 77)))
                                   "rst_n"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("test_if_params_empty #() I_TEST_IF_PARAMS_EMPTY (.clk(clk), .rst_n(rst_n));" 61 66
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        67 72
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 83)
                                     (:type nil :desc
                                      #("test_if_params_array # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS_ARRAY[5:0] (.clk(clk), .rst_n(rst_n));" 98 103
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        104 109
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 81)
                                     (:type nil :desc
                                      #("test_if_params # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS (.clk(clk), .rst_n(rst_n));" 81 86
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        87 92
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 79)
                                     (:type nil :desc
                                      #("test_if I_TEST_IF (.clk(clk), .rst_n(rst_n));" 31 36
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        37 42
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 77)))
                                   "test_if_params"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("test_if_params # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS (.clk(clk), .rst_n(rst_n));" 0 14
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 79)))
                                   "param1"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("test_if_params_array # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS_ARRAY[5:0] (.clk(clk), .rst_n(rst_n));" 25 31
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        32 38
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 81)
                                     (:type nil :desc
                                      #("test_if_params # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS (.clk(clk), .rst_n(rst_n));" 19 25
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        26 32
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 79)))
                                   "param2"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("test_if_params_array # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS_ARRAY[5:0] (.clk(clk), .rst_n(rst_n));" 42 48
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        49 55
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 81)
                                     (:type nil :desc
                                      #("test_if_params # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS (.clk(clk), .rst_n(rst_n));" 36 42
                                        (face
                                         (:foreground "goldenrod" :weight bold))
                                        43 49
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 79)))
                                   "ITEST_IF_PARAMS"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("test_if_params # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS (.clk(clk), .rst_n(rst_n));" 52 67
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 79)))
                                   "test_if_params_array"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("test_if_params_array # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS_ARRAY[5:0] (.clk(clk), .rst_n(rst_n));" 0 20
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 81)))
                                   "ITEST_IF_PARAMS_ARRAY"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("test_if_params_array # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS_ARRAY[5:0] (.clk(clk), .rst_n(rst_n));" 58 79
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 81)))
                                   "test_if_params_empty"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("test_if_params_empty #() I_TEST_IF_PARAMS_EMPTY (.clk(clk), .rst_n(rst_n));" 0 20
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 83)))
                                   "I_TEST_IF_PARAMS_EMPTY"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("test_if_params_empty #() I_TEST_IF_PARAMS_EMPTY (.clk(clk), .rst_n(rst_n));" 25 47
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 83)))
                                   "block_ws_0"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("block_ws_0" 0 10
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 87)))
                                   "I_BLOCK_WS_0"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("I_BLOCK_WS_0 (" 0 12
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 88)))
                                   "block_ws_1"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("block_ws_1 // Comment" 0 10
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 94)))
                                   "I_BLOCK_WS_1"
                                   (:items nil :locs
                                    ((:type nil :desc
                                      #("I_BLOCK_WS_1 // More comments here" 0 12
                                        (face
                                         (:foreground "goldenrod" :weight bold)))
                                      :file "instances.sv" :line 100))))))

    ("tb_program.sv" #s(hash-table size 65 test equal rehash-size 1.5 rehash-threshold 0.8125 data
                                   ("tb_program"
                                    (:items
                                     ("Clk" "Rst_n" "RXD" "TXD" "Temp" "Switches" "ROM_Data" "ROM_Addr" "FREQ_CLK" "TX_SPEED" "BIT_CYCLES" "ROM" "Data" "i" "init_rom" "init_values" "reset_system" "serial_rx")
                                     :locs
                                     ((:type "module" :desc
                                       #("module automatic tb_program (" 17 27
                                         (face
                                          (:foreground "goldenrod" :weight bold)))
                                       :file "tb_program.sv" :line 23)))
                                    "Clk"
                                    (:items nil :locs
                                     ((:type "input logic" :desc
                                       #("input logic         Clk," 20 23
                                         (face
                                          (:foreground "goldenrod" :weight bold)))
                                       :file "tb_program.sv" :line 24)))
                                    "Rst_n"
                                    (:items nil :locs
                                     ((:type "output logic" :desc
                                       #("output logic        Rst_n," 20 25
                                         (face
                                          (:foreground "goldenrod" :weight bold)))
                                       :file "tb_program.sv" :line 25)))
                                    "RXD"
                                    (:items nil :locs
                                     ((:type "output logic" :desc
                                       #("output logic        RXD," 20 23
                                         (face
                                          (:foreground "goldenrod" :weight bold)))
                                       :file "tb_program.sv" :line 26)))
                                    "TXD"
                                    (:items nil :locs
                                     ((:type "input logic" :desc
                                       #("input logic         TXD," 20 23
                                         (face
                                          (:foreground "goldenrod" :weight bold)))
                                       :file "tb_program.sv" :line 27)))
                                    "Temp"
                                    (:items nil :locs
                                     ((:type "input logic [7:0]" :desc
                                       #("input logic [7:0]   Temp," 20 24
                                         (face
                                          (:foreground "goldenrod" :weight bold)))
                                       :file "tb_program.sv" :line 28)))
                                    "Switches"
                                    (:items nil :locs
                                     ((:type "input logic [7:0]" :desc
                                       #("input logic [7:0]   Switches," 20 28
                                         (face
                                          (:foreground "goldenrod" :weight bold)))
                                       :file "tb_program.sv" :line 29)))
                                    "ROM_Data"
                                    (:items nil :locs
                                     ((:type "output logic [11:0]" :desc
                                       #("output logic [11:0] ROM_Data," 20 28
                                         (face
                                          (:foreground "goldenrod" :weight bold)))
                                       :file "tb_program.sv" :line 30)))
                                    "ROM_Addr"
                                    (:items nil :locs
                                     ((:type "input logic [11:0]" :desc
                                       #("input logic [11:0]  ROM_Addr" 20 28
                                         (face
                                          (:foreground "goldenrod" :weight bold)))
                                       :file "tb_program.sv" :line 31)))
                                    "FREQ_CLK"
                                    (:items nil :locs
                                     ((:type "localparam logic [31:0]" :desc
                                       #("localparam logic [31:0] FREQ_CLK = 100000000;" 24 32
                                         (face
                                          (:foreground "goldenrod" :weight bold)))
                                       :file "tb_program.sv" :line 37)))
                                    "TX_SPEED"
                                    (:items nil :locs
                                     ((:type "localparam logic [31:0]" :desc
                                       #("localparam logic [31:0] TX_SPEED = 115200;" 24 32
                                         (face
                                          (:foreground "goldenrod" :weight bold)))
                                       :file "tb_program.sv" :line 38)))
                                    "BIT_CYCLES"
                                    (:items nil :locs
                                     ((:type "localparam integer" :desc
                                       #("localparam integer BIT_CYCLES = FREQ_CLK / TX_SPEED;" 19 29
                                         (face
                                          (:foreground "goldenrod" :weight bold)))
                                       :file "tb_program.sv" :line 39)))
                                    "ROM"
                                    (:items nil :locs
                                     ((:type "logic [11:0]" :desc
                                       #("logic [11:0] ROM [4096];" 13 16
                                         (face
                                          (:foreground "goldenrod" :weight bold)))
                                       :file "tb_program.sv" :line 55)))
                                    "Data"
                                    (:items nil :locs
                                     ((:type "input logic [7:0]" :desc
                                       #("task serial_rx (input logic [7:0] Data);" 34 38
                                         (face
                                          (:foreground "goldenrod" :weight bold)))
                                       :file "tb_program.sv" :line 115)))
                                    "i"
                                    (:items nil :locs
                                     ((:type "int" :desc
                                       #("for (int i=0; i<8; ++i) begin" 9 10
                                         (face
                                          (:foreground "goldenrod" :weight bold))
                                         14 15
                                         (face
                                          (:foreground "goldenrod" :weight bold))
                                         21 22
                                         (face
                                          (:foreground "goldenrod" :weight bold)))
                                       :file "tb_program.sv" :line 121)))
                                    "init_rom"
                                    (:items nil :locs
                                     ((:type "task" :desc
                                       #("task init_rom ();" 5 13
                                         (face
                                          (:foreground "goldenrod" :weight bold)))
                                       :file "tb_program.sv" :line 58)))
                                    "init_values"
                                    (:items nil :locs
                                     ((:type "task" :desc
                                       #("task init_values;" 5 16
                                         (face
                                          (:foreground "goldenrod" :weight bold)))
                                       :file "tb_program.sv" :line 99)))
                                    "reset_system"
                                    (:items nil :locs
                                     ((:type "task" :desc
                                       #("task reset_system;" 5 17
                                         (face
                                          (:foreground "goldenrod" :weight bold)))
                                       :file "tb_program.sv" :line 104)))
                                    "serial_rx"
                                    (:items nil :locs
                                     ((:type "task" :desc
                                       #("task serial_rx (input logic [7:0] Data);" 5 14
                                         (face
                                          (:foreground "goldenrod" :weight bold)))
                                       :file "tb_program.sv" :line 115))))))

    ("ucontroller.sv" #s(hash-table size 97 test equal rehash-size 1.5 rehash-threshold 0.8125 data
                                    ("ucontroller"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #("endmodule: ucontroller" 11 22
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 213)
                                       (:type nil :desc
                                        #("module ucontroller # (" 7 18
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 21)))
                                     "FREQ_CLK"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".FREQ_CLK (FREQ_CLK)," 1 9
                                          (face
                                           (:foreground "goldenrod" :weight bold))
                                          11 19
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 153)
                                       (:type nil :desc
                                        #("parameter logic [31:0] FREQ_CLK = 100000000," 23 31
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 22)))
                                     "TX_SPEED"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".TX_SPEED (TX_SPEED)" 1 9
                                          (face
                                           (:foreground "goldenrod" :weight bold))
                                          11 19
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 154)
                                       (:type nil :desc
                                        #("parameter logic [31:0] TX_SPEED = 115200" 23 31
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 23)))
                                     "Clk"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Clk," 1 4
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 198)
                                       (:type nil :desc
                                        #(".Clk," 1 4
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 173)
                                       (:type nil :desc
                                        #(".Clk," 1 4
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 156)
                                       (:type nil :desc
                                        #(".Clk," 1 4
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 126)
                                       (:type nil :desc
                                        #(".Clk," 1 4
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 113)
                                       (:type nil :desc
                                        #(".Clk," 1 4
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 84)
                                       (:type nil :desc
                                        #("input logic         Clk," 20 23
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 25)))
                                     "Rst_n"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Rst_n," 1 6
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 199)
                                       (:type nil :desc
                                        #(".Rst_n," 1 6
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 174)
                                       (:type nil :desc
                                        #(".Rst_n," 1 6
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 157)
                                       (:type nil :desc
                                        #(".Rst_n," 1 6
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 127)
                                       (:type nil :desc
                                        #(".Rst_n," 1 6
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 114)
                                       (:type nil :desc
                                        #(".Rst_n," 1 6
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 85)
                                       (:type nil :desc
                                        #("input logic         Rst_n," 20 25
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 26)))
                                     "RXD"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".RXD," 1 4
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 166)
                                       (:type nil :desc
                                        #("input logic         RXD," 20 23
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 28)))
                                     "TXD"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".TXD," 1 4
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 162)
                                       (:type nil :desc
                                        #("output logic        TXD," 20 23
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 29)))
                                     "ROM_Data"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".ROM_Data," 1 9
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 87)
                                       (:type nil :desc
                                        #("input logic [11:0]  ROM_Data," 20 28
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 31)))
                                     "ROM_Addr"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".ROM_Addr," 1 9
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 88)
                                       (:type nil :desc
                                        #("output logic [11:0] ROM_Addr," 20 28
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 32)))
                                     "Temp"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Temp" 1 5
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 207)
                                       (:type nil :desc
                                        #("output logic [7:0]  Temp," 20 24
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 34)))
                                     "Switches"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Switches," 1 9
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 206)
                                       (:type nil :desc
                                        #("output logic [7:0]  Switches" 20 28
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 35)))
                                     "DMA_Oen"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".DMA_Oen," 1 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 188)
                                       (:type nil :desc
                                        #(".Oen     (DMA_Oen)" 10 17
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 148)
                                       (:type nil :desc
                                        #("logic       DMA_Oen;" 12 19
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 40)))
                                     "DMA_Wen"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".DMA_Wen," 1 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 191)
                                       (:type nil :desc
                                        #(".Wen     (DMA_Wen)," 10 17
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 147)
                                       (:type nil :desc
                                        #("logic       DMA_Wen;" 12 19
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 41)))
                                     "DMA_Cs"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".DMA_Cs," 1 7
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 185)
                                       (:type nil :desc
                                        #(".Cs      (DMA_Cs)," 10 16
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 146)
                                       (:type nil :desc
                                        #("logic       DMA_Cs;" 12 18
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 42)))
                                     "CPU_Oen"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".CPU_Oen," 1 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 187)
                                       (:type nil :desc
                                        #(".RAM_Oen      (CPU_Oen)," 15 22
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 95)
                                       (:type nil :desc
                                        #("logic       CPU_Oen;" 12 19
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 43)))
                                     "CPU_Wen"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".CPU_Wen," 1 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 190)
                                       (:type nil :desc
                                        #(".RAM_Wen      (CPU_Wen)," 15 22
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 94)
                                       (:type nil :desc
                                        #("logic       CPU_Wen;" 12 19
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 44)))
                                     "CPU_Cs"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".CPU_Cs," 1 7
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 184)
                                       (:type nil :desc
                                        #(".RAM_Cs       (CPU_Cs)," 15 21
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 93)
                                       (:type nil :desc
                                        #("logic       CPU_Cs;" 12 18
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 45)))
                                     "CPU_Address"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".CPU_Address," 1 12
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 181)
                                       (:type nil :desc
                                        #(".RAM_Addr     (CPU_Address)," 15 26
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 90)
                                       (:type nil :desc
                                        #("logic [7:0] CPU_Address;" 12 23
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 46)))
                                     "DMA_Address"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".DMA_Address," 1 12
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 182)
                                       (:type nil :desc
                                        #(".Address (DMA_Address)," 10 21
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 143)
                                       (:type nil :desc
                                        #("logic [7:0] DMA_Address;" 12 23
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 47)))
                                     "DMA_DataOut"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".DMA_DataOut," 1 12
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 179)
                                       (:type nil :desc
                                        #(".DataOut (DMA_DataOut)," 10 21
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 144)
                                       (:type nil :desc
                                        #("logic [7:0] DMA_DataOut;" 12 23
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 48)))
                                     "CPU_DataOut"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".CPU_DataOut," 1 12
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 178)
                                       (:type nil :desc
                                        #(".DataOut      (CPU_DataOut)," 15 26
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 91)
                                       (:type nil :desc
                                        #("logic [7:0] CPU_DataOut;" 12 23
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 49)))
                                     "Dma_Idle"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Dma_Idle      (Dma_Idle)," 1 9
                                          (face
                                           (:foreground "goldenrod" :weight bold))
                                          16 24
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 177)
                                       (:type nil :desc
                                        #(".Dma_Idle," 1 9
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 133)
                                       (:type nil :desc
                                        #("logic       Dma_Idle;" 12 20
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 50)))
                                     "TX_Data"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".TX_DataIn (TX_Data)," 12 19
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 160)
                                       (:type nil :desc
                                        #(".TX_Data," 1 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 140)
                                       (:type nil :desc
                                        #("logic [7:0] TX_Data;" 12 19
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 52)))
                                     "TX_Ready"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".TX_Ready," 1 9
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 161)
                                       (:type nil :desc
                                        #(".TX_Ready," 1 9
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 139)
                                       (:type nil :desc
                                        #("logic       TX_Ready;" 12 20
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 53)))
                                     "TX_Valid"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".TX_Valid," 1 9
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 159)
                                       (:type nil :desc
                                        #(".TX_Valid," 1 9
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 141)
                                       (:type nil :desc
                                        #("logic       TX_Valid;" 12 20
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 54)))
                                     "Data_Read"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Data_Read," 1 10
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 164)
                                       (:type nil :desc
                                        #(".Data_Read," 1 10
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 138)
                                       (:type nil :desc
                                        #("logic       Data_Read;" 12 21
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 55)))
                                     "RX_Data"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Data_Out  (RX_Data)," 12 19
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 165)
                                       (:type nil :desc
                                        #(".RX_Data," 1 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 135)
                                       (:type nil :desc
                                        #("logic [7:0] RX_Data;" 12 19
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 56)))
                                     "RX_Empty"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Empty     (RX_Empty)" 12 20
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 168)
                                       (:type nil :desc
                                        #(".RX_Empty," 1 9
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 136)
                                       (:type nil :desc
                                        #("logic       RX_Empty;" 12 20
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 57)))
                                     "RX_Full"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Full      (RX_Full)," 12 19
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 167)
                                       (:type nil :desc
                                        #(".RX_Full," 1 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 137)
                                       (:type nil :desc
                                        #("logic       RX_Full;" 12 19
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 58)))
                                     "RAM_DataOut"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".DataOut (RAM_DataOut)," 10 21
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 205)
                                       (:type nil :desc
                                        #(".DataIn  (RAM_DataOut)," 10 21
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 145)
                                       (:type nil :desc
                                        #(".DataIn       (RAM_DataOut)," 15 26
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 92)
                                       (:type nil :desc
                                        #("logic [7:0] RAM_DataOut;" 12 23
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 60)))
                                     "RAM_DataIn"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".DataIn  (RAM_DataIn)," 10 20
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 204)
                                       (:type nil :desc
                                        #(".RAM_DataIn," 1 11
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 180)
                                       (:type nil :desc
                                        #("logic [7:0] RAM_DataIn;" 12 22
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 61)))
                                     "ALU_DataIn"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".InData  (ALU_DataIn)," 10 20
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 115)
                                       (:type nil :desc
                                        #(".ALU_DataIn," 1 11
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 104)
                                       (:type nil :desc
                                        #("logic [7:0] ALU_DataIn;" 12 22
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 63)))
                                     "ALU_DataOut"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".OutData (ALU_DataOut)," 10 21
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 116)
                                       (:type nil :desc
                                        #(".ALU_DataOut," 1 12
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 103)
                                       (:type nil :desc
                                        #("logic [7:0] ALU_DataOut;" 12 23
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 64)))
                                     "alu_op"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #("alu_op      alu_op;" 0 6
                                          (face
                                           (:foreground "goldenrod" :weight bold))
                                          12 18
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 65)))
                                     "ALU_op"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".ALU_op," 1 7
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 117)
                                       (:type nil :desc
                                        #(".ALU_op," 1 7
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 102)
                                       (:type nil :desc
                                        #("ALU_op      ALU_op;" 0 6
                                          (face
                                           (:foreground "goldenrod" :weight bold))
                                          12 18
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 65)))
                                     "FlagE"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".FlagE" 1 6
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 121)
                                       (:type nil :desc
                                        #(".FlagE" 1 6
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 108)
                                       (:type nil :desc
                                        #("logic       FlagE;" 12 17
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 66)))
                                     "FlagN"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".FlagN," 1 6
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 120)
                                       (:type nil :desc
                                        #(".FlagN," 1 6
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 107)
                                       (:type nil :desc
                                        #("logic       FlagN;" 12 17
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 67)))
                                     "FlagC"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".FlagC," 1 6
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 119)
                                       (:type nil :desc
                                        #(".FlagC," 1 6
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 106)
                                       (:type nil :desc
                                        #("logic       FlagC;" 12 17
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 68)))
                                     "FlagZ"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".FlagZ," 1 6
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 118)
                                       (:type nil :desc
                                        #(".FlagZ," 1 6
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 105)
                                       (:type nil :desc
                                        #("logic       FlagZ;" 12 17
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 69)))
                                     "RAM_Address"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Address (RAM_Address)," 10 21
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 203)
                                       (:type nil :desc
                                        #(".RAM_Address," 1 12
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 183)
                                       (:type nil :desc
                                        #("logic [7:0] RAM_Address;" 12 23
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 71)))
                                     "RAM_Wen"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Wen     (RAM_Wen)," 10 17
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 201)
                                       (:type nil :desc
                                        #(".RAM_Wen" 1 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 192)
                                       (:type nil :desc
                                        #(".RAM_Wen      (CPU_Wen)," 1 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 94)
                                       (:type nil :desc
                                        #("logic       RAM_Wen;" 12 19
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 72)))
                                     "RAM_Oen"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Oen     (RAM_Oen)," 10 17
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 202)
                                       (:type nil :desc
                                        #(".RAM_Oen," 1 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 189)
                                       (:type nil :desc
                                        #(".RAM_Oen      (CPU_Oen)," 1 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 95)
                                       (:type nil :desc
                                        #("logic       RAM_Oen;" 12 19
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 73)))
                                     "RAM_Cs"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Cs      (RAM_Cs)," 10 16
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 200)
                                       (:type nil :desc
                                        #(".RAM_Cs," 1 7
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 186)
                                       (:type nil :desc
                                        #(".RAM_Cs       (CPU_Cs)," 1 7
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 93)
                                       (:type nil :desc
                                        #("logic       RAM_Cs;" 12 18
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 74)))
                                     "Bus_grant"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".DMA_Bus_grant (Bus_grant)," 16 25
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 176)
                                       (:type nil :desc
                                        #(".Bus_grant," 1 10
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 129)
                                       (:type nil :desc
                                        #(".DMA_Ack      (Bus_grant)," 15 24
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 98)
                                       (:type nil :desc
                                        #("logic       Bus_grant;" 12 21
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 76)))
                                     "Bus_req"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".DMA_Bus_req   (Bus_req)," 16 23
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 175)
                                       (:type nil :desc
                                        #(".Bus_req," 1 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 130)
                                       (:type nil :desc
                                        #(".DMA_Req      (Bus_req)," 15 22
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 97)
                                       (:type nil :desc
                                        #("logic       Bus_req;" 12 19
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 77)))
                                     "Dma_Tx_Ready"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Dma_Tx_Ready," 1 13
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 132)
                                       (:type nil :desc
                                        #(".DMA_Ready    (Dma_Tx_Ready)," 15 27
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 99)
                                       (:type nil :desc
                                        #("logic       Dma_Tx_Ready;" 12 24
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 78)))
                                     "Dma_Tx_Start"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Dma_Tx_Start," 1 13
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 131)
                                       (:type nil :desc
                                        #(".Dma_Tx_Start (Dma_Tx_Start)," 1 13
                                          (face
                                           (:foreground "goldenrod" :weight bold))
                                          15 27
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 100)
                                       (:type nil :desc
                                        #("logic       Dma_Tx_Start;" 12 24
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 79)))
                                     "cpu"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #("cpu I_CPU (" 0 3
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 83)))
                                     "I_CPU"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #("cpu I_CPU (" 4 9
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 83)))
                                     "RAM_Addr"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".RAM_Addr     (CPU_Address)," 1 9
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 90)))
                                     "DataOut"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".DataOut (RAM_DataOut)," 1 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 205)
                                       (:type nil :desc
                                        #(".DataOut (DMA_DataOut)," 1 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 144)
                                       (:type nil :desc
                                        #(".DataOut      (CPU_DataOut)," 1 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 91)))
                                     "DataIn"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".DataIn  (RAM_DataIn)," 1 7
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 204)
                                       (:type nil :desc
                                        #(".DataIn  (RAM_DataOut)," 1 7
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 145)
                                       (:type nil :desc
                                        #(".DataIn       (RAM_DataOut)," 1 7
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 92)))
                                     "DMA_Req"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".DMA_Req      (Bus_req)," 1 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 97)))
                                     "DMA_Ack"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".DMA_Ack      (Bus_grant)," 1 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 98)))
                                     "DMA_Ready"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".DMA_Ready    (Dma_Tx_Ready)," 1 10
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 99)))
                                     "DMA_Tx_Start"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".DMA_Tx_Start (DMA_Tx_Start)," 1 13
                                          (face
                                           (:foreground "goldenrod" :weight bold))
                                          15 27
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 100)))
                                     "alu"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #("alu I_ALU (" 0 3
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 112)))
                                     "I_ALU"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #("alu I_ALU (" 4 9
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 112)))
                                     "InData"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".InData  (ALU_DataIn)," 1 7
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 115)))
                                     "OutData"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".OutData (ALU_DataOut)," 1 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 116)))
                                     "dma"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #("dma I_DMA (" 0 3
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 125)))
                                     "I_DMA"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #("dma I_DMA (" 4 9
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 125)))
                                     "Address"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Address (RAM_Address)," 1 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 203)
                                       (:type nil :desc
                                        #(".Address (DMA_Address)," 1 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 143)))
                                     "Cs"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Cs      (RAM_Cs)," 1 3
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 200)
                                       (:type nil :desc
                                        #(".Cs      (DMA_Cs)," 1 3
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 146)))
                                     "Wen"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Wen     (RAM_Wen)," 1 4
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 201)
                                       (:type nil :desc
                                        #(".Wen     (DMA_Wen)," 1 4
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 147)))
                                     "Oen"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Oen     (RAM_Oen)," 1 4
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 202)
                                       (:type nil :desc
                                        #(".Oen     (DMA_Oen)" 1 4
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 148)))
                                     "uart"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #("uart # (" 0 4
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 152)))
                                     "I_UART"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(") I_UART (" 2 8
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 155)))
                                     "TX_DataIn"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".TX_DataIn (TX_Data)," 1 10
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 160)))
                                     "Data_Out"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Data_Out  (RX_Data)," 1 9
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 165)))
                                     "Full"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Full      (RX_Full)," 1 5
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 167)))
                                     "Empty"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".Empty     (RX_Empty)" 1 6
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 168)))
                                     "ram_arbiter"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #("ram_arbiter I_RAM_ARBITER (" 0 11
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 172)))
                                     "I_RAM_ARBITER"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #("ram_arbiter I_RAM_ARBITER (" 12 25
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 172)))
                                     "DMA_Bus_req"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".DMA_Bus_req   (Bus_req)," 1 12
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 175)))
                                     "DMA_Bus_grant"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".DMA_Bus_grant (Bus_grant)," 1 14
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 176)))
                                     "DMA_Idle"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #(".DMA_Idle      (DMA_Idle)," 1 9
                                          (face
                                           (:foreground "goldenrod" :weight bold))
                                          16 24
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 177)))
                                     "ram"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #("ram I_RAM (" 0 3
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 197)))
                                     "I_RAM"
                                     (:items nil :locs
                                      ((:type nil :desc
                                        #("ram I_RAM (" 4 9
                                          (face
                                           (:foreground "goldenrod" :weight bold)))
                                        :file "ucontroller.sv" :line 197))))))
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
