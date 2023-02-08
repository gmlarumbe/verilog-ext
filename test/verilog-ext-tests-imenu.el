;;; verilog-ext-tests-imenu.el --- Verilog-Ext ERT Imenu tests  -*- lexical-binding: t -*-

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
;; ERT Imenu Tests
;;
;;; Code:


(defmacro verilog-ext-test-imenu-file (file)
  (declare (indent 1))
  `(with-temp-buffer
     (insert-file-contents (verilog-ext-path-join verilog-ext-tests-common-dir ,file))
     (verilog-mode)
     (let ((imenu-use-markers nil)
           (print-level nil)
           (print-length nil)
           (eval-expression-print-level nil)
           (eval-expression-print-length nil))
       (verilog-ext-imenu-index))))


(ert-deftest imenu::methods ()
  (should (equal (verilog-ext-test-imenu-file "uvm_component.svh")
                 '(("*Classes*"
                    (#("uvm_component (v)" 0 13
                       (face
                        (:foreground "goldenrod" :weight bold))
                       13 17
                       (face italic))
                     (#("new [F] (e)" 0 3
                        (face
                         (:foreground "goldenrod" :weight bold))
                        7 11
                        (face italic))
                      . 2561)
                     (#("get_parent [F] (ev)" 0 10
                        (face
                         (:foreground "goldenrod" :weight bold))
                        14 19
                        (face italic))
                      . 3192)
                     (#("get_full_name [F] (ev)" 0 13
                        (face
                         (:foreground "goldenrod" :weight bold))
                        17 22
                        (face italic))
                      . 3559)
                     (#("get_children [F] (e)" 0 12
                        (face
                         (:foreground "goldenrod" :weight bold))
                        16 20
                        (face italic))
                      . 3943)
                     (#("get_child [F] (e)" 0 9
                        (face
                         (:foreground "goldenrod" :weight bold))
                        13 17
                        (face italic))
                      . 4055)
                     (#("get_next_child [F] (e)" 0 14
                        (face
                         (:foreground "goldenrod" :weight bold))
                        18 22
                        (face italic))
                      . 4155)
                     (#("get_first_child [F] (e)" 0 15
                        (face
                         (:foreground "goldenrod" :weight bold))
                        19 23
                        (face italic))
                      . 4756)
                     (#("get_num_children [F] (e)" 0 16
                        (face
                         (:foreground "goldenrod" :weight bold))
                        20 24
                        (face italic))
                      . 4960)
                     (#("has_child [F] (e)" 0 9
                        (face
                         (:foreground "goldenrod" :weight bold))
                        13 17
                        (face italic))
                      . 5170)
                     (#("set_name [F] (ev)" 0 8
                        (face
                         (:foreground "goldenrod" :weight bold))
                        12 17
                        (face italic))
                      . 5377)
                     (#("lookup [F] (e)" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold))
                        10 14
                        (face italic))
                      . 5843)
                     (#("get_depth [F] (e)" 0 9
                        (face
                         (:foreground "goldenrod" :weight bold))
                        13 17
                        (face italic))
                      . 6108)
                     (#("build_phase [F] (ev)" 0 11
                        (face
                         (:foreground "goldenrod" :weight bold))
                        15 20
                        (face italic))
                      . 7542)
                     (#("connect_phase [F] (ev)" 0 13
                        (face
                         (:foreground "goldenrod" :weight bold))
                        17 22
                        (face italic))
                      . 7807)
                     (#("end_of_elaboration_phase [F] (ev)" 0 24
                        (face
                         (:foreground "goldenrod" :weight bold))
                        28 33
                        (face italic))
                      . 8096)
                     (#("start_of_simulation_phase [F] (ev)" 0 25
                        (face
                         (:foreground "goldenrod" :weight bold))
                        29 34
                        (face italic))
                      . 8398)
                     (#("run_phase [T] (ev)" 0 9
                        (face
                         (:foreground "goldenrod" :weight bold))
                        13 18
                        (face italic))
                      . 9021)
                     (#("pre_reset_phase [T] (ev)" 0 15
                        (face
                         (:foreground "goldenrod" :weight bold))
                        19 24
                        (face italic))
                      . 9789)
                     (#("reset_phase [T] (ev)" 0 11
                        (face
                         (:foreground "goldenrod" :weight bold))
                        15 20
                        (face italic))
                      . 10555)
                     (#("post_reset_phase [T] (ev)" 0 16
                        (face
                         (:foreground "goldenrod" :weight bold))
                        20 25
                        (face italic))
                      . 11327)
                     (#("pre_configure_phase [T] (ev)" 0 19
                        (face
                         (:foreground "goldenrod" :weight bold))
                        23 28
                        (face italic))
                      . 12110)
                     (#("configure_phase [T] (ev)" 0 15
                        (face
                         (:foreground "goldenrod" :weight bold))
                        19 24
                        (face italic))
                      . 12888)
                     (#("post_configure_phase [T] (ev)" 0 20
                        (face
                         (:foreground "goldenrod" :weight bold))
                        24 29
                        (face italic))
                      . 13672)
                     (#("pre_main_phase [T] (ev)" 0 14
                        (face
                         (:foreground "goldenrod" :weight bold))
                        18 23
                        (face italic))
                      . 14449)
                     (#("main_phase [T] (ev)" 0 10
                        (face
                         (:foreground "goldenrod" :weight bold))
                        14 19
                        (face italic))
                      . 15212)
                     (#("post_main_phase [T] (ev)" 0 15
                        (face
                         (:foreground "goldenrod" :weight bold))
                        19 24
                        (face italic))
                      . 15981)
                     (#("pre_shutdown_phase [T] (ev)" 0 18
                        (face
                         (:foreground "goldenrod" :weight bold))
                        22 27
                        (face italic))
                      . 16762)
                     (#("shutdown_phase [T] (ev)" 0 14
                        (face
                         (:foreground "goldenrod" :weight bold))
                        18 23
                        (face italic))
                      . 17538)
                     (#("post_shutdown_phase [T] (ev)" 0 19
                        (face
                         (:foreground "goldenrod" :weight bold))
                        23 28
                        (face italic))
                      . 18320)
                     (#("extract_phase [F] (ev)" 0 13
                        (face
                         (:foreground "goldenrod" :weight bold))
                        17 22
                        (face italic))
                      . 18584)
                     (#("check_phase [F] (ev)" 0 11
                        (face
                         (:foreground "goldenrod" :weight bold))
                        15 20
                        (face italic))
                      . 18849)
                     (#("report_phase [F] (ev)" 0 12
                        (face
                         (:foreground "goldenrod" :weight bold))
                        16 21
                        (face italic))
                      . 19112)
                     (#("final_phase [F] (ev)" 0 11
                        (face
                         (:foreground "goldenrod" :weight bold))
                        15 20
                        (face italic))
                      . 19374)
                     (#("phase_started [F] (ev)" 0 13
                        (face
                         (:foreground "goldenrod" :weight bold))
                        17 22
                        (face italic))
                      . 19708)
                     (#("phase_ready_to_end [F] (ev)" 0 18
                        (face
                         (:foreground "goldenrod" :weight bold))
                        22 27
                        (face italic))
                      . 20992)
                     (#("phase_ended [F] (ev)" 0 11
                        (face
                         (:foreground "goldenrod" :weight bold))
                        15 20
                        (face italic))
                      . 21333)
                     (#("set_domain [F] (e)" 0 10
                        (face
                         (:foreground "goldenrod" :weight bold))
                        14 18
                        (face italic))
                      . 21935)
                     (#("get_domain [F] (e)" 0 10
                        (face
                         (:foreground "goldenrod" :weight bold))
                        14 18
                        (face italic))
                      . 22151)
                     (#("define_domain [F] (evp)" 0 13
                        (face
                         (:foreground "goldenrod" :weight bold))
                        17 23
                        (face italic))
                      . 23754)
                     (#("suspend [T] (ev)" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold))
                        11 16
                        (face italic))
                      . 24155)
                     (#("resume [T] (ev)" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold))
                        10 15
                        (face italic))
                      . 24525)
                     (#("resolve_bindings [F] (ev)" 0 16
                        (face
                         (:foreground "goldenrod" :weight bold))
                        20 25
                        (face italic))
                      . 24848)
                     (#("massage_scope [F] (e)" 0 13
                        (face
                         (:foreground "goldenrod" :weight bold))
                        17 21
                        (face italic))
                      . 24901)
                     (#("apply_config_settings [F] (ev)" 0 21
                        (face
                         (:foreground "goldenrod" :weight bold))
                        25 30
                        (face italic))
                      . 27202)
                     (#("use_automatic_config [F] (ev)" 0 20
                        (face
                         (:foreground "goldenrod" :weight bold))
                        24 29
                        (face italic))
                      . 27491)
                     (#("print_config [F] (e)" 0 12
                        (face
                         (:foreground "goldenrod" :weight bold))
                        16 20
                        (face italic))
                      . 28204)
                     (#("print_config_with_audit [F] (e)" 0 23
                        (face
                         (:foreground "goldenrod" :weight bold))
                        27 31
                        (face italic))
                      . 28656)
                     (#("get_print_config_matches [F] (s)" 0 24
                        (face
                         (:foreground "goldenrod" :weight bold))
                        28 32
                        (face italic))
                      . 29349)
                     (#("set_print_config_matches [F] (s)" 0 24
                        (face
                         (:foreground "goldenrod" :weight bold))
                        28 32
                        (face italic))
                      . 29826)
                     (#("raised [F] (v)" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold))
                        10 14
                        (face italic))
                      . 30799)
                     (#("dropped [F] (v)" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold))
                        11 15
                        (face italic))
                      . 31416)
                     (#("all_dropped [T] (v)" 0 11
                        (face
                         (:foreground "goldenrod" :weight bold))
                        15 19
                        (face italic))
                      . 32028)
                     (#("create_component [F] (e)" 0 16
                        (face
                         (:foreground "goldenrod" :weight bold))
                        20 24
                        (face italic))
                      . 33609)
                     (#("create_object [F] (e)" 0 13
                        (face
                         (:foreground "goldenrod" :weight bold))
                        17 21
                        (face italic))
                      . 34420)
                     (#("set_type_override_by_type [F] (es)" 0 25
                        (face
                         (:foreground "goldenrod" :weight bold))
                        29 34
                        (face italic))
                      . 35511)
                     (#("set_inst_override_by_type [F] (e)" 0 25
                        (face
                         (:foreground "goldenrod" :weight bold))
                        29 33
                        (face italic))
                      . 38009)
                     (#("set_type_override [F] (es)" 0 17
                        (face
                         (:foreground "goldenrod" :weight bold))
                        21 26
                        (face italic))
                      . 39120)
                     (#("set_inst_override [F] (e)" 0 17
                        (face
                         (:foreground "goldenrod" :weight bold))
                        21 25
                        (face italic))
                      . 40398)
                     (#("print_override_info [F] (e)" 0 19
                        (face
                         (:foreground "goldenrod" :weight bold))
                        23 27
                        (face italic))
                      . 40906)
                     (#("set_report_id_verbosity_hier [F] (e)" 0 28
                        (face
                         (:foreground "goldenrod" :weight bold))
                        32 36
                        (face italic))
                      . 41730)
                     (#("set_report_severity_id_verbosity_hier [F] (e)" 0 37
                        (face
                         (:foreground "goldenrod" :weight bold))
                        41 45
                        (face italic))
                      . 42366)
                     (#("set_report_severity_action_hier [F] (e)" 0 31
                        (face
                         (:foreground "goldenrod" :weight bold))
                        35 39
                        (face italic))
                      . 42655)
                     (#("set_report_id_action_hier [F] (e)" 0 25
                        (face
                         (:foreground "goldenrod" :weight bold))
                        29 33
                        (face italic))
                      . 42866)
                     (#("set_report_severity_id_action_hier [F] (e)" 0 34
                        (face
                         (:foreground "goldenrod" :weight bold))
                        38 42
                        (face italic))
                      . 43487)
                     (#("set_report_default_file_hier [F] (e)" 0 28
                        (face
                         (:foreground "goldenrod" :weight bold))
                        32 36
                        (face italic))
                      . 43775)
                     (#("set_report_severity_file_hier [F] (e)" 0 29
                        (face
                         (:foreground "goldenrod" :weight bold))
                        33 37
                        (face italic))
                      . 43903)
                     (#("set_report_id_file_hier [F] (e)" 0 23
                        (face
                         (:foreground "goldenrod" :weight bold))
                        27 31
                        (face italic))
                      . 44103)
                     (#("set_report_severity_id_file_hier [F] (e)" 0 32
                        (face
                         (:foreground "goldenrod" :weight bold))
                        36 40
                        (face italic))
                      . 44801)
                     (#("set_report_verbosity_level_hier [F] (e)" 0 31
                        (face
                         (:foreground "goldenrod" :weight bold))
                        35 39
                        (face italic))
                      . 45415)
                     (#("pre_abort [F] (v)" 0 9
                        (face
                         (:foreground "goldenrod" :weight bold))
                        13 17
                        (face italic))
                      . 46266)
                     (#("accept_tr [F] (e)" 0 9
                        (face
                         (:foreground "goldenrod" :weight bold))
                        13 17
                        (face italic))
                      . 47514)
                     (#("do_accept_tr [F] (evp)" 0 12
                        (face
                         (:foreground "goldenrod" :weight bold))
                        16 22
                        (face italic))
                      . 47866)
                     (#("begin_tr [F] (e)" 0 8
                        (face
                         (:foreground "goldenrod" :weight bold))
                        12 16
                        (face italic))
                      . 48639)
                     (#("do_begin_tr [F]" 0 11
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 49298)
                     (#("end_tr [F] (e)" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold))
                        10 14
                        (face italic))
                      . 50589)
                     (#("do_end_tr [F] (evp)" 0 9
                        (face
                         (:foreground "goldenrod" :weight bold))
                        13 19
                        (face italic))
                      . 51002)
                     (#("record_error_tr [F] (e)" 0 15
                        (face
                         (:foreground "goldenrod" :weight bold))
                        19 23
                        (face italic))
                      . 51839)
                     (#("record_event_tr [F] (e)" 0 15
                        (face
                         (:foreground "goldenrod" :weight bold))
                        19 23
                        (face italic))
                      . 52728)
                     (#("get_tr_stream [F] (ev)" 0 13
                        (face
                         (:foreground "goldenrod" :weight bold))
                        17 22
                        (face italic))
                      . 53159)
                     (#("free_tr_stream [F] (ev)" 0 14
                        (face
                         (:foreground "goldenrod" :weight bold))
                        18 23
                        (face italic))
                      . 53353)
                     (#("do_execute_op [F] (ev)" 0 13
                        (face
                         (:foreground "goldenrod" :weight bold))
                        17 22
                        (face italic))
                      . 53793)
                     (#("get_tr_database [F] (ev)" 0 15
                        (face
                         (:foreground "goldenrod" :weight bold))
                        19 24
                        (face italic))
                      . 54158)
                     (#("set_tr_database [F] (ev)" 0 15
                        (face
                         (:foreground "goldenrod" :weight bold))
                        19 24
                        (face italic))
                      . 54262)
                     (#("set_local [F] (e)" 0 9
                        (face
                         (:foreground "goldenrod" :weight bold))
                        13 17
                        (face italic))
                      . 55681)
                     (#("m_add_child [F] (epv)" 0 11
                        (face
                         (:foreground "goldenrod" :weight bold))
                        15 21
                        (face italic))
                      . 55916)
                     (#("m_set_full_name [F] (elv)" 0 15
                        (face
                         (:foreground "goldenrod" :weight bold))
                        19 25
                        (face italic))
                      . 55991)
                     (#("do_resolve_bindings [F] (e)" 0 19
                        (face
                         (:foreground "goldenrod" :weight bold))
                        23 27
                        (face italic))
                      . 56052)
                     (#("do_flush [F] (e)" 0 8
                        (face
                         (:foreground "goldenrod" :weight bold))
                        12 16
                        (face italic))
                      . 56116)
                     (#("flush [F] (ev)" 0 5
                        (face
                         (:foreground "goldenrod" :weight bold))
                        9 14
                        (face italic))
                      . 56170)
                     (#("m_extract_name [F] (el)" 0 14
                        (face
                         (:foreground "goldenrod" :weight bold))
                        18 23
                        (face italic))
                      . 56222)
                     (#("create [F] (ev)" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold))
                        10 15
                        (face italic))
                      . 56480)
                     (#("clone [F] (ev)" 0 5
                        (face
                         (:foreground "goldenrod" :weight bold))
                        9 14
                        (face italic))
                      . 56542)
                     (#("m_begin_tr [F] (ep)" 0 10
                        (face
                         (:foreground "goldenrod" :weight bold))
                        14 19
                        (face italic))
                      . 56686)
                     (#("get_recording_enabled [F] (ev)" 0 21
                        (face
                         (:foreground "goldenrod" :weight bold))
                        25 30
                        (face italic))
                      . 57265)
                     (#("set_recording_enabled [F] (ev)" 0 21
                        (face
                         (:foreground "goldenrod" :weight bold))
                        25 30
                        (face italic))
                      . 57771)
                     (#("set_recording_enabled_hier [F] (ev)" 0 26
                        (face
                         (:foreground "goldenrod" :weight bold))
                        30 35
                        (face italic))
                      . 57877)
                     (#("do_print [F] (e)" 0 8
                        (face
                         (:foreground "goldenrod" :weight bold))
                        12 16
                        (face italic))
                      . 57951)
                     (#("m_set_cl_msg_args [F] (e)" 0 17
                        (face
                         (:foreground "goldenrod" :weight bold))
                        21 25
                        (face italic))
                      . 58082)
                     (#("m_set_cl_verb [F] (e)" 0 13
                        (face
                         (:foreground "goldenrod" :weight bold))
                        17 21
                        (face italic))
                      . 58124)
                     (#("m_set_cl_action [F] (e)" 0 15
                        (face
                         (:foreground "goldenrod" :weight bold))
                        19 23
                        (face italic))
                      . 58162)
                     (#("m_set_cl_sev [F] (e)" 0 12
                        (face
                         (:foreground "goldenrod" :weight bold))
                        16 20
                        (face italic))
                      . 58202)
                     (#("m_apply_verbosity_settings [F] (e)" 0 26
                        (face
                         (:foreground "goldenrod" :weight bold))
                        30 34
                        (face italic))
                      . 58239)
                     (#("m_do_pre_abort [F]" 0 14
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 58411)
                     (#("m_unsupported_set_local [F] (e)" 0 23
                        (face
                         (:foreground "goldenrod" :weight bold))
                        27 31
                        (face italic))
                      . 58587)))
                   ("uvm_component"
                    ("new" . 59131)
                    ("m_add_child" . 61930)
                    ("get_children" . 62937)
                    ("get_first_child" . 63127)
                    ("get_next_child" . 63273)
                    ("get_child" . 63417)
                    ("has_child" . 63704)
                    ("get_num_children" . 63845)
                    ("get_full_name" . 63972)
                    ("get_parent" . 64256)
                    ("set_name" . 64359)
                    ("m_set_full_name" . 64698)
                    ("lookup" . 65057)
                    ("get_depth" . 66038)
                    ("m_extract_name" . 66236)
                    ("flush" . 66777)
                    ("do_flush" . 66879)
                    ("create" . 67220)
                    ("clone" . 67435)
                    ("print_override_info" . 67723)
                    ("create_component" . 68100)
                    ("create_object" . 68526)
                    ("set_type_override" . 68945)
                    ("set_type_override_by_type" . 69423)
                    ("set_inst_override" . 69904)
                    ("set_inst_override_by_type" . 70643)
                    ("set_report_id_verbosity_hier" . 71544)
                    ("set_report_severity_id_verbosity_hier" . 71856)
                    ("set_report_severity_action_hier" . 72353)
                    ("set_report_id_action_hier" . 72734)
                    ("set_report_severity_id_action_hier" . 73032)
                    ("set_report_severity_file_hier" . 73520)
                    ("set_report_default_file_hier" . 73894)
                    ("set_report_id_file_hier" . 74152)
                    ("set_report_severity_id_file_hier" . 74432)
                    ("set_report_verbosity_level_hier" . 74909)
                    ("build_phase" . 75512)
                    ("connect_phase" . 75831)
                    ("start_of_simulation_phase" . 75915)
                    ("end_of_elaboration_phase" . 76011)
                    ("run_phase" . 76106)
                    ("extract_phase" . 76182)
                    ("check_phase" . 76266)
                    ("report_phase" . 76348)
                    ("final_phase" . 76431)
                    ("pre_reset_phase" . 76584)
                    ("reset_phase" . 76659)
                    ("post_reset_phase" . 76734)
                    ("pre_configure_phase" . 76809)
                    ("configure_phase" . 76884)
                    ("post_configure_phase" . 76959)
                    ("pre_main_phase" . 77034)
                    ("main_phase" . 77109)
                    ("post_main_phase" . 77184)
                    ("pre_shutdown_phase" . 77259)
                    ("shutdown_phase" . 77334)
                    ("post_shutdown_phase" . 77409)
                    ("phase_started" . 77902)
                    ("phase_ended" . 78007)
                    ("phase_ready_to_end" . 78125)
                    ("define_domain" . 78578)
                    ("set_domain" . 79480)
                    ("get_domain" . 79768)
                    ("suspend" . 79945)
                    ("resume" . 80071)
                    ("resolve_bindings" . 80224)
                    ("do_resolve_bindings" . 80344)
                    ("accept_tr" . 80720)
                    ("begin_tr" . 81052)
                    ("get_tr_database" . 81572)
                    ("set_tr_database" . 81878)
                    ("get_tr_stream" . 82045)
                    ("free_tr_stream" . 82519)
                    ("m_begin_tr" . 83373)
                    ("end_tr" . 86225)
                    ("record_error_tr" . 87004)
                    ("record_event_tr" . 88489)
                    ("do_accept_tr" . 89965)
                    ("do_begin_tr" . 90084)
                    ("do_end_tr" . 90317)
                    ("massage_scope" . 90656)
                    ("use_automatic_config" . 91112)
                    ("apply_config_settings" . 91241)
                    ("print_config" . 92304)
                    ("print_config_with_audit" . 92777)
                    ("get_recording_enabled" . 92888)
                    ("set_recording_enabled" . 93013)
                    ("set_recording_enabled_hier" . 93278)
                    ("do_print" . 93514)
                    ("do_execute_op" . 94406)
                    ("set_local" . 95135)
                    ("m_unsupported_set_local" . 95625)
                    ("m_set_cl_msg_args" . 95918)
                    ("m_set_cl_verb" . 96304)
                    ("m_set_cl_action" . 97345)
                    ("m_set_cl_sev" . 98519)
                    ("m_apply_verbosity_settings" . 99925)
                    ("m_do_pre_abort" . 100736)))))
  (should (equal (verilog-ext-test-imenu-file "axi_test.sv")
                 '(("*Classes*"
                    (#("axi_lite_driver" 0 15
                       (face
                        (:foreground "goldenrod" :weight bold)))
                     (#("new [F]" 0 3
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 1310)
                     (#("reset_master [F]" 0 12
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 1472)
                     (#("reset_slave [F]" 0 11
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 1809)
                     (#("cycle_start [T]" 0 11
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 2067)
                     (#("cycle_end [T]" 0 9
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 2113)
                     (#("send_aw [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 2214)
                     (#("send_w [T]" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 2649)
                     (#("send_b [T]" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 3078)
                     (#("send_ar [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 3414)
                     (#("send_r [T]" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 3849)
                     (#("recv_aw [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 4281)
                     (#("recv_w [T]" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 4637)
                     (#("recv_b [T]" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 4989)
                     (#("recv_ar [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 5294)
                     (#("recv_r [T]" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 5650))
                    (#("axi_ax_beat" 0 11
                       (face
                        (:foreground "goldenrod" :weight bold)))
                     . 6038)
                    (#("axi_w_beat" 0 10
                       (face
                        (:foreground "goldenrod" :weight bold)))
                     . 6715)
                    (#("axi_b_beat" 0 10
                       (face
                        (:foreground "goldenrod" :weight bold)))
                     . 7009)
                    (#("axi_r_beat" 0 10
                       (face
                        (:foreground "goldenrod" :weight bold)))
                     . 7257)
                    (#("axi_driver" 0 10
                       (face
                        (:foreground "goldenrod" :weight bold)))
                     (#("new [F]" 0 3
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 8237)
                     (#("reset_master [F]" 0 12
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 8454)
                     (#("reset_slave [F]" 0 11
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 9369)
                     (#("cycle_start [T]" 0 11
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 9770)
                     (#("cycle_end [T]" 0 9
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 9816)
                     (#("send_aw [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 9917)
                     (#("send_w [T]" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 11056)
                     (#("send_b [T]" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 11592)
                     (#("send_ar [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 12060)
                     (#("send_r [T]" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 13127)
                     (#("recv_aw [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 13732)
                     (#("recv_w [T]" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 14459)
                     (#("recv_b [T]" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 14877)
                     (#("recv_ar [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 15262)
                     (#("recv_r [T]" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 16017)
                     (#("mon_aw [T]" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 16480)
                     (#("mon_w [T]" 0 5
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 17176)
                     (#("mon_b [T]" 0 5
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 17564)
                     (#("mon_ar [T]" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 17919)
                     (#("mon_r [T]" 0 5
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 18641))
                    (#("axi_rand_master" 0 15
                       (face
                        (:foreground "goldenrod" :weight bold)))
                     (#("new [F]" 0 3
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 22168)
                     (#("reset [F]" 0 5
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 22992)
                     (#("add_memory_region [F]" 0 17
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 23238)
                     (#("add_traffic_shaping [F]" 0 19
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 23426)
                     (#("new_rand_burst [F]" 0 14
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 23761)
                     (#("rand_atop_burst [T]" 0 15
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 28279)
                     (#("rand_excl_ar [F]" 0 12
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 31523)
                     (#("rand_wait [T]" 0 9
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 32905)
                     (#("id_is_legal [F]" 0 11
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 33399)
                     (#("legalize_id [T]" 0 11
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 34520)
                     (#("send_ars [T]" 0 8
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 36016)
                     (#("recv_rs [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 36583)
                     (#("create_aws [T]" 0 10
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 37305)
                     (#("send_aws [T]" 0 8
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 37974)
                     (#("send_ws [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 38329)
                     (#("recv_bs [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 40030)
                     (#("run [T]" 0 3
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 40575))
                    (#("axi_rand_slave" 0 14
                       (face
                        (:foreground "goldenrod" :weight bold)))
                     (#("new [F]" 0 3
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 42734)
                     (#("reset [F]" 0 5
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 43030)
                     (#("rand_wait [T]" 0 9
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 43332)
                     (#("recv_ars [T]" 0 8
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 43681)
                     (#("send_rs [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 44093)
                     (#("recv_aws [T]" 0 8
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 46031)
                     (#("recv_ws [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 46716)
                     (#("send_bs [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 47868)
                     (#("run [T]" 0 3
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 48887))
                    (#("axi_lite_rand_master" 0 20
                       (face
                        (:foreground "goldenrod" :weight bold)))
                     (#("new [F]" 0 3
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 50296)
                     (#("reset [F]" 0 5
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 50656)
                     (#("rand_wait [T]" 0 9
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 50726)
                     (#("send_ars [T]" 0 8
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 51075)
                     (#("recv_rs [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 51599)
                     (#("send_aws [T]" 0 8
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 52117)
                     (#("send_ws [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 52686)
                     (#("recv_bs [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 53384)
                     (#("run [T]" 0 3
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 53896)
                     (#("write [T]" 0 5
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 54255)
                     (#("read [T]" 0 4
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 54889))
                    (#("axi_lite_rand_slave" 0 19
                       (face
                        (:foreground "goldenrod" :weight bold)))
                     (#("new [F]" 0 3
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 56343)
                     (#("reset [F]" 0 5
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 56702)
                     (#("rand_wait [T]" 0 9
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 56776)
                     (#("recv_ars [T]" 0 8
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 57125)
                     (#("send_rs [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 57521)
                     (#("recv_aws [T]" 0 8
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 58048)
                     (#("recv_ws [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 58444)
                     (#("send_bs [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 58831)
                     (#("run [T]" 0 3
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 59472))
                    (#("axi_monitor" 0 11
                       (face
                        (:foreground "goldenrod" :weight bold)))
                     (#("new [F]" 0 3
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 60422)
                     (#("monitor [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 60644))
                    (#("axi_scoreboard" 0 14
                       (face
                        (:foreground "goldenrod" :weight bold)))
                     (#("new [F]" 0 3
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 64109)
                     (#("cycle_start [T] (p)" 0 11
                        (face
                         (:foreground "goldenrod" :weight bold))
                        15 19
                        (face italic))
                      . 64409)
                     (#("cycle_end [T] (p)" 0 9
                        (face
                         (:foreground "goldenrod" :weight bold))
                        13 17
                        (face italic))
                      . 64498)
                     (#("handle_write [T] (p)" 0 12
                        (face
                         (:foreground "goldenrod" :weight bold))
                        16 20
                        (face italic))
                      . 64640)
                     (#("handle_write_resp [T] (p)" 0 17
                        (face
                         (:foreground "goldenrod" :weight bold))
                        21 25
                        (face italic))
                      . 66808)
                     (#("handle_read [T] (p)" 0 11
                        (face
                         (:foreground "goldenrod" :weight bold))
                        15 19
                        (face italic))
                      . 68057)
                     (#("mon_aw [T] (p)" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold))
                        10 14
                        (face italic))
                      . 70606)
                     (#("mon_w [T] (p)" 0 5
                        (face
                         (:foreground "goldenrod" :weight bold))
                        9 13
                        (face italic))
                      . 71518)
                     (#("mon_b [T] (p)" 0 5
                        (face
                         (:foreground "goldenrod" :weight bold))
                        9 13
                        (face italic))
                      . 72014)
                     (#("mon_ar [T] (p)" 0 6
                        (face
                         (:foreground "goldenrod" :weight bold))
                        10 14
                        (face italic))
                      . 72481)
                     (#("mon_r [T] (p)" 0 5
                        (face
                         (:foreground "goldenrod" :weight bold))
                        9 13
                        (face italic))
                      . 73402)
                     (#("monitor [T]" 0 7
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 74086)
                     (#("enable_read_check [T]" 0 17
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 74618)
                     (#("disable_read_check [T]" 0 18
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 74762)
                     (#("enable_b_resp_check [T]" 0 19
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 74977)
                     (#("disable_b_resp_check [T]" 0 20
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 75127)
                     (#("enable_r_resp_check [T]" 0 19
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 75409)
                     (#("disable_r_resp_check [T]" 0 20
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 75558)
                     (#("enable_all_checks [T]" 0 17
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 75693)
                     (#("disable_all_checks [T]" 0 18
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 75809)
                     (#("reset [T]" 0 5
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 76023)
                     (#("check_byte [T]" 0 10
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 76530)
                     (#("clear_byte [T]" 0 10
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 76916)
                     (#("clear_range [T]" 0 11
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 77160)
                     (#("get_byte [T]" 0 8
                        (face
                         (:foreground "goldenrod" :weight bold)))
                      . 77470)))
                   ("*Initial blocks*"
                    ("automatic string       log_name;" . 82923))
                   ("*Always blocks*"
                    ("automatic aw_chan_t ar_beat;" . 79692))
                   ("*Localparams*"
                    ("unsigned" . 62767)
                    ("axi_pkg::size_t" . 62889)
                    ("unsigned" . 79308)
                    ("unsigned" . 79365))
                   ("*Top*"
                    ("axi_test" . 936)
                    ("axi_chan_logger" . 78095))))))

(ert-deftest imenu::instances ()
  (should (equal (verilog-ext-test-imenu-file "ucontroller.sv")
                 '(("*Instances*"
                    ("cpu" . 2331)
                    ("alu" . 3003)
                    ("dma" . 3205)
                    ("uart" . 3755)
                    ("ram_arbiter" . 4123)
                    ("ram" . 4593))
                   ("*Top*"
                    ("ucontroller" . 834)))))
  (should (equal (verilog-ext-test-imenu-file "instances.sv")
                 '(("*Instances*"
                    ("block0" . 860)
                    ("block1" . 1031)
                    ("block2" . 1168)
                    ("block3" . 1423)
                    ("block_gen" . 1693)
                    ("test_if" . 2017)
                    ("test_if_params" . 2068)
                    ("test_if_params_array" . 2169)
                    ("test_if_params_empty" . 2287)
                    ("block_ws_0" . 2401)
                    ("block_ws_1" . 2518))
                   ("*Generates*"
                    ("for (genvar i=0; i<VALUE; i++) begin : gen_test" . 1636))
                   ("*Top*"
                    ("instances" . 820)))))
  (should (equal (verilog-ext-test-imenu-file "axi_demux.sv")
                 '(("*Instances*"
                    ("spill_register" . 3689)
                    ("spill_register" . 4161)
                    ("spill_register" . 4622)
                    ("spill_register" . 5077)
                    ("spill_register" . 5549)
                    ("spill_register" . 9163)
                    ("spill_register" . 9668)
                    ("axi_demux_id_counters" . 13911)
                    ("counter" . 15375)
                    ("spill_register" . 16156)
                    ("spill_register" . 16714)
                    ("rr_arb_tree" . 17182)
                    ("spill_register" . 17879)
                    ("spill_register" . 18324)
                    ("axi_demux_id_counters" . 21519)
                    ("spill_register" . 23003)
                    ("rr_arb_tree" . 23471)
                    ("delta_counter" . 31764)
                    ("axi_demux" . 35418))
                   ("*Initial blocks*"
                    ("no_mst_ports: assume (NoMstPorts > 0) else" . 25927))
                   ("*Always blocks*"
                    ("// AXI Handshakes" . 10365)
                    ("// AXI Handshakes" . 18953)
                    ("// default assignments" . 24322)
                    ("unique case ({push_en[i], inject_en[i], pop_en[i]})" . 30693))
                   ("*Assigns*"
                    ("slv_resp_o.aw_ready" . 10172)
                    ("slv_aw_valid" . 10243)
                    ("lookup_aw_select" . 13749)
                    ("aw_select_occupied" . 13796)
                    ("aw_id_cnt_full" . 13836)
                    ("w_select" . 15929)
                    ("w_select_valid" . 15997)
                    ("slv_resp_o.ar_ready" . 18768)
                    ("slv_ar_valid" . 18839)
                    ("lookup_ar_select" . 21357)
                    ("ar_select_occupied" . 21404)
                    ("ar_id_cnt_full" . 21444)
                    ("ar_ready" . 24003)
                    ("aw_ready" . 24072)
                    ("mst_b_chans" . 25571)
                    ("mst_b_valids" . 25626)
                    ("mst_r_chans" . 25687)
                    ("mst_r_valids" . 25742)
                    ("lookup_mst_select_o" . 30067)
                    ("lookup_mst_select_occupied_o" . 30138)
                    ("push_en" . 30303)
                    ("inject_en" . 30366)
                    ("pop_en" . 30429)
                    ("full_o" . 30492)
                    ("occupied" . 32226)
                    ("cnt_full" . 32263))
                   ("*Defines*"
                    ("TARGET_VSIM" . 1013))
                   ("*Localparams*"
                    ("unsigned" . 3473)
                    ("unsigned" . 29683))
                   ("*Top*"
                    ("axi_demux" . 1869)
                    ("axi_demux_id_counters" . 28710)
                    ("axi_demux_intf" . 32905))))))

(ert-deftest imenu::generic ()
  (should (equal (verilog-ext-test-imenu-file "tb_program.sv")
                 '(("*Task/Func*"
                    ("init_rom" . 1876)
                    ("init_values" . 3482)
                    ("reset_system" . 3552)
                    ("serial_rx" . 3804))
                   ("*Initial blocks*"
                    ("$dumpfile(\"tb_top.lx2\");  // iverilog, vpp & gtkwave" . 1619)
                    ("init_rom;" . 4325)
                    ("#10ms;" . 4541))
                   ("*Assigns*"
                    ("ROM_Data" . 1829))
                   ("*Localparams*"
                    ("FREQ_CLK" . 1190)
                    ("TX_SPEED" . 1240)
                    ("BIT_CYCLES" . 1287))
                   ("*Top*"
                    ("tb_program" . 856))))))



(provide 'verilog-ext-tests-imenu)

;;; verilog-ext-tests-imenu.el ends here
