;;; verilog-ext-tests-navigation.el --- Verilog-Ext ERT Imenu tests  -*- lexical-binding: t -*-

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
;; ERT Navigation tests
;;
;;; Code:


;;;; Aux macros/defuns
(defmacro verilog-ext-test-navigation-file (file &rest body)
  (declare (indent 1) (debug t))
  `(with-temp-buffer
     (let ((print-level nil)
           (print-length nil)
           (eval-expression-print-level nil)
           (eval-expression-print-length nil)
           (default-directory (file-name-as-directory verilog-ext-tests-common-dir)))
       (insert-file-contents (verilog-ext-path-join verilog-ext-tests-common-dir ,file))
       (verilog-mode)
       ,@body)))

(defun verilog-ext-test-navigation-instances-fwd ()
  (let (var)
    (save-excursion
      (goto-char (point-min))
      (while (verilog-ext-find-module-instance-fwd)
        (push (point) var)))
    (reverse var)))

(defun verilog-ext-test-navigation-instances-bwd ()
  (let (var)
    (save-excursion
      (goto-char (point-max))
      (while (verilog-ext-find-module-instance-bwd)
        (push (point) var)))
    (reverse var)))

(defun verilog-ext-test-navigation-instances-fwd-interactive ()
  "Hack to emulate the point position when using interactive forward navigation.
For some reason, using `call-interactively' did not work with ERT in Emacs batch mode.
It did work locally though."
  (let (var)
    (save-excursion
      (goto-char (point-min))
      (while (and (verilog-ext-find-module-instance-fwd)
                  (goto-char (match-beginning 1)))
        (push (point) var)
        (forward-char)))
    (reverse var)))

(defun verilog-ext-test-navigation-instances-bwd-interactive ()
  "Hack to emulate the point position when using interactive forward navigation.
For some reason, using `call-interactively' did not work with ERT in Emacs batch mode.
It did work locally though."
  (let (var)
    (save-excursion
      (goto-char (point-max))
      (while (and (verilog-ext-find-module-instance-bwd)
                  (goto-char (match-beginning 1)))
        (push (point) var)))
    (reverse var)))

(defun verilog-ext-test-navigation-classes-fwd ()
  (let (var)
    (save-excursion
      (goto-char (point-min))
      (while (verilog-ext-find-class-fwd)
        (push (point) var)))
    (reverse var)))

(defun verilog-ext-test-navigation-task-functions-fwd ()
  (let (var)
    (save-excursion
      (goto-char (point-min))
      (while (verilog-ext-find-function-task-fwd)
        (push (point) var)))
    (reverse var)))

(defun verilog-ext-test-navigation-classes-bwd ()
  (let (var)
    (save-excursion
      (goto-char (point-max))
      (while (verilog-ext-find-class-bwd)
        (push (point) var)))
    (reverse var)))

(defun verilog-ext-test-navigation-task-functions-bwd ()
  (let (var)
    (save-excursion
      (goto-char (point-max))
      (while (verilog-ext-find-function-task-bwd)
        (push (point) var)))
    (reverse var)))

(defmacro verilog-ext-test-jump-parent-file (file &rest body)
  (declare (indent 1) (debug t))
  `(with-temp-buffer
     (let ((print-level nil)
           (print-length nil)
           (eval-expression-print-level nil)
           (eval-expression-print-length nil)
           (default-directory (file-name-as-directory verilog-ext-tests-jump-parent-dir)))
       (insert-file-contents (verilog-ext-path-join verilog-ext-tests-jump-parent-dir ,file))
       (verilog-mode)
       ,@body)))

(defun verilog-ext-test-random-from-range (start end)
  (+ start (random (+ 1 (- end start)))))


;;;; Tests
(ert-deftest navigation::instances-fwd ()
  (verilog-ext-test-navigation-file "instances.sv"
    (should (equal (verilog-ext-test-navigation-instances-fwd)
                   '(958 1128 1352 1604 1955 2065 2166 2284 2365 2515 2806))))
  (verilog-ext-test-navigation-file "ucontroller.sv"
    (should (equal (verilog-ext-test-navigation-instances-fwd)
                   '(2999 3201 3751 4119 4588 4859))))
  (verilog-ext-test-navigation-file "axi_demux.sv"
    (should (equal (verilog-ext-test-navigation-instances-fwd)
                   '(4159 4620 5075 5547 6002 9666 10170 15076 15848 16572 17131 17711 18322 18766 22853 23420 24000 32224 36653)))))

(ert-deftest navigation::instances-bwd ()
  (verilog-ext-test-navigation-file "instances.sv"
    (should (equal (verilog-ext-test-navigation-instances-bwd)
                   '(2522 2405 2291 2173 2072 2021 1705 1427 1172 1035 864))))
  (verilog-ext-test-navigation-file "ucontroller.sv"
    (should (equal (verilog-ext-test-navigation-instances-bwd)
                   '(4597 4127 3759 3209 3007 2335))))
  (verilog-ext-test-navigation-file "axi_demux.sv"
    (should (equal (verilog-ext-test-navigation-instances-bwd)
                   '(35420 31768 23475 23007 21525 18328 17883 17186 16718 16160 15379 13917 9672 9167 5553 5081 4626 4165 3693)))))

(ert-deftest navigation::instances-fwd-interactive ()
  (verilog-ext-test-navigation-file "instances.sv"
    (should (equal (verilog-ext-test-navigation-instances-fwd-interactive)
                   '(864 1035 1172 1427 1705 2021 2072 2173 2291 2405 2522))))
  (verilog-ext-test-navigation-file "ucontroller.sv"
    (should (equal (verilog-ext-test-navigation-instances-fwd-interactive)
                   '(2335 3007 3209 3759 4127 4597))))
  (verilog-ext-test-navigation-file "axi_demux.sv"
    (should (equal (verilog-ext-test-navigation-instances-fwd-interactive)
                   '(3693 4165 4626 5081 5553 9167 9672 13917 15379 16160 16718 17186 17883 18328 21525 23007 23475 31768 35420)))))

(ert-deftest navigation::instances-bwd-interactive ()
  (verilog-ext-test-navigation-file "instances.sv"
    (should (equal (verilog-ext-test-navigation-instances-bwd-interactive)
                   '(2522 2405 2291 2173 2072 2021 1705 1427 1172 1035 864))))
  (verilog-ext-test-navigation-file "ucontroller.sv"
    (should (equal (verilog-ext-test-navigation-instances-bwd-interactive)
                   '(4597 4127 3759 3209 3007 2335))))
  (verilog-ext-test-navigation-file "axi_demux.sv"
    (should (equal (verilog-ext-test-navigation-instances-bwd-interactive)
                   '(35420 31768 23475 23007 21525 18328 17883 17186 16718 16160 15379 13917 9672 9167 5553 5081 4626 4165 3693)))))

(ert-deftest navigation::classes-fwd ()
  (verilog-ext-test-navigation-file "axi_test.sv"
    (should (equal (verilog-ext-test-navigation-classes-fwd)
                   '(1040 6057 6733 7027 7275 7602 19038 41054 49114 55420 59679 62423))))
  (verilog-ext-test-navigation-file "uvm_component.svh"
    (should (equal (verilog-ext-test-navigation-classes-fwd)
                   '(1855)))))

(ert-deftest navigation::classes-bwd ()
  (verilog-ext-test-navigation-file "axi_test.sv"
    (should (equal (verilog-ext-test-navigation-classes-bwd)
                   '(62403 59662 55395 49088 41034 19017 7586 7259 7011 6717 6040 1019))))
  (verilog-ext-test-navigation-file "uvm_component.svh"
    (should (equal (verilog-ext-test-navigation-classes-bwd)
                   '(1836)))))

(ert-deftest navigation::task-functions-fwd ()
  (verilog-ext-test-navigation-file "axi_test.sv"
    (should (equal (verilog-ext-test-navigation-task-functions-fwd)
                   '(1323 1490 1827 2076 2122 2223 2658 3087 3423 3858 4290 4646
                          4998 5303 5659 8250 8472 9387 9779 9825 9926 11065 11601
                          12069 13136 13741 14468 14886 15271 16026 16489 17185 17573
                          17928 18650 22181 23010 23256 23444 23784 28288 31541 32924
                          33416 34529 36025 36592 37314 37983 38338 40039 40584 42747
                          43048 43351 43690 44102 46040 46725 47877 48896 50309 50674
                          50745 51094 51618 52136 52705 53403 53915 54274 54908 56356
                          56720 56795 57144 57540 58067 58463 58850 59491 60435 60653
                          64122 64438 64527 64669 66837 68086 70635 71547 72043 72510
                          73431 74105 74627 74771 74986 75136 75418 75567 75702 75818
                          76042 76549 76925 77179 77489))))
  (verilog-ext-test-navigation-file "tb_program.sv"
    (should (equal (verilog-ext-test-navigation-task-functions-fwd)
                   '(1876 3482 3552 3804))))
  (verilog-ext-test-navigation-file "uvm_component.svh"
    (should (equal (verilog-ext-test-navigation-task-functions-fwd)
                   '(2579 3232 3592 3966 4087 4177 4778 4982 5192 5408 5875 6139
                          7573 7838 8127 8429 9043 9811 10577 11349 12132 12910 13694
                          14471 15234 16003 16784 17560 18342 18615 18880 19143 19405
                          19739 21023 21364 21958 22180 23795 24177 24547 24879 24926
                          27233 27521 28227 28679 29371 29850 30823 31440 32043 33641
                          34449 35541 38032 39150 40421 40929 41753 42389 42678 42889
                          43510 43798 43926 44126 44824 45440 46290 47537 47907 48662
                          49316 50612 51043 51861 52750 53199 53384 53824 54200 54293
                          55722 55957 56032 56093 56157 56211 56263 56517 56579 56718
                          57295 57802 57908 57984 58105 58147 58185 58225 58262 58444
                          58610 59131 61930 62937 63127 63273 63417 63704 63845 63972
                          64256 64359 64698 65057 66038 66236 66777 66879 67220 67435
                          67723 68100 68526 68945 69423 69904 70643 71544 71856 72353
                          72734 73032 73520 73894 74152 74432 74909 75512 75831 75915
                          76011 76106 76182 76266 76348 76431 76584 76659 76734 76809
                          76884 76959 77034 77109 77184 77259 77334 77409 77902 78007
                          78125 78578 79480 79768 79945 80071 80224 80344 80720 81052
                          81572 81878 82045 82519 83373 86225 87004 88489 89965 90084
                          90317 90656 91112 91241 92304 92777 92888 93013 93278 93514
                          94406 95135 95625 95918 96304 97345 98519 99925 100736)))))

(ert-deftest navigation::task-functions-bwd ()
  (verilog-ext-test-navigation-file "axi_test.sv"
    (should (equal (verilog-ext-test-navigation-task-functions-bwd)
                   '(77474 77164 76920 76534 76027 75813 75697 75562 75413 75131
                           74981 74766 74622 74090 73406 72485 72018 71522 70610 68061
                           66812 64644 64502 64413 64113 60648 60426 59476 58835 58448
                           58052 57525 57129 56780 56706 56347 54893 54259 53900 53388
                           52690 52121 51603 51079 50730 50660 50300 48891 47872 46720
                           46035 44097 43685 43336 43034 42738 40579 40034 38333 37978
                           37309 36587 36020 34524 33403 32909 31527 28283 23765 23430
                           23242 22996 22172 18645 17923 17568 17180 16484 16021 15266
                           14881 14463 13736 13131 12064 11596 11060 9921 9820 9774 9373
                           8458 8241 5654 5298 4993 4641 4285 3853 3418 3082 2653 2218
                           2117 2071 1813 1476 1314))))
  (verilog-ext-test-navigation-file "tb_program.sv"
    (should (equal (verilog-ext-test-navigation-task-functions-bwd)
                   '(3799 3547 3477 1871))))
  (verilog-ext-test-navigation-file "uvm_component.svh"
    (should (equal (verilog-ext-test-navigation-task-functions-bwd)
                   '(100707 99896 98490 97316 96275 95889 95596 95106 94377
                            93485 93249 92984 92860 92748 92275 91212 91084 90625 90288
                            90055 89936 88461 86976 86196 83345 82490 82007 81849 81532
                            81024 80691 80315 80195 80051 79925 79733 79451 78549 78096
                            77978 77873 77389 77314 77239 77164 77089 77014 76939 76864
                            76789 76714 76639 76564 76402 76319 76237 76153 76077 75982
                            75886 75802 75483 74880 74403 74123 73865 73491 73003 72705
                            72324 71827 71515 70614 69874 69394 68916 68491 68062 67693
                            67399 67184 66850 66748 66207 66001 65019 64669 64330 64218
                            63941 63817 63676 63379 63245 63099 62908 61902 59107 58589
                            58430 58241 58204 58164 58126 58084 57953 57879 57773 57267
                            56688 56544 56482 56224 56172 56118 56054 55993 55918 55683
                            54264 54160 53795 53355 53161 52730 51841 51004 50591 49302
                            48642 47868 47516 46268 45419 44803 44105 43905 43777 43489
                            42868 42657 42368 41732 40908 40400 39122 38011 35513 34422
                            33611 32030 31418 30801 29829 29351 28658 28206 27493 27204
                            24903 24850 24527 24157 23756 22153 21937 21335 20994 19710
                            19376 19114 18851 18586 18322 17540 16764 15983 15214 14451
                            13674 12890 12112 11329 10557 9791 9023 8400 8098 7809 7544
                            6110 5845 5379 5172 4962 4758 4157 4057 3945 3561 3194 2563)))))

(ert-deftest navigation::jump-to-parent-module-ag ()
  (cl-letf (((symbol-function 'compilation-start)
             (lambda (command &optional mode name-function highlight-regexp)
               (butlast (split-string (shell-command-to-string command) "\n") 4))))
    (let ((verilog-ext-jump-to-parent-module-engine "ag")
          (ag-arguments '("--smart-case" "--stats" "--nogroup" "--ignore-dir=test/files/beautify" "--ignore-dir=test/files/indent"))) ; Ignore instances.sv beautified file
      ;; block0
      (verilog-ext-test-jump-parent-file "block0.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("[1;32mtest/files/common/instances.sv[0m[K:[1;33m23[0m[K:5:    [30;43mblock0[0m[K I_BLOCK0 (" "1 matches" "1 files contained matches"))))
      ;; block1
      (verilog-ext-test-jump-parent-file "block1.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("[1;32mtest/files/common/instances.sv[0m[K:[1;33m30[0m[K:5:    [30;43mblock1[0m[K I_BLOCK1(" "1 matches" "1 files contained matches"))))
      ;; block2
      (verilog-ext-test-jump-parent-file "block2.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("[1;32mtest/files/common/instances.sv[0m[K:[1;33m37[0m[K:5:    [30;43mblock2[0m[K #(" "1 matches" "1 files contained matches"))))
      ;; block3
      (verilog-ext-test-jump-parent-file "block3.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("[1;32mtest/files/common/instances.sv[0m[K:[1;33m48[0m[K:5:    [30;43mblock3[0m[K#(" "1 matches" "1 files contained matches"))))
      ;; block_gen
      (verilog-ext-test-jump-parent-file "block_gen.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("[1;32mtest/files/common/instances.sv[0m[K:[1;33m62[0m[K:13:            [30;43mblock_gen[0m[K #(" "1 matches" "1 files contained matches"))))
      ;; test_if
      (verilog-ext-test-jump-parent-file "test_if.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("[1;32mtest/files/common/instances.sv[0m[K:[1;33m77[0m[K:5:    [30;43mtest_if[0m[K I_TEST_IF (.clk(clk), .rst_n(rst_n));" "1 matches" "1 files contained matches"))))
      ;; test_if_params
      (verilog-ext-test-jump-parent-file "test_if_params.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("[1;32mtest/files/common/instances.sv[0m[K:[1;33m79[0m[K:5:    [30;43mtest_if_params[0m[K # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS (.clk(clk), .rst_n(rst_n));" "1 matches" "1 files contained matches"))))
      ;; test_if_params_array
      (verilog-ext-test-jump-parent-file "test_if_params_array.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("[1;32mtest/files/common/instances.sv[0m[K:[1;33m81[0m[K:5:    [30;43mtest_if_params_array[0m[K # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS_ARRAY[5:0] (.clk(clk), .rst_n(rst_n));" "1 matches" "1 files contained matches"))))
      ;; test_if_params_empty
      (verilog-ext-test-jump-parent-file "test_if_params_empty.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("[1;32mtest/files/common/instances.sv[0m[K:[1;33m83[0m[K:5:    [30;43mtest_if_params_empty[0m[K #() I_TEST_IF_PARAMS_EMPTY (.clk(clk), .rst_n(rst_n));" "1 matches" "1 files contained matches"))))
      ;; block_ws_0
      (verilog-ext-test-jump-parent-file "block_ws_0.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("[1;32mtest/files/common/instances.sv[0m[K:[1;33m87[0m[K:5:    [30;43mblock_ws_0[0m[K" "1 matches" "1 files contained matches"))))
      ;; block_ws_1 (TODO: Referenced in instances.sv:94 but not working with current regexp)
      (verilog-ext-test-jump-parent-file "block_ws_1.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("0 matches" "0 files contained matches")))))))


(defvar verilog-ext-test-navigation-defun-level-up
  '(("tb_program.sv" ((855 . nil)
                      (1068 . ("(" . 884))
                      (1143 . ("tb_program" . 856))
                      (1684 . ("unnamed" . 1605))
                      (1829 . ("tb_program" . 856))
                      (2589 . ("init_rom" . 1871))
                      (3495 . ("init_values" . 3477))
                      (4413 . ("unnamed" . 4311))
                      (4635 . ("tb_program" . 856))
                      (4658 . nil)))
    ("axi_test.sv" ((883 . nil)
                    (936 . nil)
                    (954 . ("axi_test" . 936))
                    (1074 . ("(" . 1042))
                    (1218 . ("axi_lite_driver" . 1019))
                    (1272 . ("(" . 1243))
                    (1433 . ("new" . 1314))
                    (1471 . ("axi_lite_driver" . 1019))
                    (1636 . ("reset_master" . 1476))
                    (5977 . ("axi_test" . 936))
                    (21939 . ("(" . 21908))
                    (22413 . ("begin" . 22407))
                    (86894 . nil)
                    ))
    ("uvm_component.svh" ((1357 . nil)
                          (1516 . nil)
                          (1883 . ("uvm_component" . 1836))
                          (2595 . ("(" . 2583))
                          (58464 . ("uvm_component" . 1836))
                          (58659 . ("uvm_component" . 1836))
                          (58685 . nil)
                          (59192 . ("new" . 59107))
                          (59412 . ("begin" . 59373))
                          (59984 . ("(" . 59908))
                          (59908 . ("(" . 59897))
                          (59897 . ("begin" . 59869))
                          (59869 . ("begin" . 59546))
                          (59546 . ("new" . 59107))
                          (100840 . nil)))))

(ert-deftest navigation::defun-level-up ()
  (let ((alist verilog-ext-test-navigation-defun-level-up)
        file data block end-pos)
    (dolist (elm alist)
      (setq file (car elm))
      (setq data (cadr elm))
      (verilog-ext-test-navigation-file file
        (dolist (pos-type data)
          (goto-char (car pos-type))
          (if (cdr pos-type)
              (progn
                (setq block (cadr pos-type))
                (setq end-pos (cddr pos-type)))
            (setq block nil))
          (should (string= (verilog-ext-defun-level-up) block))
          (when block
            (should (equal (point) end-pos))))))))

(defvar verilog-ext-test-navigation-defun-level-down
  '(("tb_program.sv" ((855 . nil)
                      (1004 . nil)
                      (1189 . ("init_rom" . 1876))
                      (1680 . nil) ; Inside initial
                      (2029 . nil) ; Inside task
                      (3459 . ("init_values" . 3482))
                      (3602 . (")" . 3603))
                      (3885 . ("begin" . 4007))
                      (4007 . nil)))
    ;; TODO: If running it over parameterized classes/functions (with parenthesis expr) ...
    ;; ... running it again will move to next class/function
    ("axi_test.sv" ((883 . nil)
                    (936 . nil)
                    (954 . ("axi_lite_driver" . 1040))
                    (1074 . (")" . 1074))
                    (1245 . (")" . 1267))
                    (1309 . ("new" . 1323))
                    (1328 . (")" . 1356))
                    (1356 . (")" . 1381))
                    (1381 . (")" . 1381))
                    (1433 . nil)
                    (1471 . ("reset_master" . 1490))
                    (1490 . nil)
                    (2337 . ("begin" . 2456))
                    (2456 . nil)
                    (2337 . ("begin" . 2456))
                    ;; Trying nested begin/ends
                    (26583 . ("begin" . 26589))
                    (26589 . ("begin" . 26699))
                    (26699 . ("begin" . 27501))
                    (27501 . ("begin" . 27586))
                    (27586 . nil)
                    (86894 . nil)))
    ;; TODO: If running it over extern functions/tasks definitions...
    ;; ... running it again will move to next class/function declaration
    ("uvm_component.svh" ((1261 . nil)
                          (1357 . nil)
                          (1883 . ("new" . 2579))
                          (2703 . ("get_parent" . 3232))
                          (48756 . (")" . 48756))
                          (59192 . ("begin" . 59378))
                          (59464 . ("begin" . 59551))
                          (59551 . ("begin" . 59874))
                          (59874 . nil)
                          (60416 . (")" . 60417))
                          (60417 . (")" . 60436))
                          (60436 . (")" . 60436))
                          (100840 . nil)))))

(ert-deftest navigation::defun-level-down ()
  (let ((alist verilog-ext-test-navigation-defun-level-down)
        file data block end-pos)
    (dolist (elm alist)
      (setq file (car elm))
      (setq data (cadr elm))
      (verilog-ext-test-navigation-file file
        (dolist (pos-type data)
          (goto-char (car pos-type))
          (if (cdr pos-type)
              (progn
                (setq block (cadr pos-type))
                (setq end-pos (cddr pos-type)))
            (setq block nil))
          (when block
            (should (string= (verilog-ext-defun-level-down) block))
            (should (equal (point) end-pos))))))))


(defvar verilog-ext-test-navigation-instance-at-point
  '(("ucontroller.sv" ((833 . nil)
                       (1072 . nil)
                       (1530 . nil)
                       (2334 . nil)
                       (2335 . "cpu")
                       (2346 . "cpu")
                       (2539 . "cpu")
                       (2975 . "cpu")
                       (2999 . "cpu")
                       (3000 . nil)
                       (3112 . "alu")
                       (3204 . nil)
                       (3337 . "dma")
                       (3768 . "uart")
                       (3939 . "uart")
                       (4122 . nil)
                       (4399 . "ram_arbiter")
                       (4592 . nil)
                       (4722 . "ram")
                       (4862 . nil)
                       (4888 . nil)))
    ("instances.sv" ((819 . nil)
                     (838 . nil)
                     (906 . "block0")
                     (960 . nil)
                     (1076 . "block1")
                     (1130 . nil)
                     (1208 . "block2")
                     (1300 . "block2")
                     (1355 . nil)
                     (1462 . "block3")
                     (1552 . "block3")
                     (1607 . nil)
                     (1692 . nil)
                     (1692 . nil)
                     (1705 . "block_gen")
                     (1955 . "block_gen")
                     (1956 . nil)
                     (2017 . nil)
                     (2021 . "test_if")
                     (2065 . "test_if")
                     (2066 . nil)
                     (2103 . "test_if_params")
                     (2254 . "test_if_params_array")
                     (2314 . "test_if_params_empty")
                     (2368 . nil)
                     (2405 . "block_ws_0")
                     (2515 . "block_ws_0")
                     (2516 . nil)
                     (2602 . "block_ws_1")
                     (2730 . "block_ws_1")
                     (2808 . nil)
                     (2821 . nil)))))

(ert-deftest navigation::instance-at-point ()
  (let ((alist verilog-ext-test-navigation-instance-at-point)
        file data block)
    (dolist (elm alist)
      (setq file (car elm))
      (setq data (cadr elm))
      (verilog-ext-test-navigation-file file
        (dolist (pos-type data)
          (goto-char (car pos-type))
          (if (cdr pos-type)
              (setq block (cdr pos-type))
            (setq block nil))
          (should (string= (car (verilog-ext-instance-at-point)) block)))))))



(provide 'verilog-ext-tests-navigation)

;;; verilog-ext-tests-navigation.el ends here
