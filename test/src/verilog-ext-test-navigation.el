;;; verilog-ext-test-navigation.el --- Verilog-Ext ERT navigation tests  -*- lexical-binding: t -*-

;; Copyright (C) 2022-2025 Gonzalo Larumbe

;; Author: Gonzalo Larumbe <gonzalomlarumbe@gmail.com>
;; URL: https://github.com/gmlarumbe/test-hdl

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
;; Verilog-Ext ERT navigation tests
;;
;;; Code:

(defconst verilog-ext-test-ref-dir-navigation (file-name-concat verilog-ext-test-ref-dir "navigation"))
(defconst verilog-ext-test-dump-dir-navigation (file-name-concat verilog-ext-test-dump-dir "navigation"))

(defconst verilog-ext-test-navigation-jump-to-parent-file-list
  (test-hdl-directory-files (file-name-concat verilog-ext-test-files-dir "subblocks") verilog-ext-file-extension-re))

(defconst verilog-ext-test-navigation-rtl-file-list (mapcar (lambda (file)
                                                              (file-name-concat verilog-ext-test-files-common-dir file))
                                                            '("instances.sv"
                                                              "ucontroller.sv"
                                                              "axi_demux.sv")))
(defconst verilog-ext-test-navigation-tb-file-list (mapcar (lambda (file)
                                                             (file-name-concat verilog-ext-test-files-common-dir file))
                                                           '("axi_test.sv"
                                                             "tb_program.sv"
                                                             "uvm_component.svh")))

(defconst verilog-ext-test-navigation-block-nav-file-list verilog-ext-test-common-file-list)

(defconst verilog-ext-test-navigation-defun-up-file-and-pos
  `((,(file-name-concat verilog-ext-test-files-common-dir "tb_program.sv") 855 1068 1143 1684 1829 2589 3495 4413 4635 4658)
    (,(file-name-concat verilog-ext-test-files-common-dir "axi_test.sv") 883 936 954 1074 1218 1272 1433 1471 1636 5977 21939 22413 86894)
    (,(file-name-concat verilog-ext-test-files-common-dir "uvm_component.svh") 1357 1516 1883 2595 58464 58659 58685 59192 59412 59984 59908 59897 59869 59546 100840)))

(defconst verilog-ext-test-navigation-defun-down-file-and-pos
  `((,(file-name-concat verilog-ext-test-files-common-dir "tb_program.sv") 855 1004 1189 1680 2029 3459 3602 3885 4007)
    (,(file-name-concat verilog-ext-test-files-common-dir "axi_test.sv") 883 936 954 1074 1245 1309 1328 1356 1381 1433 1471 1490 2337 2456 2337 26583 26589 26699 27501 27586 86894)
    (,(file-name-concat verilog-ext-test-files-common-dir "uvm_component.svh") 1261 1357 1883 2703 48756 59192 59464 59551 59874 60416 60417 60436 100840)))



(cl-defun verilog-ext-test-jump-to-parent-module (&key mode engine)
  (cl-letf (((symbol-function 'compilation-start)
             (lambda (command &optional mode name-function highlight-regexp)
               (butlast (split-string (shell-command-to-string command) "\n") 4)))
            ((symbol-function 'verilog-ext-buffer-proj-root)
             (lambda (&optional project)
               verilog-ext-test-files-common-dir)))
    (let* ((verilog-ext-jump-to-parent-module-engine engine)
           ;; INFO: Using let-binding in ripgrep.el arguments for compatibility with release 0.4.0 (Feb 2017) for MELPA Stable tests
           ;;
           ;; From man rg(1):
           ;;
           ;; --vimgrep
           ;;     Show results with every match on its own line, including line
           ;;     numbers and column numbers. With this option, a line with more than
           ;;     one match will be printed more than once.
           (ripgrep-highlight-search nil)
           (ripgrep-arguments '("--vimgrep")))
      ;; Core after all the function setup, using default args for ag and rg
      (funcall mode)
      (verilog-ext-jump-to-parent-module))))

(defun verilog-ext-test-navigation-interactive-fwd-fn ()
  "Hack to emulate the point position when using interactive navigation.
For some reason, using `call-interactively' did not work with ERT in Emacs batch mode.
It did work locally though."
  (and (verilog-ext-find-module-instance-fwd)
       (goto-char (match-beginning 1))))

(defun verilog-ext-test-navigation-interactive-bwd-fn ()
  "Hack to emulate the point position when using interactive forward navigation.
For some reason, using `call-interactively' did not work with ERT in Emacs batch mode.
It did work locally though."
  (and (verilog-ext-find-module-instance-bwd)
       (goto-char (match-beginning 1))))


(defun verilog-ext-test-navigation-gen-expected-files ()
  ;; Instances fwd
  (test-hdl-gen-expected-files :file-list verilog-ext-test-navigation-rtl-file-list
                               :dest-dir verilog-ext-test-ref-dir-navigation
                               :out-file-ext "inst.fwd.el"
                               :process-fn 'eval
                               :fn #'test-hdl-navigation-nav-file-fn
                               :args '(:mode verilog-mode
                                       :fn verilog-ext-find-module-instance-fwd))
  ;; Instances bwd
  (test-hdl-gen-expected-files :file-list verilog-ext-test-navigation-rtl-file-list
                               :dest-dir verilog-ext-test-ref-dir-navigation
                               :out-file-ext "inst.bwd.el"
                               :process-fn 'eval
                               :fn #'test-hdl-navigation-nav-file-fn
                               :args '(:mode verilog-mode
                                       :fn verilog-ext-find-module-instance-bwd
                                       :start-pos-max t))
  ;; Instances fwd interactive
  (test-hdl-gen-expected-files :file-list verilog-ext-test-navigation-rtl-file-list
                               :dest-dir verilog-ext-test-ref-dir-navigation
                               :out-file-ext "inst_int.fwd.el"
                               :process-fn 'eval
                               :fn #'test-hdl-navigation-nav-file-fn
                               :args '(:mode verilog-mode
                                       :fn verilog-ext-test-navigation-interactive-fwd-fn
                                       :while-hook forward-char))
  ;; Instances bwd interactive
  (test-hdl-gen-expected-files :file-list verilog-ext-test-navigation-rtl-file-list
                               :dest-dir verilog-ext-test-ref-dir-navigation
                               :out-file-ext "inst_int.bwd.el"
                               :process-fn 'eval
                               :fn #'test-hdl-navigation-nav-file-fn
                               :args '(:mode verilog-mode
                                       :fn verilog-ext-test-navigation-interactive-bwd-fn
                                       :start-pos-max t))
  ;; Instances fwd (ts-mode)
  (test-hdl-gen-expected-files :file-list verilog-ext-test-navigation-rtl-file-list
                               :dest-dir verilog-ext-test-ref-dir-navigation
                               :out-file-ext "ts.inst.fwd.el"
                               :process-fn 'eval
                               :fn #'test-hdl-navigation-nav-file-fn
                               :args '(:mode verilog-ts-mode
                                       :fn verilog-ext-find-module-instance-fwd))
  ;; Instances bwd (ts-mode)
  (test-hdl-gen-expected-files :file-list verilog-ext-test-navigation-rtl-file-list
                               :dest-dir verilog-ext-test-ref-dir-navigation
                               :out-file-ext "ts.inst.bwd.el"
                               :process-fn 'eval
                               :fn #'test-hdl-navigation-nav-file-fn
                               :args '(:mode verilog-ts-mode
                                       :fn verilog-ext-find-module-instance-bwd
                                       :start-pos-max t))
  ;; Classes fwd
  (test-hdl-gen-expected-files :file-list verilog-ext-test-navigation-tb-file-list
                               :dest-dir verilog-ext-test-ref-dir-navigation
                               :out-file-ext "class.fwd.el"
                               :process-fn 'eval
                               :fn #'test-hdl-navigation-nav-file-fn
                               :args '(:mode verilog-mode
                                       :fn verilog-ext-find-class-fwd))
  ;; Classes bwd
  (test-hdl-gen-expected-files :file-list verilog-ext-test-navigation-tb-file-list
                               :dest-dir verilog-ext-test-ref-dir-navigation
                               :out-file-ext "class.bwd.el"
                               :process-fn 'eval
                               :fn #'test-hdl-navigation-nav-file-fn
                               :args '(:mode verilog-mode
                                       :fn verilog-ext-find-class-bwd
                                       :start-pos-max t))
  ;; Classes fwd (ts-mode)
  (test-hdl-gen-expected-files :file-list verilog-ext-test-navigation-tb-file-list
                               :dest-dir verilog-ext-test-ref-dir-navigation
                               :out-file-ext "ts.class.fwd.el"
                               :process-fn 'eval
                               :fn #'test-hdl-navigation-nav-file-fn
                               :args '(:mode verilog-ts-mode
                                       :fn verilog-ext-find-class-fwd))
  ;; Classes bwd (ts-mode)
  (test-hdl-gen-expected-files :file-list verilog-ext-test-navigation-tb-file-list
                               :dest-dir verilog-ext-test-ref-dir-navigation
                               :out-file-ext "ts.class.bwd.el"
                               :process-fn 'eval
                               :fn #'test-hdl-navigation-nav-file-fn
                               :args '(:mode verilog-ts-mode
                                       :fn verilog-ext-find-class-bwd
                                       :start-pos-max t))
  ;; Task-functions fwd
  (test-hdl-gen-expected-files :file-list verilog-ext-test-navigation-tb-file-list
                               :dest-dir verilog-ext-test-ref-dir-navigation
                               :out-file-ext "tf.fwd.el"
                               :process-fn 'eval
                               :fn #'test-hdl-navigation-nav-file-fn
                               :args '(:mode verilog-mode
                                       :fn verilog-ext-find-function-task-fwd))
  ;; Task-functions bwd
  (test-hdl-gen-expected-files :file-list verilog-ext-test-navigation-tb-file-list
                               :dest-dir verilog-ext-test-ref-dir-navigation
                               :out-file-ext "tf.bwd.el"
                               :process-fn 'eval
                               :fn #'test-hdl-navigation-nav-file-fn
                               :args '(:mode verilog-mode
                                       :fn verilog-ext-find-function-task-bwd
                                       :start-pos-max t))
  ;; Task-functions fwd (ts-mode)
  (test-hdl-gen-expected-files :file-list verilog-ext-test-navigation-tb-file-list
                               :dest-dir verilog-ext-test-ref-dir-navigation
                               :out-file-ext "ts.tf.fwd.el"
                               :process-fn 'eval
                               :fn #'test-hdl-navigation-nav-file-fn
                               :args '(:mode verilog-ts-mode
                                       :fn verilog-ext-find-function-task-fwd))
  ;; Task-functions bwd (ts-mode)
  (test-hdl-gen-expected-files :file-list verilog-ext-test-navigation-tb-file-list
                               :dest-dir verilog-ext-test-ref-dir-navigation
                               :out-file-ext "ts.tf.bwd.el"
                               :process-fn 'eval
                               :fn #'test-hdl-navigation-nav-file-fn
                               :args '(:mode verilog-ts-mode
                                       :fn verilog-ext-find-function-task-bwd
                                       :start-pos-max t))
  ;; Jump-to-parent ag
  (test-hdl-gen-expected-files :file-list verilog-ext-test-navigation-jump-to-parent-file-list
                               :dest-dir verilog-ext-test-ref-dir-navigation
                               :out-file-ext "ag"
                               :process-fn 'eval
                               :fn #'verilog-ext-test-jump-to-parent-module
                               :args `(:mode verilog-mode
                                       :engine "ag"))
  ;; Jump-to-parent rg
  (test-hdl-gen-expected-files :file-list verilog-ext-test-navigation-jump-to-parent-file-list
                               :dest-dir verilog-ext-test-ref-dir-navigation
                               :out-file-ext "rg"
                               :process-fn 'eval
                               :fn #'verilog-ext-test-jump-to-parent-module
                               :args `(:mode verilog-mode
                                       :engine "rg"))
  ;; Defun level up
  (dolist (file-and-pos verilog-ext-test-navigation-defun-up-file-and-pos)
    (let ((file (car file-and-pos))
          (pos-list (cdr file-and-pos)))
      (test-hdl-gen-expected-files :file-list `(,file)
                                   :dest-dir verilog-ext-test-ref-dir-navigation
                                   :out-file-ext "defun.up.el"
                                   :process-fn 'eval
                                   :fn #'test-hdl-pos-list-fn
                                   :args `(:mode verilog-mode
                                           :fn verilog-ext-defun-level-up
                                           :pos-list ,pos-list))))
  ;; Defun level down
  (dolist (file-and-pos verilog-ext-test-navigation-defun-down-file-and-pos)
    (let ((file (car file-and-pos))
          (pos-list (cdr file-and-pos)))
      (test-hdl-gen-expected-files :file-list `(,file)
                                   :dest-dir verilog-ext-test-ref-dir-navigation
                                   :out-file-ext "defun.down.el"
                                   :process-fn 'eval
                                   :fn #'test-hdl-pos-list-fn
                                   :args `(:mode verilog-mode
                                           :fn verilog-ext-defun-level-down
                                           :pos-list ,pos-list)))))


(ert-deftest navigation::instances ()
  (dolist (file verilog-ext-test-navigation-rtl-file-list)
    ;; Forward
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-navigation (test-hdl-basename file "inst.fwd.el"))
                                                         :process-fn 'eval
                                                         :fn #'test-hdl-navigation-nav-file-fn
                                                         :args '(:mode verilog-mode
                                                                 :fn verilog-ext-find-module-instance-fwd))
                                  (file-name-concat verilog-ext-test-ref-dir-navigation (test-hdl-basename file "inst.fwd.el"))))
    ;; Backward
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-navigation (test-hdl-basename file "inst.bwd.el"))
                                                         :process-fn 'eval
                                                         :fn #'test-hdl-navigation-nav-file-fn
                                                         :args '(:mode verilog-mode
                                                                 :fn verilog-ext-find-module-instance-bwd
                                                                 :start-pos-max t))
                                  (file-name-concat verilog-ext-test-ref-dir-navigation (test-hdl-basename file "inst.bwd.el"))))
    ;; Forward interactive
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-navigation (test-hdl-basename file "inst_int.fwd.el"))
                                                         :process-fn 'eval
                                                         :fn #'test-hdl-navigation-nav-file-fn
                                                         :args '(:mode verilog-mode
                                                                 :fn verilog-ext-test-navigation-interactive-fwd-fn
                                                                 :while-hook forward-char))
                                  (file-name-concat verilog-ext-test-ref-dir-navigation (test-hdl-basename file "inst_int.fwd.el"))))
    ;; Backward interactive
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-navigation (test-hdl-basename file "inst_int.bwd.el"))
                                                         :process-fn 'eval
                                                         :fn #'test-hdl-navigation-nav-file-fn
                                                         :args '(:mode verilog-mode
                                                                 :fn verilog-ext-test-navigation-interactive-bwd-fn
                                                                 :start-pos-max t))
                                  (file-name-concat verilog-ext-test-ref-dir-navigation (test-hdl-basename file "inst_int.bwd.el"))))))


(ert-deftest navigation::instances-ts-mode ()
  (dolist (file verilog-ext-test-navigation-rtl-file-list)
    ;; Forward
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-navigation (test-hdl-basename file "ts.inst.fwd.el"))
                                                         :process-fn 'eval
                                                         :fn #'test-hdl-navigation-nav-file-fn
                                                         :args '(:mode verilog-ts-mode
                                                                 :fn verilog-ext-find-module-instance-fwd))
                                  (file-name-concat verilog-ext-test-ref-dir-navigation (test-hdl-basename file "ts.inst.fwd.el"))))
    ;; Backward
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-navigation (test-hdl-basename file "ts.inst.bwd.el"))
                                                         :process-fn 'eval
                                                         :fn #'test-hdl-navigation-nav-file-fn
                                                         :args '(:mode verilog-ts-mode
                                                                 :fn verilog-ext-find-module-instance-bwd
                                                                 :start-pos-max t))
                                  (file-name-concat verilog-ext-test-ref-dir-navigation (test-hdl-basename file "ts.inst.bwd.el"))))))


(ert-deftest navigation::classes ()
  (dolist (file verilog-ext-test-navigation-tb-file-list)
    ;; Forward
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-navigation (test-hdl-basename file "class.fwd.el"))
                                                         :process-fn 'eval
                                                         :fn #'test-hdl-navigation-nav-file-fn
                                                         :args '(:mode verilog-mode
                                                                 :fn verilog-ext-find-class-fwd))
                                  (file-name-concat verilog-ext-test-ref-dir-navigation (test-hdl-basename file "class.fwd.el"))))
    ;; Backward
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-navigation (test-hdl-basename file "class.bwd.el"))
                                                         :process-fn 'eval
                                                         :fn #'test-hdl-navigation-nav-file-fn
                                                         :args '(:mode verilog-mode
                                                                 :fn verilog-ext-find-class-bwd
                                                                 :start-pos-max t))
                                  (file-name-concat verilog-ext-test-ref-dir-navigation (test-hdl-basename file "class.bwd.el"))))))


(ert-deftest navigation::classes-ts-mode ()
  (dolist (file verilog-ext-test-navigation-tb-file-list)
    ;; Forward
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-navigation (test-hdl-basename file "ts.class.fwd.el"))
                                                         :process-fn 'eval
                                                         :fn #'test-hdl-navigation-nav-file-fn
                                                         :args '(:mode verilog-ts-mode
                                                                 :fn verilog-ext-find-class-fwd))
                                  (file-name-concat verilog-ext-test-ref-dir-navigation (test-hdl-basename file "ts.class.fwd.el"))))
    ;; Backward
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-navigation (test-hdl-basename file "ts.class.bwd.el"))
                                                         :process-fn 'eval
                                                         :fn #'test-hdl-navigation-nav-file-fn
                                                         :args '(:mode verilog-ts-mode
                                                                 :fn verilog-ext-find-class-bwd
                                                                 :start-pos-max t))
                                  (file-name-concat verilog-ext-test-ref-dir-navigation (test-hdl-basename file "ts.class.bwd.el"))))))


(ert-deftest navigation::task-functions ()
  (dolist (file verilog-ext-test-navigation-tb-file-list)
    ;; Forward
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-navigation (test-hdl-basename file "tf.fwd.el"))
                                                         :process-fn 'eval
                                                         :fn #'test-hdl-navigation-nav-file-fn
                                                         :args '(:mode verilog-mode
                                                                 :fn verilog-ext-find-function-task-fwd))
                                  (file-name-concat verilog-ext-test-ref-dir-navigation (test-hdl-basename file "tf.fwd.el"))))
    ;; Backward
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-navigation (test-hdl-basename file "tf.bwd.el"))
                                                         :process-fn 'eval
                                                         :fn #'test-hdl-navigation-nav-file-fn
                                                         :args '(:mode verilog-mode
                                                                 :fn verilog-ext-find-function-task-bwd
                                                                 :start-pos-max t))
                                  (file-name-concat verilog-ext-test-ref-dir-navigation (test-hdl-basename file "tf.bwd.el"))))))


(ert-deftest navigation::task-functions-ts-mode ()
  (dolist (file verilog-ext-test-navigation-tb-file-list)
    ;; Forward
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-navigation (test-hdl-basename file "ts.tf.fwd.el"))
                                                         :process-fn 'eval
                                                         :fn #'test-hdl-navigation-nav-file-fn
                                                         :args '(:mode verilog-ts-mode
                                                                 :fn verilog-ext-find-function-task-fwd))
                                  (file-name-concat verilog-ext-test-ref-dir-navigation (test-hdl-basename file "ts.tf.fwd.el"))))
    ;; Backward
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-navigation (test-hdl-basename file "ts.tf.bwd.el"))
                                                         :process-fn 'eval
                                                         :fn #'test-hdl-navigation-nav-file-fn
                                                         :args '(:mode verilog-ts-mode
                                                                 :fn verilog-ext-find-function-task-bwd
                                                                 :start-pos-max t))
                                  (file-name-concat verilog-ext-test-ref-dir-navigation (test-hdl-basename file "ts.tf.bwd.el"))))))


(ert-deftest navigation::jump-to-parent-module-ag ()
  ;; INFO: block_ws_1 referenced in instances.sv:94 but not working with current regexp
  (dolist (file verilog-ext-test-navigation-jump-to-parent-file-list)
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-navigation (test-hdl-basename file "ag"))
                                                         :process-fn 'eval
                                                         :fn #'verilog-ext-test-jump-to-parent-module
                                                         :args '(:mode verilog-mode
                                                                 :engine "ag"))
                                  (file-name-concat verilog-ext-test-ref-dir-navigation (test-hdl-basename file "ag"))))))


(ert-deftest navigation::jump-to-parent-module-rg ()
  ;; INFO: block_ws_1 referenced in instances.sv:94 but not working with current regexp
  (dolist (file verilog-ext-test-navigation-jump-to-parent-file-list)
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-navigation (test-hdl-basename file "rg"))
                                                         :process-fn 'eval
                                                         :fn #'verilog-ext-test-jump-to-parent-module
                                                         :args '(:mode verilog-mode
                                                                 :engine "rg"))
                                  (file-name-concat verilog-ext-test-ref-dir-navigation (test-hdl-basename file "rg"))))))


(ert-deftest navigation::defun-level-up ()
  (dolist (file-and-pos verilog-ext-test-navigation-defun-up-file-and-pos)
    (let ((file (car file-and-pos))
          (pos-list (cdr file-and-pos)))
      (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                           :dump-file (file-name-concat verilog-ext-test-dump-dir-navigation (test-hdl-basename file "defun.up.el"))
                                                           :process-fn 'eval
                                                           :fn #'test-hdl-pos-list-fn
                                                           :args `(:mode verilog-mode
                                                                   :fn verilog-ext-defun-level-up
                                                                   :pos-list ,pos-list))
                                    (file-name-concat verilog-ext-test-ref-dir-navigation (test-hdl-basename file "defun.up.el")))))))


(ert-deftest navigation::defun-level-down ()
  (dolist (file-and-pos verilog-ext-test-navigation-defun-down-file-and-pos)
    (let ((file (car file-and-pos))
          (pos-list (cdr file-and-pos)))
      (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                           :dump-file (file-name-concat verilog-ext-test-dump-dir-navigation (test-hdl-basename file "defun.down.el"))
                                                           :process-fn 'eval
                                                           :fn #'test-hdl-pos-list-fn
                                                           :args `(:mode verilog-mode
                                                                   :fn verilog-ext-defun-level-down
                                                                   :pos-list ,pos-list))
                                    (file-name-concat verilog-ext-test-ref-dir-navigation (test-hdl-basename file "defun.down.el")))))))



(provide 'verilog-ext-test-navigation)

;;; verilog-ext-test-navigation.el ends here
