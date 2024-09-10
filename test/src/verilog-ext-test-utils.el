;;; verilog-ext-test-utils.el --- Verilog-Ext ERT utils tests  -*- lexical-binding: t -*-

;; Copyright (C) 2022-2024 Gonzalo Larumbe

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
;; Verilog-Ext ERT utils tests
;;
;;; Code:

(defconst verilog-ext-test-utils-file-list verilog-ext-test-common-file-list)
(defconst verilog-ext-test-ref-dir-utils (file-name-concat verilog-ext-test-ref-dir "utils"))
(defconst verilog-ext-test-dump-dir-utils (file-name-concat verilog-ext-test-dump-dir "utils"))

(defconst verilog-ext-test-dummy-file-list `(,(file-name-concat verilog-ext-test-files-common-dir "instances.sv")))
(defconst verilog-ext-test-utils-proj-name "verilog-ext-test-utils")


(defconst verilog-ext-test-utils-block-at-point-file-and-pos
  `((,(file-name-concat verilog-ext-test-files-common-dir "ucontroller.sv") 839 840 988 1288 2699 4873 4874 4888)
    (,(file-name-concat verilog-ext-test-files-common-dir "instances.sv") 820 826 906 1423 1623 1627 1634 1635 1764 1984 1995 1996 2632 2810 2819 2820)
    (,(file-name-concat verilog-ext-test-files-common-dir "tb_program.sv") 855 975 1287 1619 1781 1866 1889 2029 3436 3459 3495 3515 3541 3643 4343 4556 4634 4635 4645)
    (,(file-name-concat verilog-ext-test-files-common-dir "uvm_component.svh") 1790 1840 1841 2747 7601 7602 29886 30879 31499 32030 58460 58668 59430 63161 76134 76584 76623 76638 100707 100752 100839)
    (,(file-name-concat verilog-ext-test-files-common-dir "axi_test.sv") 954 1074 1245 1386 1433 77731 77760 77772 78713 79365 79753 82960 86883 86893)))

(defconst verilog-ext-test-utils-point-inside-block-file-pos-and-match
  `((,(file-name-concat verilog-ext-test-files-common-dir "ucontroller.sv") ((1267 . module)
                                                                       (1270 . module)
                                                                       (4334 . module)))
    (,(file-name-concat verilog-ext-test-files-common-dir "instances.sv") ((1423 . module)
                                                                     (1635 . generate)
                                                                     (1764 . generate)
                                                                     (1984 . generate)
                                                                     (1985 . module)
                                                                     (2632 . module)))
    (,(file-name-concat verilog-ext-test-files-common-dir "tb_program.sv") ((1287 . module)
                                                                      (1619 . initial)
                                                                      (2029 . task)
                                                                      (3495 . task)
                                                                      (3643 . task)
                                                                      (4343 . initial)
                                                                      (4556 . initial)
                                                                      (4635 . module)
                                                                      (4635 . module)))
    (,(file-name-concat verilog-ext-test-files-common-dir "uvm_component.svh") ((1882 . class)
                                                                          (2747 . class)
                                                                          (7601 . class)
                                                                          (7602 . class)
                                                                          (29886 . function)
                                                                          (30916 . function)
                                                                          (31534 . function)
                                                                          (32030 . class)
                                                                          (58460 . class)
                                                                          (59430 . function)
                                                                          (63161 . function)
                                                                          (76134 . task)
                                                                          (76623 . task)
                                                                          (100752 . function)))
    (,(file-name-concat verilog-ext-test-files-common-dir "axi_test.sv") ((954 . package)
                                                                    (1074 . package)
                                                                    (1245 . class)
                                                                    (1386 . class)
                                                                    (1433 . function)
                                                                    (77731 . class)
                                                                    (77760 . package)
                                                                    (79365 . module)
                                                                    (79753 . always)
                                                                    (82960 . initial)
                                                                    (86883 . module)))))

(defconst verilog-ext-test-utils-module-at-point-file-and-pos
  `((,(file-name-concat verilog-ext-test-files-common-dir "ucontroller.sv") 335 833 834 856 857 1345 2331 2608 3129 3483 3939 4169 4639 4863 4865 4887)
    (,(file-name-concat verilog-ext-test-files-common-dir "instances.sv") 1 690 819 820 837 838 1182 1355 1636 1692 1911 1999 2809 2811)
    (,(file-name-concat verilog-ext-test-files-common-dir "tb_program.sv") 465 855 856 885 1219 4607 4635 4657 4658)
    (,(file-name-concat verilog-ext-test-files-common-dir "uvm_component.svh") 526 1128 1790 3025 28721 86490 93485 98428 100752)
    (,(file-name-concat verilog-ext-test-files-common-dir "axi_test.sv") 62 882 883 936 1074 2597 5924 7945 9876 14175 18417 25888 32247 38877 41513 77708 77812 78095 78401 78941 79881 85928 86861 86884 86893 86894)
    (,(file-name-concat verilog-ext-test-files-common-dir "axi_demux.sv") 1833 1869 1888 2231 3066 4183 5183 13228 27844 28709 28710 28838 29284 29879 31415 32706 32814 32820 32829 32830 32878 32905 32930 34046 34562 36282 36664)))

(defconst verilog-ext-test-utils-instance-at-point-file-and-pos
  `((,(file-name-concat verilog-ext-test-files-common-dir "instances.sv") 819 838 906 960 1076 1130 1208 1300 1355 1462 1552 1607 1692 1692 1705 1955 1956 2017 2021 2065 2066 2103 2254 2314 2368 2405 2515 2516 2602 2730 2808 2821)
    (,(file-name-concat verilog-ext-test-files-common-dir "ucontroller.sv") 833 1072 1530 2334 2335 2346 2539 2975 2999 3000 3112 3204 3337 3768 3939 4122 4399 4592 4722 4862 4888)))


(defmacro verilog-ext-test-with-test-project (project &rest body)
  (declare (indent 1) (debug t))
  ;; Mock `verilog-ext-buffer-proj' so that function can be run outside of a Verilog
  ;; project buffer and sources are extracted project
  `(cl-letf (((symbol-function 'verilog-ext-buffer-proj)
              (lambda () ,project)))
     ,@body))

(cl-defun verilog-ext-test-utils-scan-modules-fn (&key mode)
  (verilog-ext-with-no-hooks
    (funcall mode))
  (verilog-ext-scan-buffer-modules))

(cl-defun verilog-ext-test-proj-files-fn (&key root dirs ignore-dirs files ignore-files)
  "Show as one file per line instead of as an Elisp string list."
  (let* ((verilog-ext-project-alist `((,verilog-ext-test-utils-proj-name
                                       :root ,root
                                       :dirs ,dirs
                                       :ignore-dirs ,ignore-dirs
                                       :files ,files
                                       :ignore-files ,ignore-files)))
         (file-list (verilog-ext-proj-files)))
    (mapconcat (lambda (file)
                 (file-relative-name file verilog-ext-test-files-dir))
               file-list
               "\n")))


(defun verilog-ext-test-utils-gen-expected-files ()
  ;; Point inside block
  (dolist (file-pos-and-match verilog-ext-test-utils-point-inside-block-file-pos-and-match)
    (let ((file (car file-pos-and-match))
          (pos-and-match-alist (cadr file-pos-and-match)))
      (test-hdl-gen-expected-files :file-list `(,file)
                                   :dest-dir verilog-ext-test-ref-dir-utils
                                   :out-file-ext "point.inside.block.el"
                                   :process-fn 'eval
                                   :fn #'test-hdl-pos-and-match-alist-fn
                                   :args `(:mode verilog-mode
                                           :fn verilog-ext-point-inside-block
                                           :pos-and-match-alist ,pos-and-match-alist))))
  ;; Point inside block (ts-mode)
  (dolist (file-pos-and-match verilog-ext-test-utils-point-inside-block-file-pos-and-match)
    (let ((file (car file-pos-and-match))
          (pos-and-match-alist (cadr file-pos-and-match)))
      (test-hdl-gen-expected-files :file-list `(,file)
                                   :dest-dir verilog-ext-test-ref-dir-utils
                                   :out-file-ext "ts.point.inside.block.el"
                                   :process-fn 'eval
                                   :fn #'test-hdl-pos-and-match-alist-fn
                                   :args `(:mode verilog-ts-mode
                                           :fn verilog-ext-point-inside-block
                                           :pos-and-match-alist ,pos-and-match-alist))))
  ;; Block at point
  (dolist (file-and-pos verilog-ext-test-utils-block-at-point-file-and-pos)
    (let ((file (car file-and-pos))
          (pos-list (cdr file-and-pos)))
      (test-hdl-gen-expected-files :file-list `(,file)
                                   :dest-dir verilog-ext-test-ref-dir-utils
                                   :out-file-ext "block.at.point.el"
                                   :process-fn 'eval
                                   :fn #'test-hdl-pos-list-fn
                                   :args `(:mode verilog-mode
                                           :fn verilog-ext-block-at-point
                                           :pos-list ,pos-list))))
  ;; Block at point (ts-mode)
  (dolist (file-and-pos verilog-ext-test-utils-block-at-point-file-and-pos)
    (let ((file (car file-and-pos))
          (pos-list (cdr file-and-pos)))
      (test-hdl-gen-expected-files :file-list `(,file)
                                   :dest-dir verilog-ext-test-ref-dir-utils
                                   :out-file-ext "ts.block.at.point.el"
                                   :process-fn 'eval
                                   :fn #'test-hdl-pos-list-fn
                                   :args `(:mode verilog-ts-mode
                                           :fn verilog-ext-block-at-point
                                           :pos-list ,pos-list))))
  ;; Instance at point
  (dolist (file-and-pos verilog-ext-test-utils-instance-at-point-file-and-pos)
    (let ((file (car file-and-pos))
          (pos-list (cdr file-and-pos)))
      (test-hdl-gen-expected-files :file-list `(,file)
                                   :dest-dir verilog-ext-test-ref-dir-utils
                                   :out-file-ext "inst.point.el"
                                   :process-fn 'eval
                                   :fn #'test-hdl-pos-list-fn
                                   :args `(:mode verilog-mode
                                           :fn verilog-ext-instance-at-point
                                           :pos-list ,pos-list))))
  ;; Instance at point (ts-mode)
  (dolist (file-and-pos verilog-ext-test-utils-instance-at-point-file-and-pos)
    (let ((file (car file-and-pos))
          (pos-list (cdr file-and-pos)))
      (test-hdl-gen-expected-files :file-list `(,file)
                                   :dest-dir verilog-ext-test-ref-dir-utils
                                   :out-file-ext "ts.inst.point.el"
                                   :process-fn 'eval
                                   :fn #'test-hdl-pos-list-fn
                                   :args `(:mode verilog-ts-mode
                                           :fn verilog-ext-instance-at-point
                                           :pos-list ,pos-list))))
  ;; Scan buffer modules
  (test-hdl-gen-expected-files :file-list verilog-ext-test-utils-file-list
                               :dest-dir verilog-ext-test-ref-dir-utils
                               :out-file-ext "scan.modules.el"
                               :process-fn 'eval
                               :fn #'verilog-ext-test-utils-scan-modules-fn
                               :args `(:mode verilog-mode))
  ;; Scan buffer modules (ts-mode)
  (test-hdl-gen-expected-files :file-list verilog-ext-test-utils-file-list
                               :dest-dir verilog-ext-test-ref-dir-utils
                               :out-file-ext "ts.scan.modules.el"
                               :process-fn 'eval
                               :fn #'verilog-ext-test-utils-scan-modules-fn
                               :args `(:mode verilog-ts-mode))
  ;; Proj files
  (let ((file-list verilog-ext-test-dummy-file-list))
    (verilog-ext-test-with-test-project verilog-ext-test-utils-proj-name
      ;; Test1: Set only `:root'
      (test-hdl-gen-expected-files :file-list file-list
                                   :dest-dir verilog-ext-test-ref-dir-utils
                                   :out-file-ext "files.test1"
                                   :process-fn 'eval
                                   :fn #'verilog-ext-test-proj-files-fn
                                   :args `(:root ,verilog-ext-test-files-common-dir))
      ;; Test2: Set `:root' and `:dirs' (put dirs as directory names with slash at the end to check that expansion works well)
      (test-hdl-gen-expected-files :file-list file-list
                                   :dest-dir verilog-ext-test-ref-dir-utils
                                   :out-file-ext "files.test2"
                                   :process-fn 'eval
                                   :fn #'verilog-ext-test-proj-files-fn
                                   :args `(:root ,verilog-ext-test-files-dir
                                           :dirs ("common/"
                                                  "ucontroller/rtl/")))
      ;; Test3: Set `:root' and `:dirs' recursively
      (test-hdl-gen-expected-files :file-list file-list
                                   :dest-dir verilog-ext-test-ref-dir-utils
                                   :out-file-ext "files.test3"
                                   :process-fn 'eval
                                   :fn #'verilog-ext-test-proj-files-fn
                                   :args `(:root ,verilog-ext-test-files-dir
                                           :dirs ("-r common"
                                                  "-r ucontroller")))
      ;; Test4: Set `:root', `:dirs' and `:files'
      (test-hdl-gen-expected-files :file-list file-list
                                   :dest-dir verilog-ext-test-ref-dir-utils
                                   :out-file-ext "files.test4"
                                   :process-fn 'eval
                                   :fn #'verilog-ext-test-proj-files-fn
                                   :args `(:root ,verilog-ext-test-files-dir
                                           :dirs ("ucontroller/rtl")
                                           :files ("ucontroller/tb/tb_top.sv"
                                                   "ucontroller/tb/tb_alu.sv")))
      ;; Test5: Set `:root' and `:ignore-dirs'
      (test-hdl-gen-expected-files :file-list file-list
                                   :dest-dir verilog-ext-test-ref-dir-utils
                                   :out-file-ext "files.test5"
                                   :process-fn 'eval
                                   :fn #'verilog-ext-test-proj-files-fn
                                   :args `(:root ,verilog-ext-test-files-common-dir
                                           :ignore-dirs ("subblocks")))
      ;; Test6: Set `:root', `:ignore-dirs' and `:ignore-files'
      (test-hdl-gen-expected-files :file-list file-list
                                   :dest-dir verilog-ext-test-ref-dir-utils
                                   :out-file-ext "files.test6"
                                   :process-fn 'eval
                                   :fn #'verilog-ext-test-proj-files-fn
                                   :args `(:root ,verilog-ext-test-files-common-dir
                                           :ignore-dirs ("subblocks")
                                           :ignore-files ("ucontroller.sv"
                                                          "instances.sv")))
      ;; Test7: Set glob pattern: files
      (test-hdl-gen-expected-files :file-list file-list
                                   :dest-dir verilog-ext-test-ref-dir-utils
                                   :out-file-ext "files.test7"
                                   :process-fn 'eval
                                   :fn #'verilog-ext-test-proj-files-fn
                                   :args `(:root ,verilog-ext-test-files-dir
                                           :files ("ucontroller/rtl/*.sv"
                                                   "ucontroller/tb/*.*v"
                                                   "common/*.sv")
                                           :ignore-files ("common/axi_*.sv"
                                                          "common/tb_*.sv")))
      ;; Test8: Set glob pattern: directories
      (test-hdl-gen-expected-files :file-list file-list
                                   :dest-dir verilog-ext-test-ref-dir-utils
                                   :out-file-ext "files.test8"
                                   :process-fn 'eval
                                   :fn #'verilog-ext-test-proj-files-fn
                                   :args `(:root ,verilog-ext-test-files-dir
                                           :dirs ("ucontroller/*" ; ucontroller rtl/tb
                                                  "comm*n/*")))   ; common/subblocks
      ;; Test9: Set glob pattern: recursive directories and ignoring
      (test-hdl-gen-expected-files :file-list file-list
                                   :dest-dir verilog-ext-test-ref-dir-utils
                                   :out-file-ext "files.test9"
                                   :process-fn 'eval
                                   :fn #'verilog-ext-test-proj-files-fn
                                   :args `(:root ,verilog-ext-test-files-dir
                                           :dirs ("-r comm*n"       ; common/subblocks
                                                  "-r *controller") ; ucontroller rtl/tb
                                           :ignore-dirs ("*controller/tb"))) ; ignore ucontroller/tb

      ;; Test10: Set globstar pattern
      (test-hdl-gen-expected-files :file-list file-list
                                   :dest-dir verilog-ext-test-ref-dir-utils
                                   :out-file-ext "files.test10"
                                   :process-fn 'eval
                                   :fn #'verilog-ext-test-proj-files-fn
                                   :args `(:root ,verilog-ext-test-dir
                                           :dirs ("files/**/rtl"
                                                  "**/tb"))))))



(ert-deftest utils::point-inside-block ()
  (dolist (file-pos-and-match verilog-ext-test-utils-point-inside-block-file-pos-and-match)
    (let ((file (car file-pos-and-match))
          (pos-and-match-alist (cadr file-pos-and-match)))
      (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                           :dump-file (file-name-concat verilog-ext-test-dump-dir-utils (test-hdl-basename file "point.inside.block.el"))
                                                           :process-fn 'eval
                                                           :fn #'test-hdl-pos-and-match-alist-fn
                                                           :args `(:mode verilog-mode
                                                                   :fn verilog-ext-point-inside-block
                                                                   :pos-and-match-alist ,pos-and-match-alist))
                                    (file-name-concat verilog-ext-test-ref-dir-utils (test-hdl-basename file "point.inside.block.el")))))))


(ert-deftest utils::point-inside-block-ts-mode ()
  (dolist (file-pos-and-match verilog-ext-test-utils-point-inside-block-file-pos-and-match)
    (let ((file (car file-pos-and-match))
          (pos-and-match-alist (cadr file-pos-and-match)))
      (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                           :dump-file (file-name-concat verilog-ext-test-dump-dir-utils (test-hdl-basename file "ts.point.inside.block.el"))
                                                           :process-fn 'eval
                                                           :fn #'test-hdl-pos-and-match-alist-fn
                                                           :args `(:mode verilog-ts-mode
                                                                   :fn verilog-ext-point-inside-block
                                                                   :pos-and-match-alist ,pos-and-match-alist))
                                    (file-name-concat verilog-ext-test-ref-dir-utils (test-hdl-basename file "ts.point.inside.block.el")))))))


(ert-deftest utils::block-at-point ()
  (dolist (file-and-pos verilog-ext-test-utils-block-at-point-file-and-pos)
    (let ((file (car file-and-pos))
          (pos-list (cdr file-and-pos)))
      (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                           :dump-file (file-name-concat verilog-ext-test-dump-dir-utils (test-hdl-basename file "block.at.point.el"))
                                                           :process-fn 'eval
                                                           :fn #'test-hdl-pos-list-fn
                                                           :args `(:mode verilog-mode
                                                                   :fn verilog-ext-block-at-point
                                                                   :pos-list ,pos-list))
                                    (file-name-concat verilog-ext-test-ref-dir-utils (test-hdl-basename file "block.at.point.el")))))))


(ert-deftest utils::block-at-point-ts-mode ()
  (dolist (file-and-pos verilog-ext-test-utils-block-at-point-file-and-pos)
    (let ((file (car file-and-pos))
          (pos-list (cdr file-and-pos)))
      (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                           :dump-file (file-name-concat verilog-ext-test-dump-dir-utils (test-hdl-basename file "ts.block.at.point.el"))
                                                           :process-fn 'eval
                                                           :fn #'test-hdl-pos-list-fn
                                                           :args `(:mode verilog-ts-mode
                                                                   :fn verilog-ext-block-at-point
                                                                   :pos-list ,pos-list))
                                    (file-name-concat verilog-ext-test-ref-dir-utils (test-hdl-basename file "ts.block.at.point.el")))))))


(ert-deftest utils::instance-at-point ()
  (dolist (file-and-pos verilog-ext-test-utils-instance-at-point-file-and-pos)
    (let ((file (car file-and-pos))
          (pos-list (cdr file-and-pos)))
      (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                           :dump-file (file-name-concat verilog-ext-test-dump-dir-utils (test-hdl-basename file "inst.point.el"))
                                                           :process-fn 'eval
                                                           :fn #'test-hdl-pos-list-fn
                                                           :args `(:mode verilog-mode
                                                                   :fn verilog-ext-instance-at-point
                                                                   :pos-list ,pos-list))
                                    (file-name-concat verilog-ext-test-ref-dir-utils (test-hdl-basename file "inst.point.el")))))))


(ert-deftest utils::instance-at-point-ts-mode ()
  (dolist (file-and-pos verilog-ext-test-utils-instance-at-point-file-and-pos)
    (let ((file (car file-and-pos))
          (pos-list (cdr file-and-pos)))
      (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                           :dump-file (file-name-concat verilog-ext-test-dump-dir-utils (test-hdl-basename file "ts.inst.point.el"))
                                                           :process-fn 'eval
                                                           :fn #'test-hdl-pos-list-fn
                                                           :args `(:mode verilog-ts-mode
                                                                   :fn verilog-ext-instance-at-point
                                                                   :pos-list ,pos-list))
                                    (file-name-concat verilog-ext-test-ref-dir-utils (test-hdl-basename file "ts.inst.point.el")))))))


(ert-deftest utils::scan-buffer-modules ()
  (dolist (file verilog-ext-test-utils-file-list)
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-utils (test-hdl-basename file "scan.modules.el"))
                                                         :process-fn 'eval
                                                         :fn #'verilog-ext-test-utils-scan-modules-fn
                                                         :args `(:mode verilog-mode))
                                  (file-name-concat verilog-ext-test-ref-dir-utils (test-hdl-basename file "scan.modules.el"))))))


(ert-deftest utils::scan-buffer-modules-ts-mode ()
  (dolist (file verilog-ext-test-utils-file-list)
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-utils (test-hdl-basename file "ts.scan.modules.el"))
                                                         :process-fn 'eval
                                                         :fn #'verilog-ext-test-utils-scan-modules-fn
                                                         :args `(:mode verilog-ts-mode))
                                  (file-name-concat verilog-ext-test-ref-dir-utils (test-hdl-basename file "ts.scan.modules.el"))))))


(ert-deftest utils::proj-files ()
  (let ((file (car verilog-ext-test-dummy-file-list)))
    (verilog-ext-test-with-test-project verilog-ext-test-utils-proj-name
      ;; Test1: Set only `:root'
      (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                           :dump-file (file-name-concat verilog-ext-test-dump-dir-utils (test-hdl-basename file "files.test1"))
                                                           :process-fn 'eval
                                                           :fn #'verilog-ext-test-proj-files-fn
                                                           :args `(:root ,verilog-ext-test-files-common-dir))
                                    (file-name-concat verilog-ext-test-ref-dir-utils (test-hdl-basename file "files.test1"))))
      ;; Test2: Set `:root' and `:dirs' (put dirs as directory names with slash at the end to check that expansion works well)
      (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                           :dump-file (file-name-concat verilog-ext-test-dump-dir-utils (test-hdl-basename file "files.test2"))
                                                           :process-fn 'eval
                                                           :fn #'verilog-ext-test-proj-files-fn
                                                           :args `(:root ,verilog-ext-test-files-dir
                                                                   :dirs ("common/"
                                                                          "ucontroller/rtl/")))
                                    (file-name-concat verilog-ext-test-ref-dir-utils (test-hdl-basename file "files.test2"))))
      ;; Test3: Set `:root' and `:dirs' recursively
      (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                           :dump-file (file-name-concat verilog-ext-test-dump-dir-utils (test-hdl-basename file "files.test3"))
                                                           :process-fn 'eval
                                                           :fn #'verilog-ext-test-proj-files-fn
                                                           :args `(:root ,verilog-ext-test-files-dir
                                                                   :dirs ("-r common"
                                                                          "-r ucontroller")))
                                    (file-name-concat verilog-ext-test-ref-dir-utils (test-hdl-basename file "files.test3"))))
      ;; Test4: Set `:root', `:dirs' and `:files'
      (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                           :dump-file (file-name-concat verilog-ext-test-dump-dir-utils (test-hdl-basename file "files.test4"))
                                                           :process-fn 'eval
                                                           :fn #'verilog-ext-test-proj-files-fn
                                                           :args `(:root ,verilog-ext-test-files-dir
                                                                   :dirs ("ucontroller/rtl")
                                                                   :files ("ucontroller/tb/tb_top.sv"
                                                                           "ucontroller/tb/tb_alu.sv")))
                                    (file-name-concat verilog-ext-test-ref-dir-utils (test-hdl-basename file "files.test4"))))
      ;; Test5: Set `:root' and `:ignore-dirs'
      (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                           :dump-file (file-name-concat verilog-ext-test-dump-dir-utils (test-hdl-basename file "files.test5"))
                                                           :process-fn 'eval
                                                           :fn #'verilog-ext-test-proj-files-fn
                                                           :args `(:root ,verilog-ext-test-files-common-dir
                                                                   :ignore-dirs ("subblocks")))
                                    (file-name-concat verilog-ext-test-ref-dir-utils (test-hdl-basename file "files.test5"))))
      ;; Test6: Set `:root', `:ignore-dirs' and `:ignore-files'
      (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                           :dump-file (file-name-concat verilog-ext-test-dump-dir-utils (test-hdl-basename file "files.test6"))
                                                           :process-fn 'eval
                                                           :fn #'verilog-ext-test-proj-files-fn
                                                           :args `(:root ,verilog-ext-test-files-common-dir
                                                                   :ignore-dirs ("subblocks")
                                                                   :ignore-files ("ucontroller.sv"
                                                                                  "instances.sv")))
                                    (file-name-concat verilog-ext-test-ref-dir-utils (test-hdl-basename file "files.test6"))))
      ;; Test7: Set glob pattern: files
      (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                           :dump-file (file-name-concat verilog-ext-test-dump-dir-utils (test-hdl-basename file "files.test7"))
                                                           :process-fn 'eval
                                                           :fn #'verilog-ext-test-proj-files-fn
                                                           :args `(:root ,verilog-ext-test-files-dir
                                                                   :files ("ucontroller/rtl/*.sv"
                                                                           "ucontroller/tb/*.*v"
                                                                           "common/*.sv")
                                                                   :ignore-files ("common/axi_*.sv"
                                                                                  "common/tb_*.sv")))
                                    (file-name-concat verilog-ext-test-ref-dir-utils (test-hdl-basename file "files.test7"))))
      ;; Test8: Set glob pattern: directories
      (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                           :dump-file (file-name-concat verilog-ext-test-dump-dir-utils (test-hdl-basename file "files.test8"))
                                                           :process-fn 'eval
                                                           :fn #'verilog-ext-test-proj-files-fn
                                                           :args `(:root ,verilog-ext-test-files-dir
                                                                   :dirs ("ucontroller/*" ; ucontroller rtl/tb
                                                                          "comm*n/*")))   ; common/subblocks
                                    (file-name-concat verilog-ext-test-ref-dir-utils (test-hdl-basename file "files.test8"))))
      ;; Test9: Set glob pattern: recursive directories and ignoring
      (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                           :dump-file (file-name-concat verilog-ext-test-dump-dir-utils (test-hdl-basename file "files.test9"))
                                                           :process-fn 'eval
                                                           :fn #'verilog-ext-test-proj-files-fn
                                                           :args `(:root ,verilog-ext-test-files-dir
                                                                   :dirs ("-r comm*n"       ; common/subblocks
                                                                          "-r *controller") ; ucontroller rtl/tb
                                                                   :ignore-dirs ("*controller/tb"))) ; ignore ucontroller/tb
                                    (file-name-concat verilog-ext-test-ref-dir-utils (test-hdl-basename file "files.test9"))))
      ;; Test10: Set globstar pattern
      (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                           :dump-file (file-name-concat verilog-ext-test-dump-dir-utils (test-hdl-basename file "files.test10"))
                                                           :process-fn 'eval
                                                           :fn #'verilog-ext-test-proj-files-fn
                                                           :args `(:root ,verilog-ext-test-dir
                                                                   :dirs ("files/**/rtl"
                                                                          "**/tb")))
                                    (file-name-concat verilog-ext-test-ref-dir-utils (test-hdl-basename file "files.test10")))))))



(provide 'verilog-ext-test-utils)

;;; verilog-ext-test-utils.el ends here
