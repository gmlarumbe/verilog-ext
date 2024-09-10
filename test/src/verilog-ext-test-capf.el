;;; verilog-ext-test-capf.el --- Verilog-Ext ERT capf tests  -*- lexical-binding: t -*-

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
;; Verilog-Ext ERT capf tests
;;
;;; Code:

(defconst verilog-ext-test-ref-dir-capf (file-name-concat verilog-ext-test-ref-dir "capf"))
(defconst verilog-ext-test-dump-dir-capf (file-name-concat verilog-ext-test-dump-dir "capf"))

(defconst verilog-ext-test-capf-file-pos-init-string-alist
  `((,(file-name-concat verilog-ext-test-ucontroller-dir "rtl/ucontroller.sv")
     ((853 "mod")         ; module keyword
      (874 "input logic ") ; port
      (2956 "cpu::")       ; module scope completion (all matches)
      (2956 "I_CPU.")      ; hierarchical reference (all matches)
      (2956 "alu::In")     ; module scope completion (with some input)
      (2956 "I_ALU.In")    ; hierarchical reference (with some input)
      (point-max "end")))  ; end keywords
    (,(file-name-concat verilog-ext-test-ucontroller-dir "tb/tb_program.sv")
     ((1782 "ta")         ; task completion
      (1782 "fun")        ; function completion
      (4626 "init")       ; init_rom task call
      (point-max "pac"))) ; create package at the end of the file
    ))

(defun verilog-ext-test-capf-anotation-fn ()
  (mapcar (lambda (cand)
            (verilog-ext-capf-annotation-function cand))
          (nth 2 (verilog-ext-capf))))


(defun verilog-ext-test-capf-gen-expected-files ()
  (verilog-ext-test-with-test-project verilog-ext-test-tags-proj-name
    ;; Generate/update tags for test project
    (verilog-ext-test-tags-get :backend 'tree-sitter
                               :root verilog-ext-test-ucontroller-dir
                               :dirs `(,verilog-ext-test-ucontroller-rtl-dir ,verilog-ext-test-ucontroller-tb-dir)
                               :rel-path t)
    (dolist (file-pos-and-init-string verilog-ext-test-capf-file-pos-init-string-alist)
      (let ((file (car file-pos-and-init-string))
            (pos-and-init-string-alist (cadr file-pos-and-init-string)))
        ;; Completion
        (test-hdl-gen-expected-files :file-list `(,file)
                                     :dest-dir verilog-ext-test-ref-dir-capf
                                     :out-file-ext "capf.el"
                                     :process-fn 'eval
                                     :fn #'test-hdl-capf-fn
                                     :args `(:capf-fn verilog-ext-capf
                                             :pos-init-string-alist ,pos-and-init-string-alist))
        ;; Annotation
        (test-hdl-gen-expected-files :file-list `(,file)
                                     :dest-dir verilog-ext-test-ref-dir-capf
                                     :out-file-ext "annotations.el"
                                     :process-fn 'eval
                                     :fn #'test-hdl-capf-fn
                                     :args `(:capf-fn verilog-ext-test-capf-anotation-fn
                                             :pos-init-string-alist ,pos-and-init-string-alist))))))


(ert-deftest capf::completions ()
  (verilog-ext-test-with-test-project verilog-ext-test-tags-proj-name
    ;; Generate/update tags for test project
    (verilog-ext-test-tags-get :backend 'tree-sitter
                               :root verilog-ext-test-ucontroller-dir
                               :dirs `(,verilog-ext-test-ucontroller-rtl-dir ,verilog-ext-test-ucontroller-tb-dir)
                               :rel-path t)
    ;; Test each file
    (dolist (file-pos-and-init-string verilog-ext-test-capf-file-pos-init-string-alist)
      (let ((file (car file-pos-and-init-string))
            (pos-and-init-string-alist (cadr file-pos-and-init-string)))
        (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                             :dump-file (file-name-concat verilog-ext-test-dump-dir-capf (test-hdl-basename file "capf.el"))
                                                             :process-fn 'eval
                                                             :fn #'test-hdl-capf-fn
                                                             :args `(:capf-fn verilog-ext-capf
                                                                     :pos-init-string-alist ,pos-and-init-string-alist))
                                      (file-name-concat verilog-ext-test-ref-dir-capf (test-hdl-basename file "capf.el"))))))))


(ert-deftest capf::annotations ()
  (verilog-ext-test-with-test-project verilog-ext-test-tags-proj-name
    ;; Generate/update tags for test project
    (verilog-ext-test-tags-get :backend 'tree-sitter
                               :root verilog-ext-test-ucontroller-dir
                               :dirs `(,verilog-ext-test-ucontroller-rtl-dir ,verilog-ext-test-ucontroller-tb-dir)
                               :rel-path t)
    ;; Test each file
    (dolist (file-pos-and-init-string verilog-ext-test-capf-file-pos-init-string-alist)
      (let ((file (car file-pos-and-init-string))
            (pos-and-init-string-alist (cadr file-pos-and-init-string)))
        (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                             :dump-file (file-name-concat verilog-ext-test-dump-dir-capf (test-hdl-basename file "annotations.el"))
                                                             :process-fn 'eval
                                                             :fn #'test-hdl-capf-fn
                                                             :args `(:capf-fn verilog-ext-test-capf-anotation-fn
                                                                     :pos-init-string-alist ,pos-and-init-string-alist))
                                      (file-name-concat verilog-ext-test-ref-dir-capf (test-hdl-basename file "annotations.el"))))))))


(provide 'verilog-ext-test-capf)

;;; verilog-ext-test-capf.el ends here
