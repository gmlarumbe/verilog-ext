;;; verilog-ext-test-hierarchy.el --- Verilog-Ext ERT hierarchy tests  -*- lexical-binding: t -*-

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
;; Verilog-Ext ERT hierarchy tests
;;
;;; Code:

(defconst verilog-ext-test-ref-dir-hierarchy (file-name-concat verilog-ext-test-ref-dir "hierarchy"))
(defconst verilog-ext-test-dump-dir-hierarchy (file-name-concat verilog-ext-test-dump-dir "hierarchy"))

(defconst verilog-ext-test-hierarchy-ucontroller-rtl-file-list
  (test-hdl-directory-files verilog-ext-test-ucontroller-rtl-dir verilog-ext-file-extension-re))
(defconst verilog-ext-test-hierarchy-ucontroller-tb-file-list
  (test-hdl-directory-files verilog-ext-test-ucontroller-tb-dir verilog-ext-file-extension-re))
(defconst verilog-ext-test-hierarchy-ucontroller-file-list
  (append verilog-ext-test-hierarchy-ucontroller-rtl-file-list
          verilog-ext-test-hierarchy-ucontroller-tb-file-list))

(defconst verilog-ext-test-hierarchy-file-list (mapcar (lambda (file)
                                                         (file-name-concat verilog-ext-test-files-common-dir file))
                                                       '("instances.sv"
                                                         "ucontroller.sv"
                                                         "axi_demux.sv")))
(defconst verilog-ext-test-hierarchy-sources-list
  (append (test-hdl-directory-files (file-name-concat verilog-ext-test-files-dir "subblocks") verilog-ext-file-extension-re)
          verilog-ext-test-hierarchy-file-list
          verilog-ext-test-hierarchy-ucontroller-file-list))

(defconst verilog-ext-test-hierarchy-vhier-lib-search-path
  `(,verilog-ext-test-files-common-dir
    ,verilog-ext-test-ucontroller-rtl-dir
    ,(file-name-concat verilog-ext-test-files-dir "subblocks")))


(defun verilog-ext-test-hierarchy--hierarchy-fn ()
  (let ((hier (verilog-ext-hierarchy-current-buffer)))
    (with-temp-buffer
      (hierarchy-print hier (lambda (node) node))
      (buffer-substring-no-properties (point-min) (point-max)))))

(defun verilog-ext-test-hierarchy--outline-fn ()
  (verilog-ext-hierarchy-current-buffer)
  (buffer-substring-no-properties (point-min) (point-max)))


(cl-defun verilog-ext-test-hierarchy-buffer (&key mode backend frontend root files lib-search-path module)
  (let* ((verilog-ext-hierarchy-backend backend)
         (verilog-ext-hierarchy-frontend frontend)
         ;; Vhier
         (verilog-ext-hierarchy-vhier-use-open-buffers nil)
         ;; Project-alist
         (proj-name "verilog-ext-test-hierarchy")
         (verilog-ext-project-alist `((,proj-name
                                       :root ,(or root verilog-ext-test-files-common-dir)
                                       :files ,files
                                       :lib-search-path ,lib-search-path))))
    ;; Mock functions
    (cl-letf (((symbol-function 'verilog-ext-hierarchy-twidget-display)
               (lambda (hierarchy &optional module)
                 hierarchy))
              ((symbol-function 'verilog-ext-select-file-module)
               (lambda (&optional file)
                 (or module
                     (car (mapcar #'car (verilog-ext-read-file-modules file)))))))
      ;; Run tests
      (test-hdl-no-messages
        ;; INFO: This one seems important to have a clear state on each file parsed.
        (verilog-ext-hierarchy-clear-cache)
        (funcall mode)
        (cond (;; vhier-outline
               ;;  - vhier cannot use temp-buffer since executes a command that requires a filename as an argument
               (and (eq backend 'vhier)
                    (eq frontend 'outline))
               (verilog-ext-test-hierarchy--outline-fn))
              ;; vhier-hierarchy
              ;;  - vhier cannot use temp-buffer since executes a command that requires a filename as an argument
              ((and (eq backend 'vhier)
                    (eq frontend 'hierarchy))
               (verilog-ext-test-hierarchy--hierarchy-fn))
              ;; builtin-hierarchy
              ((and (eq backend 'builtin)
                    (eq frontend 'hierarchy))
               (verilog-ext-hierarchy-parse)
               (verilog-ext-test-hierarchy--hierarchy-fn))
              ;; builtin-outline
              ((and (eq backend 'builtin)
                    (eq frontend 'outline))
               (verilog-ext-hierarchy-parse)
               (verilog-ext-test-hierarchy--outline-fn))
              ;; tree-sitter-hierarchy
              ((and (eq backend 'tree-sitter)
                    (eq frontend 'hierarchy))
               (verilog-ext-hierarchy-parse)
               (verilog-ext-test-hierarchy--hierarchy-fn))
              ;; tree-sitter-outline
              ((and (eq backend 'tree-sitter)
                    (eq frontend 'outline))
               (verilog-ext-hierarchy-parse)
               (verilog-ext-test-hierarchy--outline-fn))
              ;; Fallback
              (t
               (error "Not a proper backend-frontend combination!")))))))


(defun verilog-ext-test-hierarchy-gen-expected-files ()
  ;; vhier-hierarchy
  (let ((file (file-name-concat verilog-ext-test-files-common-dir "instances.sv")))
    (test-hdl-gen-expected-files :file-list `(,file)
                                 :dest-dir verilog-ext-test-ref-dir-hierarchy
                                 :out-file-ext "vhier.hier.el"
                                 :process-fn 'eval-ff
                                 :fn #'verilog-ext-test-hierarchy-buffer
                                 :args `(:mode verilog-mode
                                         :backend vhier
                                         :frontend hierarchy
                                         :root ,verilog-ext-test-files-common-dir
                                         :files (,file)
                                         :lib-search-path ,verilog-ext-test-hierarchy-vhier-lib-search-path)))
  ;; INFO: For some reason, the one ucontroller.sv in `verilog-ext-test-files-common-dir
  ;; had the package line removed and didn't work as expected
  (let ((file (file-name-concat verilog-ext-test-ucontroller-rtl-dir "ucontroller.sv")))
    (test-hdl-gen-expected-files :file-list `(,file)
                                 :dest-dir verilog-ext-test-ref-dir-hierarchy
                                 :out-file-ext "vhier.hier.el"
                                 :process-fn 'eval-ff
                                 :fn #'verilog-ext-test-hierarchy-buffer
                                 :args `(:mode verilog-mode
                                         :backend vhier
                                         :frontend hierarchy
                                         :root ,verilog-ext-test-ucontroller-rtl-dir
                                         :files (,(file-name-concat verilog-ext-test-ucontroller-rtl-dir "global_pkg.sv")
                                                 ,@verilog-ext-test-hierarchy-ucontroller-file-list)
                                         :lib-search-path ,verilog-ext-test-hierarchy-vhier-lib-search-path)))
  ;; vhier-outline
  (let ((file (file-name-concat verilog-ext-test-files-common-dir "instances.sv")))
    (test-hdl-gen-expected-files :file-list `(,file)
                                 :dest-dir verilog-ext-test-ref-dir-hierarchy
                                 :out-file-ext "vhier.outline.sv"
                                 :process-fn 'eval-ff
                                 :fn #'verilog-ext-test-hierarchy-buffer
                                 :args `(:mode verilog-mode
                                         :backend vhier
                                         :frontend outline
                                         :root ,verilog-ext-test-files-common-dir
                                         :files (,file)
                                         :lib-search-path ,verilog-ext-test-hierarchy-vhier-lib-search-path)))
  ;; INFO: For some reason, the one ucontroller.sv in `verilog-ext-test-files-common-dir
  ;; had the package line removed and didn't work as expected
  (let ((file (file-name-concat verilog-ext-test-ucontroller-rtl-dir "ucontroller.sv")))
    (test-hdl-gen-expected-files :file-list `(,file)
                                 :dest-dir verilog-ext-test-ref-dir-hierarchy
                                 :out-file-ext "vhier.outline.sv"
                                 :process-fn 'eval-ff
                                 :fn #'verilog-ext-test-hierarchy-buffer
                                 :args `(:mode verilog-mode
                                         :backend vhier
                                         :frontend outline
                                         :root ,verilog-ext-test-ucontroller-rtl-dir
                                         :files (,(file-name-concat verilog-ext-test-ucontroller-rtl-dir "global_pkg.sv")
                                                 ,@verilog-ext-test-hierarchy-ucontroller-file-list)
                                         :lib-search-path ,verilog-ext-test-hierarchy-vhier-lib-search-path)))
  ;; builtin-hierarchy
  (test-hdl-gen-expected-files :file-list verilog-ext-test-hierarchy-file-list
                               :dest-dir verilog-ext-test-ref-dir-hierarchy
                               :out-file-ext "builtin.hier.el"
                               :process-fn 'eval-ff
                               :fn #'verilog-ext-test-hierarchy-buffer
                               :args `(:mode verilog-mode
                                       :backend builtin
                                       :frontend hierarchy
                                       :files ,verilog-ext-test-hierarchy-sources-list))
  ;; builtin-outline
  (test-hdl-gen-expected-files :file-list verilog-ext-test-hierarchy-file-list
                               :dest-dir verilog-ext-test-ref-dir-hierarchy
                               :out-file-ext "builtin.outline.sv"
                               :process-fn 'eval-ff
                               :fn #'verilog-ext-test-hierarchy-buffer
                               :args `(:mode verilog-mode
                                       :backend builtin
                                       :frontend outline
                                       :files ,verilog-ext-test-hierarchy-sources-list))
  ;; tree-sitter-hierarchy
  (test-hdl-gen-expected-files :file-list verilog-ext-test-hierarchy-file-list
                               :dest-dir verilog-ext-test-ref-dir-hierarchy
                               :out-file-ext "ts.hier.el"
                               :process-fn 'eval-ff
                               :fn #'verilog-ext-test-hierarchy-buffer
                               :args `(:mode verilog-ts-mode
                                       :backend tree-sitter
                                       :frontend hierarchy
                                       :files ,verilog-ext-test-hierarchy-sources-list))
  ;; tree-sitter-outline
  (test-hdl-gen-expected-files :file-list verilog-ext-test-hierarchy-file-list
                               :dest-dir verilog-ext-test-ref-dir-hierarchy
                               :out-file-ext "ts.outline.sv"
                               :process-fn 'eval-ff
                               :fn #'verilog-ext-test-hierarchy-buffer
                               :args `(:mode verilog-ts-mode
                                       :backend tree-sitter
                                       :frontend outline
                                       :files ,verilog-ext-test-hierarchy-sources-list))
  ;; More custom ones (e.g. need to explicit module to be parsed from a file with multiple modules declared)
  ;; - axi_demux / builtin-hierarchy
  (test-hdl-gen-expected-files :file-list `(,(file-name-concat verilog-ext-test-files-common-dir "axi_demux.sv"))
                               :dest-dir verilog-ext-test-ref-dir-hierarchy
                               :out-file-ext "mm.builtin.hier.el"
                               :process-fn 'eval-ff
                               :fn #'verilog-ext-test-hierarchy-buffer
                               :args `(:mode verilog-mode
                                       :backend builtin
                                       :frontend hierarchy
                                       :files ,verilog-ext-test-hierarchy-sources-list
                                       :module "axi_demux_intf"))
  ;; - axi_demux / builtin-outline
  (test-hdl-gen-expected-files :file-list `(,(file-name-concat verilog-ext-test-files-common-dir "axi_demux.sv"))
                               :dest-dir verilog-ext-test-ref-dir-hierarchy
                               :out-file-ext "mm.builtin.outline.sv"
                               :process-fn 'eval-ff
                               :fn #'verilog-ext-test-hierarchy-buffer
                               :args `(:mode verilog-mode
                                       :backend builtin
                                       :frontend outline
                                       :files ,verilog-ext-test-hierarchy-sources-list
                                       :module "axi_demux_intf"))
  ;; - axi_demux / tree-sitter-hierarchy
  (test-hdl-gen-expected-files :file-list `(,(file-name-concat verilog-ext-test-files-common-dir "axi_demux.sv"))
                               :dest-dir verilog-ext-test-ref-dir-hierarchy
                               :out-file-ext "mm.ts.hier.el"
                               :process-fn 'eval-ff
                               :fn #'verilog-ext-test-hierarchy-buffer
                               :args `(:mode verilog-ts-mode
                                       :backend tree-sitter
                                       :frontend hierarchy
                                       :files ,verilog-ext-test-hierarchy-sources-list
                                       :module "axi_demux_intf"))
  ;; - axi_demux / tree-sitter-outline
  (test-hdl-gen-expected-files :file-list `(,(file-name-concat verilog-ext-test-files-common-dir "axi_demux.sv"))
                               :dest-dir verilog-ext-test-ref-dir-hierarchy
                               :out-file-ext "mm.ts.outline.sv"
                               :process-fn 'eval-ff
                               :fn #'verilog-ext-test-hierarchy-buffer
                               :args `(:mode verilog-ts-mode
                                       :backend tree-sitter
                                       :frontend outline
                                       :files ,verilog-ext-test-hierarchy-sources-list
                                       :module "axi_demux_intf")))

(ert-deftest hierarchy::vhier-hierarchy ()
  ;; instances.sv
  (let ((file (file-name-concat verilog-ext-test-files-common-dir "instances.sv")))
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-hierarchy (test-hdl-basename file "vhier.hier.el"))
                                                         :process-fn 'eval-ff
                                                         :fn #'verilog-ext-test-hierarchy-buffer
                                                         :args `(:mode verilog-mode
                                                                 :backend vhier
                                                                 :frontend hierarchy
                                                                 :root ,verilog-ext-test-files-common-dir
                                                                 :files (,file)
                                                                 :lib-search-path ,verilog-ext-test-hierarchy-vhier-lib-search-path
                                                                 ))
                                  (file-name-concat verilog-ext-test-ref-dir-hierarchy (test-hdl-basename file "vhier.hier.el")))))
  ;; ucontroller.sv
  ;; INFO: For some reason, the one ucontroller.sv in `verilog-ext-test-files-common-dir
  ;; had the package line removed and didn't work as expected
  (let ((file (file-name-concat verilog-ext-test-ucontroller-rtl-dir "ucontroller.sv")))
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-hierarchy (test-hdl-basename file "vhier.hier.el"))
                                                         :process-fn 'eval-ff
                                                         :fn #'verilog-ext-test-hierarchy-buffer
                                                         :args `(:mode verilog-mode
                                                                 :backend vhier
                                                                 :frontend hierarchy
                                                                 :root ,verilog-ext-test-ucontroller-rtl-dir
                                                                 :files (,(file-name-concat verilog-ext-test-ucontroller-rtl-dir "global_pkg.sv")
                                                                         ,@verilog-ext-test-hierarchy-ucontroller-file-list)
                                                                 :lib-search-path ,verilog-ext-test-hierarchy-vhier-lib-search-path
                                                                 ))
                                  (file-name-concat verilog-ext-test-ref-dir-hierarchy (test-hdl-basename file "vhier.hier.el"))))))

(ert-deftest hierarchy::vhier-outline ()
  ;; instances.sv
  (let ((file (file-name-concat verilog-ext-test-files-common-dir "instances.sv")))
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-hierarchy (test-hdl-basename file "vhier.outline.sv"))
                                                         :process-fn 'eval-ff
                                                         :fn #'verilog-ext-test-hierarchy-buffer
                                                         :args `(:mode verilog-mode
                                                                 :backend vhier
                                                                 :frontend outline
                                                                 :root ,verilog-ext-test-files-common-dir
                                                                 :files (,file)
                                                                 :lib-search-path ,verilog-ext-test-hierarchy-vhier-lib-search-path
                                                                 ))
                                  (file-name-concat verilog-ext-test-ref-dir-hierarchy (test-hdl-basename file "vhier.outline.sv")))))
  ;; ucontroller.sv
  ;; INFO: For some reason, the one ucontroller.sv in `verilog-ext-test-files-common-dir
  ;; had the package line removed and didn't work as expected
  (let ((file (file-name-concat verilog-ext-test-ucontroller-rtl-dir "ucontroller.sv")))
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-hierarchy (test-hdl-basename file "vhier.outline.sv"))
                                                         :process-fn 'eval-ff
                                                         :fn #'verilog-ext-test-hierarchy-buffer
                                                         :args `(:mode verilog-mode
                                                                 :backend vhier
                                                                 :frontend outline
                                                                 :root ,verilog-ext-test-ucontroller-rtl-dir
                                                                 :files (,(file-name-concat verilog-ext-test-ucontroller-rtl-dir "global_pkg.sv")
                                                                         ,@verilog-ext-test-hierarchy-ucontroller-file-list)
                                                                 :lib-search-path ,verilog-ext-test-hierarchy-vhier-lib-search-path
                                                                 ))
                                  (file-name-concat verilog-ext-test-ref-dir-hierarchy (test-hdl-basename file "vhier.outline.sv"))))))

(ert-deftest hierarchy::builtin-hierarchy ()
  (dolist (file verilog-ext-test-hierarchy-file-list)
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-hierarchy (test-hdl-basename file "builtin.hier.el"))
                                                         :process-fn 'eval-ff
                                                         :fn #'verilog-ext-test-hierarchy-buffer
                                                         :args `(:mode verilog-mode
                                                                 :backend builtin
                                                                 :frontend hierarchy
                                                                 :files ,verilog-ext-test-hierarchy-sources-list))
                                  (file-name-concat verilog-ext-test-ref-dir-hierarchy (test-hdl-basename file "builtin.hier.el"))))))

(ert-deftest hierarchy::builtin-outline ()
  (dolist (file verilog-ext-test-hierarchy-file-list)
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-hierarchy (test-hdl-basename file "builtin.outline.sv"))
                                                         :process-fn 'eval-ff
                                                         :fn #'verilog-ext-test-hierarchy-buffer
                                                         :args `(:mode verilog-mode
                                                                 :backend builtin
                                                                 :frontend outline
                                                                 :files ,verilog-ext-test-hierarchy-sources-list))
                                  (file-name-concat verilog-ext-test-ref-dir-hierarchy (test-hdl-basename file "builtin.outline.sv"))))))

(ert-deftest hierarchy::tree-sitter-hierarchy ()
  (dolist (file verilog-ext-test-hierarchy-file-list)
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-hierarchy (test-hdl-basename file "ts.hier.el"))
                                                         :process-fn 'eval-ff
                                                         :fn #'verilog-ext-test-hierarchy-buffer
                                                         :args `(:mode verilog-ts-mode
                                                                 :backend tree-sitter
                                                                 :frontend hierarchy
                                                                 :files ,verilog-ext-test-hierarchy-sources-list))
                                  (file-name-concat verilog-ext-test-ref-dir-hierarchy (test-hdl-basename file "ts.hier.el"))))))

(ert-deftest hierarchy::tree-sitter-outline ()
  (dolist (file verilog-ext-test-hierarchy-file-list)
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-hierarchy (test-hdl-basename file "ts.outline.sv"))
                                                         :process-fn 'eval-ff
                                                         :fn #'verilog-ext-test-hierarchy-buffer
                                                         :args `(:mode verilog-ts-mode
                                                                 :backend tree-sitter
                                                                 :frontend outline
                                                                 :files ,verilog-ext-test-hierarchy-sources-list))
                                  (file-name-concat verilog-ext-test-ref-dir-hierarchy (test-hdl-basename file "ts.outline.sv"))))))

(ert-deftest hierarchy::builtin-hierarchy::multiple-modules ()
  (let ((file (file-name-concat verilog-ext-test-files-common-dir "axi_demux.sv")))
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-hierarchy (test-hdl-basename file "mm.builtin.hier.el"))
                                                         :process-fn 'eval-ff
                                                         :fn #'verilog-ext-test-hierarchy-buffer
                                                         :args `(:mode verilog-mode
                                                                 :backend builtin
                                                                 :frontend hierarchy
                                                                 :files ,verilog-ext-test-hierarchy-sources-list
                                                                 :module "axi_demux_intf"))
                                  (file-name-concat verilog-ext-test-ref-dir-hierarchy (test-hdl-basename file "mm.builtin.hier.el"))))))

(ert-deftest hierarchy::builtin-outline::multiple-modules ()
  (let ((file (file-name-concat verilog-ext-test-files-common-dir "axi_demux.sv")))
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-hierarchy (test-hdl-basename file "mm.builtin.outline.sv"))
                                                         :process-fn 'eval-ff
                                                         :fn #'verilog-ext-test-hierarchy-buffer
                                                         :args `(:mode verilog-mode
                                                                 :backend builtin
                                                                 :frontend outline
                                                                 :files ,verilog-ext-test-hierarchy-sources-list
                                                                 :module "axi_demux_intf"))
                                  (file-name-concat verilog-ext-test-ref-dir-hierarchy (test-hdl-basename file "mm.builtin.outline.sv"))))))

(ert-deftest hierarchy::tree-sitter-hierarchy::multiple-modules ()
  (let ((file (file-name-concat verilog-ext-test-files-common-dir "axi_demux.sv")))
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-hierarchy (test-hdl-basename file "mm.ts.hier.el"))
                                                         :process-fn 'eval-ff
                                                         :fn #'verilog-ext-test-hierarchy-buffer
                                                         :args `(:mode verilog-ts-mode
                                                                 :backend tree-sitter
                                                                 :frontend hierarchy
                                                                 :files ,verilog-ext-test-hierarchy-sources-list
                                                                 :module "axi_demux_intf"))
                                  (file-name-concat verilog-ext-test-ref-dir-hierarchy (test-hdl-basename file "mm.ts.hier.el"))))))

(ert-deftest hierarchy::tree-sitter-outline::multiple-modules ()
  (let ((file (file-name-concat verilog-ext-test-files-common-dir "axi_demux.sv")))
    (should (test-hdl-files-equal (test-hdl-process-file :test-file file
                                                         :dump-file (file-name-concat verilog-ext-test-dump-dir-hierarchy (test-hdl-basename file "mm.ts.outline.sv"))
                                                         :process-fn 'eval-ff
                                                         :fn #'verilog-ext-test-hierarchy-buffer
                                                         :args `(:mode verilog-ts-mode
                                                                 :backend tree-sitter
                                                                 :frontend outline
                                                                 :files ,verilog-ext-test-hierarchy-sources-list
                                                                 :module "axi_demux_intf"))
                                  (file-name-concat verilog-ext-test-ref-dir-hierarchy (test-hdl-basename file "mm.ts.outline.sv"))))))


(provide 'verilog-ext-test-hierarchy)

;;; verilog-ext-test-hierarchy.el ends here
