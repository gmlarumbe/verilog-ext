;;; verilog-ext-test.el --- Verilog-Ext ERT tests  -*- lexical-binding: t -*-

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
;; Verilog-Ext ERT tests
;;
;;; Code:

;; Allow loading of packages in Emacs interactive session
(defconst verilog-ext-test-dir (file-name-parent-directory (file-name-directory (or load-file-name (buffer-file-name)))))
(defconst verilog-ext-test-hdl-dir (file-name-concat verilog-ext-test-dir "test-hdl"))

(unless noninteractive
  (dolist (dir `(,(file-name-concat verilog-ext-test-dir "src")
                 ,verilog-ext-test-hdl-dir))
    (unless (member dir load-path)
      (add-to-list 'load-path dir))))

;; Setup tree-sitter-systemverilog parser
(when (treesit-available-p)
  (add-to-list 'treesit-load-name-override-list '(verilog "libtree-sitter-systemverilog" "tree_sitter_systemverilog")))


(require 'test-hdl)
(require 'verilog-ext)


;;;; Directories
(defconst verilog-ext-test-ref-dir (file-name-concat verilog-ext-test-dir "ref"))
(defconst verilog-ext-test-dump-dir (file-name-concat verilog-ext-test-dir "dump"))
(defconst verilog-ext-test-files-dir (file-name-concat verilog-ext-test-dir "files"))
(defconst verilog-ext-test-files-common-dir (file-name-concat verilog-ext-test-files-dir "common"))
(defconst verilog-ext-test-ucontroller-dir (file-name-concat verilog-ext-test-files-dir "ucontroller"))
(defconst verilog-ext-test-ucontroller-rtl-dir (file-name-concat verilog-ext-test-ucontroller-dir "rtl"))
(defconst verilog-ext-test-ucontroller-tb-dir (file-name-concat verilog-ext-test-ucontroller-dir "tb"))

(defconst verilog-ext-test-common-file-list (test-hdl-directory-files verilog-ext-test-files-common-dir
                                                                      verilog-ext-file-extension-re))

;;;; Tests
(require 'verilog-ext-test-faceup)
(require 'verilog-ext-test-indent)
(require 'verilog-ext-test-utils)
(require 'verilog-ext-test-navigation)
(require 'verilog-ext-test-imenu)
(require 'verilog-ext-test-beautify)
(require 'verilog-ext-test-hierarchy)
(require 'verilog-ext-test-tags)
(require 'verilog-ext-test-capf)
(require 'verilog-ext-test-xref)


;;;; Aux funcs
(defun verilog-ext-test-gen-expected-files ()
  (verilog-ext-test-faceup-gen-expected-files)
  (verilog-ext-test-indent-gen-expected-files)
  (verilog-ext-test-utils-gen-expected-files)
  (verilog-ext-test-navigation-gen-expected-files)
  (verilog-ext-test-imenu-gen-expected-files)
  (verilog-ext-test-beautify-gen-expected-files)
  (verilog-ext-test-hierarchy-gen-expected-files)
  (verilog-ext-test-tags-gen-expected-files)
  (verilog-ext-test-capf-gen-expected-files)
  (verilog-ext-test-xref-gen-expected-files))


(provide 'verilog-ext-test)

;;; verilog-ext-test.el ends here
