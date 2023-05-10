;;; verilog-ext-tests.el --- Verilog-Ext ERT tests  -*- lexical-binding: t -*-

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
;; ERT Tests
;;
;;; Code:


;;;; Performance utils
(require 'profiler)

(defun verilog-ext-profile-file (file)
  "Use Emacs profiler in FILE."
  (profiler-start 'cpu+mem)
  (find-file file)
  (profiler-stop)
  (profiler-report))

(defun verilog-ext-profile-imenu ()
  "Use Emacs profiler on `verilog-ext-imenu-list'."
  (profiler-start 'cpu+mem)
  (verilog-ext-imenu-list)
  (profiler-stop)
  (profiler-report))

;;;; Native compile
(defun verilog-ext-compile-dir (dir)
  "Compile DIR.
Native compile if native compilation is available.
Otherwise, byte-compile."
  (if (native-comp-available-p)
      (dolist (file (directory-files-recursively dir "\.el$"))
        (message "Native compiling %s" file)
        (native-compile file))
    ;; Nix Emacs images might still lack native compilation support, so byte-compile them
    (message "Byte-compiling %s" dir)
    (byte-recompile-directory dir 0)))


;;;; Tests
(require 'verilog-ext)

(defvar verilog-ext-tests-test-dir (if (bound-and-true-p straight-base-dir)
                                       (file-name-concat (expand-file-name straight-base-dir) "straight/repos/verilog-ext/test")
                                     (file-name-directory (or load-file-name (buffer-file-name)))))
(defvar verilog-ext-tests-files-dir (file-name-concat verilog-ext-tests-test-dir "files"))
(defvar verilog-ext-tests-beautify-dir (file-name-concat verilog-ext-tests-files-dir "beautify"))
(defvar verilog-ext-tests-common-dir (file-name-concat verilog-ext-tests-files-dir "common"))
(defvar verilog-ext-tests-faceup-dir (file-name-concat verilog-ext-tests-files-dir "faceup"))
(defvar verilog-ext-tests-indent-dir (file-name-concat verilog-ext-tests-files-dir "indent"))
(defvar verilog-ext-tests-jump-parent-dir (file-name-concat verilog-ext-tests-files-dir "jump-parent"))
(defvar verilog-ext-tests-hierarchy-dir (file-name-concat verilog-ext-tests-files-dir "hierarchy"))

(unless (member verilog-ext-tests-test-dir load-path)
  (add-to-list 'load-path verilog-ext-tests-test-dir))

(require 'verilog-ext-tests-imenu)
(require 'verilog-ext-tests-navigation)
(require 'verilog-ext-tests-font-lock)
(require 'verilog-ext-tests-utils)
(require 'verilog-ext-tests-beautify)
(require 'verilog-ext-tests-indent)
(require 'verilog-ext-tests-hierarchy)
(require 'verilog-ext-tests-tags)
(require 'verilog-ext-tests-workspace)

(message "Emacs version: %s" emacs-version)
(if (< emacs-major-version 29)
    (message "Skipping verilog-ext-tests-tree-sitter...")
  ;; Else
  (message "(treesit-available-p): %s" (treesit-available-p))
  (when (treesit-available-p)
    (require 'treesit)
    (message "(treesit-language-available-p 'verilog): %s" (treesit-language-available-p 'verilog))
    (when (treesit-language-available-p 'verilog)
      (message "(functionp 'verilog-ts-mode): %s" (functionp 'verilog-ts-mode))
      (when (functionp 'verilog-ts-mode)
        (require 'verilog-ext-tests-tree-sitter)))))


;;;; Report loaded file
;; TODO: Not sure if this one really reports if functions have been loaded from .eln files
(message "verilog-ext is: %s" (locate-library "verilog-ext"))
;; TODO: `describe-function' is not intended to be used programatically
;; (describe-function 'verilog-ext-hs-setup)

;; INFO: However, if files are compiled successfully, subsequent invocations of Emacs should
;; try to load files from native compiled instead of byte-compiled or interactive ones.


(provide 'verilog-ext-tests)

;;; verilog-ext-tests.el ends here
