;;; verilog-imenu.el --- Verilog Imenu  -*- lexical-binding: t -*-

;; Copyright (C) 2022 Gonzalo Larumbe

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
;; Improved `imenu' functionality for Verilog:
;;  - Show instances of current module
;;  - Show classes and their methods
;;
;;; Code:

(require 'imenu)
(require 'hideshow)
(require 'verilog-mode)
(require 'verilog-utils)
(require 'verilog-navigation)

;;;; Regexps, vars
(defconst verilog-ext-imenu-top-re        "^\\s-*\\(?1:connectmodule\\|m\\(?:odule\\|acromodule\\)\\|p\\(?:rimitive\\|rogram\\|ackage\\)\\)\\(\\s-+automatic\\)?\\s-+\\(?2:[a-zA-Z0-9_.:]+\\)")
(defconst verilog-ext-imenu-localparam-re "^\\s-*localparam\\(?1:\\s-+\\(logic\\|bit\\|int\\|integer\\)\\s-*\\(\\[.*\\]\\)?\\)?\\s-+\\(?2:[a-zA-Z0-9_.:]+\\)")
(defconst verilog-ext-imenu-define-re     "^\\s-*`define\\s-+\\([a-zA-Z0-9_.:]+\\)")
(defconst verilog-ext-imenu-assign-re     "^\\s-*assign\\s-+\\([a-zA-Z0-9_.:]+\\)")
(defconst verilog-ext-imenu-generate-re   "^\\s-*generate[ \t\n]*\\(?1:.*\\)")
(defconst verilog-ext-imenu-always-re     "^\\s-*always\\(_ff\\|_comb\\|_latch\\)?\\s-*\\(.*\\)\\(begin\\)?[ |\n]*\\(.*\\)")
(defconst verilog-ext-imenu-initial-re    "^\\s-*initial\\s-+\\(.*\\)\\(begin\\)?[ |\n]*\\(.*\\)")

(defvar verilog-ext-imenu-generic-expression
  `(;; Search by regexp
    (nil                ,verilog-ext-imenu-top-re 2)
    ("*Localparams*"    ,verilog-ext-imenu-localparam-re 2)
    ("*Defines*"        ,verilog-ext-imenu-define-re 1)
    ("*Assigns*"        ,verilog-ext-imenu-assign-re 1)
    ("*Generates*"      ,verilog-ext-imenu-generate-re 1)
    ("*Always blocks*"  ,verilog-ext-imenu-always-re 4)
    ("*Initial blocks*" ,verilog-ext-imenu-initial-re 3)
    ;; Search by function
    ("*Task/Func*" verilog-ext-imenu-find-tf-outside-class-bwd 1)
    ("*Instances*" verilog-ext-find-module-instance-bwd 1))) ; Use capture group index 3 to get instance name


;;;; Tree
(defun verilog-ext-imenu-find-tf-outside-class-bwd ()
  "Find backwards tasks and functions outside classes."
  (let (found pos)
    (save-excursion
      (while (and (not found)
                  (verilog-ext-find-function-task-bwd))
        (when (not (verilog-ext-point-inside-block-p 'class))
          (setq found t)
          (setq pos (point)))))
    (when found
      (goto-char pos))))

(defun verilog-ext-imenu--format-class-item-label (type name)
  "Return Imenu label for single node using TYPE and NAME."
  (let ((short-type (pcase type
                      ("task"     (propertize "(t)" 'face 'italic))
                      ("function" (propertize "(f)" 'face 'italic))
                      ("class"    "")
                      (_          type))))
    (format "%s %s" name short-type)))

(defun verilog-ext-imenu--class-put-parent (type name pos tree)
  "Create parent node (classes).
Use TYPE and NAME to format the node name.
Create cons cell with the label and the POS if it is a leaf node.
Otherwsise create the cons cell with the label and the TREE."
  (let* ((label (verilog-ext-imenu--format-class-item-label type name)))
    (if (not tree)
        (cons label pos)
      (cons label tree))))

(defun verilog-ext-imenu--build-class-tree (&optional tree)
  "Build the imenu class alist TREE recursively.
Find recursively tasks and functions inside classes."
  (save-restriction
    (narrow-to-region (point-min) (point))
    (let* ((pos (progn
                  (verilog-ext-search-class-backwards)
                  (verilog-forward-sexp)
                  (verilog-re-search-backward "\\<\\(function\\|task\\|class\\)\\>" nil t)))
           (type (when (and pos
                            (or (looking-at verilog-ext-task-re)
                                (looking-at verilog-ext-function-re)
                                (verilog-ext-looking-at-class-declaration)))
                   (match-string-no-properties 1)))
           (name (match-string-no-properties 3))
           (label (when name
                    (verilog-ext-imenu--format-class-item-label type name))))
      (cond ((not pos)
             nil)
            ((verilog-ext-looking-at-class-declaration)
             (verilog-ext-imenu--class-put-parent type name pos tree))
            ((or (looking-at verilog-ext-task-re)
                 (looking-at verilog-ext-function-re))
             (verilog-ext-imenu--build-class-tree (cons (cons label pos) tree)))
            (t ; Build subtrees recursively
             (verilog-ext-imenu--build-class-tree
              (cons (verilog-ext-imenu--build-class-tree
                     (list (cons label pos))) tree)))))))

(defun verilog-ext-imenu-classes-index ()
  "Create entries of tasks and functions within classes."
  (save-excursion
    (goto-char (point-max))
    (let ((index)
          (tree))
      (while (setq tree (verilog-ext-imenu--build-class-tree))
        (setq index (cons tree index)))
      (when index
        (list (cons "Classes" index))))))

(defun verilog-ext-imenu-index ()
  "Index builder function for Verilog Imenu.
Makes use of `verilog-ext-imenu-generic-expression' for everything but classes
and methods.  These are collected with `verilog-ext-imenu-classes-index'."
  (append (verilog-ext-imenu-classes-index)
          (imenu--generic-function verilog-ext-imenu-generic-expression)))

(defun verilog-ext-imenu-hook ()
  "Imenu hook to create entries."
  (setq-local imenu-create-index-function #'verilog-ext-imenu-index))


;;;;; Setup
(add-hook 'verilog-mode-hook #'verilog-ext-imenu-hook)


;;;; Imenu-list
(defun verilog-ext-imenu-hide-all (&optional first)
  "Hide all the blocks at `imenu-list' buffer.
If optional arg FIRST is non-nil show first Imenu block
which by default corresponds to *instances*."
  (if (string-equal major-mode "imenu-list-major-mode")
      (progn
        (goto-char (point-min))
        (while (< (point) (point-max))
          (hs-hide-block)
          (line-move-visual 1))
        (goto-char (point-min))
        (when first
          (hs-show-block)))
    (message "Not in imenu-list mode !!")))

;;;###autoload
(defun verilog-ext-imenu-list ()
  "Wrapper for `imenu-list' for Verilog mode with `verilog-ext'."
  (interactive)
  (imenu-list)
  (verilog-ext-imenu-hide-all t))



;;;; Provide
(provide 'verilog-imenu)

;;; verilog-imenu.el ends here
