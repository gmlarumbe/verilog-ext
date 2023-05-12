;;; verilog-ext-imenu.el --- Verilog-ext Imenu  -*- lexical-binding: t -*-

;; Copyright (C) 2022-2023 Gonzalo Larumbe

;; Author: Gonzalo Larumbe <gonzalomlarumbe@gmail.com>
;; URL: https://github.com/gmlarumbe/verilog-ext
;; Version: 0.1.0
;; Package-Requires: ((emacs "28.1") (verilog-mode "2022.12.18.181110314"))

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

;; Improved `imenu' functionality
;;  - Show instances of current module
;;  - Show classes and their methods

;;; Code:

(require 'imenu)
(require 'verilog-ext-nav)


(defconst verilog-ext-imenu-top-re        "^\\s-*\\(?1:connectmodule\\|m\\(?:odule\\|acromodule\\)\\|p\\(?:rimitive\\|rogram\\|ackage\\)\\)\\(\\s-+automatic\\)?\\s-+\\(?2:[a-zA-Z0-9_.:]+\\)")
(defconst verilog-ext-imenu-localparam-re "^\\s-*localparam\\(?1:\\s-+\\(logic\\|bit\\|int\\|integer\\)\\s-*\\(\\[.*\\]\\)?\\)?\\s-+\\(?2:[a-zA-Z0-9_.:]+\\)")
(defconst verilog-ext-imenu-define-re     "^\\s-*`define\\s-+\\([a-zA-Z0-9_.:]+\\)")
(defconst verilog-ext-imenu-assign-re     "^\\s-*assign\\s-+\\([a-zA-Z0-9_.:]+\\)")
(defconst verilog-ext-imenu-generate-re   "^\\s-*generate[ \t\n]*\\(?1:.*\\)")
(defconst verilog-ext-imenu-always-re     "^\\s-*always\\(_ff\\|_comb\\|_latch\\)?\\s-*\\(.*\\)\\(begin\\)?[ |\n]*\\(.*\\)")
(defconst verilog-ext-imenu-initial-re    "^\\s-*initial\\s-+\\(.*\\)\\(begin\\)?[ |\n]*\\(.*\\)")

(defvar verilog-ext-imenu-generic-expression
  `(;; Search by regexp
    ("*Top*"            ,verilog-ext-imenu-top-re 2)
    ("*Localparams*"    ,verilog-ext-imenu-localparam-re 2)
    ("*Defines*"        ,verilog-ext-imenu-define-re 1)
    ("*Assigns*"        ,verilog-ext-imenu-assign-re 1)
    ("*Generates*"      ,verilog-ext-imenu-generate-re 1)
    ("*Always blocks*"  ,verilog-ext-imenu-always-re 4)
    ("*Initial blocks*" ,verilog-ext-imenu-initial-re 3)))

(defun verilog-ext-imenu-find-module-instance-index ()
  "Create imenu entries of modules and instances.
Placing this outside of `imenu--generic-function' avoids running it if
`which-func' is enabled.  It also allows to conditionally disable the index
building if file cannot contain instances."
  (save-excursion
    (goto-char (point-max))
    (let ((group-name "*Instances*")
          index)
      (when verilog-ext-file-allows-instances
        (while (verilog-ext-find-module-instance-bwd)
          ;; Use capture group index 3 to get instance name
          (push (cons (match-string-no-properties 1) (line-beginning-position)) index))
        (when index
          (list (cons group-name index)))))))

(defun verilog-ext-imenu-find-tf-outside-class-index ()
  "Create entries of tasks and functions outside classes.
Group the ones that belong to same external method definitions."
  (save-excursion
    (goto-char (point-max))
    (let ((tf-group-name "*Task/Func*")
          index node data pos name class-name)
      (while (setq data (verilog-ext-find-function-task-bwd))
        (unless (verilog-ext-point-inside-block 'class)
          ;; Get information from the subroutine
          (setq pos (alist-get 'pos data))
          (setq name (alist-get 'name data))
          (setq class-name (alist-get 'class-name data))
          ;; Add element to the tree
          (setq node (cons name pos))
          (if class-name
              ;; Externally declared methods
              (if (not (assoc class-name index))
                  (setq index `((,class-name ,node)))
                ;; Add to existing class
                (setf (cdr (assoc class-name index)) (cons node (cdr (assoc class-name index)))))
            ;; Non-methods
            (if (not (assoc tf-group-name index))
                (setq index `((,tf-group-name ,node)))
              (setf (cdr (assoc tf-group-name index)) (cons node (cdr (assoc tf-group-name index))))))))
      index)))

(defun verilog-ext-imenu--format-class-item-label (type name modifiers)
  "Return Imenu label for single node using TYPE, NAME and MODIFIERS."
  (let* ((prop-name (propertize name 'face '(:foreground "goldenrod" :weight bold)))
         (short-type (pcase type
                       ("task"     " [T]")
                       ("function" " [F]")
                       ("class"    "")
                       (_          type)))
         (modifiers-string (mapconcat (lambda (x) (substring-no-properties x 0 1)) modifiers ""))
         (prop-modifiers (if (string= modifiers-string "")
                             ""
                           (propertize (concat " (" modifiers-string ")") 'face 'italic))))
    (format "%s%s%s" prop-name short-type prop-modifiers)))

(defun verilog-ext-imenu--class-put-parent (type name pos tree modifiers)
  "Create parent node (classes).
Use TYPE, NAME and MODIFIERS to format the node name.
Create cons cell with the label and the POS if it is a leaf node.
Otherwsise create the cons cell with the label and the TREE."
  (let* ((label (verilog-ext-imenu--format-class-item-label type name modifiers)))
    (if (not tree)
        (cons label pos)
      (cons label tree))))

(defun verilog-ext-imenu--build-class-tree (&optional tree)
  "Build the imenu class alist TREE recursively.
Find recursively tasks and functions inside classes."
  (save-restriction
    (narrow-to-region (point-min) (point))
    (let* ((data (and (verilog-ext-find-class-bwd)
                      (verilog-ext-forward-sexp)
                      (verilog-ext-find-function-task-class-bwd)))
           (pos (when (alist-get 'pos data)
                  (save-excursion
                    (goto-char (alist-get 'pos data))
                    (line-beginning-position))))
           (type (alist-get 'type data))
           (name (alist-get 'name data))
           (modifiers (alist-get 'modifiers data))
           (label (when name
                    (verilog-ext-imenu--format-class-item-label type name modifiers))))
      (cond ((not pos)
             nil)
            ((verilog-ext-looking-at-class-declaration)
             (verilog-ext-imenu--class-put-parent type name pos tree modifiers))
            ((or (string= type "function")
                 (string= type "task"))
             (verilog-ext-imenu--build-class-tree (cons (cons label pos) tree)))
            (t ; Build subtrees recursively
             (verilog-ext-imenu--build-class-tree
              (cons (verilog-ext-imenu--build-class-tree
                     (list (cons label pos))) tree)))))))

(defun verilog-ext-imenu-classes-index ()
  "Create entries of tasks and functions within classes."
  (save-excursion
    (goto-char (point-max))
    (let (index tree)
      (while (setq tree (verilog-ext-imenu--build-class-tree))
        (setq index (cons tree index)))
      (when index
        (list (cons "*Classes*" index))))))

(defun verilog-ext-imenu-index ()
  "Index builder function for Verilog Imenu.
Makes use of `verilog-ext-imenu-generic-expression' for everything but classes
and methods.  These are collected with `verilog-ext-imenu-classes-index'."
  (append (verilog-ext-imenu-find-module-instance-index)
          (verilog-ext-imenu-classes-index)
          (verilog-ext-imenu-find-tf-outside-class-index)
          (imenu--generic-function verilog-ext-imenu-generic-expression)))


(provide 'verilog-ext-imenu)

;;; verilog-ext-imenu.el ends here
