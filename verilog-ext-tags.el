;;; verilog-ext-tags.el --- Verilog-ext Tags  -*- lexical-binding: t -*-

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

;; Tag collection for jump to definition/reference and semantic completion.

;;; Code:

(require 'verilog-ext-nav)


(defmacro verilog-ext-tags-table-push-tag (table tag type desc &optional file parent)
  "Push TAG in hash table TABLE.

TAG is of string type TYPE and with string description DESC and located in FILE
for `xref'.

Optional arg PARENT is the module where TAG is defined/instantiated for dot
completion."
  (declare (indent 0) (debug t))
  `(setq ,table (verilog-ext-tags-table-add-entry ,table ,tag ,type ,desc ,file ,parent)))

(defmacro verilog-ext-tags-table-push-definitions (tag-type table &optional file start limit parent)
  "Push definitions of TAG-TYPE inside hash table TABLE.

Optional arg FILE might be specified for the cases when a temp-buffer without an
associated file is being parsed.

Limit search between START and LIMIT if provided, otherwise search the whole
buffer.

Optional arg PARENT is the module where TAG is defined/instantiated for dot
completion."
  (declare (indent 0) (debug t))
  `(setq ,table (verilog-ext-tags-get-definitions ,tag-type ,table ,file ,start ,limit ,parent)))

(defmacro verilog-ext-tags-table-push-references (table &optional defs-table file start limit)
  "Push references found in FILE inside hash table TABLE.

Optional definitions table DEFS-TABLE is used to filter out references that have
already been parsed as definitions.

Limit search between START and LIMIT if provided, otherwise search the whole
buffer."
  (declare (indent 0) (debug t))
  `(setq ,table (verilog-ext-tags-get-references ,table ,defs-table ,file ,start ,limit)))

(defun verilog-ext-tags-tag-properties (type desc &optional file)
  "Return :locs properties for current tag.
These include tag TYPE and description DESC as well as FILE and current line."
  `(:type ,type
    :desc ,desc
    :file ,(or file buffer-file-name)
    :line ,(line-number-at-pos)))

(defun verilog-ext-tags-table-add-entry (table tag type desc &optional file parent)
  "Add entry for TAG in hash-table TABLE.

It is needed to provide TYPE, description DESC and FILE properties to add the
entry in the table.

Optional arg PARENT is the module where TAG is defined/instantiated for dot
completion.

If there is no entry in the table for TAG add one.  Otherwise update the
existing one with current location properties."
  (let ((tag-value (gethash tag table))
        (parent-value (gethash parent table))
        locs-plist loc-new parent-items)
    (if (not tag-value)
        ;; Add tag with properties
        (puthash tag `(:items nil :locs (,(verilog-ext-tags-tag-properties type desc file))) table)
      ;; Otherwise update existing tag properties
      (setq locs-plist (plist-get tag-value :locs))
      (setq loc-new (verilog-ext-tags-tag-properties type desc file))
      (unless (member loc-new locs-plist)
        (push loc-new locs-plist)
        (plist-put tag-value :locs locs-plist)
        (puthash tag `(:items ,(plist-get tag-value :items) :locs ,locs-plist) table)))
    (when parent
      (if (not parent-value)
          (error "%s should be in the table" parent)
        (setq parent-items (plist-get parent-value :items))
        (unless (member tag parent-items)
          (plist-put parent-value :items (append parent-items `(,tag)))
          (puthash parent parent-value table))))
    table))

(defun verilog-ext-tags-get-definitions (tag-type table &optional file start limit parent)
  "Add definitions of TAG-TYPE to hash-table TABLE for FILE.

Limit search between START and LIMIT if provided.

Optional arg PARENT is the module where TAG is defined/instantiated for dot
completion."
  (let ((ignore-paren-decl (eq tag-type 'declarations-no-parens))
        tag type desc data inner-start inner-limit)
    (unless start (setq start (point-min)))
    (unless limit (setq limit (point-max)))
    (when (eq tag-type 'declarations-no-parens)
      (setq tag-type 'declarations))
    (save-match-data
      (save-excursion
        (goto-char start)
        (pcase (symbol-name tag-type)
          ("declarations" (while (verilog-re-search-forward (verilog-get-declaration-re) limit :no-error)
                            (setq type (string-trim (match-string-no-properties 0)))
                            (setq tag (thing-at-point 'symbol :no-props))
                            (unless (or (member tag verilog-keywords)
                                        (when ignore-paren-decl
                                          (verilog-in-parenthesis-p))
                                        (not tag))
                              (setq desc (verilog-ext-tags-desc))
                              (verilog-ext-tags-table-push-tag table tag type desc file parent))))
          ("tf" (while (setq data (verilog-ext-find-function-task-fwd limit))
                  (setq type (alist-get 'type data))
                  (setq tag (match-string-no-properties 1))
                  (setq desc (verilog-ext-tags-desc))
                  (verilog-ext-tags-table-push-tag table tag type desc file parent)
                  ;; Get tasks and function declarations
                  (save-excursion
                    (when (< (setq inner-start (alist-get 'pos data))
                             (setq inner-limit (save-excursion
                                                 (verilog-re-search-backward "\\<\\(function\\|task\\)\\>" (line-beginning-position) :no-error)
                                                 (verilog-ext-pos-at-forward-sexp))))
                      (verilog-ext-tags-table-push-definitions 'declarations-no-parens table file inner-start inner-limit tag)))))
          ("instances" (while (verilog-ext-find-module-instance-fwd limit)
                         (setq tag (match-string-no-properties 2))
                         (setq type (match-string-no-properties 1))
                         (setq desc (verilog-ext-tags-desc))
                         (verilog-ext-tags-table-push-tag table tag type desc file parent)))
          ("structs" (while (setq data (verilog-ext-find-struct))
                       (setq tag (alist-get 'name data))
                       (setq type "struct")
                       (setq desc (verilog-ext-tags-desc))
                       (verilog-ext-tags-table-push-tag table tag type desc file parent)
                       ;; Get struct items
                       (save-excursion
                         (verilog-ext-backward-syntactic-ws)
                         (setq inner-limit (point))
                         (setq inner-start (verilog-ext-pos-at-backward-sexp))
                         (verilog-ext-tags-table-push-definitions 'declarations table file inner-start inner-limit tag))))
          ("classes" (while (setq data (verilog-ext-find-class-fwd limit))
                       (setq type "class")
                       (setq tag (alist-get 'name data))
                       (setq desc (verilog-ext-tags-desc))
                       (verilog-ext-tags-table-push-tag table tag type desc file parent)
                       ;; Get class items
                       (save-excursion
                         (verilog-re-search-backward "\\<class\\>" nil :no-error)
                         (setq inner-start (point))
                         (setq inner-limit (verilog-ext-pos-at-forward-sexp)))
                       (dolist (defs '(declarations-no-parens tf structs))
                         (verilog-ext-tags-table-push-definitions defs table file inner-start inner-limit tag))))
          ("top-items" (while (verilog-re-search-forward verilog-ext-top-re nil :no-error)
                         (setq tag (match-string-no-properties 3))
                         (setq type (match-string-no-properties 1))
                         (setq desc (verilog-ext-tags-desc))
                         (verilog-ext-tags-table-push-tag table tag type desc file)
                         ;; Get top-block items
                         (setq inner-start (match-beginning 1))
                         (save-excursion
                           (goto-char inner-start)
                           (setq inner-limit (verilog-ext-pos-at-forward-sexp)))
                         (let ((top-items-defs '(declarations tf structs classes)))
                           (when (string-match "\\<\\(module\\|interface\\)\\>" type)
                             (setq top-items-defs (append top-items-defs '(instances))))
                           (dolist (defs top-items-defs)
                             (verilog-ext-tags-table-push-definitions defs table file inner-start inner-limit tag)))))
          (_ (error "Unsupported tag type")))))
    ;; Return table initial-table
    table))

(defun verilog-ext-tags-get-references (table &optional defs-table file start limit)
  "Add refrences to hash-table TABLE.

Optional definitions table DEFS-TABLE is used to filter out references that have
already been parsed as definitions.

Optional FILE is explicitly provided for the case when references are fetched
from a temp-buffer.

Limit search between START and LIMIT if provided."
  (let (tag type desc begin existing-def existing-def-props)
    (unless start (setq start (point-min)))
    (unless limit (setq limit (point-max)))
    (save-match-data
      (save-excursion
        (goto-char start)
        (while (verilog-re-search-forward verilog-identifier-sym-re limit :no-error)
          (setq begin (match-beginning 0))
          (setq tag (match-string-no-properties 0))
          (setq type nil) ; Does not apply for references
          (setq desc (verilog-ext-tags-desc))
          (unless (or (member tag verilog-keywords) ; Filter verilog keywords
                      ;; Filter existing definitions
                      (and defs-table
                           (setq existing-def (gethash tag defs-table))
                           (setq existing-def-props (plist-get existing-def :locs))
                           (progn (catch 'exit
                                    (dolist (prop-list existing-def-props)
                                      (when (and (eq (plist-get prop-list :file) file)
                                                 (eq (plist-get prop-list :line) (line-number-at-pos)))
                                        (throw 'exit t))))))
                      ;; Filter bit-width expressions
                      (save-excursion
                        (goto-char begin)
                        (eq (preceding-char) ?')))
            (verilog-ext-tags-table-push-tag table tag type desc file)))))
    ;; Return updated table
    table))

(defun verilog-ext-tags-desc ()
  "Return description for current TAG.
Meant to be used for `xref' backend."
  (string-trim (buffer-substring-no-properties (line-beginning-position) (line-end-position))))


(provide 'verilog-ext-tags)

;;; verilog-ext-tags.el ends here
