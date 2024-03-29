;;; verilog-ext-xref.el --- Verilog-ext Xref Backend  -*- lexical-binding: t -*-

;; Copyright (C) 2022-2024 Gonzalo Larumbe

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

;; Find definitions and references `xref' backend.

;;; Code:

(require 'xref)
(require 'verilog-ext-tags)


(defgroup verilog-ext-xref nil
  "Verilog-ext xref customization."
  :group 'verilog-ext)

(defface verilog-ext-xref-match-face '((t :inherit match))
  "Verilog-ext face used to highlight matches in xref."
  :group 'verilog-ext-xref)


(defun verilog-ext-xref--find-symbol (symbol type)
  "Return list of TYPE xref objects for SYMBOL."
  (let* ((proj (verilog-ext-buffer-proj))
         (table (cond ((eq type 'def)
                       (verilog-ext-aget verilog-ext-tags-defs-table proj))
                      ((eq type 'ref)
                       (verilog-ext-aget verilog-ext-tags-refs-table proj))
                      (t
                       (error "Wrong table"))))
         (table-entry (if table
                          (gethash symbol table)
                        (error "Tags table empty.  Run first `verilog-ext-tags-get' or `verilog-ext-tags-get-async'")))
         (entry-locs (plist-get table-entry :locs))
         (entry-locs-grouped (seq-group-by (lambda (loc)
                                             (equal buffer-file-name (plist-get loc :file)))
                                           entry-locs))
         ;; Locs in current file should show up first
         (entry-locs-sorted (append (alist-get nil entry-locs-grouped)
                                    (alist-get t entry-locs-grouped)))
         file line column desc xref-entries)
    (when entry-locs-sorted
      (dolist (loc entry-locs-sorted)
        (setq file (plist-get loc :file))
        (setq line (plist-get loc :line))
        (setq column (plist-get loc :col))
        (setq desc (replace-regexp-in-string (concat "\\_<" symbol "\\_>")
                                             (propertize symbol 'face 'verilog-ext-xref-match-face)
                                             (plist-get loc :desc)
                                             :fixedcase))
        (push (xref-make desc (xref-make-file-location file line column)) xref-entries)))
    xref-entries))

(defun verilog-ext-xref-backend ()
  "Verilog-ext backend for Xref."
  (let (proj symbol proj-table)
    (and (setq proj (verilog-ext-buffer-proj))
         (setq symbol (thing-at-point 'symbol :no-props))
         (or (and (setq proj-table (verilog-ext-aget verilog-ext-tags-defs-table proj))
                  (gethash symbol proj-table))
             (and (setq proj-table (verilog-ext-aget verilog-ext-tags-refs-table proj))
                  (gethash symbol proj-table)))
         'verilog-ext)))

(cl-defmethod xref-backend-identifier-at-point ((_backend (eql verilog-ext)))
  "Implementation of `xref-backend-identifier-at-point' for verilog-ext-xref."
  (thing-at-point 'symbol :no-props))

(cl-defmethod xref-backend-definitions ((_backend (eql verilog-ext)) symbol)
  "Implementation of `xref-backend-definitions' for verilog-ext-xref.
Find definitions of SYMBOL."
  (verilog-ext-xref--find-symbol symbol 'def))

(cl-defmethod xref-backend-references ((_backend (eql verilog-ext)) symbol)
  "Implementation of `xref-backend-references' for verilog-ext-xref.
Find references of SYMBOL."
  (verilog-ext-xref--find-symbol symbol 'ref))

(cl-defmethod xref-backend-identifier-completion-table ((_backend (eql verilog-ext)))
  "Implementation of `xref-backend-identifier-completion-table'."
  nil)

(defun verilog-ext-xref-backend-enable ()
  "Enable `verilog-ext' backend on current buffer."
  (setq-local xref-backend-functions `(verilog-ext-xref-backend ,@xref-backend-functions)))

(defun verilog-ext-xref-set (&optional disable)
  "Setup `verilog-ext' to use builtin `xref' backend.

If optional arg DISABLE is provided, remove the hook that enabled the backend.

Removes the rest of xref backends by being a hook for `verilog-ext-mode' instead
of to `verilog-mode', since the first one is loaded later and overwrites the
hook value.  Otherwise, hooks are not ran in a specific order, and rely on the
priority argument."
  (if disable
      (remove-hook 'verilog-ext-mode-hook #'verilog-ext-xref-backend-enable)
    (add-hook 'verilog-ext-mode-hook #'verilog-ext-xref-backend-enable)))



(provide 'verilog-ext-xref)

;;; verilog-ext-xref.el ends here
