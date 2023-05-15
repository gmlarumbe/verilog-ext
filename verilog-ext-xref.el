;;; verilog-ext-xref.el --- Verilog-ext Xref Backend  -*- lexical-binding: t -*-

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

;; Find definitions and references builtin backend.

;;; Code:

(require 'verilog-ext-workspace)

(defun verilog-ext-xref--find-symbol (symbol type)
  "Return list of TYPE xref objects for SYMBOL."
  (let* ((table (cond ((eq type 'def)
                       verilog-ext-workspace-tags-defs-table)
                      ((eq type 'ref)
                       verilog-ext-workspace-tags-refs-table)
                      (t
                       (error "Wrong table"))))
         (table-entry (gethash symbol table))
         (entry-locs (plist-get table-entry :locs))
         file line column desc xref-entries)
    (when table-entry
      (dolist (loc entry-locs)
        (setq file (plist-get loc :file))
        (setq line (plist-get loc :line))
        (setq column nil)
        (setq desc (replace-regexp-in-string (concat "\\_<" symbol "\\_>")
                                             (propertize symbol 'face '(:foreground "goldenrod" :weight bold))
                                             (plist-get loc :desc)
                                             :fixedcase))
        (push (xref-make desc (xref-make-file-location file line column)) xref-entries)))
    xref-entries))

(defun verilog-ext-xref-backend ()
  "Verilog-ext backend for Xref."
  (when (verilog-ext-workspace-root)
    'verilog-ext-xref))

(cl-defmethod xref-backend-identifier-at-point ((_backend (eql verilog-ext-xref)))
  "Implementation of `xref-backend-identifier-at-point' for verilog-ext-xref."
  (thing-at-point 'symbol :no-props))

(cl-defmethod xref-backend-definitions ((_backend (eql verilog-ext-xref)) symbol)
  "Implementation of `xref-backend-definitions' for verilog-ext-xref.
Find definitions of SYMBOL."
  (verilog-ext-xref--find-symbol symbol 'def))

(cl-defmethod xref-backend-references ((_backend (eql verilog-ext-xref)) symbol)
  "Implementation of `xref-backend-references' for verilog-ext-xref.
Find references of SYMBOL."
  (verilog-ext-xref--find-symbol symbol 'ref))

(cl-defmethod xref-backend-identifier-completion-table ((_backend (eql verilog-ext-xref)))
  "Implementation of `xref-backend-identifier-completion-table'."
  nil)

(defun verilog-ext-xref-backend-enable ()
  "Enable `verilog-ext-xref' backend on current buffer.
Still experimental.  Removes the rest of xref backends."
  (setq-local xref-backend-functions '(verilog-ext-xref-backend t)))

(defun verilog-ext-xref-set (&optional disable)
  "Setup `verilog-ext' to use builtin `xref' backend.
If optional arg DISABLE is provided, remove the hook that enabled the backend.
Still experimental:
- Removes the rest of xref backends by being a hook for `verilog-ext-mode'
instead of to `verilog-mode', since the first one is loaded later and overwrites
the hook value.  Otherwise, hooks are not ran in a specific order, and rely on
the priority argument."
  (if disable
      (remove-hook 'verilog-ext-mode-hook #'verilog-ext-xref-backend-enable :local)
    (add-hook 'verilog-ext-mode-hook #'verilog-ext-xref-backend-enable nil :local)))



(provide 'verilog-ext-xref)

;;; verilog-ext-xref.el ends here
