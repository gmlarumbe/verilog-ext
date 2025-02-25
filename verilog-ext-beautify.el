;;; verilog-ext-beautify.el --- Verilog-ext Beautify  -*- lexical-binding: t -*-

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

;; Indent, align parameters and ports:
;;  - Interactively for module at point
;;  - Interactively for current buffer
;;  - In batch for list of files and files of current directory

;;; Code:

(require 'verilog-ext-nav)


(defgroup verilog-ext-beautify nil
  "Verilog-ext beautify"
  :group 'verilog-ext)

(defcustom verilog-ext-beautify-instance-extra nil
  "Set to non-nil to perform extra formatting on instances."
  :type 'boolean
  :group 'verilog-ext-beautify)


(defun verilog-ext-beautify-block-at-point-indent ()
  "Indent current block at point."
  (let ((data (verilog-ext-block-at-point :return-pos))
        start-pos end-pos block name)
    (unless data
      (user-error "Not inside a block"))
    (save-excursion
      (setq block (alist-get 'type data))
      (setq name (alist-get 'name data))
      (goto-char (alist-get 'beg-point data))
      (setq start-pos (line-beginning-position))
      (goto-char (alist-get 'end-point data))
      (setq end-pos (line-end-position))
      (verilog-ext-indent-region start-pos end-pos)
      (message "Indented %s : %s" block name))))

(defun verilog-ext-beautify--module-at-point-indent ()
  "Indent current module."
  (let ((case-fold-search nil)
        (current-ids (verilog-ext-instance-at-point))
        current-module beg end)
    (unless current-ids
      (user-error "Not inside an instance!"))
    (setq current-module (car current-ids))
    (save-excursion
      (goto-char (match-beginning 0))
      (beginning-of-line)
      (setq beg (point))
      (goto-char (match-end 0))
      (end-of-line)
      (setq end (point)))
    (verilog-ext-indent-region beg end)
    (message "Indented %s" current-module)))

(defun verilog-ext-beautify--module-at-point-align (thing)
  "Align THING of current module at point (ports/parameters)."
  (let ((case-fold-search nil)
        (re-open-par          "\\(\\s-*\\)(")                 ; Port opening parenthesis
        (re-blank-open-par    "\\(\\s-*\\)(\\(\\s-*\\)")      ; Set 1 blank after port opening parenthesis
        (re-blank-closing-par "\\(\\s-*\\))")                 ; Set 1 blank before port closing parenthesis
        (re-port-comma        "\\(\\s-*\\),")                 ; Remove blanks between closing parenthesis and port comma
        (re-comment           "\\(\\(\\,\\|)\\)\\s-*\\)\/\/") ; Leave 1 blank before port inline comments
        (current-ids (verilog-ext-instance-at-point))
        (idx (cond ((eq thing 'parameters) 1)
                   ((eq thing 'ports) 2)
                   (t (error "Invalid thing to align"))))
        (beg (make-marker))
        (end (make-marker))
        (comment-end (make-marker))
        current-module)
    (unless current-ids
      (user-error "Not inside an instance!"))
    (setq current-module (car current-ids))
    (save-excursion
      (goto-char (match-beginning idx))
      (verilog-re-search-forward "(" nil t)
      (verilog-forward-syntactic-ws)
      (set-marker beg (point))
      (verilog-backward-up-list -1)
      (backward-char)
      (set-marker comment-end (point))
      (verilog-backward-syntactic-ws)
      (set-marker end (point)))
    (align-regexp beg end re-open-par 1 1 t)
    (when verilog-ext-beautify-instance-extra
      (align-regexp beg end re-blank-open-par 2 1 t)
      (align-regexp beg end re-blank-closing-par 1 1 t)
      (align-regexp beg end re-port-comma 1 0 t)
      (align-regexp beg comment-end re-comment 1 2 nil))
    (if (eq idx 1)
        (message "Parameters of %s aligned..." current-module)
      (message "Ports of %s aligned..." current-module))))

(defun verilog-ext-beautify--module-at-point-align-ports ()
  "Align ports of current module."
  (verilog-ext-beautify--module-at-point-align 'ports))

(defun verilog-ext-beautify--module-at-point-align-params ()
  "Align parameters of current module."
  (verilog-ext-beautify--module-at-point-align 'parameters))

(defun verilog-ext-beautify-module-at-point ()
  "Beautify current module:
- Indent
- Align ports
- Align parameters"
  (interactive)
  (save-excursion
    (verilog-ext-beautify--module-at-point-indent)
    (verilog-ext-beautify--module-at-point-align-ports)
    (verilog-ext-beautify--module-at-point-align-params)))

(defun verilog-ext-beautify-block-at-point ()
  "Beautify/indent block at point.

If block is an instance, also align parameters and ports."
  (interactive)
  ;; Precedence is relevant in the subsequent conditional clause
  (cond (;; Tree-sitter implementation
         (eq major-mode 'verilog-ts-mode)
         (verilog-ts-beautify-block-at-point))
        (;; Module instance
         (and verilog-ext-file-allows-instances
              (verilog-ext-instance-at-point))
         (verilog-ext-beautify-module-at-point))
        (t
         (verilog-ext-beautify-block-at-point-indent))))

(defun verilog-ext-beautify-current-buffer ()
  "Beautify current buffer:
- Indent whole buffer
- Beautify every instantiated module
- Untabify and delete trailing whitespace"
  (interactive)
  (if (eq major-mode 'verilog-ts-mode)
      ;; `verilog-ts-mode' based beautifying
      (verilog-ts-beautify-current-buffer)
    ;; `verilog-mode' based beautifying
    (verilog-ext-indent-region (point-min) (point-max))
    (save-excursion
      (goto-char (point-min))
      (while (verilog-ext-find-module-instance-fwd)
        (verilog-ext-beautify-module-at-point)))
    (untabify (point-min) (point-max))
    (delete-trailing-whitespace (point-min) (point-max))))

(defun verilog-ext-beautify-files (files ts-mode)
  "Beautify Verilog FILES.

FILES is a list of strings containing the filepaths.

If TS-MODE is non-nil use tree-sitter implementation if `verilog-ts-mode' is
available."
  (dolist (file files)
    (unless (file-exists-p file)
      (error "File %s does not exist! Aborting!" file)))
  (save-window-excursion
    (dolist (file files)
      (message "Processing %s..." file)
      (with-temp-file file
        (insert-file-contents file)
        (if ts-mode
            (progn
              (verilog-ts-mode)
              (verilog-ts-beautify-current-buffer))
          (verilog-ext-with-no-hooks
            (verilog-mode))
          (verilog-ext-beautify-current-buffer))))))

(defun verilog-ext-beautify-dir-files (dir &optional ts-mode)
  "Beautify Verilog files on DIR.

Include subdirectory files recursively.

With prefix arg, or if TS-MODE is non-nil, use `verilog-ts-mode' beautifying
implementation."
  (interactive "DDirectory: \nP")
  (let ((files (verilog-ext-dir-files dir :recursive)))
    (verilog-ext-beautify-files files ts-mode)))


(provide 'verilog-ext-beautify)

;;; verilog-ext-beautify.el ends here
