;;; verilog-ext-typedef.el --- Verilog-ext Typedefs  -*- lexical-binding: t -*-

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

;; Typedef utils

;;; Code:


(require 'verilog-ext-nav)

(defvar verilog-ext-typedef-align-words nil)
(defvar verilog-ext-typedef-align-words-re nil)

(defun verilog-ext-typedef--var-find (regex &optional limit)
  "Search for REGEX and bound to LIMIT.
Match data is expected to fits that one of
`verilog-ext-typedef-var-decl-single-re' or
`verilog-ext-typedef-var-decl-multiple-re'."
  (let (found pos type)
    (save-excursion
      (while (and (not found)
                  (verilog-re-search-forward regex limit t))
        (setq type (match-string-no-properties 1))
        (unless (or (member type verilog-keywords)
                    (save-excursion
                      (goto-char (match-beginning 1))
                      (verilog-in-parenthesis-p)))
          (setq found t)
          (setq pos (point)))))
    (when found
      (goto-char pos)
      type)))

(defun verilog-ext-typedef--var-buffer-update (regex)
  "Scan REGEX on current buffer and update list of user typedefs.
See `verilog-ext-typedef-align-words'.
Used for fontification and alignment."
  (let (type)
    (save-excursion
      (goto-char (point-min))
      (while (setq type (verilog-ext-typedef--var-find regex))
        (unless (member type verilog-ext-typedef-align-words)
          (push type verilog-ext-typedef-align-words))))))

(defun verilog-ext-typedef--tf-args-buffer-update ()
  "Scan functions/tasks arguments on current buffer to update user typedefs list.
See `verilog-ext-typedef-align-words'.
Used for fontification and alignment."
  (let (tf-args arg-proc) ; tf-args is expected to be a list of strings
    (save-excursion
      (goto-char (point-min))
      ;; Iterate over file functions and tasks
      (while (setq tf-args (alist-get 'args (verilog-ext-find-function-task-fwd)))
        (unless (equal tf-args '(""))
          (dolist (arg tf-args)
            ;; Iterate over words of one argument and process them to obtain the typedef
            (setq arg-proc arg)
            ;; Skip verilog keywords
            (while (string-match (concat "^" verilog-ext-keywords-re "\\s-*") arg-proc)
              (setq arg-proc (substring arg-proc (match-end 0) (length arg-proc))))
            ;; Typedef word will be the first one of the argument
            (when (equal 0 (string-match (string-remove-suffix ";" verilog-ext-typedef-var-decl-single-re) arg-proc))
              (setq arg-proc (car (split-string arg-proc " ")))
              (unless (member arg-proc verilog-ext-typedef-align-words)
                (push arg-proc verilog-ext-typedef-align-words)))))))))

(defun verilog-ext-typedef--class-buffer-update ()
  "Scan class declarations on current buffer to update user typedef list."
  (let (word)
    (save-excursion
      (goto-char (point-min))
      (while (setq word (alist-get 'name (verilog-ext-find-class-fwd)))
        (unless (member word verilog-ext-typedef-align-words)
          (push word verilog-ext-typedef-align-words))))))

(defun verilog-ext-typedef--typedef-buffer-update (regex)
  "Scan REGEX typedef declarations on current buffer to update user typedef list."
  (let (word)
    (save-excursion
      (goto-char (point-min))
      (while (verilog-re-search-forward regex nil t)
        (setq word (match-string-no-properties 2))
        (unless (member word verilog-ext-typedef-align-words)
          (push word verilog-ext-typedef-align-words))))))

(defun verilog-ext-typedef--var-decl-update ()
  "Scan and update Verilog buffers and `verilog-ext-typedef-align-words'."
  (verilog-ext-typedef--var-buffer-update verilog-ext-typedef-var-decl-single-re)
  (verilog-ext-typedef--var-buffer-update verilog-ext-typedef-var-decl-multiple-re)
  (verilog-ext-typedef--tf-args-buffer-update)
  (verilog-ext-typedef--class-buffer-update)
  (verilog-ext-typedef--typedef-buffer-update verilog-ext-typedef-class-re)
  (verilog-ext-typedef--typedef-buffer-update verilog-ext-typedef-generic-re))


(provide 'verilog-ext-typedef)

;;; verilog-ext-typedef.el ends here


