;;; verilog-ext-beautify.el --- Verilog-ext Beautify  -*- lexical-binding: t -*-

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

;; Indent, align parameters and ports:
;;  - Interactively for module at point
;;  - Interactively for current buffer
;;  - In batch for files of current directory

;;; Code:

(require 'verilog-ext-nav)

(defun verilog-ext-beautify-block-at-point-indent ()
  "Indent current block at point."
  (interactive)
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

(defun verilog-ext-beautify--module-at-point-align (thing)
  "Align THING of current module at point (ports/parameters)."
  (let ((case-fold-search nil)
        (re "\\(\\s-*\\)(")
        (current-ids (verilog-ext-instance-at-point))
        (idx (cond ((eq thing 'parameters) 1)
                   ((eq thing 'ports) 2)
                   (t (error "Invalid thing to align"))))
        current-module beg end)
    (unless current-ids
      (user-error "Not inside an instance!"))
    (setq current-module (car current-ids))
    (save-excursion
      (goto-char (match-beginning idx))
      (verilog-re-search-forward "(" nil t)
      (verilog-forward-syntactic-ws)
      (setq beg (point))
      (verilog-backward-up-list -1)
      (backward-char)
      (verilog-backward-syntactic-ws)
      (setq end (point)))
    (align-regexp beg end re 1 1 nil)
    (if (eq idx 1)
        (message "Parameters of %s aligned..." current-module)
      (message "Ports of %s aligned..." current-module))))

(defun verilog-ext-beautify--module-at-point-align-ports ()
  "Align ports of current module."
  (interactive)
  (verilog-ext-beautify--module-at-point-align 'ports))

(defun verilog-ext-beautify--module-at-point-align-params ()
  "Align parameters of current module."
  (interactive)
  (verilog-ext-beautify--module-at-point-align 'parameters))

(defun verilog-ext-beautify-module-at-point-indent ()
  "Indent current module."
  (interactive)
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

(defun verilog-ext-beautify-module-at-point ()
  "Beautify current module:
- Indent
- Align ports
- Align parameters"
  (interactive)
  (save-excursion
    (verilog-ext-beautify-module-at-point-indent)
    (verilog-ext-beautify--module-at-point-align-ports)
    (verilog-ext-beautify--module-at-point-align-params)))

(defun verilog-ext-beautify-current-buffer ()
  "Beautify current buffer:
- Indent whole buffer
- Beautify every instantiated module
- Untabify and delete trailing whitespace"
  (interactive)
  (save-excursion
    (verilog-ext-indent-region (point-min) (point-max))
    (goto-char (point-min))
    (while (verilog-ext-find-module-instance-fwd)
      (verilog-ext-beautify-module-at-point))
    (untabify (point-min) (point-max))
    (delete-trailing-whitespace (point-min) (point-max))))

(defun verilog-ext-beautify-files (files)
  "Beautify Verilog FILES.
FILES is a list of strings containing the filepaths."
  (dolist (file files)
    (unless (file-exists-p file)
      (error "File %s does not exist! Aborting!" file)))
  (save-window-excursion
    (dolist (file files)
      (find-file file)
      (verilog-mode)
      (verilog-ext-beautify-current-buffer)
      (write-file file))))

(defun verilog-ext-beautify-dir-files (dir)
  "Beautify Verilog files on DIR."
  (interactive "DDirectory: ")
  (let ((files (verilog-ext-dir-files dir)))
    (verilog-ext-beautify-files files)))


(provide 'verilog-ext-beautify)

;;; verilog-ext-beautify.el ends here
