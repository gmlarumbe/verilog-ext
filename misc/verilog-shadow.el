;;; verilog-shadow.el --- Verilog Shadow Buffers  -*- lexical-binding: t -*-

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
;; This was an attempt to create buffers without comments for better parsing.
;; Comments are a major problem for regexp-based parsing, in particular in
;; multiline constructs (e.g. a module instance).  It has been workedaround in
;; `verilog-navigation' by using `verilog-re-search-forward', which ignores
;; comments but limits these searchs to one word per regexp.
;;
;; Anyway, this package is left here for the unlikely case this could be of use
;; to someone willing to use it, maybe as a starting point, to add new
;; functionality. However, there seem to be better alternatives, like using a
;; parser based on an external application (e.g. tree-sitter, verilator, slang
;; or verible).
;;
;;; Code:


(defun verilog-ext-shadow-buffer ()
  (concat " #" buffer-file-name "#"))

(defun verilog-ext-shadow-buffer-create ()
  "Create shadow buffer if it does not already exist."
  (let ((buf (verilog-ext-shadow-buffer))
        (orig (current-buffer)))
    (unless (get-buffer buf)
      (get-buffer-create buf))
    (with-current-buffer buf
      (erase-buffer)
      (insert-buffer-substring-no-properties orig)
      (verilog-ext-shadow-replace-comments-with-blanks)
      (goto-char (point-min)))))

(defun verilog-ext-shadow-buffer-update ()
  "Update shadow buffer and fontify."
  (verilog-ext-shadow-buffer-create)
  (font-lock-fontify-block))

(defun verilog-ext-shadow-buffer-kill ()
  "Kill shadow buffer after killing its buffer to avoid Emacs cluttering."
  (let ((buf (verilog-ext-shadow-buffer)))
    (when (get-buffer buf)
      (kill-buffer buf))))

;; TODO: Still seems very slow to be used for syntax-higlighting by maintaining point position
(defun verilog-ext-shadow-replace-comments-with-blanks ()
  "Remove comments from current buffer and replace them with blanks.
Main purpose is to have a reformatted buffer without comments that has
the same structure (point) as original buffer."
  (let ((unicode-spc 32)
        posA posB num)
    (save-excursion
      ;; Remove // style comments
      (goto-char (point-min))
      (while (re-search-forward "//" (point-max) :noerror)
        (backward-char 2)
        (setq posA (point))
        (setq posB (point-at-eol))
        (setq num (- posB posA))
        (kill-line)
        (insert-char unicode-spc num))
      ;; Remove /* */ style comments
      (goto-char (point-min))
      (while (re-search-forward "/\\*" (point-max) :noerror)
        (backward-char 2)
        (setq posA (point))
        (re-search-forward "\\*/" (point-max) :noerror)
        (setq posB (point))
        (setq num (- posB posA))
        (kill-backward-chars num)
        (insert-char unicode-spc num)))))

;;;###autoload
(defmacro with-verilog-shadow (&rest body)
  "Ensure command is executed in associated verilog shadow buffer."
  (declare (indent 0) (debug t))
  `(save-excursion
     (unless (get-buffer (verilog-ext-shadow-buffer))
       (verilog-ext-shadow-buffer-create))
     (let ((orig-pos (point)))
       (with-current-buffer (verilog-ext-shadow-buffer)
         (goto-char orig-pos)
         ,@body))))

;;;###autoload
(define-minor-mode verilog-shadow-mode
  "Use verilog shadow buffers for regexp parsing to detect instances.
Shadow buffers are same buffers but without comments."
  :global nil
  (if verilog-shadow-mode
      (progn
        ;; Enable
        (add-hook 'verilog-mode-hook (lambda () (add-hook 'after-save-hook #'verilog-ext-shadow-buffer-update nil :local)))
        (add-hook 'verilog-mode-hook (lambda () (add-hook 'kill-buffer-hook #'verilog-ext-shadow-buffer-kill nil :local))))
    ;; Disable
    (remove-hook 'verilog-mode-hook (lambda () (add-hook 'after-save-hook #'verilog-ext-shadow-buffer-update nil :local)))
    (remove-hook 'verilog-mode-hook (lambda () (add-hook 'kill-buffer-hook #'verilog-ext-shadow-buffer-kill nil :local)))))


(provide 'verilog-shadow)

;;; verilog-shadow.el ends here
