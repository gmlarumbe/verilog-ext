;;; verilog-vhier.el --- Verilog-Perl Hierarchy  -*- lexical-binding: t -*-

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
;; - Extract hierarchy of current file with `verilog-ext-vhier-current-file'
;; - Visualize and navigate it with `vhier-outshine-mode'
;;
;; Requires `outshine' and `ggtags'.
;;
;;; Code:

(require 'ggtags)
(require 'outshine)
(require 'verilog-utils)


(defcustom verilog-ext-vhier-command-file nil
  "Verilog-ext vhier command file."
  :type 'string
  :group 'verilog-ext)

(defcustom verilog-ext-vhier-output-file nil
  "Verilog-ext vhier output file."
  :type 'string
  :group 'verilog-ext)


;;;; Hierarchy navigation
(define-minor-mode vhier-outshine-mode
  "Instance navigation frontend for Verilog-Perl `vhier'.
Makes use of processed output under `outline-minor-mode' and `outshine'."
  :lighter " vH"
  :keymap
  '(;; Hide/Show
    ("a"       . outline-show-all)
    ("i"       . outline-show-children)
    ("h"       . outline-show-children)
    ("l"       . vhier-hide-sublevels)
    ("I"       . outline-show-branches)
    (";"       . outline-hide-other)
    ;; Movement
    ("u"       . vhier-up-heading)
    ("C-c C-u" . vhier-up-heading)
    ("n"       . vhier-next-visible-heading)
    ("j"       . vhier-next-visible-heading)
    ("p"       . vhier-previous-visible-heading)
    ("k"       . vhier-previous-visible-heading)
    ("C-c C-n" . vhier-forward-same-level)
    ("C-c C-p" . vhier-backward-same-level)
    ;; Jump
    ("o"       . vhier-outline-jump-to-file)
    ("RET"     . vhier-outline-jump-to-file)
    ("C-j"     . vhier-outline-jump-to-file))
  ;; Enable outshine
  (outshine-mode 1)
  (setq buffer-read-only t)
  (view-mode -1))

(defmacro vhier-outline-nav (vhier-func outline-func)
  "Define function VHIER-FUNC to call OUTLINE-FUNC in a vhier buffer.
Move through headings and point at the beginning of the tag."
  (declare (indent 0) (debug t))
  `(defun ,vhier-func ()
     (interactive)
     (beginning-of-line) ; Required for `outline-hide-sublevels'
     (call-interactively ,outline-func)
     (skip-chars-forward (car (car outshine-promotion-headings)))))

(vhier-outline-nav vhier-previous-visible-heading #'outline-previous-visible-heading)
(vhier-outline-nav vhier-next-visible-heading     #'outline-next-visible-heading)
(vhier-outline-nav vhier-up-heading               #'outline-up-heading)
(vhier-outline-nav vhier-forward-same-level       #'outline-forward-same-level)
(vhier-outline-nav vhier-backward-same-level      #'outline-backward-same-level)
(vhier-outline-nav vhier-hide-sublevels           #'outline-hide-sublevels)

(defun vhier-outline-jump-to-file ()
  "Jump to file at cursor on Verilog-Perl hierarchy file."
  (interactive)
  (unless vhier-outshine-mode
    (error "Vhier mode not enabled on current buffer"))
  (unless (executable-find "global")
    (error "Vhier mode requires global to work"))
  (unless (featurep 'ggtags)
    (error "ggtags not available, required for jumping to a file"))
  (unless (ggtags-find-project)
    (error "Associated GTAGS file not found.  Make sure hierarchy file is in the same folder as its matching GTAGS file"))
  (delete-other-windows)
  (split-window-right)
  (shrink-window-horizontally 40)
  (other-window 1)
  (end-of-line)
  (xref-find-definitions (thing-at-point 'symbol t)))


;;;; Hierarchy extraction
(defvar verilog-ext-vhier-buffer-name "*Verilog-Perl*"
  "Buffer name to use for the hierarchy file.")
(defvar verilog-ext-vhier-shell-cmds-buffer-name "*Verilog-Perl-Shell*"
  "Buffer name to use for the output of the shell commands vppreproc and vhier.")
(defvar verilog-ext-vhier-vhier-args '("--cells"
                                       "--no-missing"
                                       "--missing-modules"))

(defun verilog-ext-vhier-format-hierarchy-write-file (output-file)
  "Process Verilog-Perl buffer and write it to OUTPUT-FILE hierarchy file.
Make an outline/outshine tree-view buffer.  Save as .v extension to allow
compatibility with outshine comments and Gtags/Xref."
  (with-current-buffer (get-buffer verilog-ext-vhier-buffer-name)
    (goto-char (point-min))
    (verilog-ext-replace-regexp-whole-buffer "  " "*")
    (verilog-ext-replace-regexp-whole-buffer "*\\([a-zA-Z0-9_-]\\)" "* \\1")
    (verilog-ext-replace-regexp-whole-buffer "^*" "// *")
    ;; Parse not-used/not-found modules/files
    (goto-char (point-min))
    (re-search-forward "// \\* ")
    (when (re-search-forward "// \\* " nil t)
      (beginning-of-line)
      (open-line 3)
      (forward-line 2)
      (insert "// * Not found module references")
      (verilog-ext-replace-string "// * " "// ** " (point) nil))
    ;; Insert local variables at the end of the file
    (goto-char (point-max))
    (newline 1)
    (insert "\n// * Buffer local variables\n// Local Variables:\n// eval: (vhier-outshine-mode 1)\n// End:\n")
    ;; Insert header to get some info of the file
    (goto-char (point-min))
    (open-line 1)
    (insert (concat "// Hierarchy generated by `verilog-ext' at " (format-time-string "%d-%m-%Y, %H:%M:%S") "\n"))
    (write-file output-file)
    (vhier-outshine-mode)))

(defun verilog-ext-vhier-current-file ()
  "Extract hierarchy of current file module using Verilog-Perl backend."
  (interactive)
  (unless (executable-find "vhier")
    (error "Executable vhier not found"))
  (let* ((library-args (verilog-expand-command "__FLAGS__"))
         (vhier-args (mapconcat #'identity verilog-ext-vhier-vhier-args " "))
         (top-module (verilog-ext-select-file-module buffer-file-name))
         (file-path (or verilog-ext-vhier-output-file
                        (concat (verilog-ext-path-join default-directory "vhier/") top-module ".v")))
         (buf verilog-ext-vhier-buffer-name)
         (buf-err verilog-ext-vhier-shell-cmds-buffer-name)
         (err-msg (format "vhier returned with errors\nCheck %s buffer" buf-err))
         (cmd (concat "vhier "
                      library-args " "
                      vhier-args " "
                      "--top-module " top-module " "
                      (when verilog-ext-vhier-command-file
                        (concat "-f " verilog-ext-vhier-command-file " "))
                      buffer-file-name)))
    (make-directory (file-name-directory file-path) t)
    (unless (= 0 (shell-command cmd buf buf-err))
      (pop-to-buffer buf-err)
      (error err-msg))
    (verilog-ext-vhier-format-hierarchy-write-file file-path)
    (pop-to-buffer (get-file-buffer file-path))))




(provide 'verilog-vhier)

;;; verilog-vhier.el ends here
