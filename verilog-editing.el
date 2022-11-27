;;; verilog-editing.el --- Editing  -*- lexical-binding: t -*-

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
;; Additional functions to edit (System)Verilog source code
;;
;;; Code:

(require 'verilog-mode)
(require 'verilog-utils)
(require 'verilog-navigation)

;;;; Syntax table override functions
(defun verilog-ext-kill-word (&optional arg)
  "Make verilog `kill-word' command stop at underscores.
Optional ARG sets number of words to kill."
  (interactive "p")
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (with-syntax-table table
      (kill-word arg))))

(defun verilog-ext-backward-kill-word (&optional arg)
  "Make verilog `backward-kill-word' command stop at underscores.
Optional ARG sets number of words to kill."
  (interactive "p")
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (with-syntax-table table
      (backward-kill-word arg))))


;;;; Indentation
(defun verilog-ext-indent-block-at-point ()
  "Indent current block at point.
Prevents indentation issues with compiler directives with a modified syntax
table."
  (interactive)
  (let ((table (make-syntax-table verilog-mode-syntax-table))
        (data (verilog-ext-block-at-point))
        start-pos end-pos block name)
    (modify-syntax-entry ?` "w" table)
    (with-syntax-table table
      (unless data
        (user-error "Not inside a block"))
      (save-excursion
        (setq block (alist-get 'type data))
        (setq name (alist-get 'name data))
        (goto-char (alist-get 'beg-point data))
        (setq start-pos (line-beginning-position))
        (goto-char (alist-get 'end-point data))
        (setq end-pos (line-end-position))
        (indent-region start-pos end-pos)
        (message "Indented %s : %s" block name)))))

;;;; Misc
(defun verilog-ext-clean-port-blanks ()
  "Cleans blanks inside port connections of current block."
  (interactive)
  (let ((old-re (concat "\\(?1:^\\s-*\\)\\.\\(?2:" verilog-identifier-re "\\)\\(?3:\\s-*\\)(\\(?4:\\s-*\\)\\(?5:[^ ]+\\)\\(?6:\\s-*\\))"))
        (new-re "\\1.\\2\\3\(\\5\)")
        data start-pos end-pos module-name instance-name)
    (when (setq data (verilog-ext-instance-at-point))
      (setq start-pos (match-beginning 0))
      (setq end-pos (match-end 0))
      (setq module-name (car data))
      (setq instance-name (cadr data))
      (save-excursion
        (goto-char start-pos)
        (while (re-search-forward old-re end-pos :noerror)
          (replace-match new-re)))
      (message "Removed port blanks from %s : %s" module-name instance-name))))

(defun verilog-ext-toggle-connect-port (&optional force-connect)
  "Toggle connect/disconnect port at current line.

Return non-nil if a port regex was found on current line.

If called with universal arg, FORCE-CONNECT will force connection
of current port instead of toggling."
  (interactive "P")
  (let* ((case-fold-search verilog-case-fold)
         (re (concat "\\(?1:^\\s-*\\)\\.\\(?2:" verilog-identifier-re "\\)\\(?3:\\s-*\\)\\(?4:(\\(?5:.*\\))\\)?"))
         port-found port conn sig)
    (save-excursion
      (beginning-of-line)
      (if (verilog-re-search-forward re (line-end-position) t)
          (progn
            (setq port-found t)
            (setq port (match-string-no-properties 2))
            (setq conn (match-string-no-properties 5))
            (if (or (string-equal conn "") force-connect) ; Disconnected or forced connection
                (progn ; Connect
                  (setq sig (read-string (concat "Connect [" port "] to: ") port))
                  (replace-match (concat "\\1.\\2\\3\(" sig "\)") t))
              ;; Else disconnect
              (replace-match (concat "\\1.\\2\\3\(" nil "\)") t)))
        ;; No port found
        (message "No port detected at current line")))
    (when port-found
      (forward-line 1))))

(defun verilog-ext-connect-ports-recursively ()
  "Connect ports of current instance recursively.
Ask for connection of ports until no port is found at current line."
  (interactive)
  (while (verilog-ext-toggle-connect-port :force-connect)
    (verilog-ext-toggle-connect-port :force-connect)))



;;;; Block end comments to block names
;; Many thanks to Kaushal Modi!
(defconst verilog-ext-block-end-keywords-re
  (eval-when-compile
    (verilog-regexp-words
     '("end" "join" "join_any" "join_none" "endchecker" "endclass" "endclocking"
       "endconfig" "endfunction" "endgenerate" "endgroup" "endinterface"
       "endmodule" "endpackage" "endprimitive" "endprogram" "endproperty"
       "endsequence" "endtask")))
  "Regexp to match Verilog/SystemVerilog block end keywords.
IEEE 1800-2012 SystemVerilog Section 9.3.4 Block names.")

(defconst verilog-ext-block-end-keywords-complete-re
  (concat "^\\(?1:\\s-*" verilog-ext-block-end-keywords-re "\\)\\s-*"       ; Blanks and block end keyword
          "//\\s-*\\(\\(block:\\|" verilog-identifier-sym-re "\\s-*::\\)\\s-*\\)*" ; Comments
          "\\(?2:" verilog-identifier-sym-re "\\)\\s-*$"))                 ; Block name to be replaced

(defun verilog-ext-block-end-comments-to-names ()
  "Convert valid block-end comments to ': BLOCK_NAME'.

Examples: endmodule // module_name             → endmodule : module_name
          endfunction // some comment          → endfunction // some comment
          endfunction // class_name::func_name → endfunction : func_name
          end // block: block_name             → end : block_name"
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward verilog-ext-block-end-keywords-complete-re nil :noerror)
      (when (not (member (match-string-no-properties 2) verilog-keywords))
        (replace-match "\\1 : \\2")))))

(define-minor-mode verilog-ext-block-end-comments-to-names-mode
  "Minor mode to convert block end comments to block names after saving a file.
See `verilog-ext-block-end-comments-to-names' for an example."
  :global nil
  (if verilog-ext-block-end-comments-to-names-mode
      (progn
        (add-hook 'before-save-hook #'verilog-ext-block-end-comments-to-names nil :local)
        (message "Enabled verilog-ext-block-end-comments-to-names-mode [current buffer]"))
    (remove-hook 'before-save-hook #'verilog-ext-block-end-comments-to-names :local)
    (message "Disabled verilog-ext-block-end-comments-to-names-mode [current buffer]")))


;;;; Code formatting
(defun verilog-ext-code-formatter-setup ()
  "Setup `apheleia' with Verible code formatter."
  (interactive)
  (require 'apheleia)
  (unless (and (alist-get 'verilog-mode apheleia-mode-alist)
               (alist-get 'verible apheleia-formatters))
    (setq apheleia-mode-alist (assq-delete-all 'verilog-mode apheleia-mode-alist))
    (push '(verilog-mode . verible) apheleia-mode-alist)
    (setq apheleia-formatters (assq-delete-all 'verible apheleia-formatters))
    (push '(verible . ("verible-verilog-format"
                       "--indentation_spaces" (number-to-string verilog-indent-level)
                       "-"))
          apheleia-formatters))
  (if (called-interactively-p 'any)
      (message "Configured %s" (alist-get 'verilog-mode apheleia-mode-alist))
    (alist-get 'verilog-mode apheleia-mode-alist)))



(provide 'verilog-editing)

;;; verilog-editing.el ends here
