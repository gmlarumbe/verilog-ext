;;; verilog-ext-ports.el --- Verilog-ext ports  -*- lexical-binding: t -*-

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

;; Port connections utils

;;; Code:

(require 'verilog-ext-nav)


(defun verilog-ext-ports-clean-blanks ()
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

(defun verilog-ext-ports-toggle-connect (&optional force-connect)
  "Toggle connect/disconnect port at current line.

Return non-nil if a port regex was found on current line.

If called with universal arg, FORCE-CONNECT will force connection
of current port instead of toggling."
  (interactive "P")
  (let* ((case-fold-search verilog-case-fold)
         (re (concat "\\(?1:^\\s-*\\)\\.\\(?2:" verilog-identifier-re "\\)\\(?3:\\s-*\\)\\(?4:(\\s-*\\(?5:" verilog-identifier-re "\\)*\\s-*)\\)?"))
         port-found port conn sig)
    (save-excursion
      (beginning-of-line)
      (if (looking-at re)
          (progn
            (setq port-found t)
            (setq port (match-string-no-properties 2))
            (setq conn (match-string-no-properties 5))
            (if (or (not conn) force-connect) ; Disconnected or forced connection
                (progn ; Connect
                  (setq sig (read-string (concat "Connect [" port "] to: ") port))
                  (looking-at re) ; Needed before `replace-match' to avoid buggy situations
                  (replace-match (concat "\\1.\\2\\3\(" sig "\)") t))
              ;; Else disconnect
              (replace-match (concat "\\1.\\2\\3\(" nil "\)") t)))
        ;; No port found
        (message "No port detected at current line")))
    (when port-found
      (forward-line 1))))

(defun verilog-ext-ports-connect-recursively ()
  "Connect ports of current instance recursively.
Ask for connection of ports until no port is found at current line."
  (interactive)
  (while (verilog-ext-ports-toggle-connect :force-connect)
    (verilog-ext-ports-toggle-connect :force-connect)))


(provide 'verilog-ext-ports)

;;; verilog-ext-ports.el ends here
