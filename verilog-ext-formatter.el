;;; verilog-ext-formatter.el --- Verilog-ext Code Formatter  -*- lexical-binding: t -*-

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

;; Code formatter setup

;;; Code:

(require 'verilog-mode)
(require 'apheleia)

(defgroup verilog-ext-formatter nil
  "Verilog-ext formatter."
  :group 'verilog-ext)

(defcustom verilog-ext-formatter-column-limit 100
  "Verible code formatter column limit.
See https://chipsalliance.github.io/verible/verilog_format.html."
  :type 'integer
  :group 'verilog-ext-formatter)

(defcustom verilog-ext-formatter-indentation-spaces verilog-indent-level
  "Verible code formatter indentation spaces.
See https://chipsalliance.github.io/verible/verilog_format.html."
  :type 'integer
  :group 'verilog-ext-formatter)

(defcustom verilog-ext-formatter-line-break-penalty 2
  "Verible code formatter line break penalty.
See https://chipsalliance.github.io/verible/verilog_format.html."
  :type 'integer
  :group 'verilog-ext-formatter)

(defcustom verilog-ext-formatter-over-column-limit-penalty 100
  "Verible code formatter line break penalty.
See https://chipsalliance.github.io/verible/verilog_format.html."
  :type 'integer
  :group 'verilog-ext-formatter)

(defcustom verilog-ext-formatter-wrap-spaces 4
  "Verible code formatter wrap spaces.
See https://chipsalliance.github.io/verible/verilog_format.html."
  :type 'integer
  :group 'verilog-ext-formatter)

(defun verilog-ext-formatter-setup ()
  "Setup `apheleia' with Verible code formatter."
  (interactive)
  (unless (and (alist-get 'verilog-mode apheleia-mode-alist)
               (alist-get 'verilog-ts-mode apheleia-mode-alist)
               (alist-get 'verible apheleia-formatters))
    (dolist (mode '(verilog-mode verilog-ts-mode))
      (setq apheleia-mode-alist (assq-delete-all mode apheleia-mode-alist))
      (push `(,mode . verible) apheleia-mode-alist))
    (setq apheleia-formatters (assq-delete-all 'verible apheleia-formatters))
    (push '(verible . ("verible-verilog-format"
                       "--column_limit" (number-to-string verilog-ext-formatter-column-limit)
                       "--indentation_spaces" (number-to-string verilog-ext-formatter-indentation-spaces)
                       "--line_break_penalty" (number-to-string verilog-ext-formatter-line-break-penalty)
                       "--over_column_limit_penalty" (number-to-string verilog-ext-formatter-over-column-limit-penalty)
                       "--wrap_spaces" (number-to-string verilog-ext-formatter-wrap-spaces)
                       "-"))
          apheleia-formatters))
  (if (called-interactively-p 'any)
      (message "Configured %s" (alist-get 'verilog-mode apheleia-mode-alist))
    (alist-get 'verilog-mode apheleia-mode-alist)))

(defun verilog-ext-formatter-run ()
  "Run Verible code formatter."
  (interactive)
  (unless (executable-find "verible-verilog-format")
    (error "Binary verible-verilog-format not found.  Visit https://github.com/chipsalliance/verible to download/install it"))
  (unless (and (assoc major-mode apheleia-mode-alist)
               (assoc 'verible apheleia-formatters))
    (error "Code formatter not setup.  Did you run `verilog-ext-mode-setup'?"))
  (apheleia-format-buffer 'verible))


(provide 'verilog-ext-formatter)

;;; verilog-ext-formatter.el ends here
