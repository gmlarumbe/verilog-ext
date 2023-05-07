;;; verilog-ext-time-stamp.el --- Verilog-ext Timestamp  -*- lexical-binding: t -*-

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

;; Timestamp setup

;;; Code:

(defgroup verilog-ext-time-stamp nil
  "Verilog-ext time-stamp."
  :group 'verilog-ext)

(defcustom verilog-ext-time-stamp-enable t
  "Enable `verilog-ext-time-stamp-mode'."
  :type 'boolean
  :group 'verilog-ext-time-stamp)

(defcustom verilog-ext-time-stamp-regex "^// Last modified : "
  "Timestamp regexp."
  :type 'string
  :group 'verilog-ext-time-stamp)

(defcustom verilog-ext-time-stamp-pattern (concat verilog-ext-time-stamp-regex "%%$")
  "Timestamp pattern.  See `time-stamp-pattern'."
  :type 'string
  :group 'verilog-ext-time-stamp)

(defcustom verilog-ext-time-stamp-format  "%:y/%02m/%02d"
  "Timestamp format.  See `time-stamp-format'."
  :type 'string
  :group 'verilog-ext-time-stamp)

(defcustom verilog-ext-time-stamp-start nil
  "If using `time-stamp-start' and `time-stamp-end':
`'time-stamp' deletes the text between the first match of `time-stamp-start'.
and the following match of `time-stamp-end', then writes the time stamp
specified by `time-stamp-format' between them."
  :type 'string
  :group 'verilog-ext-time-stamp)

(defcustom verilog-ext-time-stamp-end nil
  "If using `time-stamp-start' and `time-stamp-end':
`time-stamp' deletes the text between the first match of `time-stamp-start'.
and the following match of `time-stamp-end', then writes the time stamp
specified by `time-stamp-format' between them."
  :type 'string
  :group 'verilog-ext-time-stamp)


(define-minor-mode verilog-ext-time-stamp-mode
  "Setup `time-stamp' format for Verilog files.
By default `time-stamp' looks for the pattern in the first 8 lines.
This can be changed by setting the local variables `time-stamp-start'
and `time-stamp-end' for custom scenarios."
  :global nil
  (setq-local time-stamp-pattern verilog-ext-time-stamp-pattern)
  (setq-local time-stamp-format verilog-ext-time-stamp-format)
  (setq-local time-stamp-start verilog-ext-time-stamp-start)
  (setq-local time-stamp-end verilog-ext-time-stamp-end)
  (if verilog-ext-time-stamp-mode
      (add-hook 'before-save-hook #'time-stamp nil :local)
    (remove-hook 'before-save-hook #'time-stamp :local)))


(provide 'verilog-ext-time-stamp)

;;; verilog-ext-time-stamp.el ends here
