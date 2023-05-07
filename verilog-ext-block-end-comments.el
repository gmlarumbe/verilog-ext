;;; verilog-ext-block-end-comments.el --- Verilog-ext block end comments to names mode -*- lexical-binding: t -*-

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

;; Block end comments to names mode

;;; Code:

(require 'verilog-mode)


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
      (add-hook 'before-save-hook #'verilog-ext-block-end-comments-to-names nil :local)
    (remove-hook 'before-save-hook #'verilog-ext-block-end-comments-to-names :local)))



(provide 'verilog-ext-block-end-comments)

;;; verilog-ext-block-end-comments.el ends here


