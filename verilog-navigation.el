;;; verilog-navigation.el --- Verilog Navigation  -*- lexical-binding: t -*-

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
;; Navigation functions:
;;  - Find instances forward/backwards
;;  - Jump to definition/reference of module at point (requires gtags/xref)
;;  - Override syntax table to move forward/backwards until reaching an underscore
;;
;;; Code:


(require 'verilog-mode)
(require 'verilog-utils)
(require 'xref)
(require 'ggtags)


;;;; Syntax table override functions
(defun verilog-ext-forward-word (&optional arg)
  "Make verilog word navigation commands stop at underscores.
Move forward ARG words."
  (interactive "p")
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (with-syntax-table table
      (forward-word arg))))

(defun verilog-ext-backward-word (&optional arg)
  "Make verilog word navigation commands stop at underscores.
Move backward ARG words."
  (interactive "p")
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (with-syntax-table table
      (backward-word arg))))

(defun verilog-ext-electric-verilog-tab ()
  "Run `electric-verilog-tab' with original `verilog-mode' syntax table.
Prevents indentation issues with compiler directives with a modified syntax table."
  (interactive)
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?` "w" table)
    (with-syntax-table table
      (electric-verilog-tab))))


;;;; Module/instance
(defun verilog-ext-find-module-instance-fwd (&optional limit)
  "Search forwards for a Verilog module/instance.

If executing interactively place cursor at the beginning of the module name and
show module and instance names in the minibuffer.

If executing programatically move to the end of the module and return point
position.

Updates `match-data' so that the function can be used in other contexts:
- (match-string 0) = Whole module instantiation: from beg of module name to ;
- (match-string 1) = Module name
- (match-string 2) = Instance name

Bound search to LIMIT in case optional argument is non-nil."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (identifier-re (concat "\\(" verilog-identifier-sym-re "\\)"))
        (module-end (make-marker))
        module-name module-pos module-match-data
        instance-name instance-match-data
        pos found)
    (save-excursion
      (save-match-data
        (when (called-interactively-p 'interactive)
          (forward-char)) ; Avoid getting stuck if executing interactively
        (while (and (not (eobp))
                    (when-t limit
                      (> limit (point)))
                    (not (and (verilog-re-search-forward (concat "\\s-*" identifier-re) limit 'move) ; Module name
                              (not (verilog-parenthesis-depth)) ; Optimize search by avoiding looking for identifiers in parenthesized expressions
                              (unless (member (match-string-no-properties 1) verilog-keywords)
                                (setq module-name (match-string-no-properties 1))
                                (setq module-pos (match-beginning 1))
                                (setq module-match-data (match-data)))
                              (verilog-ext-forward-syntactic-ws)
                              (when-t (= (following-char) ?\#)
                                (and (verilog-ext-forward-char)
                                     (verilog-ext-forward-syntactic-ws)
                                     (= (following-char) ?\()
                                     (verilog-ext-forward-sexp)
                                     (= (preceding-char) ?\))
                                     (verilog-ext-forward-syntactic-ws)))
                              (looking-at identifier-re) ; Instance name
                              (unless (member (match-string-no-properties 1) verilog-keywords)
                                (setq instance-name (match-string-no-properties 1))
                                (setq instance-match-data (match-data)))
                              (verilog-ext-skip-identifier-forward)
                              (verilog-ext-forward-syntactic-ws)
                              (when-t (= (following-char) ?\[)
                                (and (verilog-ext-forward-sexp)
                                     (= (preceding-char) ?\])
                                     (verilog-ext-forward-syntactic-ws)))
                              (= (following-char) ?\()
                              (verilog-ext-forward-sexp)
                              (= (preceding-char) ?\))
                              (verilog-ext-forward-syntactic-ws)
                              (= (following-char) ?\;)
                              (set-marker module-end (1+ (point)))
                              (setq found t)
                              (if (called-interactively-p 'interactive)
                                  (progn
                                    (setq pos module-pos)
                                    (message "%s : %s" module-name instance-name))
                                (setq pos (point))))))
          (if (verilog-parenthesis-depth)
              (verilog-backward-up-list -1)
            (forward-line)))))
    (if found
        (progn
          (set-match-data (list (nth 0 module-match-data)
                                module-end
                                (nth 2 module-match-data)
                                (nth 3 module-match-data)
                                (nth 2 instance-match-data)
                                (nth 3 instance-match-data)))
          (goto-char pos)
          (if (called-interactively-p 'interactive)
              (message "%s : %s" module-name instance-name)
            (point)))
      (when (called-interactively-p 'interactive)
        (message "Could not find any instance forward")))))

(defun verilog-ext-find-module-instance-bwd (&optional limit)
  "Search backwards for a Verilog module/instance.

If executing interactively place cursor at the beginning of the module name and
show module and instance names in the minibuffer.

If executing programatically move to the beginning of the module and return
point position.

Updates `match-data' so that the function can be used in other contexts:
- (match-string 0) = Whole module instantiation: from beg of module name to ;
- (match-string 1) = Module name
- (match-string 2) = Instance name

Bound search to LIMIT in case it is non-nil."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (identifier-re (concat "\\(" verilog-identifier-sym-re "\\)"))
        (module-end (make-marker))
        module-name module-pos module-match-data
        instance-name instance-match-data
        pos found)
    (save-excursion
      (save-match-data
        (while (and (not (bobp))
                    (when-t limit
                      (< limit (point)))
                    (not (and (set-marker module-end (verilog-re-search-backward ";" limit 'move))
                              (not (verilog-parenthesis-depth))
                              (verilog-ext-backward-syntactic-ws)
                              (= (preceding-char) ?\))
                              (verilog-ext-backward-sexp)
                              (= (following-char) ?\()
                              (verilog-ext-backward-syntactic-ws)
                              (when-t (= (preceding-char) ?\])
                                (and (verilog-ext-backward-sexp)
                                     (= (following-char) ?\[)
                                     (verilog-ext-backward-syntactic-ws)))
                              (verilog-ext-skip-identifier-backwards)
                              (looking-at identifier-re)
                              (unless (member (match-string-no-properties 1) verilog-keywords)
                                (setq instance-name (match-string-no-properties 1))
                                (setq instance-match-data (match-data)))
                              (verilog-ext-backward-syntactic-ws)
                              (when-t (= (preceding-char) ?\))
                                (and (verilog-ext-backward-sexp)
                                     (= (following-char) ?\()
                                     (verilog-ext-backward-syntactic-ws)
                                     (= (preceding-char) ?\#)
                                     (verilog-ext-backward-char)
                                     (verilog-ext-backward-syntactic-ws)))
                              (verilog-ext-skip-identifier-backwards)
                              (looking-at identifier-re)
                              (unless (member (match-string-no-properties 1) verilog-keywords)
                                (setq module-name (match-string-no-properties 1))
                                (setq module-pos (match-beginning 1))
                                (setq module-match-data (match-data)))
                              (setq found t)
                              (if (called-interactively-p 'interactive)
                                  (setq pos module-pos)
                                (setq pos (point))))))
          (if (verilog-parenthesis-depth)
              (verilog-backward-up-list 1)
            (beginning-of-line)))))
    (if found
        (progn
          (set-match-data (list (nth 0 module-match-data)
                                module-end
                                (nth 2 module-match-data)
                                (nth 3 module-match-data)
                                (nth 2 instance-match-data)
                                (nth 3 instance-match-data)))
          (goto-char pos)
          (if (called-interactively-p 'interactive)
              (message "%s : %s" module-name instance-name)
            (point)))
      (when (called-interactively-p 'interactive)
        (message "Could not find any instance backwards")))))

(defun verilog-ext-instance-at-point ()
  "Return list with module and instance names if point is at an instance."
  (let ((point-cur (point))
        point-instance-begin point-instance-end instance-type instance-name)
    (save-excursion
      (when (and (verilog-re-search-forward ";" nil t)
                 (verilog-ext-find-module-instance-bwd)) ; Sets match data
        (setq instance-type (match-string-no-properties 1))
        (setq instance-name (match-string-no-properties 2))
        (setq point-instance-begin (match-beginning 0))
        (setq point-instance-end   (match-end 0))
        (if (and (>= point-cur point-instance-begin)
                 (<= point-cur point-instance-end))
            (list instance-type instance-name)
          nil)))))

(defun verilog-ext-jump-to-module-at-point (&optional ref)
  "Jump to definition of module at point.
If REF is non-nil show references instead."
  (interactive)
  (let (module)
    (unless (executable-find "global")
      (error "Couldn't find executable `global' in PATH"))
    (unless (member 'ggtags--xref-backend xref-backend-functions)
      (error "Error: ggtags not configured as an xref backend.  Is ggtags-mode enabled?"))
    (unless ggtags-project-root
      (error "Error: `ggtags-project-root' not set.  Are GTAGS/GRTAGS/GPATH files created?"))
    (if (setq module (car (verilog-ext-instance-at-point)))
        (progn
          (if ref
              (xref-find-references module)
            (xref-find-definitions module))
          module) ; Report module name
      (user-error "Not inside a Verilog instance"))))

(defun verilog-ext-jump-to-module-at-point-def ()
  "Jump to definition of module at point."
  (interactive)
  (verilog-ext-jump-to-module-at-point))

(defun verilog-ext-jump-to-module-at-point-ref ()
  "Show references of module at point."
  (interactive)
  (verilog-ext-jump-to-module-at-point :ref))


;;; Hooks
(defun verilog-ext-navigation-hook ()
  "Verilog-ext navigation hook."
  ;; Avoid considering tick as part of a symbol on preprocessor directives while
  ;; isearching.  Works in conjunction with `verilog-ext-electric-verilog-tab'
  ;; to get back standard table to avoid indentation issues with compiler directives.
  (modify-syntax-entry ?` "."))


;;; Setup
(add-hook 'verilog-mode-hook #'verilog-ext-navigation-hook)


(provide 'verilog-navigation)

;;; verilog-navigation.el ends here
