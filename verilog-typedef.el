;;; verilog-typedef.el --- Update list of typedefs for alignment and fontification  -*- lexical-binding: t -*-

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
;; Some functions to extract typedefs/classes from a set of directories and
;; update some variables accordingly.
;;
;; This enables the fontification and alignment via
;; `verilog-pretty-declarations' and `verilog-pretty-expr' of these types.
;;
;; To make it efficient it is required to update this regexp with `regexp-opt',
;; but doing it frequently to update the variable (e.g. on file opening, closing
;; or saving) gives a poor performance.  Hence the best approach is to run
;; `verilog-ext-typedef-batch-update' and update manually the value of
;; `verilog-align-typedef-regexp' in some other Elisp configuration file.
;;
;; Usage example:
;;  - Go to project directory, set by projectile, ggtags, project or current dir
;;
;;  - Set the variable `verilog-ext-align-typedef-uvm-dir' to include UVM directories:
;;      (setq verilog-ext-align-typedef-uvm-dir "/home/user/UVM/1800.2-2020-1.1/src/")
;;
;;  - M-x `verilog-ext-typedef-project-update' RET
;;
;;  - Wait for processing (might take some minutes depending on the number of files)
;;
;;  - Check if variables were updated:
;;     - C-h v `verilog-ext-align-typedef-words'
;;     - C-h v `verilog-ext-align-typedef-words-re'
;;     - C-h v `verilog-align-typedef-regexp'
;;
;;  - Update your init file with one of the two following options:
;;      a) Copy the value of `verilog-ext-align-typedef-words-re' and set it to `verilog-align-typedef-regexp'
;;      b) Copy the value of `verilog-ext-align-typedef-words', remove any undesired word and:
;;        - (setq verilog-align-typedef-regexp
;;             (eval-when-compile
;;                (verilog-regexp-words <pasted-value>)))
;;
;;; Code:


(require 'verilog-mode)
(require 'verilog-navigation)


(defconst verilog-ext-range-optional-re
  (concat "\\(\\s-*" verilog-range-re "\\)?"))
(defconst verilog-ext-range-or-class-params-optional-re
  (concat "\\(\\s-*\\(\\(" verilog-range-re "\\)\\|\\(#\\s-*([^)]*)\\)\\)\\)?"))
(defconst verilog-ext-typedef-var-decl-single-re
  (concat "\\<\\(?1:" verilog-identifier-re "\\)\\>" verilog-ext-range-or-class-params-optional-re "\\s-+"  ; Var type
          "\\<\\(?3:" verilog-identifier-re "\\)\\>\\s-*" verilog-ext-range-optional-re "\\s-*"              ; Var name
          "\\(?4:=.*\\)?" ; Optional initialization value
          ";")
  "type_t foo;
   type_t [10:0] foo;
   type_t [10:0] foo = 'h0;")
(defconst verilog-ext-typedef-var-decl-multiple-re
  (concat "\\<\\(?1:" verilog-identifier-re "\\)\\>" verilog-ext-range-or-class-params-optional-re "\\s-+"  ; Var type
          "\\(?3:\\(" verilog-identifier-re "\\s-*,\\s-*\\)+\\(" verilog-identifier-re "\\s-*\\)\\)"                ; Var names
          ";")
  "type_t foo1, foo2 , foo4, foo6[], foo7 [25], foo8 ;")
(defconst verilog-ext-typedef-class-params-optional-re "\\(\\s-*#([^)]*)\\)?")
(defconst verilog-ext-typedef-class-re (concat "^\\s-*typedef\\s-+\\(?1:\\<class\\>\\)\\s-+\\(?2:\\<" verilog-identifier-re "\\>\\)"))
(defconst verilog-ext-typedef-generic-re (concat "^\\s-*typedef\\s-+\\(?1:\\<" verilog-identifier-re "\\>\\)"
                                                 "\\(" verilog-ext-typedef-class-params-optional-re "\\|" verilog-ext-range-optional-re "\\)"
                                                 "\\s-*\\(?2:\\<" verilog-identifier-re "\\>\\)"))


(defvar verilog-ext-align-typedef-words nil)
(defvar verilog-ext-align-typedef-words-re nil)
(defvar verilog-ext-align-typedef-uvm-dir nil)


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
See `verilog-ext-align-typedef-words'.
Used for fontification and alignment."
  (let (type)
    (save-excursion
      (goto-char (point-min))
      (while (setq type (verilog-ext-typedef--var-find regex))
        (unless (member type verilog-ext-align-typedef-words)
          (push type verilog-ext-align-typedef-words))))))

(defun verilog-ext-typedef--tf-args-buffer-update ()
  "Scan functions/tasks arguments on current buffer to update user typedefs list.
See `verilog-ext-align-typedef-words'.
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
              (unless (member arg-proc verilog-ext-align-typedef-words)
                (push arg-proc verilog-ext-align-typedef-words)))))))))

(defun verilog-ext-typedef--class-buffer-update ()
  "Scan class declarations on current buffer to update user typedef list."
  (let (word)
    (save-excursion
      (goto-char (point-min))
      (while (setq word (alist-get 'name (verilog-ext-find-class-fwd)))
        (unless (member word verilog-ext-align-typedef-words)
          (push word verilog-ext-align-typedef-words))))))

(defun verilog-ext-typedef--typedef-buffer-update (regex)
  "Scan REGEX typedef declarations on current buffer to update user typedef list."
  (let (word)
    (save-excursion
      (goto-char (point-min))
      (while (verilog-re-search-forward regex nil t)
        (setq word (match-string-no-properties 2))
        (unless (member word verilog-ext-align-typedef-words)
          (push word verilog-ext-align-typedef-words))))))

(defun verilog-ext-typedef--var-decl-update ()
  "Scan and update Verilog buffers and update `verilog-ext-align-typedef-words'."
  (verilog-ext-typedef--var-buffer-update verilog-ext-typedef-var-decl-single-re)
  (verilog-ext-typedef--var-buffer-update verilog-ext-typedef-var-decl-multiple-re)
  (verilog-ext-typedef--tf-args-buffer-update)
  (verilog-ext-typedef--class-buffer-update)
  (verilog-ext-typedef--typedef-buffer-update verilog-ext-typedef-class-re)
  (verilog-ext-typedef--typedef-buffer-update verilog-ext-typedef-generic-re))

(defun verilog-ext-typedef-batch-update (dirs)
  "Scan recursively all (System)Verilog files under DIRS and udpate typedef list.

It will return the updated value of `verilog-ext-align-typedef-words', which can
be used later along with `verilog-regexp-words' to update the variable
`verilog-align-typedef-regexp'.  This enables the fontification and alignment of
user typedefs."
  (interactive "DDirectory: ")
  (unless (listp dirs)
    (setq dirs (list dirs)))
  (let (dir-files)
    (setq verilog-ext-align-typedef-words nil) ; Reset value
    (dolist (dir dirs)
      (setq dir-files (directory-files-recursively dir "\.s?vh?$" nil nil t)) ; Follow symlinks
      (dolist (file dir-files)
        (message "Processing %s ..." file)
        (with-temp-buffer
          (insert-file-contents file)
          (verilog-mode)
          (verilog-ext-typedef--var-decl-update))))
    ;; Postprocess obtained results (remove keywords and generic types that were uppercase)
    (mapc #'(lambda (elm)
                (when (member elm verilog-keywords)
                  (delete elm verilog-ext-align-typedef-words)))
            verilog-ext-align-typedef-words)
    (let ((case-fold-search nil))
      (setq verilog-ext-align-typedef-words (seq-remove #'(lambda (s)
                                                            (not (string-match-p "[[:lower:]]" s)))
                                                        verilog-ext-align-typedef-words)))
    ;; Store results
    (when verilog-ext-align-typedef-words
      (setq verilog-ext-align-typedef-words-re (verilog-regexp-words verilog-ext-align-typedef-words))
      (setq verilog-align-typedef-regexp verilog-ext-align-typedef-words-re))))

;;;###autoload
(defun verilog-ext-typedef-project-update ()
  "Update typedef list of current project.

If `verilog-ext-align-typedef-uvm-dir' is non nil, also include it
for the search of typedefs"
  (interactive)
  (let (proj-dir)
  (unless (setq proj-dir (verilog-ext-project-root))
    (error "Could not find project root!"))
  (verilog-ext-typedef-batch-update
   `(,proj-dir ,verilog-ext-align-typedef-uvm-dir))))



(provide 'verilog-typedef)

;;; verilog-typedef.el ends here
