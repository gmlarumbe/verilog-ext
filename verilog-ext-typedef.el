;;; verilog-ext-typedef.el --- Verilog-ext Typedefs  -*- lexical-binding: t -*-

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

;; Typedef utils

;;; Code:


(require 'async)
(require 'verilog-ext-nav)

(defvar verilog-ext-typedef-align-words-current-proj nil)
(defvar verilog-ext-typedef-align-words-re-alist nil)

(defconst verilog-ext-typedef-cache-file (file-name-concat verilog-ext-cache-dir "typedefs"))
(defconst verilog-ext-typedef-cache-log-file (file-name-concat verilog-ext-cache-dir "typedefs.log"))

(defconst verilog-ext-typedef-async-inject-variables-re
  (eval-when-compile
    (regexp-opt '("load-path"
                  "buffer-file-name"
                  "default-directory"
                  "verilog-ext-project-alist")
                'symbols)))

(defun verilog-ext-typedef--var-find (regex &optional limit)
  "Search for REGEX and bound to LIMIT.
Match data is expected to fit that one of
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
See `verilog-ext-typedef-align-words-current-proj'.
Used for fontification and alignment."
  (let (type)
    (save-excursion
      (goto-char (point-min))
      (while (setq type (verilog-ext-typedef--var-find regex))
        (unless (member type verilog-ext-typedef-align-words-current-proj)
          (push type verilog-ext-typedef-align-words-current-proj))))))

(defun verilog-ext-typedef--tf-args-buffer-update ()
  "Scan functions/tasks arguments on current buffer to update user typedefs list.
See `verilog-ext-typedef-align-words-current-proj'.
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
              (unless (member arg-proc verilog-ext-typedef-align-words-current-proj)
                (push arg-proc verilog-ext-typedef-align-words-current-proj)))))))))

(defun verilog-ext-typedef--class-buffer-update ()
  "Scan class declarations on current buffer to update user typedef list."
  (let (word)
    (save-excursion
      (goto-char (point-min))
      (while (setq word (alist-get 'name (verilog-ext-find-class-fwd)))
        (unless (member word verilog-ext-typedef-align-words-current-proj)
          (push word verilog-ext-typedef-align-words-current-proj))))))

(defun verilog-ext-typedef--typedef-buffer-update (regex)
  "Scan REGEX typedef declarations on current buffer to update user typedef list."
  (let (word)
    (save-excursion
      (goto-char (point-min))
      (while (verilog-re-search-forward regex nil t)
        (setq word (match-string-no-properties 2))
        (unless (member word verilog-ext-typedef-align-words-current-proj)
          (push word verilog-ext-typedef-align-words-current-proj))))))

(defun verilog-ext-typedef--var-decl-update ()
  "Scan Verilog buffers and update typedef vars.

I.e: populate `verilog-ext-typedef-align-words-current-proj'."
  (verilog-ext-typedef--var-buffer-update verilog-ext-typedef-var-decl-single-re)
  (verilog-ext-typedef--var-buffer-update verilog-ext-typedef-var-decl-multiple-re)
  (verilog-ext-typedef--tf-args-buffer-update)
  (verilog-ext-typedef--class-buffer-update)
  (verilog-ext-typedef--typedef-buffer-update verilog-ext-typedef-class-re)
  (verilog-ext-typedef--typedef-buffer-update verilog-ext-typedef-generic-re))

(defun verilog-ext-typedef-get (&optional verbose)
  "Scan all (System)Verilog files of current project and udpate typedef list.

It will return the updated value of
`verilog-ext-typedef-align-words-current-proj', which can be used later along
with `verilog-regexp-words' to update the variable
`verilog-align-typedef-regexp'.  This enables the fontification and alignment of
user typedefs.

If optional arg VERBOSE is enabled, dump output to a logfile for potential debug
in corresponding async function."
  (interactive "P")
  (let* ((proj (verilog-ext-buffer-proj))
         (files (verilog-ext-proj-files proj))
         (num-files (length files))
         (num-files-processed 0)
         (log-file verilog-ext-typedef-cache-log-file)
         (tags-progress-reporter (make-progress-reporter "[Typedefs collection]: " 0 num-files)))
    (setq verilog-ext-typedef-align-words-current-proj nil) ; Reset value
    (when verbose
      (delete-file log-file))
    (dolist (file files)
      (progress-reporter-update tags-progress-reporter num-files-processed (format "[%s]" file))
      (when verbose
        (append-to-file (format "(%0d%%) [Typedef collection] Processing %s\n" (/ (* num-files-processed 100) num-files) file) nil log-file))
      (with-temp-buffer
        (insert-file-contents file)
        (verilog-ext-with-no-hooks
          (verilog-mode))
        (verilog-ext-typedef--var-decl-update))
      (setq num-files-processed (1+ num-files-processed)))
    ;; Postprocess obtained results (remove keywords and generic types that were uppercase)
    (mapc (lambda (elm)
            (when (member elm verilog-keywords)
              (delete elm verilog-ext-typedef-align-words-current-proj)))
          verilog-ext-typedef-align-words-current-proj)
    (let ((case-fold-search nil))
      (setq verilog-ext-typedef-align-words-current-proj (seq-remove (lambda (s)
                                                                       (not (string-match-p "[[:lower:]]" s)))
                                                                     verilog-ext-typedef-align-words-current-proj)))
    ;; Store results
    (when verilog-ext-typedef-align-words-current-proj
      (verilog-ext-proj-setcdr proj verilog-ext-typedef-align-words-re-alist (verilog-regexp-words verilog-ext-typedef-align-words-current-proj)))
    (when verilog-ext-cache-enable
      (verilog-ext-serialize verilog-ext-typedef-align-words-re-alist verilog-ext-typedef-cache-file))
    ;; Report end and return value for async processing
    (message "Finished collection of typedefs!")
    verilog-ext-typedef-align-words-re-alist))

(defun verilog-ext-typedef-get-async (&optional verbose)
  "Update typedef list of current asynchronously.
With current-prefix or VERBOSE, dump output log."
  (interactive "P")
  (let ((proj-root (verilog-ext-buffer-proj-root)))
    (unless proj-root
      (user-error "Not in a Verilog project buffer"))
    (message "Starting typedef collection for %s" proj-root)
    (async-start
     `(lambda ()
        ,(async-inject-variables verilog-ext-typedef-async-inject-variables-re)
        (require 'verilog-ext)
        (verilog-ext-typedef-get ,@verbose))
     (lambda (result)
       (message "Finished collection of typedefs!")
       (setq verilog-ext-typedef-align-words-re-alist result)))))

(defun verilog-ext-typedef-proj-hook ()
  "Hook to run when typedef feature is enabled."
  (let ((proj (verilog-ext-buffer-proj)))
    (when (and (eq major-mode 'verilog-mode) proj)
      (setq-local verilog-align-typedef-regexp (verilog-ext-aget verilog-ext-typedef-align-words-re-alist proj)))))

(defun verilog-ext-typedef-set (&optional disable)
  "Enable or DISABLE typedef feature.

INFO: Enabling this feature will override the value of
`verilog-align-typedef-regexp'."
  (if disable
      (remove-hook 'verilog-mode-hook #'verilog-ext-typedef-proj-hook)
    (add-hook 'verilog-mode-hook #'verilog-ext-typedef-proj-hook)
    (when verilog-ext-cache-enable
      (setq verilog-ext-typedef-align-words-re-alist (verilog-ext-unserialize verilog-ext-typedef-cache-file)))))

(defun verilog-ext-typedef-clear-cache (&optional all)
  "Clear typedef cache files for current project.

With prefix arg, clear cache for ALL projects."
  (interactive "P")
  (if (not all)
      (let ((proj (verilog-ext-buffer-proj)))
        (unless proj
          (user-error "Not in a Verilog project buffer"))
        (verilog-ext-proj-setcdr proj verilog-ext-typedef-align-words-re-alist nil)
        (verilog-ext-serialize verilog-ext-typedef-align-words-re-alist verilog-ext-typedef-cache-file)
        (message "[%s] Cleared typedef cache!" proj))
    (setq verilog-ext-typedef-align-words-re-alist nil)
    (verilog-ext-serialize verilog-ext-typedef-align-words-re-alist verilog-ext-typedef-cache-file)
    (message "Cleared all projects tags cache!")))


(provide 'verilog-ext-typedef)

;;; verilog-ext-typedef.el ends here


