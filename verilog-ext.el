;;; verilog-ext.el --- SystemVerilog Extensions  -*- lexical-binding: t -*-

;; Copyright (C) 2022-2024 Gonzalo Larumbe

;; Author: Gonzalo Larumbe <gonzalomlarumbe@gmail.com>
;; URL: https://github.com/gmlarumbe/verilog-ext
;; Version: 0.5.0
;; Keywords: Verilog, IDE, Tools
;; Package-Requires: ((emacs "29.1") (verilog-mode "2024.3.1.121933719") (verilog-ts-mode "0.1.3") (lsp-mode "8.0.0") (ag "0.48") (ripgrep "0.4.0") (hydra "0.15.0") (apheleia "3.1") (yasnippet "0.14.0") (flycheck "32") (outshine "3.0.1") (async "1.9.7"))

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

;; Extensions for Verilog Mode:
;;
;;  - Tree-sitter `verilog-ts-mode' support
;;  - Project management
;;  - Improved syntax highlighting for `verilog-mode'
;;  - Find definitions and references with builtin `xref' backend
;;  - Auto-completion with dot and scope completion
;;  - Hierarchy extraction and navigation
;;  - LSP configuration for `lsp-bridge', `lsp-mode', `eglot' and `lspce'
;;  - Support for many linters via `flycheck'
;;  - Beautify modules and instances
;;  - Code navigation functions for RTL and Verification environments
;;  - Templates insertion via `hydra': custom and `yasnippet' based
;;  - Code formatter via `apheleia'
;;  - Compilation-based utilities
;;  - Improve `imenu': detect instances, classes and methods
;;  - Add support for `which-func'
;;  - Code folding via `hideshow'
;;  - Project tags, typedef analysis and caching
;;  - `time-stamp' auto-configuration
;;  - Convert block end comments to names
;;  - Port connections utilities

;;; Code:

;;; Customization
(defgroup verilog-ext nil
  "Verilog Extensions."
  :group 'languages
  :group 'verilog-mode)

(defcustom verilog-ext-feature-list '(font-lock
                                      xref
                                      capf
                                      hierarchy
                                      eglot
                                      lsp
                                      lsp-bridge
                                      lspce
                                      flycheck
                                      beautify
                                      navigation
                                      template
                                      formatter
                                      compilation
                                      imenu
                                      which-func
                                      hideshow
                                      typedefs
                                      time-stamp
                                      block-end-comments
                                      ports)
  "Which `verilog-ext' features to enable."
  :type '(set (const :tag "Improved syntax highlighting via `font-lock'."
                font-lock)
              (const :tag "Xref backend to navigate definitions/references in current project."
                xref)
              (const :tag "Completion at point builtin function with dot and scope completion."
                capf)
              (const :tag "Hierarchy extraction and visualization."
                hierarchy)
              (const :tag "Setup LSP servers for `eglot'."
                eglot)
              (const :tag "Setup LSP servers for `lsp-mode'."
                lsp)
              (const :tag "Setup LSP servers for `lsp-bridge'."
                lsp-bridge)
              (const :tag "Setup LSP servers for `lspce'."
                lspce)
              (const :tag "Setup linters for `flycheck'."
                flycheck)
              (const :tag "Code beautifying functions."
                beautify)
              (const :tag "Code Navigation functions."
                navigation)
              (const :tag "`yasnippet' and custom templates via `hydra'."
                template)
              (const :tag "`verible' formatter via `apheleia'."
                formatter)
              (const :tag "Compilation functions."
                compilation)
              (const :tag "Improved `imenu'."
                imenu)
              (const :tag "Support for `which-function-mode'."
                which-func)
              (const :tag "`hideshow' configuration."
                hideshow)
              (const :tag "Scan typedefs and classes of current project for syntax highlighting and alignment."
                typedefs)
              (const :tag "`time-stamp' configuration."
                time-stamp)
              (const :tag "Convert block end comments to names (endmodule // top → endmodule : top)"
                block-end-comments)
              (const :tag "Port connections utilities."
                ports))
  :group 'verilog-ext)

(defmacro verilog-ext-when-feature (features &rest body)
  "Macro to run BODY if `verilog-ext' feature is enabled.
FEATURES can be a single feature or a list of features."
  (declare (indent 1) (debug 1))
  `(let (enabled)
     (if (listp ,features)
         (dolist (feature ,features)
           (when (member feature verilog-ext-feature-list)
             (setq enabled t)))
       ;; Else
       (when (member ,features verilog-ext-feature-list)
         (setq enabled t)))
     (when enabled
       ,@body)))


;;; Features
(require 'verilog-ext-hs)
(require 'verilog-ext-time-stamp)
(require 'verilog-ext-block-end-comments)
(require 'verilog-ext-utils)
(require 'verilog-ext-compile)
(require 'verilog-ext-nav)
(require 'verilog-ext-font-lock)
(require 'verilog-ext-imenu)
(require 'verilog-ext-which-func)
(require 'verilog-ext-ports)
(require 'verilog-ext-beautify)
(require 'verilog-ext-template)
(require 'verilog-ext-typedef)
(require 'verilog-ext-hierarchy)
(require 'verilog-ext-tags)
(require 'verilog-ext-capf)
(require 'verilog-ext-xref)
(require 'verilog-ext-formatter)
(require 'verilog-ext-flycheck)
(require 'verilog-ext-eglot)
(require 'verilog-ext-lsp)
(require 'verilog-ext-lsp-bridge)
(require 'verilog-ext-lspce)

;;; Major-mode
(defvar verilog-ext-mode-map
  (let ((map (make-sparse-keymap)))
    ;; Features
    (verilog-ext-when-feature '(capf xref)
      (define-key map (kbd "C-c C-u") 'verilog-ext-tags-get))
    (verilog-ext-when-feature 'hierarchy
      (define-key map (kbd "C-c C-v") 'verilog-ext-hierarchy-current-buffer))
    (verilog-ext-when-feature 'flycheck
      (define-key map (kbd "C-c C-f") 'verilog-ext-flycheck-mode))
    (verilog-ext-when-feature 'template
      (define-key map (kbd "C-c C-t") 'verilog-ext-hydra/body))
    (verilog-ext-when-feature 'formatter
      (define-key map (kbd "C-c C-l") 'verilog-ext-formatter-run))
    (verilog-ext-when-feature 'beautify
      (define-key map (kbd "C-M-i") 'verilog-ext-beautify-block-at-point)
      (define-key map (kbd "C-c C-b") 'verilog-ext-beautify-current-buffer))
    (verilog-ext-when-feature 'navigation
      (define-key map (kbd "C-M-.") 'verilog-ext-jump-to-parent-module)
      (define-key map (kbd "C-c M-.") 'verilog-ext-jump-to-module-at-point-def)
      (define-key map (kbd "C-c M-?") 'verilog-ext-jump-to-module-at-point-ref)
      (define-key map (kbd "C-M-a") 'verilog-ext-nav-beg-of-defun-dwim)
      (define-key map (kbd "C-M-e") 'verilog-ext-nav-end-of-defun-dwim)
      (define-key map (kbd "C-M-d") 'verilog-ext-nav-down-dwim)
      (define-key map (kbd "C-M-u") 'verilog-ext-nav-up-dwim)
      (define-key map (kbd "C-M-p") 'verilog-ext-nav-prev-dwim)
      (define-key map (kbd "C-M-n") 'verilog-ext-nav-next-dwim))
    (verilog-ext-when-feature 'compilation
      (define-key map (kbd "C-c <f5>") 'verilog-ext-compile-project)
      (define-key map (kbd "C-c C-p") 'verilog-ext-preprocess))
    (verilog-ext-when-feature 'hideshow
      (define-key map (kbd "C-<tab>") 'verilog-ext-hs-toggle-hiding))
    (verilog-ext-when-feature 'ports
      (define-key map (kbd "C-c C-c c") 'verilog-ext-ports-clean-blanks)
      (define-key map (kbd "C-c C-c t") 'verilog-ext-ports-toggle-connect)
      (define-key map (kbd "C-c C-c r") 'verilog-ext-ports-connect-recursively))
    ;; Misc
    (define-key map (kbd "TAB") 'verilog-ext-tab)
    (define-key map (kbd "M-d") 'verilog-ext-kill-word)
    (define-key map (kbd "M-f") 'verilog-ext-forward-word)
    (define-key map (kbd "M-b") 'verilog-ext-backward-word)
    (define-key map (kbd "C-<backspace>") 'verilog-ext-backward-kill-word)
    (define-key map (kbd "M-DEL") 'verilog-ext-backward-kill-word)
    map)
  "Keymap for `verilog-ext'.")

;;;###autoload
(defun verilog-ext-mode-setup ()
  "Setup `verilog-ext-mode' depending on enabled features."
  (interactive)
  ;; Features
  (verilog-ext-when-feature 'font-lock
    (verilog-ext-font-lock-setup))
  (verilog-ext-when-feature '(capf xref)
    (verilog-ext-tags-setup))
  (verilog-ext-when-feature 'hierarchy
    (verilog-ext-hierarchy-setup))
  (verilog-ext-when-feature 'eglot
    (verilog-ext-eglot-set-server verilog-ext-eglot-default-server))
  (verilog-ext-when-feature 'lsp
    (verilog-ext-lsp-setup)
    (verilog-ext-lsp-set-server verilog-ext-lsp-mode-default-server))
  (verilog-ext-when-feature 'lsp-bridge
    (verilog-ext-lsp-bridge-set-server verilog-ext-lsp-bridge-default-server))
  (verilog-ext-when-feature 'lspce
    (verilog-ext-lspce-set-server verilog-ext-lspce-default-server))
  (verilog-ext-when-feature 'flycheck
    (verilog-ext-flycheck-setup))
  (verilog-ext-when-feature 'template
    (verilog-ext-template-add-snippets))
  (verilog-ext-when-feature 'formatter
    (verilog-ext-formatter-setup))
  (verilog-ext-when-feature 'hideshow
    (verilog-ext-hs-setup))
  (verilog-ext-when-feature 'typedefs
    (verilog-ext-typedef-set))
  ;; Jump to parent module ag/ripgrep hooks
  (add-hook 'ag-search-finished-hook #'verilog-ext-navigation-ag-rg-hook)
  (add-hook 'ripgrep-search-finished-hook #'verilog-ext-navigation-ag-rg-hook))

;;;###autoload
(define-minor-mode verilog-ext-mode
  "Minor mode for editing SystemVerilog files.

\\{verilog-ext-mode-map}"
  :lighter " vX"
  :global nil
  (unless (derived-mode-p 'verilog-mode)
    (error "Verilog-ext only works with `verilog-mode' or `verilog-ts-mode'"))
  (if verilog-ext-mode
      (progn
        ;; Common
        (verilog-ext-scan-buffer-modules)
        (verilog-ext-update-buffer-file-and-dir-list)
        (add-hook 'kill-buffer-hook #'verilog-ext-kill-buffer-hook nil :local)
        ;; Features
        (verilog-ext-when-feature 'xref
          (verilog-ext-xref-set))
        (verilog-ext-when-feature 'capf
          (verilog-ext-capf-set))
        (verilog-ext-when-feature 'hierarchy
          (if verilog-ext-hierarchy-vhier-use-open-buffers
              (progn (setq verilog-ext-hierarchy-vhier-open-dirs verilog-ext-dir-list)
                     (setq verilog-ext-hierarchy-vhier-open-files verilog-ext-file-list))
            (setq verilog-ext-hierarchy-vhier-open-dirs nil)
            (setq verilog-ext-hierarchy-vhier-open-files nil)))
        (verilog-ext-when-feature 'flycheck
          (if verilog-ext-flycheck-use-open-buffers
              (progn (setq verilog-ext-flycheck-dirs verilog-ext-dir-list)
                     (setq verilog-ext-flycheck-files verilog-ext-file-list))
            (setq verilog-ext-flycheck-dirs nil)
            (setq verilog-ext-flycheck-files nil)))
        (verilog-ext-when-feature 'block-end-comments
          (verilog-ext-block-end-comments-to-names-mode))
        (verilog-ext-when-feature 'time-stamp
          (verilog-ext-time-stamp-mode))
        ;; `verilog-mode'-only customization (exclude `verilog-ts-mode')
        (when (eq major-mode 'verilog-mode)
          ;; Syntax table overriding:
          ;; Avoid considering tick as part of a symbol on preprocessor directives while
          ;; isearching.  Works in conjunction with `verilog-ext-tab'
          ;; and `verilog-ext-indent-region' to get back standard table to avoid
          ;; indentation issues with compiler directives.
          (modify-syntax-entry ?` ".")
          ;; Font-lock
          ;;   It's not possible to add font-lock keywords to minor-modes.
          ;;   The workaround consists in add/remove keywords to the major mode when
          ;;   the minor mode is loaded/unloaded.
          ;;   https://emacs.stackexchange.com/questions/60198/font-lock-add-keywords-is-not-working
          (verilog-ext-when-feature 'font-lock
            (font-lock-flush)
            (setq-local font-lock-multiline nil))
          ;; Imenu
          (verilog-ext-when-feature 'imenu
            (setq-local imenu-create-index-function #'verilog-ext-imenu-index))
          ;; Which-func
          (verilog-ext-when-feature 'which-func
            (verilog-ext-which-func))))
    ;; Cleanup
    (remove-hook 'kill-buffer-hook #'verilog-ext-kill-buffer-hook :local)
    (verilog-ext-when-feature 'xref
      (verilog-ext-xref-set :disable))
    (verilog-ext-when-feature 'capf
      (verilog-ext-capf-set :disable))
    (verilog-ext-when-feature 'typedef
      (verilog-ext-typedef-set :disable))
    (verilog-ext-when-feature 'block-end-comments
      (verilog-ext-block-end-comments-to-names-mode -1))
    (verilog-ext-when-feature 'time-stamp
      (verilog-ext-time-stamp-mode -1))))


;;; Provide
(provide 'verilog-ext)

;;; verilog-ext.el ends here

