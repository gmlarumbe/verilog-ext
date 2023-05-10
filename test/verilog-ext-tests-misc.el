;;; verilog-ext-tests-misc.el --- Verilog-Ext ERT Misc  -*- lexical-binding: t -*-

;; Copyright (C) 2022-2023 Gonzalo Larumbe

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
;; ERT Tests that have not been included to main regression for various reasons.
;;
;;; Code:


(require 'verilog-ext-tests-navigation)


;;;; Work locally, fail in GitHub actions
(defmacro verilog-ext-test-with-gtags (file &rest body)
  (declare (indent 1) (debug t))
  `(cl-letf (((symbol-function 'message)
              (lambda (FORMAT-STRING &rest ARGS)
                nil))) ; Mock `message' to silence all the indentation reporting
     (let ((default-directory verilog-ext-tests-examples-dir)
           (process-environment process-environment))
       ;; Setup environment lexically only for current process
       (push "GTAGSLABEL=ctags" process-environment)
       ;; Remove/recreate gtags.file
       (dolist (file '("gtags.files" "GTAGS" "GPATH" "GRTAGS"))
         (when (file-exists-p file)
           (delete-file file)))
       (with-temp-file "gtags.files"
         (insert (mapconcat #'identity (directory-files-recursively default-directory "\.s?vh?$" nil nil t) "\n")))
       (ggtags-create-tags default-directory)
       ;; Enable ggtags and run body
       (find-file (file-name-concat verilog-ext-tests-examples-dir ,file))
       (ggtags-mode 1)
       (goto-char (point-min))
       ,@body)))

(defmacro verilog-ext-test-with-gtags-verbose (file &rest body)
  "Similar as `verilog-ext-test-with-gtags' but without mocking `message'
for verbosity purposes."
  (declare (indent 1) (debug t))
  `(let ((default-directory verilog-ext-tests-examples-dir)
         (process-environment process-environment))
     ;; Setup environment lexically only for current process
     (push "GTAGSLABEL=ctags" process-environment)
     ;; Remove/recreate gtags.file
     (dolist (file '("gtags.files" "GTAGS" "GPATH" "GRTAGS"))
       (when (file-exists-p file)
         (delete-file file)))
     (with-temp-file "gtags.files"
       (insert (mapconcat #'identity (directory-files-recursively default-directory "\.s?vh?$" nil nil t) "\n")))
     (message "%s" default-directory)
     (ggtags-create-tags default-directory)
     (message (shell-command-to-string "ls -al"))
     ;; Enable ggtags and run body
     (find-file (file-name-concat verilog-ext-tests-examples-dir ,file))
     (ggtags-mode 1)
     (goto-char (point-min))
     ,@body))

(ert-deftest navigation::xref-definition ()
  (verilog-ext-test-with-gtags "instances.sv"
    (verilog-ext-find-module-instance-fwd)
    (goto-char (match-beginning 0))
    ;; DANGER: At some point, for some unknown reason, ERT got frozen if ran interactive while executing `xref-find-definitions'.
    ;; Tested many things and changed many others but it seemed to be random and related to xref more than to any other thing
    ;; It works fine though if run in a subshell
    (xref-find-definitions (thing-at-point 'symbol :no-props)) ; `xref-find-definitions' could hang the ERT interactive test
    (should (string= buffer-file-name (file-name-concat verilog-ext-tests-examples-dir "jump-parent/block0.sv")))
    (should (equal (point) 15))))

(ert-deftest navigation::jump-to-module-at-point ()
  (verilog-ext-test-with-gtags "instances.sv"
    (verilog-ext-find-module-instance-fwd)
    (goto-char (match-beginning 0))
    (forward-line)
    ;; DANGER: At some point, for some unknown reason, ERT got frozen if ran interactive while executing `xref-find-definitions'.
    ;; Tested many things and changed many others but it seemed to be random and related to xref more than to any other thing
    ;; It works fine though if run in a subshell
    (verilog-ext-jump-to-module-at-point)
    (should (string= buffer-file-name (file-name-concat verilog-ext-tests-examples-dir "jump-parent/block0.sv")))
    (should (equal (point) 15))))

;; INFO: The analogous `navigation::jump-to-parent-module-ag' test works fine also in GitHub actions
;; Tried checking `default-directory', actual command, case-fold-search and the --line-buffered or --block-buffered option
;; However, interactively and in a shell local works fine but in GitHub action does not find any result in
;; verilog-ext folder.
;; Also tried with latest 13.0.0-musl and 13.0.0 in Ubuntu repo rg versions (same result)
;;  - Added this code at the end of setup-env.sh
;;    $ echo ""
;;    $ echo "Setting up manually last ripgrep version:"
;;    $ curl -L -o ripgrep.tar.gz https://github.com/BurntSushi/ripgrep/releases/download/13.0.0/ripgrep-13.0.0-x86_64-unknown-linux-musl.tar.gz
;;    $ tar xvzf ripgrep.tar.gz
;;    $ cd ripgrep-13.0.0-x86_64-unknown-linux-musl
;;    $ export PATH=$PWD:$PATH
;;    $ cd -
;;    $ which rg
;;    $ rg --version
(ert-deftest navigation::jump-to-parent-module-rg ()
  (cl-letf (((symbol-function 'compilation-start)
             (lambda (command &optional mode name-function highlight-regexp)
               (message "rg cmd: %s" command)
               (message "default-directory: %s" default-directory)
               (butlast (split-string (shell-command-to-string command) "\n") 6))))
    (let ((verilog-ext-jump-to-parent-module-engine "rg")
          (ripgrep-arguments '("--line-number" "--smart-case" "--max-columns" "240" "-w" "--line-buffered")))
      (message "case-fold-search %s" case-fold-search)
      ;; block0
      (verilog-ext-test-navigation-file "jump-parent/block0.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("[0m[35m./tests/examples/instances.sv[0m:[0m[32m23[0m:    [0m[1m[31mblock0[0m I_BLOCK0 (" "" "1 matches" "1 matched lines" "1 files contained matches"))))
      ;; block1
      (verilog-ext-test-navigation-file "jump-parent/block1.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("[0m[35m./tests/examples/instances.sv[0m:[0m[32m30[0m:    [0m[1m[31mblock1[0m I_BLOCK1(" "" "1 matches" "1 matched lines" "1 files contained matches"))))
      ;; block2
      (verilog-ext-test-navigation-file "jump-parent/block2.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("[0m[35m./tests/examples/instances.sv[0m:[0m[32m37[0m:    [0m[1m[31mblock2[0m #(" "" "1 matches" "1 matched lines" "1 files contained matches"))))
      ;; block3
      (verilog-ext-test-navigation-file "jump-parent/block3.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("[0m[35m./tests/examples/instances.sv[0m:[0m[32m48[0m:    [0m[1m[31mblock3[0m#(" "" "1 matches" "1 matched lines" "1 files contained matches"))))
      ;; block_gen
      (verilog-ext-test-navigation-file "jump-parent/block_gen.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("[0m[35m./tests/examples/instances.sv[0m:[0m[32m62[0m:            [0m[1m[31mblock_gen[0m #(" "" "1 matches" "1 matched lines" "1 files contained matches"))))
      ;; test_if
      (verilog-ext-test-navigation-file "jump-parent/test_if.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("[0m[35m./tests/examples/instances.sv[0m:[0m[32m77[0m:    [0m[1m[31mtest_if[0m I_TEST_IF (.clk(clk), .rst_n(rst_n));" "" "1 matches" "1 matched lines" "1 files contained matches"))))
      ;; test_if_params
      (verilog-ext-test-navigation-file "jump-parent/test_if_params.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("[0m[35m./tests/examples/instances.sv[0m:[0m[32m79[0m:    [0m[1m[31mtest_if_params[0m # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS (.clk(clk), .rst_n(rst_n));" "" "1 matches" "1 matched lines" "1 files contained matches"))))
      ;; test_if_params_array
      (verilog-ext-test-navigation-file "jump-parent/test_if_params_array.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("[0m[35m./tests/examples/instances.sv[0m:[0m[32m81[0m:    [0m[1m[31mtest_if_params_array[0m # (.param1(param1), .param2(param2)) ITEST_IF_PARAMS_ARRAY[5:0] (.clk(clk), .rst_n(rst_n));" "" "1 matches" "1 matched lines" "1 files contained matches"))))
      ;; test_if_params_empty
      (verilog-ext-test-navigation-file "jump-parent/test_if_params_empty.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("[0m[35m./tests/examples/instances.sv[0m:[0m[32m83[0m:    [0m[1m[31mtest_if_params_empty[0m #() I_TEST_IF_PARAMS_EMPTY (.clk(clk), .rst_n(rst_n));" "" "1 matches" "1 matched lines" "1 files contained matches"))))
      ;; block_ws_0
      (verilog-ext-test-navigation-file "jump-parent/block_ws_0.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("[0m[35m./tests/examples/instances.sv[0m:[0m[32m87[0m:    [0m[1m[31mblock_ws_0[0m" "" "1 matches" "1 matched lines" "1 files contained matches"))))
      ;; block_ws_1 (TODO: Referenced in instances.sv:94 but not working with current regexp)
      (verilog-ext-test-navigation-file "jump-parent/block_ws_1.sv"
        (should (equal (verilog-ext-jump-to-parent-module)
                       '("" "0 matches" "0 matched lines" "0 files contained matches")))))))


(provide 'verilog-ext-tests-misc)

;;; verilog-ext-tests-misc.el ends here
