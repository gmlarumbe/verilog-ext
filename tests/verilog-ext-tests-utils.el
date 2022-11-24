;;; verilog-ext-tests-utils.el --- Verilog-Ext ERT utils tests  -*- lexical-binding: t -*-

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
;; ERT Utils Tests
;;
;;; Code:


(defmacro verilog-ext-test-utils-file (file &rest body)
  (declare (indent 1) (debug t))
  `(with-temp-buffer
     (insert-file-contents (verilog-ext-path-join verilog-ext-tests-examples-dir ,file))
     (verilog-mode)
     ,@body))


(defvar verilog-ext-test-utils-point-inside-block-alist
  '(("ucontroller.sv" ((1266 . nil)
                       (1267 . "module")
                       (1270 . "module")
                       (4334 . "module")
                       (4865 . nil)))
    ("instances.sv" ((1423 . "module")
                     (1635 . "generate")
                     (1764 . "generate")
                     (1984 . "generate")
                     (1985 . "module")
                     (2632 . "module")
                     (2820 . nil)))
    ("tb_program.sv" ((855 . nil)
                      (975 . nil)
                      (1287 . "module")
                      (1619 . "initial")
                      (2029 . "task")
                      (3495 . "task")
                      (3643 . "task")
                      (4343 . "initial")
                      (4556 . "initial")
                      (4635 . "module")
                      (4635 . "module")
                      (4636 . nil)))
    ("uvm_component.svh" ((1790 . nil)
                          (1881 . nil)
                          (1882 . "class")
                          (2747 . "class")
                          (7601 . "class")
                          (7602 . "class")
                          (29886 . "function")
                          ;; (30879 . "function") ; ERROR in utils::block-at-point: virtual function void raised
                          ;; (31499 . "function") ; ERROR in utils::block-at-point: virtual function void dropped
                          (32030 . "class")
                          (58668 . nil)
                          (59430 . "function")
                          (63161 . "function")
                          (76134 . "task")
                          (76584 . nil)
                          (76623 . "task")
                          (76638 . nil)
                          (100707 . nil)
                          (100752 . "function")
                          (100828 . nil)))
    ("axi_test.sv" ((954 . "package")
                    (1074 . "package")
                    (1245 . "class")
                    (1386 . "class")
                    (1433 . "function")
                    (77731 . "class")
                    (77760 . "package")
                    (77772 . nil)
                    (78713 . nil)
                    (79365 . "module")
                    (79753 . "always")
                    (82960 . "initial")
                    (86883 . "module")
                    (86893 . nil)))))


(ert-deftest utils::scan-buffer-modules ()
  (should (equal (verilog-ext-test-utils-file "tb_program.sv"
                   (verilog-ext-scan-buffer-modules))
                 '("tb_program")))
  (should (equal (verilog-ext-test-utils-file "ucontroller.sv"
                   (verilog-ext-scan-buffer-modules))
                 '("ucontroller")))
  (should (equal (verilog-ext-test-utils-file "axi_test.sv"
                   (verilog-ext-scan-buffer-modules))
                 '("axi_chan_logger")))
  (should (equal (verilog-ext-test-utils-file "axi_demux.sv"
                   (verilog-ext-scan-buffer-modules))
                 '("axi_demux_intf" "axi_demux_id_counters" "axi_demux")))
  (should (equal (verilog-ext-test-utils-file "instances.sv"
                   (verilog-ext-scan-buffer-modules))
                 '("instances")))
  (should (equal (verilog-ext-test-utils-file "uvm_component.svh"
                   (verilog-ext-scan-buffer-modules))
                 nil)))

(ert-deftest utils::point-inside-block ()
  (let ((alist verilog-ext-test-utils-point-inside-block-alist)
        file data block)
    (dolist (elm alist)
      (setq file (car elm))
      (setq data (cadr elm))
      (verilog-ext-test-utils-file file
        (dolist (pos-type data)
          (goto-char (car pos-type))
          (if (cdr pos-type)
              (setq block (intern (cdr pos-type)))
            (setq block nil))
          (when block
            (should (verilog-ext-point-inside-block-p block))))))))

(ert-deftest utils::block-at-point ()
  (let ((alist verilog-ext-test-utils-point-inside-block-alist)
        file data)
    (dolist (elm alist)
      (setq file (car elm))
      (setq data (cadr elm))
      (verilog-ext-test-utils-file file
        (dolist (pos-type data)
          (goto-char (car pos-type))
          (should (equal (alist-get 'type (verilog-ext-block-at-point))
                         (cdr pos-type))))))))



(provide 'verilog-ext-tests-utils)

;;; verilog-ext-tests-utils.el ends here
