;;; verilog-ext-tests-setup-faces.el --- Verilog-ext tests faces setup  -*- lexical-binding: t -*-

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

;; Setup faces

;;; Code:

(set-face-attribute 'verilog-ext-font-lock-grouping-keywords-face nil :foreground "dark olive green")
(set-face-attribute 'verilog-ext-font-lock-punctuation-face nil       :foreground "burlywood")
(set-face-attribute 'verilog-ext-font-lock-operator-face nil          :foreground "burlywood" :weight 'extra-bold)
(set-face-attribute 'verilog-ext-font-lock-brackets-face nil          :foreground "goldenrod")
(set-face-attribute 'verilog-ext-font-lock-parenthesis-face nil       :foreground "dark goldenrod")
(set-face-attribute 'verilog-ext-font-lock-curly-braces-face nil      :foreground "DarkGoldenrod2")
(set-face-attribute 'verilog-ext-font-lock-port-connection-face nil   :foreground "bisque2")
(set-face-attribute 'verilog-ext-font-lock-dot-name-face nil          :foreground "gray70")
(set-face-attribute 'verilog-ext-font-lock-brackets-content-face nil  :foreground "yellow green")
(set-face-attribute 'verilog-ext-font-lock-width-num-face nil         :foreground "chartreuse2")
(set-face-attribute 'verilog-ext-font-lock-width-type-face nil        :foreground "sea green" :weight 'bold)
(set-face-attribute 'verilog-ext-font-lock-module-face nil            :foreground "green1")
(set-face-attribute 'verilog-ext-font-lock-instance-face nil          :foreground "medium spring green")
(set-face-attribute 'verilog-ext-font-lock-time-event-face nil        :foreground "deep sky blue" :weight 'bold)
(set-face-attribute 'verilog-ext-font-lock-time-unit-face nil         :foreground "light steel blue")
(set-face-attribute 'verilog-ext-font-lock-preprocessor-face nil      :foreground "pale goldenrod")
(set-face-attribute 'verilog-ext-font-lock-modport-face nil           :foreground "light blue")
(set-face-attribute 'verilog-ext-font-lock-direction-face nil         :foreground "RosyBrown3")
(set-face-attribute 'verilog-ext-font-lock-typedef-face nil           :foreground "light blue")
(set-face-attribute 'verilog-ext-font-lock-translate-off-face nil     :background "gray20" :slant 'italic)
(set-face-attribute 'verilog-ext-font-lock-uvm-classes-face nil       :foreground "light blue")
(set-face-attribute 'verilog-ext-font-lock-xilinx-attributes-face nil :foreground "orange1")

(set-face-attribute 'verilog-ts-font-lock-grouping-keywords-face nil :foreground "dark olive green")
(set-face-attribute 'verilog-ts-font-lock-punctuation-face nil       :foreground "burlywood")
(set-face-attribute 'verilog-ts-font-lock-operator-face nil          :foreground "burlywood" :weight 'extra-bold)
(set-face-attribute 'verilog-ts-font-lock-brackets-face nil          :foreground "goldenrod")
(set-face-attribute 'verilog-ts-font-lock-parenthesis-face nil       :foreground "dark goldenrod")
(set-face-attribute 'verilog-ts-font-lock-curly-braces-face nil      :foreground "DarkGoldenrod2")
(set-face-attribute 'verilog-ts-font-lock-port-connection-face nil   :foreground "bisque2")
(set-face-attribute 'verilog-ts-font-lock-dot-name-face nil          :foreground "gray70")
(set-face-attribute 'verilog-ts-font-lock-brackets-content-face nil  :foreground "yellow green")
(set-face-attribute 'verilog-ts-font-lock-width-num-face nil         :foreground "chartreuse2")
(set-face-attribute 'verilog-ts-font-lock-width-type-face nil        :foreground "sea green" :weight 'bold)
(set-face-attribute 'verilog-ts-font-lock-module-face nil            :foreground "green1")
(set-face-attribute 'verilog-ts-font-lock-instance-face nil          :foreground "medium spring green")
(set-face-attribute 'verilog-ts-font-lock-time-event-face nil        :foreground "deep sky blue" :weight 'bold)
(set-face-attribute 'verilog-ts-font-lock-time-unit-face nil         :foreground "light steel blue")
(set-face-attribute 'verilog-ts-font-lock-preprocessor-face nil      :foreground "pale goldenrod")
(set-face-attribute 'verilog-ts-font-lock-modport-face nil           :foreground "light blue")
(set-face-attribute 'verilog-ts-font-lock-direction-face nil         :foreground "RosyBrown3")
(set-face-attribute 'verilog-ts-font-lock-translate-off-face nil     :background "gray20" :slant 'italic)
(set-face-attribute 'verilog-ts-font-lock-attribute-face nil         :foreground "orange1")


(provide 'verilog-ext-tests-setup-faces)

;;; verilog-ext-tests-setup-faces.el ends here
