; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
; Model validation must check nullable replacement at an assigned String value.
(set-logic QF_SLIA)
(set-info :status sat)
(declare-const subject String)
(assert (= subject "aabaaa"))
(assert (= (str.replace_re subject (re.* (str.to_re "a")) "X") "Xaabaaa"))
(assert (= (str.replace_re_all subject (re.* (str.to_re "a")) "X") "XXbXXX"))
(check-sat)
