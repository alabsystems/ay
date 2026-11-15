; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
; Any disagreement with the Unicode Strings replacement clauses is SAT.
; Expected: UNSAT. Unicode Strings 2.7, shortest leftmost matches.
(set-logic QF_SLIA)
(assert (or
  (distinct (str.replace_re "bbb" (re.* (str.to_re "a")) "X") "Xbbb")
  (distinct (str.replace_re_all "bbb" (re.* (str.to_re "a")) "X") "bbb")
  (distinct (str.replace_re "aabaaa" (re.* (str.to_re "a")) "X") "Xaabaaa")
  (distinct (str.replace_re_all "aabaaa" (re.* (str.to_re "a")) "X") "XXbXXX")
  (distinct (str.replace_re "\u{3b1}a" (re.* (str.to_re "a")) "X") "X\u{3b1}a")
  (distinct (str.replace_re_all "\u{3b1}a" (re.* (str.to_re "a")) "X") "\u{3b1}X")
  (distinct (str.replace_re "abc" (str.to_re "") "X") "Xabc")
  (distinct (str.replace_re_all "abc" (str.to_re "") "X") "abc")
  (distinct (str.replace_re "" (str.to_re "") "X") "X")
  (distinct (str.replace_re_all "" (str.to_re "") "X") "")
  (distinct (str.replace_re "abc" re.all "X") "Xabc")
  (distinct (str.replace_re_all "abc" re.all "X") "XXX")
  (distinct (str.replace_re "abc" (re.opt (str.to_re "a")) "X") "Xabc")
  (distinct (str.replace_re_all "abc" (re.opt (str.to_re "a")) "X") "Xbc")
  (distinct (str.replace_re "bab" (re.union (str.to_re "a") (str.to_re "")) "X") "Xbab")
))
(check-sat)
