; Array store chain equality: two arrays must be equal
; Tests: array extensionality via store chains
(set-info :status unsat)
(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))

; store(a, 0, v) then select at 0 must give v
(declare-const v (_ BitVec 8))
(define-fun a1 () (Array (_ BitVec 8) (_ BitVec 8))
  (store a #x00 v))
(assert (not (= (select a1 #x00) v)))

(check-sat)
(exit)
