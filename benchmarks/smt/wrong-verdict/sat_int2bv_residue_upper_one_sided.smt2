; D5 (2026-09-23 BV hunt): x = -1 gives int2bv_8(x) = #xff. main f399eca07a
; answered unsat in both postures (default: discharged-trust).
(set-logic ALL)
(declare-fun x () Int)
(assert (<= x 5))
(assert (> (bv2nat ((_ int2bv 8) x)) 5))
(check-sat)
