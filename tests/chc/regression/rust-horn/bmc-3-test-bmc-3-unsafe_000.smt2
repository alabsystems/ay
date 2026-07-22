; Reduced rust-horn BMC unsafe canary for #9618.
;
; Provenance: the original rust-horn file named
; bmc-3-test-bmc-3-unsafe_000.smt2 was not present in this workspace or in the
; local benchmark/reference directories searched on 2026-05-01. This checked-in
; fixture keeps the missing filename and reduces the required behavior to a
; three-step reachable bad state: AY must print first-line `unsat` plus an
; UNSAFE CHC certificate marker, never `sat`/SAFE.
(set-info :status unsat)
(set-logic HORN)

(declare-fun Inv (Int) Bool)

(assert (forall ((x Int))
  (=> (= x 0)
      (Inv x))))

(assert (forall ((x Int))
  (=> (and (Inv x) (< x 3))
      (Inv (+ x 1)))))

(assert (forall ((x Int))
  (=> (and (Inv x) (>= x 3))
      false)))

(check-sat)
