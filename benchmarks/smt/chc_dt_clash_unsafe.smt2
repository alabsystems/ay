; CHC with DT constructor clash — UNSAT (unsafe).
; The safety property requires is-Some(x), but the transition produces None.
; Expected: unsat (counterexample: init -> trans -> bad).
(set-logic HORN)

(declare-datatype OptionInt (
  (None)
  (Some (val Int))))

(declare-fun |inv| (OptionInt) Bool)

; Init: x = Some(42)
(assert
  (forall ((x OptionInt))
    (=> (= x (Some 42))
        (inv x))))

; Trans: any Some(n) transitions to None
(assert
  (forall ((x OptionInt) (y OptionInt))
    (=> (and (inv x) (is-Some x) (= y (as None OptionInt)))
        (inv y))))

; Safety: is-Some(x) must always hold
; This is VIOLATED because the transition produces None.
(assert
  (forall ((x OptionInt))
    (=> (and (inv x) (is-None x))
        false)))

(check-sat)
(exit)
