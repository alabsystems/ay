; Simple CHC with Array-sorted predicate parameter
; Expected: sat (safe)
;
; P(a) := a is an array where a[0] = 42
; Init: a = store(const_array(0), 0, 42) => P(a)
; Trans: P(a) => P(a)  (identity transition)
; Bad:  P(a) /\ select(a, 0) != 42 => false
;
; Invariant: select(a, 0) = 42

(set-logic HORN)

(declare-fun P ((Array Int Int)) Bool)

(assert (forall ((a (Array Int Int)))
  (=> (= (select a 0) 42) (P a))))

(assert (forall ((a (Array Int Int)) (b (Array Int Int)))
  (=> (and (P a) (= b a)) (P b))))

(assert (forall ((a (Array Int Int)))
  (=> (and (P a) (not (= (select a 0) 42))) false)))

(check-sat)
