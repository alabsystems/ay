; Minimal CHC with DT-sorted predicate parameter.
; Pattern: construct a Pair(x, y), store it, read fields back.
; Invariant: fld_0(p) >= 0  (the first field is non-negative).
; Expected: sat (safe) — init sets fld_0 to 42.
(set-logic HORN)

; A simple pair of two ints
(declare-datatype IntPair ((mkpair (fst Int) (snd Int))))

; Predicate: inv(p) where p is DT-sorted
(declare-fun |inv| (IntPair) Bool)

; Init: p = mkpair(42, 7)
(assert
  (forall ((p IntPair))
    (=> (= p (mkpair 42 7))
        (inv p))))

; Trans: identity (no modification)
(assert
  (forall ((p IntPair))
    (=> (inv p) (inv p))))

; Bad: fst(p) < 0
(assert
  (forall ((p IntPair))
    (=> (and (inv p) (< (fst p) 0))
        false)))

(check-sat)
(exit)
