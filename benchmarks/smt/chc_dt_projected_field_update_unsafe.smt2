; Datatype projected-field update shaped like model-checker-consumer WriteAnySlim field havoc.
;
; State is a Pair(target, other). The transition rebuilds the root value with
; one updated target field while preserving the sibling through a selector:
;   p' = mkPair(target(p) + 1, other(p))
;
; Safety requires target to remain at its initial value. This is unsafe because
; the transition increments target while preserving other.
; Expected: unsat/unsafe.
(set-logic HORN)

(declare-datatype Pair ((mkPair (target Int) (other Int))))

(declare-fun |inv| (Pair) Bool)

; Init: target starts at 1.
(assert
  (forall ((p Pair))
    (=> (= p (mkPair 1 10))
        (inv p))))

; Projected-field update: only target changes.
(assert
  (forall ((p Pair) (p2 Pair))
    (=> (and (inv p)
             (= p2 (mkPair (+ (target p) 1) (other p))))
        (inv p2))))

; Bad: the target field changed while the preserved sibling still has its
; initial value.
(assert
  (forall ((p Pair))
    (=> (and (inv p)
             (= (other p) 10)
             (not (= (target p) 1)))
        false)))

(check-sat)
(exit)
