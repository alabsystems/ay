; Verus-style: EucDiv/EucMod/Mul defined by triggered universals.
; Equisatisfiable with its ground twin, which z3 4.12.5 answers sat.
; AY answered unsat before the fixed-term export required both sides justified.
(declare-fun f (Int) Int)
(declare-fun EucDiv (Int Int) Int)
(declare-fun Mul (Int Int) Int)
(assert (forall ((a Int) (b Int)) (! (= (EucDiv a b) (div a b)) :pattern ((EucDiv a b)))))
(assert (forall ((a Int) (b Int)) (! (= (Mul a b) (* a b)) :pattern ((Mul a b)))))
(declare-const x Int)
(declare-const d Int)
(declare-const e Int)
(declare-const c Int)
(assert (= (EucDiv d d) 5))
(assert (not (= (Mul c d) (Mul x x))))
(assert (= 3 (EucDiv 7 (f e))))
(check-sat)
