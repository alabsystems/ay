; Copyright 2026 Andrew Yates
; Author: Andrew Yates
; Licensed under the Apache License, Version 2.0
; Ground UF+LIA regression, with the original ten-second query budget.
; Exact query dumped by unchanged f33 driver; only diagnostic assume/goal wrappers and nullary-call notation translated to standard SMT-LIB.
(set-option :timeout 10000)
(set-option :produce-models true)
(declare-const v0 Int) ; i
(declare-const v1 Int) ; j
(declare-const v2 Int) ; decreases
(declare-const v3 Int) ; j
(declare-const v4 Int) ; j
(declare-const v5 Int) ; j
(declare-fun nl_mul (Int Int) Int)
(declare-fun nl_div (Int Int) Int)
(declare-fun nl_mod (Int Int) Int)
(declare-fun clip_u8_oob (Int) Int)
(declare-fun clip_u16_oob (Int) Int)
(declare-fun clip_u32_oob (Int) Int)
(declare-fun clip_u64_oob (Int) Int)
(declare-fun clip_i8_oob (Int) Int)
(declare-fun clip_i16_oob (Int) Int)
(declare-fun clip_i32_oob (Int) Int)
(declare-fun clip_i64_oob (Int) Int)
(declare-fun clip_nat_oob (Int) Int)
(declare-fun sf0 (Int) Int)
(declare-fun rf0 (Int) Int)
(declare-fun sf1 () Int)
(assert (<= 0 v0)) ; h1 TypeFact
(assert (<= 0 v1)) ; h2 TypeFact
(assert (<= v0 v1)) ; h3 Requires
(assert (= v2 (- v1 v0))) ; h4 Binding
(assert (<= 0 v3)) ; h5 TypeFact
(assert (=> (and (not (and (< v0 2) (< v1 2))) (not (= v0 v1)) (= v0 (- v1 1))) (= v3 (ite (<= 0 (- v1 1)) (- v1 1) (clip_nat_oob (- v1 1)))))) ; h6 Binding
(assert (=> (and (not (and (< v0 2) (< v1 2))) (not (= v0 v1)) (= v0 (- v1 1))) (<= (sf0 v0) (sf0 v3)))) ; h15 CalleeEnsures
(assert (<= 0 v4)) ; h16 TypeFact
(assert (=> (and (not (and (< v0 2) (< v1 2))) (not (= v0 v1)) (not (= v0 (- v1 1)))) (= v4 (ite (<= 0 (- v1 1)) (- v1 1) (clip_nat_oob (- v1 1)))))) ; h17 Binding
(assert (=> (and (not (and (< v0 2) (< v1 2))) (not (= v0 v1)) (not (= v0 (- v1 1)))) (<= (sf0 v0) (sf0 v4)))) ; h30 CalleeEnsures
(assert (<= 0 v5)) ; h31 TypeFact
(assert (=> (and (not (and (< v0 2) (< v1 2))) (not (= v0 v1)) (not (= v0 (- v1 1)))) (= v5 (ite (<= 0 (- v1 2)) (- v1 2) (clip_nat_oob (- v1 2)))))) ; h32 Binding
(assert (=> (and (not (and (< v0 2) (< v1 2))) (not (= v0 v1)) (not (= v0 (- v1 1)))) (<= (sf0 v0) (sf0 v5)))) ; h65 CalleeEnsures
(assert (=> (<= 0 v0) (= (sf0 v0) (rf0 v0)))) ; fu66 Axiom
(assert (=> (and (not (= v4 v0)) (not (and (not (<= 2 v0)) (not (<= 2 v1)))) (not (= v0 v1)) (not (= v0 (- v1 1)))) (=> (<= 0 v4) (= (sf0 v4) (rf0 v4))))) ; fu67 Axiom
(assert (=> (<= 0 v1) (= (sf0 v1) (rf0 v1)))) ; fu68 Axiom
(assert (=> (<= 0 v0) (= (rf0 v0) (ite (= v0 0) 0 (ite (= v0 1) 1 (+ (rf0 (ite (<= 0 (- v0 2)) (- v0 2) (clip_nat_oob (- v0 2)))) (rf0 (ite (<= 0 (- v0 1)) (- v0 1) (clip_nat_oob (- v0 1)))))))))) ; fu69 Axiom
(assert (=> (and (not (= v4 v0)) (not (and (not (<= 2 v0)) (not (<= 2 v1)))) (not (= v0 v1)) (not (= v0 (- v1 1)))) (=> (<= 0 v4) (= (rf0 v4) (ite (= v4 0) 0 (ite (= v4 1) 1 (+ (rf0 (ite (<= 0 (- v4 2)) (- v4 2) (clip_nat_oob (- v4 2)))) (rf0 (ite (<= 0 (- v4 1)) (- v4 1) (clip_nat_oob (- v4 1))))))))))) ; fu70 Axiom
(assert (=> (<= 0 v1) (= (rf0 v1) (ite (= v1 0) 0 (ite (= v1 1) 1 (+ (rf0 (ite (<= 0 (- v1 2)) (- v1 2) (clip_nat_oob (- v1 2)))) (rf0 (ite (<= 0 (- v1 1)) (- v1 1) (clip_nat_oob (- v1 1)))))))))) ; fu71 Axiom
(assert (<= 0 (clip_nat_oob (- v1 1)))) ; ax72 Axiom
(assert (<= 0 (sf0 v0))) ; ax73 Axiom
(assert (<= 0 (sf0 v3))) ; ax74 Axiom
(assert (<= 0 (sf0 v4))) ; ax75 Axiom
(assert (<= 0 (clip_nat_oob (- v1 2)))) ; ax76 Axiom
(assert (<= 0 (sf0 v5))) ; ax77 Axiom
(assert (<= 0 (sf0 v1))) ; ax78 Axiom
(assert (<= 0 (clip_nat_oob (- v0 2)))) ; ax79 Axiom
(assert (<= 0 (clip_nat_oob (- v0 1)))) ; ax80 Axiom
(assert (<= 0 (clip_nat_oob (- v4 2)))) ; ax81 Axiom
(assert (<= 0 (clip_nat_oob (- v4 1)))) ; ax82 Axiom
(assert (not (<= (sf0 v0) (sf0 v1))))
(check-sat)
(get-model)
