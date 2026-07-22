; Z3 issue #9063 — Free variable in model (seq + datatypes).
; Source: https://github.com/Z3Prover/z3/issues/9063
;
; Minimized form (ay does not yet support parametric `(par ...)` datatypes,
; so we inline the monomorphic instance the Z3 repro actually uses:
; `SBVTuple2<(Seq Int), (Seq (Seq Int))>`).
;
; Original: the returned Z3 model contains `(seq.nth_i k!0 0)` where `k!0`
; is an internal variable leaking out of the model (not closed).
;
; Expected: sat with a closed model. Soundness check: ay must not claim
; unsat on this satisfiable seq+DT formula.
(set-logic ALL)
(declare-datatypes ((SBVTuple2 0))
  (((mkSBVTuple2 (proj_1_SBVTuple2 (Seq Int)) (proj_2_SBVTuple2 (Seq (Seq Int)))))))
(define-fun s1 () Int 0)
(define-fun s2 () Int 1)
(declare-fun s0 () SBVTuple2)
(declare-fun s11 () (Seq Int))
(define-fun s3 () (Seq (Seq Int)) (proj_2_SBVTuple2 s0))
(define-fun s4 () Int (seq.len s3))
(define-fun s5 () Bool (= s1 s4))
(define-fun s6 () (Seq Int) (proj_1_SBVTuple2 s0))
(define-fun s7 () (Seq Int) (seq.nth s3 s1))
(define-fun s8 () Int (- s4 s2))
(define-fun s9 () (Seq (Seq Int)) (seq.extract s3 s2 s8))
(define-fun s10 () SBVTuple2 (mkSBVTuple2 s6 s9))
(define-fun s12 () (Seq Int) (seq.++ s7 s11))
(define-fun s13 () (Seq Int) (ite s5 s6 s12))
(define-fun s14 () Int (seq.len s6))
(define-fun s15 () (Seq Int) (proj_1_SBVTuple2 s10))
(define-fun s16 () Int (seq.len s15))
(define-fun s17 () Bool (not s5))
(define-fun s18 () Bool (> s14 s16))
(define-fun s19 () Bool (=> s17 s18))
(assert (not s19))
(check-sat)
