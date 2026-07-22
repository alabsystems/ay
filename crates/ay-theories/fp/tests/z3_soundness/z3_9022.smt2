; Z3 issue #9022 — FPA soundness in incremental solving (push/pop).
; Source: https://github.com/Z3Prover/z3/issues/9022
;
; Z3 reports unsat at the (check-sat) inside the push. Removing the push
; changes the answer to sat (unsound incremental behaviour).
; Expected (SMT-LIB semantics): sat — the int_to_fp axiom is consistent
; with the triggering_term assertions.
;
; ay contract: must NOT claim unsat. Partial quantifier support is OK
; (answer `unknown` is acceptable; `unsat` is a soundness violation).
(declare-fun int_to_fp (Int) (_ FloatingPoint 5 11))

(assert (forall ((i Int))
  (! (= (int_to_fp i) ((_ to_fp 5 11) ((_ int2bv 16) i)))
     :pattern ((int_to_fp i))
     :qid |int_to_fp_def|)))

(assert (forall ((i Int) (j Int))
  (! (and (= (fp.to_real (fp.add RNE (int_to_fp i) (int_to_fp j)))
             (fp.to_real (fp.add RNE ((_ to_fp 5 11) ((_ int2bv 16) i)) ((_ to_fp 5 11) ((_ int2bv 16) j)))))
          (= (fp.to_real (fp.sub RNE (int_to_fp i) (int_to_fp j)))
             (fp.to_real (fp.sub RNE ((_ to_fp 5 11) ((_ int2bv 16) i)) ((_ to_fp 5 11) ((_ int2bv 16) j))))))
     :pattern ((int_to_fp i) (int_to_fp j))
     :qid |int_to_fp_ax|)))

(push)
(declare-fun triggering_term ((_ FloatingPoint 5 11)) Bool)

(assert (triggering_term (int_to_fp 16384)))
(assert (triggering_term (int_to_fp 15820)))
(check-sat)
