; Z3 issue #7135 — Refutational soundness in FP (minimized cvc5 vs Z3 mismatch).
; Source: https://github.com/Z3Prover/z3/issues/7135
;
; z3   ./small.smt2  -> unsat
; cvc5 ./small.smt2 --fp-exp --produce-models --check-models -> sat (validated model)
;
; Expected: sat (cvc5 verified model). Z3 reports unsat. This is a Z3
; refutational-soundness bug in QF_BVFP; ay must NOT claim unsat.
(set-logic QF_BVFP)
(declare-fun x_ackermann!1 () (_ BitVec 64))
(declare-fun x_ackermann!0 () (_ BitVec 64))
(declare-fun x_ackermann!2 () (_ BitVec 64))
(declare-fun x_ackermann!3 () (_ BitVec 64))
(declare-fun x_ackermann!4 () (_ BitVec 64))
(declare-fun x_ackermann!5 () (_ BitVec 64))
(declare-fun generated_0 () (_ BitVec 32))
(declare-fun generated_1 () (_ BitVec 13))
(assert (not (fp.gt ((_ to_fp 11 53) x_ackermann!4) ((_ to_fp_unsigned 11 53) RNA (bvsdiv (bvneg ((_ repeat 2) (bvand #b11000000101101011101010111101100 generated_0))) ((_ fp.to_ubv 64) RNA (fp.sub RNA (fp.sqrt RTZ (fp #b0 #b1000111110 #b10001010111110001100011100011001000101100101010100100)) (fp.mul RNA (fp #b0 #b1000111110 #b01110101000000010010101010011111001011010111011000110) (fp #b0 #b1000111101 #b10100001011100001000101001101010011010111100111001001)))))))))
(assert (= (fp.gt (fp.add RTN (fp.neg (fp.neg (fp #b0 #b11010 #b011110))) (fp.fma RTZ (fp.sub RNA (fp #b0 #b11001 #b110011) (fp #b0 #b11000 #b000011)) (fp.fma RNA (fp #b0 #b11010 #b111100) (fp #b0 #b11010 #b011010) (fp #b0 #b11010 #b010100)) (fp.neg (fp #b0 #b11001 #b110000)))) (fp #b0 #b11010 #b001001)) (and (fp.isNormal ((_ to_fp_unsigned 2 11) RTN (bvsrem #b1110001100001 generated_1))) (=> (fp.isSubnormal (fp.div RTZ (_ +oo 3 3) (_ +oo 3 3))) (xor (fp.gt (_ +oo 2 27) (_ +oo 2 27)) (fp.lt (_ +oo 4 10) (_ +oo 4 10)))))))
(assert (bvsle #b01101101000011101110000000110010 generated_0))
(assert (bvsge generated_1 #b1100001100101))
(check-sat)
