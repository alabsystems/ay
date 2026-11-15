; D13 (2026-09-24 fp-strings fix-up, conversion audit witness fbvA). The exact
; reference (the hunt's fpref.py) and z3 5.1.0: sat. main 6818b5d067: unsat
; in both postures. The conversion of a bv_sz-bit integer starts its exponent at
; bv_sz - 2 = 22, which wrapped in (2,3)'s eb + 2 = 4 bits: 1 read as +0.
(set-logic QF_BVFP)
(declare-const b (_ BitVec 24))
(declare-const y (_ FloatingPoint 2 3))
(assert (= b #x000001))
(assert (= y ((_ to_fp_unsigned 2 3) RNE b)))
(assert (not (fp.isZero y)))
(check-sat)
