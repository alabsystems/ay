; The SAT half of the same family, and it decides.
;
; A positive-polarity FP `exists` in a DISJUNCTIVE position. The lane fixes the
; quantifier's truth value under the pins with checked UNSAT solves and
; substitutes a constant — position-independent, so the enclosing `or` costs it
; nothing:
;
;   FMQ round 0: pins=1 total=true model=true
;   FMQ round 0: all determined; confirm=true
;   FMQ gate-hook: installed=true
;   sat
;
; Ground truth: SAT (take Y = 1.0, which falsifies the first disjunct's negand
; is irrelevant — the disjunct `(not (= Y 0.0))` holds outright). bitwuzla
; agrees.
;
; Kept next to `negated_exists_unsat_still_declines.smt2` so the pair shows what
; the lane can and cannot do: it establishes SATISFIABILITY, never refutation.
(set-logic BVFPLRA)
(declare-fun Y () (_ FloatingPoint 8 24))
(assert (or (not (= Y ((_ to_fp 8 24) RNE (_ bv0 32))))
            (exists ((d (_ FloatingPoint 8 24)))
              (and (fp.geq d (_ +zero 8 24))
                   (fp.leq d ((_ to_fp 8 24) RNE 16.0))
                   (= Y (fp.sub RNE ((_ to_fp 8 24) RNE (_ bv0 32)) d))))))
(check-sat)
