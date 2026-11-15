; D7 (2026-09-23 hunt, witness w10). z3 5.1.0: sat. main f399eca07a: unsat.
; 12.0 is out of range for a 3-bit unsigned conversion, so both values are
; unspecified -- but fp.to_ubv is a function of (rm, x), and RNE and RTZ are
; different arguments: the two values may differ. AY keyed the unspecified
; value on x alone and forced them equal.
(set-logic ALL)
(assert (not (= ((_ fp.to_ubv 3) RNE ((_ to_fp 3 4) RNE 12.0)) ((_ fp.to_ubv 3) RTZ ((_ to_fp 3 4) RNE 12.0)))))
(check-sat)
