; Two NaNs denote the same abstract SMT-LIB value, irrespective of payload.
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 15 113))
(declare-fun y () (_ FloatingPoint 15 113))
(assert (fp.isNaN x))
(assert (fp.isNaN y))
(assert (not (= x y)))
(check-sat)
