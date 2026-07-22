; expected: sat
; QF_ABV — bit-vector-indexed array, satisfiable store/select.
(set-logic QF_ABV)
(set-info :status sat)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const i (_ BitVec 4))
(assert (= (select (store a i #xff) i) #xff))
(check-sat)
