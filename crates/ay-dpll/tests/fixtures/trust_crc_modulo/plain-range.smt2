(set-logic QF_NIA)
(declare-fun __trust_u_crc () Int)
(assert (and (<= 0 __trust_u_crc) (<= __trust_u_crc 4294967295) (not (or (= (mod __trust_u_crc 2) 0) (= (mod __trust_u_crc 2) 1)))))
(check-sat)
