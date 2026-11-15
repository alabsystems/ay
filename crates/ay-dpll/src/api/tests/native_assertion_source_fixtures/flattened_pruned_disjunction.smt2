(declare-const cond Bool)
(declare-const x Int)
(declare-const y Int)
(assert (and (and (<= 0 x) (<= x 4294967295)) (and (<= 0 y) (<= y 4294967295)) (or (and (not cond) (and (<= 0 x) (<= x 1000)) (and (<= 0 y) (<= y 1000)) (and (and (<= 0 x) (<= x 4294967295)) (and (<= 0 y) (<= y 4294967295)) (and (and (<= 0 x) (<= x 4294967295)) (and (<= 0 y) (<= y 4294967295)) (or (< (+ x y) 0) (> (+ x y) 4294967295))))) (and false (and (<= 0 x) (<= x 1000)) (and (<= 0 y) (<= y 1000)) (and (and (<= 0 x) (<= x 4294967295)) (and (<= 0 y) (<= y 4294967295)) (and (and (<= 0 x) (<= x 4294967295)) (and (<= 0 y) (<= y 4294967295)) (or (< (+ x y) 0) (> (+ x y) 4294967295))))))))
