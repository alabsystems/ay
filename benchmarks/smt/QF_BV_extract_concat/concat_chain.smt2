; Andrew Yates <andrewyates.name@gmail.com>
; Chained concat operations
(set-logic QF_BV)
(set-info :status sat)

(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))
(declare-fun c () (_ BitVec 4))
(declare-fun d () (_ BitVec 4))

; Chain: concat(concat(concat(a, b), c), d) = concat(a, concat(b, concat(c, d)))
; 4 nibbles = 16 bits = #xABCD
(assert (= (concat (concat (concat a b) c) d) #xABCD))
(assert (= (concat a (concat b (concat c d))) #xABCD))

(check-sat)
(exit)
