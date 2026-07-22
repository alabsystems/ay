; Struct with two fields requiring relational invariant.
; Init: x = 0, y = 0
; Trans: x' = x + 1, y' = y + 2
; Safety: y = 2 * x (fields maintain a ratio)
; Expected: sat (safe) -- y always equals 2*x.
; This requires PDR to discover the relational invariant y = 2*x.
(set-logic HORN)

(declare-datatype State ((mkState (x Int) (y Int))))

(declare-fun |inv| (State) Bool)

; Init: State(0, 0)
(assert
  (forall ((s State))
    (=> (and (= (x s) 0) (= (y s) 0))
        (inv s))))

; Trans: x' = x + 1, y' = y + 2
(assert
  (forall ((s State) (s2 State))
    (=> (and (inv s)
             (= (x s2) (+ (x s) 1))
             (= (y s2) (+ (y s) 2)))
        (inv s2))))

; Safety: y = 2 * x
(assert
  (forall ((s State))
    (=> (and (inv s) (not (= (y s) (* 2 (x s)))))
        false)))

(check-sat)
(exit)
