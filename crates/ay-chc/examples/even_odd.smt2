; Even-Odd mutual recursion example
; Two predicates: Even(x) and Odd(x)
; Invariant:
;   - Even(x) holds when x is even and x >= 0
;   - Odd(x) holds when x is odd and x >= 0
; This system is SAFE - we can never reach negative x

(set-logic HORN)

; Declare predicates
(declare-rel Even (Int))
(declare-rel Odd (Int))

; Declare variables
(declare-var x Int)

; Base cases
; x = 0 => Even(x)
(rule (=> (= x 0) (Even x)))

; x = 1 => Odd(x)
(rule (=> (= x 1) (Odd x)))

; Recursive cases: Even(x) /\ x > 0 => Odd(x-1) and Odd(x) /\ x > 1 => Even(x-1)
; But actually we want forward: Even(x) /\ x >= 0 => Even(x+2), etc.

; Forward transitions:
; Even(x) => Even(x + 2)  (when x >= 0)
(rule (=> (and (Even x) (>= x 0)) (Even (+ x 2))))

; Odd(x) => Odd(x + 2)  (when x >= 1)
(rule (=> (and (Odd x) (>= x 1)) (Odd (+ x 2))))

; Safety: Even(x) /\ x < 0 => false
(query (and (Even x) (< x 0)))
