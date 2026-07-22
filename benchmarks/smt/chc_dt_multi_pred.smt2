; Multi-predicate CHC with DT arguments.
; Two predicates: Init and Loop, both take a Pair struct.
; Tests that DT flattening works across multiple predicates.
; Init: Pair(0, 0) => Init(p)
; Trans: Init(p) => Loop(p)
;         Loop(p) AND p2 = Pair(x+1, y+1) => Loop(p2)
; Safety: x(p) = y(p)
; Expected: sat (safe)
(set-logic HORN)

(declare-datatype Pair ((mk (fst Int) (snd Int))))

(declare-fun |Init| (Pair) Bool)
(declare-fun |Loop| (Pair) Bool)

; Init predicate
(assert
  (forall ((p Pair))
    (=> (and (= (fst p) 0) (= (snd p) 0))
        (Init p))))

; Transfer from Init to Loop
(assert
  (forall ((p Pair))
    (=> (Init p)
        (Loop p))))

; Loop transition: increment both fields
(assert
  (forall ((p Pair) (p2 Pair))
    (=> (and (Loop p)
             (= (fst p2) (+ (fst p) 1))
             (= (snd p2) (+ (snd p) 1)))
        (Loop p2))))

; Safety: fields always equal
(assert
  (forall ((p Pair))
    (=> (and (Loop p) (not (= (fst p) (snd p))))
        false)))

(check-sat)
(exit)
