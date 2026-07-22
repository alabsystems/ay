; Harder binary 0/1 ILP that is UNSAT
; Many variables, LP relaxation is SAT at fractional point 0.5
; Integer infeasible.
;
; Encodes: does a bipartite graph K_{3,3} have a perfect matching
; where each vertex is covered exactly once AND the total weight
; exceeds the maximum possible? (Infeasible weight constraint)
(set-logic QF_LIA)

; 9 binary variables for edges in K_{3,3}
(declare-fun e00 () Int) (declare-fun e01 () Int) (declare-fun e02 () Int)
(declare-fun e10 () Int) (declare-fun e11 () Int) (declare-fun e12 () Int)
(declare-fun e20 () Int) (declare-fun e21 () Int) (declare-fun e22 () Int)

; Binary domains
(assert (and (<= 0 e00) (<= e00 1)))
(assert (and (<= 0 e01) (<= e01 1)))
(assert (and (<= 0 e02) (<= e02 1)))
(assert (and (<= 0 e10) (<= e10 1)))
(assert (and (<= 0 e11) (<= e11 1)))
(assert (and (<= 0 e12) (<= e12 1)))
(assert (and (<= 0 e20) (<= e20 1)))
(assert (and (<= 0 e21) (<= e21 1)))
(assert (and (<= 0 e22) (<= e22 1)))

; Left vertices: exactly one edge selected per left vertex
(assert (= (+ e00 e01 e02) 1))
(assert (= (+ e10 e11 e12) 1))
(assert (= (+ e20 e21 e22) 1))

; Right vertices: exactly one edge selected per right vertex
(assert (= (+ e00 e10 e20) 1))
(assert (= (+ e01 e11 e21) 1))
(assert (= (+ e02 e12 e22) 1))

; Weight constraint: total must equal 4 (but max possible with matching is 3)
; Weights: w(e00)=1, w(e01)=1, ..., all weights = 1
; So total weight of any matching = 3 (exactly 3 edges with value 1)
; Requiring total = 4 makes it UNSAT.
(assert (= (+ e00 e01 e02 e10 e11 e12 e20 e21 e22) 4))

(check-sat)
