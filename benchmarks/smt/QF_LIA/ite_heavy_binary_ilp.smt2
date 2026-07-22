; ITE-heavy binary ILP encoding (ASP-style)
; Models a simple graph coloring problem that is UNSAT
; 3 nodes, 2 colors, triangle graph -> UNSAT (need 3 colors for triangle)
;
; Uses ITE expressions to encode "if node i gets color c, then contribution is 1"
; This mimics the ASP->SMT encoding pattern from cmodelsdiff
(set-logic QF_LIA)

; Node-color assignment: c_ij = 1 means node i gets color j
(declare-fun c11 () Int) (declare-fun c12 () Int)
(declare-fun c21 () Int) (declare-fun c22 () Int)
(declare-fun c31 () Int) (declare-fun c32 () Int)

; Binary domains
(assert (and (<= 0 c11) (<= c11 1)))
(assert (and (<= 0 c12) (<= c12 1)))
(assert (and (<= 0 c21) (<= c21 1)))
(assert (and (<= 0 c22) (<= c22 1)))
(assert (and (<= 0 c31) (<= c31 1)))
(assert (and (<= 0 c32) (<= c32 1)))

; Each node gets exactly one color
(assert (= (+ c11 c12) 1))
(assert (= (+ c21 c22) 1))
(assert (= (+ c31 c32) 1))

; Auxiliary variables for ITE encoding of conflict detection
(declare-fun conflict12_1 () Int) ; conflict between node 1 and 2 on color 1
(declare-fun conflict12_2 () Int) ; conflict between node 1 and 2 on color 2
(declare-fun conflict13_1 () Int)
(declare-fun conflict13_2 () Int)
(declare-fun conflict23_1 () Int)
(declare-fun conflict23_2 () Int)

; Binary domains for conflict vars
(assert (and (<= 0 conflict12_1) (<= conflict12_1 1)))
(assert (and (<= 0 conflict12_2) (<= conflict12_2 1)))
(assert (and (<= 0 conflict13_1) (<= conflict13_1 1)))
(assert (and (<= 0 conflict13_2) (<= conflict13_2 1)))
(assert (and (<= 0 conflict23_1) (<= conflict23_1 1)))
(assert (and (<= 0 conflict23_2) (<= conflict23_2 1)))

; ITE encoding: conflict_ij_k = (ite (and (= c_ik 1) (= c_jk 1)) 1 0)
; Linearized: conflict_ij_k >= c_ik + c_jk - 1 and conflict_ij_k <= c_ik and conflict_ij_k <= c_jk
(assert (>= conflict12_1 (- (+ c11 c21) 1)))
(assert (<= conflict12_1 c11))
(assert (<= conflict12_1 c21))

(assert (>= conflict12_2 (- (+ c12 c22) 1)))
(assert (<= conflict12_2 c12))
(assert (<= conflict12_2 c22))

(assert (>= conflict13_1 (- (+ c11 c31) 1)))
(assert (<= conflict13_1 c11))
(assert (<= conflict13_1 c31))

(assert (>= conflict13_2 (- (+ c12 c32) 1)))
(assert (<= conflict13_2 c12))
(assert (<= conflict13_2 c32))

(assert (>= conflict23_1 (- (+ c21 c31) 1)))
(assert (<= conflict23_1 c21))
(assert (<= conflict23_1 c31))

(assert (>= conflict23_2 (- (+ c22 c32) 1)))
(assert (<= conflict23_2 c22))
(assert (<= conflict23_2 c32))

; Total conflict count via ITE-style aggregation
(declare-fun total_conflict () Int)
(assert (= total_conflict (+ conflict12_1 conflict12_2 conflict13_1 conflict13_2 conflict23_1 conflict23_2)))

; No conflicts allowed
(assert (= total_conflict 0))

(check-sat)
