; Minimal Hamiltonian circuit encoding on K4 minus two directed edges
; 4 nodes, edges encoded as 0/1 integer variables, MTZ subtour elimination
; Expected: SAT (circuit 0→2→3→1→0 avoids missing edges (0,3) and (3,0))
; Originally misclassified as UNSAT — Z3 confirms SAT.
(set-logic QF_LIA)

; Edge variables: x_ij = 1 if edge (i,j) is in the circuit, 0 otherwise
; Graph: complete graph K4 minus edge (0,3) and (3,0)
(declare-fun x01 () Int)
(declare-fun x02 () Int)
(declare-fun x10 () Int)
(declare-fun x12 () Int)
(declare-fun x13 () Int)
(declare-fun x20 () Int)
(declare-fun x21 () Int)
(declare-fun x23 () Int)
(declare-fun x31 () Int)
(declare-fun x32 () Int)

; Binary domain: 0 <= x_ij <= 1
(assert (and (<= 0 x01) (<= x01 1)))
(assert (and (<= 0 x02) (<= x02 1)))
(assert (and (<= 0 x10) (<= x10 1)))
(assert (and (<= 0 x12) (<= x12 1)))
(assert (and (<= 0 x13) (<= x13 1)))
(assert (and (<= 0 x20) (<= x20 1)))
(assert (and (<= 0 x21) (<= x21 1)))
(assert (and (<= 0 x23) (<= x23 1)))
(assert (and (<= 0 x31) (<= x31 1)))
(assert (and (<= 0 x32) (<= x32 1)))

; Out-degree = 1 for each node
(assert (= (+ x01 x02) 1))           ; node 0 out-degree (no edge to 3)
(assert (= (+ x10 x12 x13) 1))       ; node 1 out-degree
(assert (= (+ x20 x21 x23) 1))       ; node 2 out-degree
(assert (= (+ x31 x32) 1))           ; node 3 out-degree (no edge to 0)

; In-degree = 1 for each node
(assert (= (+ x10 x20) 1))           ; node 0 in-degree (no edge from 3)
(assert (= (+ x01 x21 x31) 1))       ; node 1 in-degree
(assert (= (+ x02 x12 x32) 1))       ; node 2 in-degree
(assert (= (+ x13 x23) 1))           ; node 3 in-degree (no edge from 0)

; Subtour elimination (MTZ formulation): position variables
(declare-fun p1 () Int)
(declare-fun p2 () Int)
(declare-fun p3 () Int)

; Position bounds: 1 <= p_i <= 3
(assert (and (<= 1 p1) (<= p1 3)))
(assert (and (<= 1 p2) (<= p2 3)))
(assert (and (<= 1 p3) (<= p3 3)))

; MTZ constraints: if x_ij = 1 then p_j >= p_i + 1
; Encoded as: p_j - p_i + 3*x_ij <= 3  (for edges from non-0 nodes)
; Standard: p_j >= p_i + 1 - n*(1 - x_ij) => p_j - p_i + n*x_ij >= 1 + n - n = 1
; Equivalently: p_i - p_j + n*x_ij <= n - 1

; For edges from node 0 (position 0):
; if x01 = 1 then p1 >= 1 (always true by bounds)
; if x02 = 1 then p2 >= 1 (always true by bounds)

; For edges between non-zero nodes:
; x12: p2 >= p1 + 1 - 3*(1-x12) => p2 - p1 + 3*x12 >= -2 AND p1 - p2 + 3*x12 <= 2
(assert (<= (+ (- p1 p2) (* 3 x12)) 2))
; x13: p3 >= p1 + 1 - 3*(1-x13)
(assert (<= (+ (- p1 p3) (* 3 x13)) 2))
; x21: p1 >= p2 + 1 - 3*(1-x21)
(assert (<= (+ (- p2 p1) (* 3 x21)) 2))
; x23: p3 >= p2 + 1 - 3*(1-x23)
(assert (<= (+ (- p2 p3) (* 3 x23)) 2))
; x31: p1 >= p3 + 1 - 3*(1-x31)
(assert (<= (+ (- p3 p1) (* 3 x31)) 2))
; x32: p2 >= p3 + 1 - 3*(1-x32)
(assert (<= (+ (- p3 p2) (* 3 x32)) 2))

(check-sat)
