; WARNING: NOT oracle-equivalent for external solvers (e.g. z3).
; The following sorts are native DATATYPE sorts whose constructor/
; selector/tester semantics are NOT captured by this script; they are
; declared below as uninterpreted sorts, so this script is a UF
; over-abstraction of the original query: `unsat` here implies the
; original is unsat, but `sat` here is INCONCLUSIVE.
;   datatype sort: Thing
(set-option :produce-unsat-cores true)
(set-logic ALL)
(declare-sort Poly 0)
(declare-sort Thing 0)
(declare-fun is-Thing_Thing (Thing) Bool)
(declare-const z (_ BitVec 32))
(declare-fun Thing_Thing (Poly) Thing)
(declare-fun Thing_Thing_a (Thing) Poly)
(declare-const y (_ BitVec 32))
(declare-const x (_ BitVec 32))
(assert (! (bvult x #x00000fff) :named dn0))
(assert (! (= (bvadd (bvmul x x) x) (bvmul x (bvadd x #x00000001))) :named dn1))
(assert (! (= (bvmul (bvmul x y) z) (bvmul (bvmul y x) z)) :named dn2))
(assert (! (or (not (bvult x #x00000fff)) (bvult (bvand x y) #x00000fff)) :named dn3))
(assert (! (not (= ((_ extract 63 32) (bvmul ((_ zero_extend 32) x) ((_ zero_extend 32) x))) #x00000000)) :named dn4))
(check-sat)
