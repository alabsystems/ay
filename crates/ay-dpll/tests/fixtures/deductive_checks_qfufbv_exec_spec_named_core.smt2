; WARNING: NOT oracle-equivalent for external solvers (e.g. z3).
; The following sorts are native DATATYPE sorts whose constructor/
; selector/tester semantics are NOT captured by this script; they are
; declared below as uninterpreted sorts, so this script is a UF
; over-abstraction of the original query: `unsat` here implies the
; original is unsat, but `sat` here is INCONCLUSIVE.
;   datatype sort: ExecSpecVerifiedA
(set-option :produce-unsat-cores true)
(set-logic ALL)
(declare-sort ExecSpecVerifiedA 0)
(declare-const result (_ BitVec 32))
(declare-const x (_ BitVec 32))
(declare-fun ExecSpecVerifiedA_ExecSpecVerifiedA_a (ExecSpecVerifiedA) (_ BitVec 32))
(declare-fun ExecSpecVerifiedA_ExecSpecVerifiedA_b (ExecSpecVerifiedA) (_ BitVec 32))
(declare-const __deductive_checks_spec_exec_spec_verified_square_bounded_x (_ BitVec 32))
(declare-fun ExecSpecVerifiedA_ExecSpecVerifiedA ((_ BitVec 32) (_ BitVec 32)) ExecSpecVerifiedA)
(declare-fun is-ExecSpecVerifiedA_ExecSpecVerifiedA (ExecSpecVerifiedA) Bool)
(declare-fun exec_spec_verified_square_bounded ((_ BitVec 32)) (_ BitVec 32))
(assert (! (bvule x #x0000ffff) :named dn0))
(assert (! (= result (bvmul x x)) :named dn1))
(assert (! true :named dn2))
(assert (! true :named dn3))
(assert (! (not (= ((_ extract 63 32) (bvmul ((_ zero_extend 32) x) ((_ zero_extend 32) x))) #x00000000)) :named dn4))
(check-sat)
