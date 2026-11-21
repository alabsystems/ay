; AY-SMT-3, second cause: ay answered `unknown` where the formula is sat.
; Fix on branch fix/smt-incremental-20261119 (gate fixpoint for a self-referential
; array definition), expected to answer sat, pending measurement; test
; gate_confirms_sat_on_a_self_referential_nested_store_definition.
; The model gate reports "model does not pin this leaf: d : Array(Int, Array(Int, Int))":
; `d` is defined only through a store chain that reads `d` itself, so the
; gate's definition index cuts the cycle and the solver's model does not
; publish `d`. Reduced (by assertion delta-debugging, then by hand) from check-sat
; number 10 of SMT-COMP 2026 incremental QF_AUFLIA/2721719d; yices2 answers sat.
; Of the 31 `unknown` answers ay gave there in its first 30 s, 26 carry this
; reason and 5 "model value shape Uninterpreted does not inhabit the declared sort".
(set-logic QF_AUFLIA)
(declare-fun c () (Array Int (Array Int Int)))
(declare-fun d () (Array Int (Array Int Int)))
(declare-fun i () Int)
(declare-fun j () Int)
(assert (= (store c i (store (select c i) j (select (select d i) j))) d))
(check-sat)
