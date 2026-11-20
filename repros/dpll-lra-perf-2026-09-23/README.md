# ay-dpll on the CHC campaign's Real (QF_LRA / QF_LIRA) query corpus — 2026-09-23

Two things are pinned here, both extracted from AY's own CHC engines on CHC-COMP 2026 LRA-Lin instances
(`benchmarks/chc/chc-comp26-benchmarks/sally-chc-benchmarks`, `…/cav12-benchmarks`); the SMT-LIB text is
exactly what the engines hand to `ay_dpll::Executor` (competition posture, fresh executor per query).

## 1. `bmc_kstar/` — one BMC depth-k\* check per instance (11 scripts)

`<instance>_k<k*>.smt2` is `BmcSolver::ts_incremental_script_segments_for_test` for the instance's
transition system at its shortest counterexample depth k\* (init + trans@0..k\*-1 + query@k\*, a
single `check-sat`, expected `sat`). k\* comes from a z3 scan of AY's unrollings
(the development design notes at `9598c4206`, §1). These are the queries where LRA_BMC §2 B8
found that "one fresh depth-k\* check does not finish in 60 s on AY while z3 needs 0.2–2 s" (approx_hybrid.6.c,
scenario2 ×3, scenario3 at k\*=1; the two tte_synchro clock-distance systems at k\*=6) plus the three om1/tte
queries AY does decide (5–19 s) and s3_clnt_2 at k\*=8.

## 2. `imc_om1/` — IMC interpolation queries on oral_messages (16 scripts + metadata)

`<instance>__imc_k<k>.smt2` (k = 3, 4) is the k-step IMC check on eight oral_messages instances, the
A-D0 wall of the development design notes at `9598c4206` ("om1 k=3–4 unrollings take ay-dpll 6–>20 s vs z3 0.03–0.5 s").
The sibling `.json` records the source instance, `k`, the assertion group sizes, the interpolation
partition masks and the shared-variable frontier between partitions, so the same query can be re-emitted
as a proof/interpolant request.

## 3. The invalid-model defect (fixed on this branch)

`om1_with_relays_agreement_two_faults_000_k3.smt2` (also the LRA_BMC §2 B6 repro): under host load about
one fresh run in three answered `unknown` after `c !! MODEL-UNCONFIRMED … model validation violated`
(the ITE-heavy transition disjunction, whose ITE conditions are Real equalities). Mechanism: an equality
atom assigned false is a disequality; the LRA final check accepts the assignment but the extracted model
may sit exactly on the excluded value, validation fails, and the #9604 recovery re-solves the assignment's
theory atoms — but it re-solved them WITHOUT the assignment's Bool-sorted constants, so the recovered model
had those leaves at a completion default, failed validation again, and the nested recovery failed closed.
The fix pins the Bool constants in the recovery conjunction
(`Executor::lra_recover_assignment_verdict(.., bool_pins)`); regression test
`executor::theories::lra::tests::recovery_bool_pins`. Which split-loop iteration publishes depends on
wall-clock iteration budgets, which is why the symptom was load-dependent (8 quiet runs identical: sat in
5.2 s, 6927 conflicts).

## 4. Measuring

```
ay --competition --timeout 60000 <query>.smt2      # AY, as the CHC lanes run it
z3 -T:60 <query>.smt2
```
The leased baseline/candidate tables were recorded in the development design notes at `9598c4206`.
