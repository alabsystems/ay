# ny-cert absent-callee CHC corpus

Four **production** CHC systems captured from `offline deductive checker check -p ny-cert` on the
deployed toolchain (`trust-recon` @ `21f1dfb1b4`, driver
`librustc_driver-ade33dacdb256b45.dylib sha256:ee0e22d35eba9261`, ay
`0.9.0+build.7625.886920d1d86a2667b`). They pin the two verdict classes that the
ny-cert panic-freedom frontier actually consists of.

## Why this corpus exists

An earlier round of the ny-cert campaign concluded that the dominant frontier
bucket ("ay-chc returned unknown: Inconclusive") was an **ay engine-capability
gap**, on the reported evidence that "z3/Spacer proves the same obligations SAFE
in 0.02-0.04s while ay returns unknown after 30s".

That is false, and this corpus is the counter-evidence. On these exact systems
**z3 and ay agree**, and what z3 answers in 0.02-0.04s is `unsat` — which under
the SMT-LIB HORN convention means *error is reachable*, i.e. **UNSAFE**, the
opposite of a safety proof. The 0.02-0.04s figure is z3's *refutation* time.

## The shape

Every one of these systems has `error` clauses whose constraint is the literal
`true`, and **no guarded error clause at all**:

```
clause action=none body=[p0(var:"bb0_v0_field0":BitVec(32))] constraint=bool:true head=p6()
```

(see `PROVENANCE_rat_is_negative.normalized-input.txt`, the producer's own
`ay.chc.normalized-input/v1` rendering of `rat_is_negative_absent_callee_unsafe.smt2`).

That clause is the lowering's `[trust-absent-callee-assumption]` may-panic
marker: "the body of callee X was not in the lowered bundle, so assume the call
may panic". Safety of the obligation therefore reduces entirely to *is the
marked basic block unreachable*. When it is reachable the Horn system is
unsatisfiable **by construction** and no engine can prove it — any engine answer
of SAFE on these files would be a false proof.

## Files

| file | ny-cert obligation | absent callee | verdict |
|---|---|---|---|
| `rat_is_negative_absent_callee_unsafe.smt2` | `vc:ny_cert__rational__Rat__is_negative:assertion:panic-freedom:0` | `ny_cert::rational::val` | UNSAFE (`unsat`) |
| `selfcheck_negated_coeffs_absent_callee_unsafe.smt2` | `vc:ny_cert__selfcheck__negated_coeffs:assertion:panic-freedom:0` | `<btree::map::Iter<..> as Iterator>::next` | UNSAFE (`unsat`) |
| `rational_val_safe.smt2` | `vc:ny_cert__rational__val:assertion:panic-freedom:0` | — | SAFE (`sat`) |
| `rational_val_closure_safe.smt2` | `vc:h0_ny_ucert__rational__val___x7bclosure_x230_x7d:assertion:panic-freedom:0` | — | SAFE (`sat`) |

The two SAFE files are the *only* two obligations out of 24 consecutive
full-verifier obligations in that ny-cert run that the production verifier
`proved` — and they are exactly the two that are satisfiable as Horn systems.
The correspondence over the 24 sampled obligations is 24/24 exact.

## Regenerating

```
MODEL_CHECKER_CONSUMER_DUMP_CHC=<out.txt> compiler_consumer --edition 2024 --crate-type lib \
  --crate-name ny_cert crates/ny-cert/src/lib.rs --cfg deductive_verify \
  -Z deductive-verify-output=json -Z trust-policy=advisory \
  -Z deductive-verify-profile=unix_hardened -Z deductive-verify-level=2 \
  -Z deductive-verify-session=probe
```

`MODEL_CHECKER_CONSUMER_DUMP_CHC` (model-checker-consumer-driver `native.rs`) appends one
`ay.chc.normalized-input/v1` block per obligation, in solve order, *before*
routing — so the dump is complete regardless of the solve budget. Obligation
`k` of the full-verifier stream is dump block `2k` (each obligation is prepared
twice, `request-0` and `request-1`, with identical content).

The `.smt2` files here are a mechanical HORN rendering of those blocks.
**Emit nullary predicates as bare `P6`, never `(P6)`** — the parenthesised form
makes z3 error out on exactly the two clauses that mention `error`, silently
drop them, and then answer `sat` in ~0.03s. That artefact is the most likely
origin of the "z3 proves these SAFE in 0.02-0.04s" claim this corpus refutes.
