# `deductive_checks_seq_length_frame` — provenance

These `.smt2` files are **byte-exact captures**, not reconstructions.

They were dumped from `Solver::to_smtlib2()` at deductive-checks's shared
`try_check_sat_with_details` boundary while its whole `vec_pop_capability`
capability suite ran (18 capability tests, 284 solver calls, 80 distinct query
texts). Every file here is UNEDITED. The ten `a032_*` files are the `Seq`
length-frame class of that capture; the two `a005_i2b_*` files are the
SATISFIABLE members of the same class (`5 <= len` asked of a length-1 frame),
carried as the no-over-acceptance twins.

What the class is, in deductive-checks terms: a `Vec` built by three `push`es, whose
element model is an `__seq_shifted` array related to the constructor carrier by
a `select`-triggered `forall` over a three-deep `store` chain whose store
indices are `((_ int2bv 64) len)` of an **Int** length variable; the goal is the
`Seq` precondition `1 <= len`, negated.

Posture, which is the part ay's own corpus does not otherwise carry:

* `(set-option :produce-unsat-cores true)` — 284/284 of the production calls;
* every assertion wrapped `(! t :named dnN)` — 284/284;
* an `(Array (_ BitVec 32|64) (_ BitVec 32))` carrier that is `select`ed from —
  284/284, and `(Array Int …)` in 0/284;
* literal-constant NAMED assertions `(! true :named dnN)`, and in the
  `*-false-sos` files a terminating `(! false :named dnN)`;
* **no** `:produce-proofs` and **no** self-check — deductive-checks requests neither,
  yet a checked certificate is still mandatory before ay may publish `unsat`.
  That combination is what makes a diagnostic option verdict-bearing here.

Names are kept as captured (`a<assertion-count>_<feature-tag>_<hash>`) so they
can be cross-referenced against the full 80-query capture.

## One thing the dump does NOT carry

`Solver::to_smtlib2()` serialises the option set above but **not the timeout**.
deductive-checks runs every one of these queries under
`Solver::set_timeout(DEFAULT_SOLVER_NOMINAL_TIMEOUT_MS = 30_000)`
(deductive-checks-core `encoder/mod.rs` `with_limits`; constant at
`encoder/verification/timeout.rs`). A bare replay of these files therefore does
*not* reproduce production: with no deadline installed the solve runs under ay's
300 s `DEFAULT_SAFETY_DEADLINE`, which is **more** permissive than production,
and the `:produce-unsat-cores` deletion scan spends a large wall-clock shrink
budget on a query it has already decided.

`deductive_checks_seq_length_frame_withholding.rs` re-installs that wall in its `solve()`
helper by prepending `(set-option :timeout 30000)` — which ay routes through the
same mechanism as `set_timeout` — so the files here stay byte-exact captures and
the replay stays in deductive-checks's posture. Do not bake the option into these files.
