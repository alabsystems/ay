# Scope and limitations

AY is a 0.x solver workspace. Support and evidence are specific to a logic,
entry point, proof format, and checker; the presence of a parser or API does not
by itself mean that the full theory combination is complete or certified.

- `sat`, `unsat`, and optimization answers are certified only when the selected
  mode emits a documented artifact and that artifact passes its named,
  designated checker. The trust boundary differs by path: some checkers are
  external tools, while native APIs also expose solver-state-independent
  in-tree verifiers. Other answers are solver results, not proof claims.
- AY's built-in DIMACS checker fails closed when it rejects a DRAT/LRAT/PR-SR
  proof, but warns and preserves the verdict when checking cannot run. SMT
  `--self-check` is the fail-closed path for AY's internal proof objects: UNSAT
  requires a strict semantic proof check and binds every reachable assumption
  to the active problem. Independent Alethe and VeriPB replay remains a separate
  certification step.
- `unknown` is an expected sound outcome for unsupported or incomplete paths.
  Callers must not reinterpret it as `sat` or `unsat`.
- `verification/lean` is the maintained Lean project named by the public proof
  claims. The public snapshot excludes admitted research modules and private
  proof-factory routing, private deductive-checker harnesses, and orchestration;
  retained proof fixtures and artifacts are not broader verification claims
  unless they identify a completed theorem and a reproducible checker invocation.
- The public workspace omits development-only code-generation integrations and
  unwired prototype crates. Their absence is deliberate; supported fallback
  solver paths remain in the exported crates and are checked under all public
  features.
- The Python incremental `arrays` and `arr_lia` fragments remain experimental
  and often return `unknown`; their bounded differential tests require zero
  verdict disagreements. `Solver` and `Optimize` fail closed with `unknown` on
  quantified-array formulas, and Python `IsSubset` deliberately raises
  `NotImplementedError`, because that FFI path is not soundly supported.
- Historical wrong-answer inputs remain in the SMT regression corpus and must
  be replayed against a reference solver before an affected logic is described
  as release-ready.
- Performance and coverage numbers are meaningful only with the exact commit,
  binary provenance, corpus, timeout, enforced memory envelope, proof mode,
  checker verdicts, and wrong/invalid counts supplied alongside them.
- Benchmark deficits are roadmap inputs, not reasons to narrow the promised
  Z3-compatibility surface or the specialist-performance target.

The release bar is zero known wrong answers and zero invalid certificates on the
advertised surface. No current public aggregate evidence packet demonstrates
that bar across the advertised surface. Treat each claim only at the granularity
of its named test or checker, and treat unlisted theory combinations and bindings
as experimental.

These are present-state limits, not a narrowing of the project goal. AY is being
built to become a universal Z3 replacement and to outperform mature specialist
solvers in their domains; each step toward that goal must earn its claim with
reproducible results and independently checked evidence.

## Known limitations (0.1.0)

- **Quantified search remains incomplete; public SAT publication fails closed
  unless a complete checked evidence lane succeeds.** Runtime-checked recovery
  was implemented 2026-08-01 for the restricted quantified-UFBV projection
  fragment; guarded external remeasurement is still pending. The 2026-07-31
  emergency closure remains in force elsewhere: syntactic
  UF-completion and QuantifierConsumer/sequence shapes are not SAT certificates, and a
  quantified assertion that model validation defers or cannot check converts
  `sat` to `unknown` in default mode as well as `--self-check`. Model-less
  quantified SAT, incomplete E-matching, finite-domain certificates, and
  non-conjunctive CEGQI refinement likewise fail closed unless they carry their
  specific semantic evidence.

  The production recovery accepts only a caller-authored, plain hard
  `check-sat`. An untrusted projection candidate must pass the unsafe-free,
  solver-independent implication checker and an independent positive source
  binding. The source layer uses allocation-stable `DeclarationId`s, a closed
  `DeclarationKind`, and a context-identity/revision stamp; only an exact live
  primary `Uninterpreted` declaration is eligible. The query layer uses a fresh
  pointer-identity epoch and an ordered inventory of roots, assumptions,
  objectives, parsed/native soft constraints, scope depth, and term count. Its
  non-`Clone` permit is captured and consumed inside one borrow-bound exclusive
  `Executor` transaction, so generic, assumption, optimization, internal, or
  stale query origins cannot acquire it.

  Accepted semantic, source, and query evidence is sealed and non-`Clone`. The
  emission boundary installs the exact total selector functions, boundedly
  completes only proof-neutral output values, rechecks the frozen graph,
  declaration identities/kinds/signatures, source and query epochs, and final
  projection map, then mints a private one-shot SAT certificate. Assertion/model
  evaluation, the independent model view, `get-value`, `get-model` rendering,
  and round-trip checking all consume the same exact symbol/signature/projection
  map. Unsupported shapes, signature conflicts, stale evidence, and resource
  stops decline to the ordinary sound fallback or `unknown`.

  The checked output-completion lane keeps the cached solve result revoked; it
  does not install even a provisional `Sat` while completing the model. Only
  the final currentness/model checks can publish cached `Sat` and mint the
  certificate. An interrupt, deadline, or memory stop clears the incomplete
  model, validation bit, and certificate and explicitly caches `Unknown`, so a
  later model/API read cannot revive a stopped solve as SAT.

  The sole full-family campaign is the checked-in guarded external harness
  `scripts/ufbv_fixpoint_audit.py`. It pins the exact 121-file family to
  canonical manifest SHA-256
  `ef9912b78e493410189a3bfa733987a873a1e7ca5d36a529f42426f312391dd9`
  (sorted basename, NUL, raw bytes, NUL) and requires the exact 26/74/21 declared
  status distribution. It launches 121 fresh default processes and 121 fresh
  `--self-check` processes, with `-st` enabled in both lanes. The closure gate
  exits nonzero unless **both** lanes return `sat` on all 26 declared-SAT cases
  and every one of those 52 SAT runs exposes exactly one canonical statistics
  block with `model_validation.checked_projection_certificate=1`. It also
  requires neither lane to return `sat` on any of the 74 declared-UNSAT or 21
  declared-unknown cases, both lanes to have zero wrong and zero invalid
  results, and the fresh self-check lane to reproduce every decisive default
  result. Self-check is reproducibility/check-policy evidence from another AY
  process, not independent corroboration or external proof replay.

  The campaign is serial under the `_oom_guard.py` host lease and planned
  per-child envelope. It passes `ay --memory`, `MEMLIMIT`, and `NBCORE`, wraps
  each process group in the zero-grace RSS watchdog, supplies a sanitized
  non-inherited environment, waits for build quiescence, and cancels/discards a
  child if its continuous build monitor sees Cargo/Targo/rustc/compiler_consumer. Its JSON
  binds the clean source HEAD, binary identity/SHA-256 and self-attested commit,
  corpus manifest and per-file hashes, harness and OOM-guard hashes, timeouts,
  resource plan, proof/checker modes, raw verdict evidence, and resumable
  byte-identical checkpoint provenance. Run it only against the final aligned
  binary:

  ```sh
  python3 scripts/ufbv_fixpoint_audit.py OUT.json
  ```

  A stored v3 report is not trusted from its summary fields. Reverify its
  integrity, raw records, statistics evidence, corpus/harness/OOM-guard binding,
  recomputed closure, and measured source identity with:

  ```sh
  python3 scripts/ufbv_fixpoint_audit.py \
    --verify-report REPORT --expect-head SHA
  ```

  Verification requires the exact measured executable at its recorded path or
  a byte-identical relocated copy supplied with `--binary`; it rechecks size and
  SHA-256 and re-runs only `ay --version` under the recorded sanitized
  environment. The report checksum and replay establish structural consistency,
  not execution authenticity: the workspace and resumable checkpoint are
  trusted-local inputs, `--expect-head` is a historical assertion, and pathname
  rechecks narrow but cannot eliminate adversarial filesystem races.

  The former environment-gated, effectively skipped in-process Rust campaign
  was removed: without its environment switch it counted as a passing test
  while doing no work, and its cooperative in-process limits were not an
  enforceable child RSS boundary. Always-on compact rotation checks and typed
  source/query/evidence, model-consumer, stop-cleanup, and end-to-end regressions
  remain in `cargo test`; full-corpus evidence comes only from the guarded
  external harness.

  The current Clean/Trust campaign discharges 264/264 obligations in an
  abstract semantic model and rejects 43/43 adversarial red cases. This is
  design evidence only. There is no proved refinement from the live Rust/MIR to
  that model and no hash-bound source/compiler/proof manifest, so the production
  lane is runtime checked and source-conformance tested, **not formally
  verified**.

  **POST-IMPLEMENTATION EXTERNAL MEASUREMENT: not yet recorded.** Do not fill in
  final counts, binary hashes, proof/checker verdicts, or performance deltas
  until the aligned release binary has completed the guarded 121-file sweep.

  **HISTORICAL BASELINE MEASURED 2026-07-31: 0 wrong answers in the exact
  121-file family.** This binary predates the production projection recovery.
  Default mode, 15 seconds per file, serial, guarded by `scripts/_oom_guard.py`;
  binary SHA-256 `e5c547f732b2a617fd13d0a839fb7424e3fb1fb9ed0a300e0ff99aacbe01eddc`;
  corpus family SHA-256
  `ef9912b78e493410189a3bfa733987a873a1e7ca5d36a529f42426f312391dd9`.
  Evidence:
  [the development design notes](the development design notes)
  and [raw JSON](the development design notes).

  | declared → AY | count |
  | --- | ---: |
  | `unsat` → `unsat` | 66 |
  | `unsat` → `unknown` / timeout | 2 / 6 |
  | `sat` → `unknown` | 26 |
  | `unknown` → `unknown` / timeout | 16 / 5 |
  | **known wrong polarity** | **0** |

  In that historical run, all 26 declared-SAT files returned `unknown` and 34
  files with known status were unresolved. Default Alethe synthesis was enabled,
  but no proof checker was run, so invalid proof count was unmeasured and the 66
  UNSAT results were not independent certificate claims. The older UFNIRA
  wrong-`sat` family was not re-measured; broader quantified fragments remain
  experimental. Do not generalize either the historical baseline or the
  restricted new certificate lane into a full-Z3-replacement claim.

  **Historical record below (superseded for current behavior).** It preserves the
  2026-07-26/29 diagnosis, rejected blanket-fix measurement, and partial-fix
  trail. Statements that the UFBV family is open or has two remaining wrong
  files describe those historical builds, not the 2026-07-31 closure or the
  2026-08-01 runtime-checked implementation.

  **HISTORICAL 2026-07-29 — the class was smaller, still OPEN, and its
  membership has fully turned over.** Full family sweep, all 121 UFBV
  `wintersteiger fmsd13 fixpoint` files, 15s, `ay 0.5.0+build.6235` @ `de03e266`,
  default mode. Evidence and reproduction:
  [the development design notes](the development design notes).

  | | `2068d68d` | HEAD `de03e266` | after the multi-point probe fix |
  | --- | --- | --- | --- |
  | correct decisions | 39 | 89 | **93** |
  | wrong `sat` | 26 | 6 | **2** |
  | sound `unknown` | — | 5 | 5 |
  | unverifiable (`:status unknown` → `sat`) | — | 12 | 12 |

  **ROOT CAUSE FOUND, and the class is now down to 2 files — but not to zero.**
  The granting authority is the STRICT UF-completion certificate:
  `quantifiers_supported_by_uf_completion` (`quantifier_loop/mod.rs:746`) carries
  **no coverage term**, so zero instantiations cannot block it, while its sibling
  `..._given_sat` leg IS gated on `!has_uninstantiated && !reached_limit`
  (`mod.rs:937`). Only one leg got the discipline. `premise_forced_binder_refutation`
  now samples up to 8 distinct premise models instead of 1 (sound by construction —
  it can only ever return `unsat`), which fixes 4 of the 6 and costs no correct
  `sat`s. `sdlx-fixpoint-4/5` remain wrong: more sampling does not reach them.

  Closing the last 2 needs the coverage premise on the strict leg, which is NOT
  free: 24 in-tree tests assert a quantified `sat` STRICTLY off the same `deferred`
  channel (13 in `auflia_verification_consumer_9185_reducers.rs` alone), and the decisive
  satisfiable case `∀s. 0 ≤ seq_len(s)` is **statistically identical** to the wrong
  answers at that gate — same `deferred`, same zero instances. The separating
  evidence has to be constructed (a materialized completion, re-checked), not read
  off an existing flag. A 4-line minimal witness is checked in and RED at
  `group_quantifiers/ufbv_strict_uf_completion_coverage.rs`.

  **The 6 wrong files share no members with the 7 named at `2068d68d`.** All 7 of
  those are now correct; 6 different files are wrong. Progress on this class has
  been instance-shaped, not mechanism-shaped — which is evidence for the
  saturation-signal route below and against repairing benchmarks one at a time. It
  also means a green in-tree fixture never establishes that this class is closed;
  only a family sweep does.

  What the reproduction shows: AY grants `sat` with `:conflicts 0 :decisions 0
  :ematching-instances-created 0` against an EMPTY model, in 5 ms — it never
  instantiates the single quantifier at all. `ay bisect` reports the bug survives
  with every known flag disabled, so the cause is in the core quantifier result
  mapping. The granting authority is **not yet identified**; the report records
  which candidate is already ruled out, so that work is not repeated.

  **All remaining numbers in this entry are the `2068d68d` reading** and are kept
  for comparison only. Do not quote them as current.

  **Measured at `2068d68d` (0.4.0+build.5825, 2026-07-26).** Re-running
  the 13 scoreboard disagreements per-file found **8 still wrong**: 7 wrong `sat`
  in UFBV (`sdlx-fixpoint-1`, `small-dyn-partition-fixpoint-3/4/10`,
  `small-synabs-fixpoint-2/3/9`) and 1 wrong `unsat` in AUFLIA (next entry). The
  other 5 UFBV files now return sound `unknown`. Sweeping the whole affected
  family — 121 UFBV `wintersteiger fmsd13 fixpoint` files at 10s — found **26
  wrong `sat`s**, so the 50-per-division sample under-counts this class by ~4x.

  **The class is not one benchmark family, and the corpus-wide count is not 13.**
  A full sweep of the UFNIRA division (266 files) found **8 further wrong `sat`s**
  — all in `20240414-funcprobs`, a family the scoreboard sample recorded ZERO
  disagreements for. z3 4.15.4 independently confirms `unsat` on
  `problem_U25_sol2`; the rest carry declared `:status unsat` and z3 times out at
  20s. All 8 degrade to `unknown` under `--self-check`, i.e. same mechanism.
  Running total at `2068d68d`: **~34 wrong answers in roughly 690 files examined**,
  every one a wrong `sat` in this single class. No wrong `unsat` remains among
  them since the AUFLIA fix below. Treat 13 as a floor set by sampling, not as
  the count.

  **CURRENCY, re-measured 2026-08-02 at `608020b1ad` (build.6432) — the UFNIRA
  half of this class is STILL LIVE, ~600 commits later.** The first 40 UFNIRA
  files swept produced a confirmed wrong answer:
  `20240414-funcprobs__check__problem_U25_sol2.smt2`, declared `:status unsat`,
  z3 4.16.0 `unsat`, **AY `sat`** — the same file named above, unfixed. So the
  UFBV progress recorded in this entry (26 → 2) did NOT generalize: the repairs
  were UFBV-local while the shared mechanism kept its other divisions. Do not
  read the UFBV row as the class's health.

  That measurement was only possible because `scripts/soundness_sweep.py` was
  repaired the same day (`02af05b9f0`): it had been pointed at
  `benchmarks/smtlib-2025/non-incremental`, which holds ONE division (QF_SLIA),
  so the tool written to sweep this class could not reach a single file of it.
  Treat every "CLEAN" this script printed before that commit as covering 1/84 of
  the corpus.

  At that pre-gate checkout, `--self-check` degraded all of them to `unknown`,
  while default mode did not. The current universal boundary applies that
  fail-closed result in both modes. **Read the historical capability result
  carefully: on this family `--self-check` answered `unknown` on 121 of 121 files
  — including the 22 correct `unsat`s and 17 correct `sat`s that default mode
  gets right.** Its zero-wrong-answer property here is obtained by deciding
  nothing, so it is evidence of soundness, not of capability, and it is not a
  usable default for this fragment. (`--self-check` is *not* vacuous in general:
  it decides quantifier-free problems and simple quantified ones — measured on
  trivial QF_LIA sat/unsat, QF_UF unsat, and `∀s. 0 ≤ g(s)` — and degrades on
  quantified `unsat` where it cannot produce a checkable refutation.)
  The two older in-tree fixtures are both answered soundly now and neither
  reproduces the class: `ufbv_wintersteiger_fixpoint_deferred_wrong_sat.smt2`
  (`AR-fixpoint-5`) was then decided correctly `unsat`, and
  `ufbv_small_synabs_fixpoint_2_wrong_sat.smt2` (picked on 2026-07-26 *because* it
  was then a live wrong `sat`) went sound after the rebase. The final historical
  reproduction was `ufbv_small_pipeline_fixpoint_1_wrong_sat.smt2` — 17 lines,
  7.5 KB, wrong
  in 5 ms, with ground truth confirmed three ways (its own `:status`, z3 4.15.4 in
  11 ms, and a hand refutation at `dataIn_64_0 = c1_64_0 = 1`). All three are
  guarded by
  `crates/ay-dpll/tests/group_quantifiers/ufbv_deferred_default_mode_wrong_sat.rs`,
  where `ufbv_small_pipeline_fixpoint_1_never_default_sat` is now a green guard
  for the mandatory publication boundary.

  **A blanket fix was implemented, measured, and initially REJECTED.** Removing the
  `self_check` condition so the deferred channel fails closed in every mode does
  eliminate the wrong answers (26 → 0 on the family), but it costs far more than
  it buys:
  - all 17 correct `sat`s in that family are lost to `unknown` (correct decisions
    39 → 22), and
  - 22 other tests break, 21 of them in `group_auflia`'s `verification_consumer` verification-
    condition suite. The decisive case is `∀s. 0 ≤ seq_len(s)`, which is
    obviously satisfiable (`seq_len ≡ 0`) and which the blanket gate answers
    `unknown`. Any quantified problem with an axiomatized function — i.e. most
    verification workloads — stops being decidable by AY.
  At that point the completeness cost caused the change to be reverted. The
  current correctness-first boundary deliberately accepts that visible
  `unknown` cost; restoring capability now requires affirmative evidence rather
  than publishing an unchecked candidate.

  **CORRECTED 2026-07-26 — the root defect is deeper than the model gate.**
  Pinning a function to a concrete interpretation only restricts, so if
  `assertions ∧ (f ≡ c)` is satisfiable the original is satisfiable: a successful
  pin is a sound SAT certificate. Applying that test to
  `small-synabs-fixpoint-2` with **all 8 arity>0 functions pinned to `#b000000`**
  — leaving no interpretation to complete at all — z3 answered `unsat` in 60s
  while AY's underlying procedure answered `sat`. So this class was not merely
  model incompleteness: the quantified-BV search proposed `sat` for an
  unsatisfiable formula. The current independent boundary withholds that
  unconfirmed proposal in every mode.

  This also rules out the obvious repair: a completion-based confirm would ask
  AY's own solver whether `assertions ∧ (f ≡ c)` is satisfiable, get the same wrong
  `sat`, and *confirm* it — turning a default-mode-only error into a `--self-check`
  error too. Confirmation for this fragment must come from a procedure independent
  of the one under test (full bit-blasting with quantifier expansion, or an
  external checker).

  **Narrowed to ONE assertion.** Delta-debugging the pinned variant removed all 8
  pins, leaving a core of exactly one assertion: the benchmark's own single
  `(assert (forall …))` over 12 BitVec-6 binders. So this is not an interaction,
  combination, or gate bug — **the historical AY search answered `sat` on a
  single unsatisfiable universally-quantified BV assertion**, whose negation is valid and for which z3
  finds a falsifying instantiation in 60s. Minimal synthetic analogues (1/3/12
  BV-6 binders with a pinned function and a premise chain) do not reproduce it, so
  the body's structure still matters.

  **The route is a saturation/completeness signal**, not model completion: emit a
  quantified `sat` only when the instantiation loop actually closed, and `unknown`
  when it ran out of candidates, budget, or applicable triggers. That is sound by
  construction, needs no synthesis, and costs only the `sat`s that were never
  justified — unlike the blanket gate, which also destroyed the justified ones. As
  a parity follow-on, instantiation completeness would turn these into correct
  `unsat` rather than `unknown`.

  (Model completion remains the right idea for the *`verification_consumer` axiom-whitelist*
  lane in `quantifier_loop/model_completion.rs`, which is a different problem:
  generalizing fourteen hand-matched QuantifierConsumer `(Seq Int)` shapes into real synthesis.)

  Reproduce the corpus set with
  `ay-z3-parity fetch <dir> --divisions UFBV,AUFLIA`.
- **FIXED 2026-07-26: a wrong REFUTATION in quantified AUFLIA.** AY answered
  `unsat` on satisfiable quantified AUFLIA — the most dangerous verdict, because
  it silently discharges an obligation that is in fact satisfiable and no consumer
  can detect it. The corpus instance was `AUFLIA 20170829-Rodin
  smt4579745768945200905` (z3 4.15.4 and its own `(set-info :status sat)` agree).

  **Root cause: E-matching instantiated a bare `Exists` and conjoined the
  instance.** Universal instantiation is sound (`∀x.P(x) ⊨ P(t)`); existential
  instantiation is not (`∃x.P(x) ⊭ P(t)` — it pins an arbitrary term as the
  witness). The E-matching loop destructured both quantifier forms as
  instantiation targets, and every caller appends the instances to
  `ctx.assertions` as top-level CONJUNCTS. The chain: instantiating the outer
  guarded universal pushes the instantiated BICONDITIONAL to top level; the
  collector's `App` arm then descends through the `=` (it tracks no polarity) and
  reaches the `exists` inside it; that existential — a subformula whose truth
  value is not established — was instantiated at `j := sk`, asserting
  `(and true (tab e0 sk))` as FACT, contradicting the soundly-derived
  `(not (tab e0 sk))` from the negated-existential goal. Hence `unsat` with
  `:conflicts 0 :decisions 0`: no search, just an unsound instance plus unit
  propagation. Negatively-occurring existentials are unaffected — the `Not` arm
  already converts `¬∃x. φ` to its sound NNF dual `∀x. ¬φ`.

  Fix (`832c8861ba`): `perform_ematching_with_generations` refuses to
  destructure an `Exists` as an instantiation target.

  **Fix it at that site and nowhere else.** Cutting the existential earlier, in
  `ematching::collect_quantifiers`, looks equivalent and is not: it converts this
  wrong `unsat` into a potential wrong `sat`. The skipped quantifier is supposed
  to keep flowing through the collector so that it lands in
  `uninstantiated_quantifiers` — one of the conjuncts blocking the
  `full_ematching_coverage` SAT certificate — and so that it still feeds
  `ematching_has_exists` and the `setup_cegqi_for_unhandled` routing. Silenced at
  the collector, a positive-position existential becomes *invisible* rather than
  *unhandled*, and the ground solve's `sat` can be returned as authoritative with
  the existential never discharged. Both halves are pinned by
  `ematching::tests::exists_is_surfaced_but_never_instantiated`.

  Guards (the fix commit shipped none; these are the executable statement of it):
  `crates/ay-dpll/tests/group_regression/false_unsat_auflia_exists_eq.rs` (with a
  license-clean fixture re-authored from the delta-debugged 4-assertion core; the
  CC BY-NC corpus file is not vendored), `…/false_unsat_auflia_rodin.rs` (runs the
  real corpus benchmark, skips unless it has been fetched), and the
  surfaced-but-never-instantiated invariant above.
- **`(mod (to_int r) k)` over a Real variable with a negative floor returns
  `unknown`.** In QF_LIRA, an Int-side `mod`/`div` whose dividend is `(to_int r)`
  for a Real variable `r` that floors to a negative integer is not decided: the
  LIA/LRA fixpoint converges but the combination does not close the branch, so
  AY answers `unknown` rather than `sat`. (Positive floors are decided, as are
  the same shapes with `div` instead of `mod`, and constant-folded arguments.)
  This is an incompleteness, not a wrong answer — AY previously answered `unsat`
  here, which is fixed and covered by
  `crates/ay-dpll/tests/group_regression/false_unsat_to_int_mod_hnf.rs`.
- **Array certificates: the one-sided read-over-write chain under an array
  equality is still an unproved (`hole`) step.** The substituted-equality
  COLLAPSE — `substitute-and-simplify` eliminates a defined array constant, so
  the assertions justifying an entailed equality never reach the proof as
  `assume` steps and the equality is exported premiseless — is now promoted: the
  originals are re-introduced into the assumption prologue and the unit is
  re-derived with the certified `eq_transitive`/`eq_congruent` toolkit
  (`plan_substituted_equality`). `benchmarks/smt/QF_AX/storeinv_cross_1idx.smt2`
  therefore checks `valid` in carcara with zero unproved steps.

  What still does NOT promote is the array lemma

  ```text
  (or (= x i) (not (= L R)) (= (select B x) (select R x)))
  ```

  where `L = (store B i v)` — one side of the conclusion is EVALUATED through
  the store chain and the other is left as a bare `select` of the whole array.
  It is a true and ordinarily derivable lemma (`arrays_row` on the left,
  `cong` from `L = R`, `symm` + `trans`), but the strict-checkable
  `ArrayRowChain` sub-schema (B) requires BOTH sides to be greedily evaluated
  (`eval(L,x)` and `eval(R,x)`), so the recognizer/validator pair in
  `ay-proof`'s `array_axiom` declines it and the leaf stays `Generic` — printed
  as `hole`. Admitting it means generalizing that schema to allow a PREFIX
  (in particular the zero-skip identity) path on one side, in the recognizer,
  the validator, and the printer's lowering together; that is a widening of a
  soundness-critical accepted schema and has not been done.

  Consequence: `benchmarks/smt/QF_AUFLIA/storeinv_sf_size2.smt2` (the 2-index
  cross-swap) still exports 10 unproved steps and carcara reports the document
  `invalid`. AY's own gate agrees — `--self-check` answers `unknown` — and the
  CLI now says so explicitly next to the file it wrote
  (`c ay.proof.certificate … ay_self_checkable=no`), so a zero exit status
  cannot be read as "externally checkable".
- **Build time and running tests.** The workspace includes one very large crate
  (`ay-dpll`, ~430,000 lines), so a from-scratch build of the whole workspace is
  slow and is the dominant compile cost. To *use* AY, prefer the release binary
  or build only the solver crate — and note that the `ay` binary is behind a
  `required-features = ["cli"]` gate, so `cargo build --release -p ay` builds the
  **library only** and silently leaves any previously built `target/release/ay`
  in place. Always build the binary explicitly:
  `cargo build --release -p ay --features cli --bin ay`, and check
  `ay --version` against your checkout before trusting a measurement — a stale
  binary reports its own older build commit, not your HEAD. **Run tests per
  crate** — `cargo test -p ay-sat`, `cargo test -p ay-dpll`, etc. A blanket
  `cargo test --workspace --features cli` does not currently link: the binary
  crates statically link the mimalloc allocator, whose symbols are then pulled
  into those crates' unit-test binaries and collide. Splitting `ay-dpll` for
  faster, parallel compilation and smoothing the whole-workspace test invocation
  are tracked for a soon release.
