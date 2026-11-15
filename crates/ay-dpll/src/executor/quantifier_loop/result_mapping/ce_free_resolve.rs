// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The counterexample-free consequence re-solve (#quantifier-ce-free-resolve),
//! stage 4 of the quantifier-instantiation plan.
//!
//! # The defect
//!
//! `CegqiInstantiator::create_ce_lemma` returns `¬B[c̄]` for an ENTAILED
//! universal `∀x̄.B` and `setup_cegqi_for_unhandled` conjoins it at top level.
//! That formula is a search HYPOTHESIS — the negation of an asserted universal
//! at fresh constants — not a consequence, so a refutation of the CE-augmented
//! ground problem says one of two things: the CE-free set is unsatisfiable
//! (a real refutation), or the counterexample search space is empty (the
//! universal holds relative to the rest — evidence for SAT). Every path out of
//! `classify_cegqi_forall_unsat` exists to tell those apart afterwards, and
//! the only one that can publish `unsat` for a public query needs a translated
//! authored-scope certificate the bounded consequence replay can build for a
//! handful of instances, not for the thousands the measured files carry.
//! Everything else fails closed: *"CEGQI could not disambiguate or refine the
//! quantified formula"*. A second exit, before any ground solve, refuses the
//! whole dispatch when a counterexample constant sits under integer
//! `div`/`mod` (`check_sat.rs`, `unsupported_int_div_mod_mentions_ce_var`),
//! because that shape once sent the nonlinear lane into an unbounded loop.
//!
//! # The mechanism
//!
//! cvc5 and z3 never conjoin the counterexample: they assert the counterexample
//! LITERAL clause `ce_lit ⇒ ¬B[k̄]` and let the SAT solver choose the side. The
//! plan asked for that shape. For a re-solve whose only purpose is a
//! refutation it is provably equivalent to something simpler, and the simpler
//! thing is what ships: for a fresh guard `g`, `{(or (not g) C)} ∪ A` is
//! unsatisfiable exactly when `A` is (extend any model of `A` by `g := false`),
//! so the guarded clauses can be OMITTED. Omitting them is also what makes the
//! div/mod exit rescuable at all — a guarded conjunct still puts the
//! counterexample constant under `div`/`mod` in the nonlinear lane.
//!
//! So this module runs as the LAST RESORT OF THE SOLVE before `unknown`:
//! strictly after every existing CEGQI arm has produced a fail-closed
//! `unknown` (which is what ARMS it, at the tail of
//! `classify_quantifier_result`), strictly after every arm of
//! `map_quantifier_result` that could still publish a verdict -- the
//! finite-table, default-row, constant-interpretation, closed-sentence and
//! datatype SAT certificates, the restoration, the closed-sentence UNSAT
//! theorem, the public-root table rescue -- has declined (which is where it
//! is PARKED), and strictly after all five EXECUTOR-level passes that can
//! still publish once the loop has returned have declined too (which is
//! where it FIRES: `Executor::fire_stashed_ce_free_resolve`, called from
//! `check_sat_guarded` after the last model-rejection re-solve). It takes
//! the EXACT vector `S` the
//! primary dispatch was handed (after the pre-dispatch soundness passes), and
//! re-solves
//!
//! ```text
//! S \ CE  ∪  { the entailed-instance support axioms recorded since }
//! ```
//!
//! live, through the same lane the primary dispatch used, where `CE` is the
//! set of counterexample conjuncts `cegqi_ce_lemma_ids` names — inside an
//! isolation window of the probe's own (next section).
//!
//! # Why last, and not merely after the CEGQI arms
//!
//! The probe can only refute; it can never publish `sat`. Hooked at the tail
//! of `classify_quantifier_result` — after the CEGQI arms but BEFORE the SAT
//! certificates of `map_quantifier_result` — it ran under the query's
//! remaining deadline with nothing bounding it but that deadline, and on a
//! satisfiable shape whose CE-free vector the nonlinear lane does not decide
//! it took all of it: `nra_cube_sortpred` (`(forall ((x Real)) (or (> b 5.0)
//! (> (* x x x) 8.0)))` next to an unhandled universal over an uninterpreted
//! sort) answers `sat` in 4.0 s on `main` through the finite-table
//! certificate, and with the probe one arm earlier it answered `unknown` at
//! `-T:20`, `-T:60` and `-T:120`, the probe holding 16 / 56 / 116 s of it.
//! A refutation-only probe has no business running before an arm that could
//! still publish a verdict. Arming and firing are separate on purpose — the
//! arming predicate (a fail-closed CEGQI `unknown` over a refuted ground
//! result) is computed where the CEGQI arms are, and only the point of
//! firing has ever moved.
//!
//! # Why the fire point is at the EXECUTOR: the loop is not the solve
//!
//! It moved twice, for the same reason, and the second time is why it is
//! where it is. A revision that fired at the tail of
//! `map_quantifier_result` said the probe "is bounded by the query's
//! remaining deadline alone: there is no share to reserve for anything after
//! it, because nothing runs after it". That is FALSE, and measured false.
//! Nothing runs after it INSIDE the quantifier loop — the three `unknown`
//! exits of `classify_and_certify_quantifier_result` converge at one point.
//! But five EXECUTOR-level passes run after `map_quantifier_result` returns,
//! every one able to turn that `unknown` into a verdict and every one gated
//! on the deadline this probe spends:
//!
//! 1. the CEGAR pending-lemma loop (`check_sat.rs`, `cegar_refine_solve`);
//! 2. `deep_qe_unknown_retry` (`check_sat/unknown_retries.rs`);
//! 3. `quantified_trace_arming_unknown_retry` (same file);
//! 4. `finite_model_last_chance` (`finite_model_mbqi.rs`), consulted on
//!    `Unknown(QuantifierUnhandled)`;
//! 5. the four model-rejection re-solves of `check_sat_guarded`
//!    (#uflia-model-repair, #uflia-cong-repair-arm, #abv-subst-model-retry,
//!    #qfax-isolated-lane-retry).
//!
//! POSTURE SPLIT, measured with `--debug-cert` instrumentation on both arms
//! (report §2.7). In the DEFAULT posture 3 is dead by construction: the
//! best-effort Alethe sidecar (`set_best_effort_produce_proofs`) makes
//! `is_producing_proofs()` true, so `competition_shedding_active()` is false.
//! 2 was dead there too until its guard moved to
//! `checked_certificate_demanded()` (#qlra-deepqe-retry); it is live now in
//! every posture that demands no checked certificate. `--z3-mode` and
//! `--no-proof` shed the sidecar and BOTH are live. Across 217
//! instrumented A/B rows: 1, and the uflia/qfax arms of 5, never ran on any
//! population measured; 4 and the BV arm of 5 ran; 2 and 4 DECIDED (38 and 1
//! base rows in `--z3-mode`).
//!
//! THE VERDICT THAT COST: on a Farkas-lambda LIA body with a CEGQI arming
//! universal grafted on (`starve/impl2_ex36_none.smt2`) the probe, fired at
//! the tail of `map_quantifier_result`, held 17.55 s of a 20 s budget, the
//! deep-QE and trace-arming retries then both read `skipped (deadline)`, and
//! the query published `unknown` — where `main` publishes `sat` in 3.6 s
//! THROUGH the deep-QE retry. Confirmed on the shipping binaries at `-T:60`:
//! `sat` in 3.74 s / 3.56 s against `unknown` at 60.06 s / 60.01 s, two reps
//! each. A verdict withdrawn against `main` in a shipping posture, which is
//! a merge blocker by this campaign's invariants.
//!
//! SO THE LOOP HANDS THE PROBE OVER INSTEAD OF FIRING IT. The tail of
//! `map_quantifier_result` parks `CeFreeResolveStash` — the snapshot, the
//! counterexample conjunct ids, the category, the solve's
//! `QuantifierVerdictInputs` and the authored vector — and returns its
//! `unknown` unchanged. `check_sat_guarded` fires it at one new site, after
//! the last model-rejection re-solve, i.e. after every one of the five
//! passes above. Nothing is left behind it to starve. Two further
//! consequences, both measured rather than argued: the probe now fires at
//! most ONCE per query rather than once per nested solve (up to three times
//! in `--z3-mode`, §2.7.1), and a query that one of those five passes
//! decides never pays for the probe at all — the stash is simply dropped.
//!
//! What the rescue has to re-establish, because it no longer runs inside
//! `check_sat_internal`, is named in `fire_stashed_ce_free_resolve` rather
//! than assumed: the scope-tracked assertion vector (`restore_assertions`
//! puts the authored one back only when `original_assertions` is `Some`) and
//! the authored window the mandatory independent model gate and the
//! `--self-check` premise read. The caller then completes it exactly as the
//! three model-rejection re-solves beside it do — `build_unsat_proof` for a
//! refutation, then the `emit_sat_verdict` chokepoint.
//!
//! # The window
//!
//! The lane is not enough; the lane's *state* is what decides what gets
//! solved. `solve_nia` (`solve_incremental_split_loop_pipeline!`, field
//! `persistent_sat`), `solve_nra` (`solve_incremental_theory_pipeline!`, the
//! same field) and `solve_propositional` reuse `self.incr_theory_state`
//! through `get_or_insert_with`, and `pipeline_incremental_setup!` encodes
//! only the assertions not already in `encoded_assertions` — every activation
//! unit the primary dispatch of the CE-augmented window added at scope depth 0
//! through `add_clause_global` is still in the persistent SAT solver,
//! **including the counterexample hypothesis `¬B[c̄]`**. Handing such a lane
//! the correct CE-free vector therefore solves `(S \ CE) ∪ CE`: the invariant
//! over the vector held, and the probe still refuted under the hypothesis.
//! Measured on `benchmarks/smt/wrong-verdict/sat_quantified_{ufnia,ufnra}_sort.smt2`
//! and `sat_quantified_eu_two_preds.smt2`: `unsat` in both postures, 18/18,
//! on a tree without the window; `sat` from main, from the kill switch and
//! from z3 5.1.0, and the emitted certificate carried the counterexample
//! conjunct as a `hole` leaf. The UF-bearing lanes (`solve_uf_nia` →
//! `with_deferred_postprocessing` → `with_isolated_incremental_state`),
//! EUF/combined and `array_fixpoint` open a window of their own and were
//! never exposed. The seq/set/map/multiset lanes were NOT among them, though
//! the first version of this note said so: `solve_seq_lia`, `solve_set_lia`,
//! `solve_map_lia` and `solve_multiset_lia` run
//! `solve_incremental_split_loop_pipeline!`, and `solve_seq`
//! `solve_incremental_theory_pipeline!`, straight on `incr_theory_state`;
//! the `with_isolated_incremental_state` in each of those files belongs to
//! the `*_with_assumptions` sibling that `solve_for_category` never
//! dispatches to. Measured on the 228-input adversarial set: 4 of 4
//! `QfSeqlia` inputs answered `unsat` — wrong — on the window-OFF tree in
//! both shipping postures, and `unknown` (as does `main`) with the window
//! below in place. LIA (`reset_lia_sat` per solve, and a fresh temporary
//! state outside incremental mode) and LRA (the standalone lane takes and
//! restores `incr_theory_state`) were safe by their own resets — by
//! accident, as far as this probe is concerned.
//! `check_sat.rs` documents exactly this hazard class for nested probes
//! (`#qmg-incr-bv-scope-leak`).
//!
//! So the probe does not rely on the lane: `try_ce_free_resolve` runs
//! `solve_for_category` inside `with_isolated_incremental_state(None, …)`,
//! structurally, for EVERY category. That window takes `incr_theory_state`
//! and `incr_bv_state` for the duration (the lane lazily creates fresh ones,
//! so it encodes exactly the vector it is handed), restores both on every
//! exit, rolls the proof ledger back on every non-`Unsat` exit and keeps it
//! on `Unsat` — the probe's refutation is the outer publication's candidate,
//! exactly the contract the UF lanes' inner refutations already use. A lane
//! that opens its own window simply nests one inside the other.
//!
//! "For EVERY category" is a claim about the executor's whole cross-solve
//! state, so it is worth saying what that state IS. No `SatSolver` is an
//! executor field; the only ones that outlive a solve are
//! `IncrementalTheoryState::{persistent_sat, lia_persistent_sat}`,
//! `IncrementalBvState::persistent_sat` and `IncrementalFpState::persistent_sat`,
//! held in exactly three fields — `incr_theory_state`, `incr_bv_state`,
//! `incr_fp_state`. The window takes the first two. It does NOT take the
//! third, and does not need to: `incr_fp_state` is read at one site
//! (`solve_fp`, behind `persistent_authorized`), and that authorization is
//! `std::mem::take(&mut self.fp_persistent_armed)` — a flag written at ONE
//! site, `check_sat.rs`'s primary dispatch, as
//! `!self.original_problem_had_quantifiers && self.last_assumptions.is_none()`,
//! and cleared the moment that dispatch returns. This probe runs only when
//! `cegqi_has_forall`, i.e. on a query whose authored assertions contained a
//! quantifier, which is precisely what sets `original_problem_had_quantifiers`
//! — captured before `process_quantifiers`, and kept live through the probe
//! by [`LaneLatches`]. So for every query the probe can run inside, the FP
//! lane is disarmed, `incr_fp_state` is never populated, and the probe's
//! `solve_fp` (reachable as `QfFp` / `QfBvfp` / `QfAbvfp`, which is where a
//! declared `FP`/`BVFP`/`ABVFP`/`FPLRA` lands) runs the stateless pipeline.
//! The window is complete because those three fields are the whole
//! population, not because every lane was read one at a time.
//!
//! One thing the window is NOT is unconditional. It opens with
//! `bounded_proof_rollback_checkpoint`, whose 128 MB query-cumulative
//! envelope a long query can exhaust; a decline returns `Unknown` WITHOUT
//! running the lane. That is sound — a probe that does not run publishes
//! nothing — but it means `quantifier.cegqi.ce_free_resolves` counts
//! ATTEMPTS, not lane runs, and a decline is indistinguishable from a
//! genuine non-refuting solve in the verdict. The refutation counter and
//! `time.quantifier.ce_free_resolve_seconds` are what say the lane ran.
//!
//! # Soundness
//!
//! Every member of the re-solved set is a consequence of the authored problem
//! under the standing invariants of the quantifier pipeline: an authored
//! (post-Skolem, post-abstraction) assertion, an instance of a universal the
//! assertion set entails, a guarded instance of a proxied universal
//! (`(or (not qproxy) B[t̄])`, valid under the proxy model extension), a
//! pre-dispatch soundness axiom, or a support axiom — exactly the population an
//! E-matching-only refutation of this problem is published from, and the
//! counterexample conjuncts are the ONLY members of `S` that are not. Hence
//! **the re-solve's UNSAT is a refutation of the authored problem**, and it is
//! classified exactly as an E-matching-only refutation: with every CEGQI flag
//! off, through the same non-conjunctive-forall firewall.
//!
//! The converse fails — a model of the CE-free set says nothing about the
//! universals — which is why this module publishes NOTHING on `Sat` or
//! `Unknown`: it restores the predecessor state and the fail-closed `unknown`
//! stands. No `sat` gate reads anything this module writes — and since the
//! probe fires last, no `sat` gate even runs after it within the query.
//!
//! A refutation is handed back to the SAME pass that produced the
//! fail-closed `unknown` (`classify_and_certify_quantifier_result`), with
//! every CEGQI flag off: the non-conjunctive-forall firewall, the
//! translation-incomplete demotion, the restoration and the UNSAT theorems
//! run over it exactly as they would over an E-matching-only refutation of
//! the same problem. (Should that firewall demote the refutation to
//! `unknown`, the pass's SAT certificates run a second time, now over the
//! probe's lane state; they declined once already on the predecessor's, and
//! the deadline bounds the repeat.)
//!
//! # Restore, don't clear
//!
//! "Restores the predecessor state" is a transaction, not a clearing. The
//! probe runs through a live theory lane, and a lane writes the executor's
//! solve outputs — the model, the refutation artifacts, the verdict fields —
//! as a side effect of solving. Every one of those outputs is MOVED OUT into
//! [`PredecessorOutputs`] before the probe (so the lane starts on the same
//! empty slate the primary dispatch starts on: `prepare_check_sat_internal_state`
//! plus the `last_model = None` after `process_quantifiers`) and MOVED BACK
//! verbatim on every non-refuting exit. Clearing instead of restoring was
//! measured to lose a correct `sat` while the probe still ran BEFORE the SAT
//! certificates: `try_finite_table_sat_certificate` seeds its completion from
//! `last_model`, and the ground witness the CEGQI disambiguation had
//! installed certified in four solver calls where an empty base exhausted
//! `MAX_TABLE_CERT_SOLVER_CALLS` (`sat_ufnia_square_nonneg.smt2`, base
//! `sat`, probe-with-clearing `unknown`). With the probe last, that
//! certificate runs first and the shape can no longer lose its `sat` to the
//! probe at all; the transaction stays because the predecessor state
//! OUTLIVES the query — the check-sat boundary reads the verdict fields for
//! its diagnostics, `check_sat_guarded`'s retries and the next `check-sat`
//! of an incremental session start from whatever was left — and a probe
//! that publishes nothing must leave nothing.
//!
//! What the probe touches, and what happens to each:
//!
//! * `ctx.assertions` — swapped for the CE-free vector, swapped back.
//! * the solve outputs a lane writes (model side, refutation side, verdict
//!   side; the inventory of `revoke_dt_lazy_attempt_artifacts`, the discarded
//!   lazy-DT sub-solve, plus the NRA/DT model side tables) — moved out, moved
//!   back.
//! * the lane-written latches and ledgers — the inventory of
//!   `DtLazyAttemptState`, the lazy-DT lane's own transaction for a discarded
//!   sub-solve of the same query ("a validation bypass, refinement lemma,
//!   model-repair latch, or TermId-keyed memo from the failed attempt can
//!   change what the eager authority accepts"), plus the model-repair stash
//!   `unrepaired_model_candidate`, the injected-axiom registry, the BV DRAT
//!   self-cert marker, the proof-problem provenance and the `last_proof_*`
//!   ledgers. Two disciplines, decided per field in `PredecessorOutputs`:
//!   TAKEN (reset to the slate a primary dispatch starts on — the resets in
//!   `prepare_check_sat_internal_state` and `check_sat_guarded` — then put
//!   back): `sat_validated_by_mod_div_or_branch` (a validation BYPASS the
//!   NIA/LIA/LIRA lanes set when they introduce an unconstrained div/mod
//!   witness; leaked, it would let the predecessor's model skip the full
//!   replay), `read_pin_repair_done`, `nested_array_row_reduction_unsat`
//!   and `last_bv_drat_self_cert` (UNSAT-side authority markers: on a
//!   refutation they must describe the PROBE's refutation, so they start
//!   false), `last_degrade_was_datatype_array`, the `uflia_*`/`qfax_*`
//!   once-per-check-sat latches and the strict-gate blocking clause
//!   (`qfax_refinement_clause`, `last_rejected_array_assertion` — derived
//!   from a rejection of the CE-augmented window's model), the model-repair
//!   stashes, `recorded_var_substitutions` and `row_seeded_terms` (per-run
//!   preprocessing registries the lane's own model completion replays),
//!   `array_axiom_scope`, `dt_pre_lift_assertions`, `dt_lazy_splits`,
//!   `injected_axiom_theory_kinds` (the DT lanes inject axioms into the
//!   vector they solve and register the kinds here; the probe's lane
//!   registers its own, and on a refutation those are the ones its
//!   certification needs). KEPT LIVE (the lane reads them as input; put
//!   back afterwards): `last_assumptions` and `last_core_term_to_name`
//!   (the query), `named_assert_rewrites` (written only by the top-level
//!   preprocessing passes, BEFORE the quantifier loop, and read by the
//!   named-core redirect of a refutation — the probe's refutation included),
//!   `original_problem_had_quantifiers` (the AUFLIA alias-collapse soundness
//!   gate reads it; a lane that saw `false` could collapse unsoundly — and it
//!   is the same bit that keeps the persistent FP lane disarmed inside the
//!   window, see "The window" above),
//!   `defer_model_validation` and `skip_model_eval` (installed by the
//!   enclosing scope), `dt_array_injectivity_gate_bypass` (a SAT gate
//!   bypass a DT lane recomputes over ITS vector; the predecessor's value,
//!   computed over the authored problem, is what the later gates must see),
//!   the CEGAR lemma/budget trio, `array_ext_shadow`, the residue-probe and
//!   mod/div re-entry guards, `proof_problem_assertion_provenance` (a lane
//!   installs and restores it symmetric to its own outcome; this is defense
//!   in depth for a lane that exits through `?`) and the `last_proof_*`
//!   ledgers (written by a proof rebuild; no lane rebuilds, so this is
//!   uniformity, not a measured leak).
//! * NOT restored, each for a reason: `active_support_axioms` — the probe's
//!   READ-ONLY input; only the instantiation rounds push to it, and no
//!   ground lane runs one. `array_ext_witness_cache`,
//!   `array_default_epsilon_by_sort`/`array_default_diag_by_sort` — term
//!   provenance keyed by terms that stay valid, because this probe never
//!   rolls `ctx.terms` back (the lazy-DT lane restores them only because it
//!   does). `conflict_semantic_verify_memo`/`prop_semantic_verify_memo` — a
//!   memoised verdict is a pure function of the literal set, the append-only
//!   term content and the support-axiom set, none of which the probe
//!   changes; an entry the probe's lane adds is exactly as valid afterwards.
//!   The quantifier-pipeline proof records (`quant_expansion_records`,
//!   `ematching_proof_records`, the Skolem/BV-MBQI/QPF instance records,
//!   `propagated_value_provenance`, `dt_context_conflict_records`) — read
//!   only when an UNSAT proof is built, and after a non-refuting exit no
//!   UNSAT route runs again in this query: the probe is now the last thing
//!   the SOLVE runs — every retry of `check_sat_guarded` is already behind
//!   it, the one pass ahead of it that re-solves (the non-string-seq
//!   corroboration) is gated on `result.is_unsat()` and a non-refuting exit
//!   leaves `Unknown`, and the next `check-sat` resets them. `ay_lia`'s thread-local probe trajectory (`save_probe_state`) —
//!   heuristic only ("a stale hint is verified by an actual probe check
//!   before use"); no other nested CEGQI leg restores it either.
//!
//! Why leaving anything else is sound: a `sat` this query can still publish
//! after a non-refuting exit passes through ONE funnel, `emit_sat_verdict`
//! (`model/sat_emit.rs`), which re-validates the candidate against the
//! restored authored assertions — the strict model gate, the
//! quantified-assertion certificate gate, the INDEPENDENT fail-closed
//! model-check gate, the authoritative gate and the validation
//! postcondition. Lane state can steer WHICH candidate reaches it and
//! whether a retry fires; it cannot make the funnel accept a refuted
//! witness. The fields taken above are the ones that could make a gate
//! skip work (`sat_validated_by_mod_div_or_branch`, the injectivity bypass,
//! `skip_model_eval`); that is why they are in the transaction and not in
//! this paragraph.
//! * the quantified SAT authority (the unit `clear_quantified_sat_authority`
//!   revokes: the typed grants, their routing bits, the parked witnesses, the
//!   model's seals) — moved out with the model, moved back. Every install
//!   site of these grants returns `Sat` on the spot and this probe runs only
//!   on a fail-closed `Unknown`, so at entry the unit is expected empty —
//!   but nothing here depends on that: a grant that IS live is put back on a
//!   non-refuting exit, and on a refutation it is dropped along with the rest
//!   of the bundle (an UNSAT publication consumes no SAT grant). Taking the
//!   unit is also how a grant the PROBE mints (its vector is a subset of the
//!   problem, so a SAT authority over it is not one over the problem) is
//!   discarded without a revoke list that has to track every future grant.
//! * `last_unknown_reason` — restored, with one deliberate exception: a
//!   deadline or interrupt that fired DURING the probe is the reason the
//!   query publishes, because the predecessor's reason would misattribute a
//!   timeout to CEGQI incompleteness.
//! * the proof ledger (`proof_tracker`) and the incremental theory/BV state —
//!   the probe's OWN `with_isolated_incremental_state` window ("The window"
//!   above) rolls the ledger back on every non-`Unsat` exit, keeps it on
//!   `Unsat`, and restores both states on every exit. An earlier revision of
//!   this module claimed the lane's window did this; the NIA, NRA and
//!   propositional lanes have none, and the claim was a wrong `unsat`.
//! * `last_statistics`, the two `ce_free_*` counters and the probe's wall
//!   (`time.quantifier.ce_free_resolve_seconds`) — cumulative diagnostics,
//!   deliberately NOT restored: they are the audit trail that the probe ran
//!   and what it cost, and no verdict path reads them.
//! * `ctx.terms` — append-only; terms the probe minted stay, as after every
//!   refinement round. No identifier is reused, so nothing restored can
//!   dangle.
//! * the finite-array expansion ledger — a deterministic per-query budget the
//!   probe's `add_finite_index_array_closure` may spend, as a refinement
//!   round's does; not replenished, by that ledger's own contract.
//!
//! On a refutation the bundle is dropped and the probe's outputs stand: the
//! CE-free refutation is then classified with the artifacts ITS lane produced,
//! never with a stale artifact of the CE-augmented solve.
//!
//! # Why the pre-dispatch vector
//!
//! The "ground-minus-CE" re-solve that `disambiguate_cegqi_unsat` used to run
//! over the LIVE assertion set was retired (`#cegqi-attribution`) because the
//! ground lane rewrites that set in place — on the recorded false-UNSAT it
//! consumed a counterexample equality as a definition, rewrote a genuine
//! assertion with it and constant-folded the residue to `false`, so filtering
//! by identity kept the CE-derived residue and dropped the authored fact. The
//! pre-dispatch vector predates every lane, so the conjunct identities
//! `setup_cegqi_for_unhandled` recorded are exact on it, and no residue exists
//! yet.
//!
//! # The invariant, computed where it is consumed
//!
//! The routing above is licensed by one property of the vector about to be
//! solved: *every counterexample conjunct recorded for this solve was present
//! in `S` and is absent from the re-solved vector, no member of the re-solved
//! vector mentions a counterexample constant, and no member carries a
//! quantifier.* It is checked by [`ce_free_vector_invariant_holds`] over that
//! vector at the point the decision to solve it is taken — never carried as a
//! boolean a producer sets. The check is `debug_assert`ed and, in release, a
//! failure declines the re-solve.

use std::sync::Arc;

use super::super::super::Executor;
use crate::ematching::contains_quantifier;
use crate::executor::bv_mbqi::CheckedBvFullDomainSatAuthority;
use crate::executor::mbqi::{ConstInterpWitnessState, FiniteTableWitnessState};
use crate::executor::model::{
    DtEgraphAssignment, Model, QuantifiedModelConfirmation, ValidationStats,
};
use crate::executor::nra_model_state::NraAlgebraicModel;
use crate::executor::proof::CheckedFiniteEnumPigeonholeProof;
use crate::executor::proof_resolution::CheckedSatRefutation;
use crate::executor::quantifier_loop::CegqiUfRecompletionGrant;
use crate::executor::theories::solve_harness::ProofProblemAssertionProvenance;
use crate::executor::{
    ArrayExtShadow, FiniteEnumPigeonholeWitness, ProofDeclineMechanism,
    QuantifiedSatAuthorityGrant, SatCertificate, UnsatCertificate,
};
use crate::executor_types::{Result, SolveResult, UnknownOrigin, UnknownReason};
use crate::logic_detection::LogicCategory;
use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::term::{TermData, TermId, TermStore};
use ay_core::{ClausificationProof, Proof, TheoryLemmaProof};
use ay_proof::{PartialProofCheck, ProofQuality};
use ay_sat::{ClauseTrace, SatUnknownReason};

/// Prefix of the counterexample constants `CegqiInstantiator::new` mints
/// through `mk_internal_symbol("ce_…")`.
const COUNTEREXAMPLE_SYMBOL_PREFIX: &str = "__ay_ce_";

/// Node budget for the whole-vector invariant scan. A vector larger than this
/// declines rather than trusting an unfinished scan.
const INVARIANT_SCAN_NODE_LIMIT: usize = 4_000_000;

/// Whether `root` mentions a variable whose name starts with
/// [`COUNTEREXAMPLE_SYMBOL_PREFIX`]. `None` when the scan budget ran out.
/// `seen` is shared across roots: a subterm scanned once is clean everywhere.
fn mentions_counterexample(
    terms: &TermStore,
    root: TermId,
    seen: &mut DetHashSet<TermId>,
    work: &mut usize,
) -> Option<bool> {
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        *work += 1;
        if *work > INVARIANT_SCAN_NODE_LIMIT {
            return None;
        }
        if !seen.insert(term) {
            continue;
        }
        if let TermData::Var(name, _) = terms.get(term) {
            if name.starts_with(COUNTEREXAMPLE_SYMBOL_PREFIX) {
                return Some(true);
            }
        }
        stack.extend(terms.children(term));
    }
    Some(false)
}

/// The publication-time invariant over the vector about to be re-solved. See
/// the module documentation for what it licenses.
///
/// `source` is the pre-dispatch vector, `conjuncts` the counterexample
/// conjuncts recorded for the solve, `vector` the rebuilt CE-free vector.
fn ce_free_vector_invariant_holds(
    terms: &TermStore,
    source: &[TermId],
    conjuncts: &DetHashSet<TermId>,
    vector: &[TermId],
) -> bool {
    // Every recorded conjunct was in the source — the identity list is exact
    // for THIS vector — and none survives.
    let source_set: DetHashSet<TermId> = source.iter().copied().collect();
    if !conjuncts.iter().all(|c| source_set.contains(c)) {
        return false;
    }
    let mut seen: DetHashSet<TermId> = DetHashSet::default();
    let mut work = 0usize;
    for &member in vector {
        if conjuncts.contains(&member) {
            return false;
        }
        if contains_quantifier(terms, member) {
            return false;
        }
        if mentions_counterexample(terms, member, &mut seen, &mut work) != Some(false) {
            return false;
        }
    }
    true
}

/// The predecessor's solve outputs: every executor field a theory lane writes
/// as the result of a solve, moved out before the counterexample-free probe
/// and moved back verbatim on every non-refuting exit (see the module
/// documentation, "Restore, don't clear").
///
/// The inventory is `revoke_dt_lazy_attempt_artifacts`'s — the fields a
/// discarded lazy-DT sub-solve is known to write — plus the NRA and DT model
/// side tables those lanes own and the `proof_term_overrides` /
/// `reconstruction_suppressed` pair `clear_cegqi_inner_unsat_artifacts` names,
/// less the objective ledger a category dispatch never touches. Moves, not
/// clones: a clause trace or a model is put back at the cost of a pointer.
struct PredecessorOutputs {
    // Verdict side.
    last_result: Option<SolveResult>,
    last_unknown_reason: Option<UnknownReason>,
    last_unknown_origin: Option<UnknownOrigin>,
    pending_sat_unknown_reason: Option<SatUnknownReason>,
    // Model side.
    last_model: Option<Model>,
    last_model_validated: bool,
    last_validation_stats: Option<ValidationStats>,
    last_sat_certificate: Option<SatCertificate>,
    model_validation_delegated_assertions: DetHashSet<TermId>,
    dt_solver_added_axiom_terms: DetHashSet<TermId>,
    nra_algebraic_model: NraAlgebraicModel,
    dt_theory_model: Option<ay_dt::DtModel>,
    dt_validation_wants_egraph: bool,
    dt_egraph_assignment: Option<Arc<DtEgraphAssignment>>,
    last_negations: Option<DetHashMap<TermId, TermId>>,
    // Refutation side.
    last_unsat_certificate: Option<UnsatCertificate>,
    last_assumption_core: Option<Vec<TermId>>,
    last_proof: Option<Proof>,
    last_finite_enum_pigeonhole: Option<FiniteEnumPigeonholeWitness>,
    last_checked_finite_enum_pigeonhole: Option<CheckedFiniteEnumPigeonholeProof>,
    last_unsat_proof_reconstruction_suppressed: bool,
    last_lrat_certificate: Option<Vec<u8>>,
    last_proof_term_overrides: Option<DetHashMap<TermId, String>>,
    last_proof_quality: Option<ProofQuality>,
    last_clause_trace: Option<ClauseTrace>,
    last_checked_sat_refutation: Option<CheckedSatRefutation>,
    last_var_to_term: Option<DetHashMap<u32, TermId>>,
    last_trail_provenance: Option<DetHashMap<u32, (u32, bool, Vec<u32>)>>,
    last_clausification_proofs: Option<Vec<Option<ClausificationProof>>>,
    last_original_clause_theory_proofs: Option<Vec<Option<TheoryLemmaProof>>>,
    proof_check_result: Option<PartialProofCheck>,
    proof_check_ok: bool,
    // Quantified SAT authority: the unit `clear_quantified_sat_authority`
    // revokes. The model's own seals travel with `last_model` above.
    quantified_model_confirmation: Option<QuantifiedModelConfirmation>,
    dt_cert_grant_active: bool,
    dt_cert_query_grant: Option<QuantifiedSatAuthorityGrant>,
    finite_table_cert_grant_active: bool,
    const_interp_cert_grant_active: bool,
    mbqi_sat_cert_grant_active: bool,
    mbqi_sat_cert_query_grant: Option<QuantifiedSatAuthorityGrant>,
    cegqi_uf_recompletion_grant: Option<CegqiUfRecompletionGrant>,
    bv_quantifier_full_domain_proof: bool,
    bv_quantifier_full_domain_pending_evidence: Option<CheckedBvFullDomainSatAuthority>,
    bv_quantifier_full_domain_query_grant: Option<QuantifiedSatAuthorityGrant>,
    finite_table_cert_witness_state: Option<FiniteTableWitnessState>,
    const_interp_cert_witness_state: Option<ConstInterpWitnessState>,
    /// The lane-written latches and ledgers (their own transaction below).
    latches: LaneLatches,
}

/// Lane-written latches and ledgers a discarded sub-solve of the same
/// query must not leave behind: the `DtLazyAttemptState` inventory (the
/// lazy-DT lane's own transaction boundary), plus the model-repair stash,
/// the injected-axiom registry, the BV self-cert marker and the proof
/// ledgers. Two disciplines, per field (see "Restore, don't clear" in the
/// module documentation): TAKEN fields are reset to the slate a primary
/// dispatch starts on and put back afterwards; KEPT fields stay live for
/// the lane (it reads them as input) and are put back afterwards.
struct LaneLatches {
    // Taken: validation bypasses, one-shot repair latches, per-run rewrite
    // and injection registries, UNSAT-side authority markers.
    sat_validated_by_mod_div_or_branch: bool,
    read_pin_repair_done: bool,
    nested_array_row_reduction_unsat: bool,
    last_degrade_was_datatype_array: bool,
    last_bv_drat_self_cert: bool,
    uflia_congruence_lane: bool,
    uflia_congruence_gate_rejected: bool,
    uflia_congruence_retry_done: bool,
    uflia_model_repair_done: bool,
    qfax_retry_done: bool,
    qfax_refinement_clause: Option<Vec<(TermId, bool)>>,
    last_rejected_array_assertion: Option<TermId>,
    unrepaired_model_candidate: Option<Model>,
    uflia_repair_candidates: Vec<Model>,
    uflia_repair_conflict_tables: Vec<String>,
    recorded_var_substitutions: DetHashMap<TermId, TermId>,
    row_seeded_terms: DetHashSet<TermId>,
    array_axiom_scope: Option<(DetHashSet<TermId>, usize)>,
    dt_pre_lift_assertions: Vec<TermId>,
    dt_lazy_splits: Option<(Vec<(String, Vec<String>, bool)>, Vec<(TermId, Vec<TermId>)>)>,
    injected_axiom_theory_kinds: DetHashMap<TermId, ay_core::TheoryLemmaKind>,
    // Kept live: query-level inputs the lane reads (the assumption set, the
    // named-core provenance recorded by the top-level preprocessing passes,
    // the quantifier bit the AUFLIA alias-collapse gate consults, the
    // validation-defer/skip bits the enclosing scope installed, the CEGAR
    // budget and its lemma ledger, the re-entry guards) and the proof
    // provenance a lane installs symmetric to its own outcome.
    last_assumptions: Option<Vec<TermId>>,
    last_core_term_to_name: Option<DetHashMap<TermId, String>>,
    named_assert_rewrites: DetHashMap<TermId, TermId>,
    original_problem_had_quantifiers: bool,
    defer_model_validation: bool,
    skip_model_eval: bool,
    dt_array_injectivity_gate_bypass: bool,
    cegar_pending_lemma: Option<TermId>,
    cegar_rounds_remaining: u32,
    cegar_emitted_lemmas: DetHashSet<TermId>,
    array_ext_shadow: ArrayExtShadow,
    in_nested_array_residue_probe: bool,
    residue_probe_failures: u32,
    mod_div_or_branch_rescue_depth: u8,
    proof_problem_assertion_provenance: Option<ProofProblemAssertionProvenance>,
    last_proof_rebuild_originals: Vec<TermId>,
    last_proof_raw_original_assertions: Vec<TermId>,
    last_proof_expanded_let_sources: Vec<(TermId, usize, String)>,
    last_proof_decline: Option<ProofDeclineMechanism>,
}

impl LaneLatches {
    /// Take the TAKEN group (leaving the primary-dispatch slate) and copy
    /// the KEPT group.
    fn take(executor: &mut Executor) -> Self {
        Self {
            sat_validated_by_mod_div_or_branch: std::mem::replace(
                &mut executor.sat_validated_by_mod_div_or_branch,
                false,
            ),
            read_pin_repair_done: std::mem::replace(&mut executor.read_pin_repair_done, false),
            nested_array_row_reduction_unsat: std::mem::replace(
                &mut executor.nested_array_row_reduction_unsat,
                false,
            ),
            last_degrade_was_datatype_array: std::mem::replace(
                &mut executor.last_degrade_was_datatype_array,
                false,
            ),
            last_bv_drat_self_cert: std::mem::replace(&mut executor.last_bv_drat_self_cert, false),
            uflia_congruence_lane: std::mem::replace(&mut executor.uflia_congruence_lane, false),
            uflia_congruence_gate_rejected: std::mem::replace(
                &mut executor.uflia_congruence_gate_rejected,
                false,
            ),
            uflia_congruence_retry_done: std::mem::replace(
                &mut executor.uflia_congruence_retry_done,
                false,
            ),
            uflia_model_repair_done: std::mem::replace(
                &mut executor.uflia_model_repair_done,
                false,
            ),
            qfax_retry_done: std::mem::replace(&mut executor.qfax_retry_done, false),
            qfax_refinement_clause: executor.qfax_refinement_clause.take(),
            last_rejected_array_assertion: executor.last_rejected_array_assertion.take(),
            unrepaired_model_candidate: executor.unrepaired_model_candidate.take(),
            uflia_repair_candidates: std::mem::take(&mut executor.uflia_repair_candidates),
            uflia_repair_conflict_tables: std::mem::take(
                &mut executor.uflia_repair_conflict_tables,
            ),
            recorded_var_substitutions: std::mem::take(&mut executor.recorded_var_substitutions),
            row_seeded_terms: std::mem::take(&mut executor.row_seeded_terms),
            array_axiom_scope: executor.array_axiom_scope.take(),
            dt_pre_lift_assertions: std::mem::take(&mut executor.dt_pre_lift_assertions),
            dt_lazy_splits: executor.dt_lazy_splits.take(),
            injected_axiom_theory_kinds: std::mem::take(&mut executor.injected_axiom_theory_kinds),
            last_assumptions: executor.last_assumptions.clone(),
            last_core_term_to_name: executor.last_core_term_to_name.clone(),
            named_assert_rewrites: executor.named_assert_rewrites.clone(),
            original_problem_had_quantifiers: executor.original_problem_had_quantifiers,
            defer_model_validation: executor.defer_model_validation,
            skip_model_eval: executor.skip_model_eval,
            dt_array_injectivity_gate_bypass: executor.dt_array_injectivity_gate_bypass,
            cegar_pending_lemma: executor.cegar_pending_lemma,
            cegar_rounds_remaining: executor.cegar_rounds_remaining,
            cegar_emitted_lemmas: executor.cegar_emitted_lemmas.clone(),
            array_ext_shadow: executor.array_ext_shadow.clone(),
            in_nested_array_residue_probe: executor.in_nested_array_residue_probe,
            residue_probe_failures: executor.residue_probe_failures,
            mod_div_or_branch_rescue_depth: executor.mod_div_or_branch_rescue_depth,
            proof_problem_assertion_provenance: executor.proof_problem_assertion_provenance.clone(),
            last_proof_rebuild_originals: executor.last_proof_rebuild_originals.clone(),
            last_proof_raw_original_assertions: executor.last_proof_raw_original_assertions.clone(),
            last_proof_expanded_let_sources: executor.last_proof_expanded_let_sources.clone(),
            last_proof_decline: executor.last_proof_decline,
        }
    }

    /// Put every field back verbatim.
    fn restore(self, executor: &mut Executor) {
        executor.sat_validated_by_mod_div_or_branch = self.sat_validated_by_mod_div_or_branch;
        executor.read_pin_repair_done = self.read_pin_repair_done;
        executor.nested_array_row_reduction_unsat = self.nested_array_row_reduction_unsat;
        executor.last_degrade_was_datatype_array = self.last_degrade_was_datatype_array;
        executor.last_bv_drat_self_cert = self.last_bv_drat_self_cert;
        executor.uflia_congruence_lane = self.uflia_congruence_lane;
        executor.uflia_congruence_gate_rejected = self.uflia_congruence_gate_rejected;
        executor.uflia_congruence_retry_done = self.uflia_congruence_retry_done;
        executor.uflia_model_repair_done = self.uflia_model_repair_done;
        executor.qfax_retry_done = self.qfax_retry_done;
        executor.qfax_refinement_clause = self.qfax_refinement_clause;
        executor.last_rejected_array_assertion = self.last_rejected_array_assertion;
        executor.unrepaired_model_candidate = self.unrepaired_model_candidate;
        executor.uflia_repair_candidates = self.uflia_repair_candidates;
        executor.uflia_repair_conflict_tables = self.uflia_repair_conflict_tables;
        executor.recorded_var_substitutions = self.recorded_var_substitutions;
        executor.row_seeded_terms = self.row_seeded_terms;
        executor.array_axiom_scope = self.array_axiom_scope;
        executor.dt_pre_lift_assertions = self.dt_pre_lift_assertions;
        executor.dt_lazy_splits = self.dt_lazy_splits;
        executor.injected_axiom_theory_kinds = self.injected_axiom_theory_kinds;
        executor.last_assumptions = self.last_assumptions;
        executor.last_core_term_to_name = self.last_core_term_to_name;
        executor.named_assert_rewrites = self.named_assert_rewrites;
        executor.original_problem_had_quantifiers = self.original_problem_had_quantifiers;
        executor.defer_model_validation = self.defer_model_validation;
        executor.skip_model_eval = self.skip_model_eval;
        executor.dt_array_injectivity_gate_bypass = self.dt_array_injectivity_gate_bypass;
        executor.cegar_pending_lemma = self.cegar_pending_lemma;
        executor.cegar_rounds_remaining = self.cegar_rounds_remaining;
        executor.cegar_emitted_lemmas = self.cegar_emitted_lemmas;
        executor.array_ext_shadow = self.array_ext_shadow;
        executor.in_nested_array_residue_probe = self.in_nested_array_residue_probe;
        executor.residue_probe_failures = self.residue_probe_failures;
        executor.mod_div_or_branch_rescue_depth = self.mod_div_or_branch_rescue_depth;
        executor.proof_problem_assertion_provenance = self.proof_problem_assertion_provenance;
        executor.last_proof_rebuild_originals = self.last_proof_rebuild_originals;
        executor.last_proof_raw_original_assertions = self.last_proof_raw_original_assertions;
        executor.last_proof_expanded_let_sources = self.last_proof_expanded_let_sources;
        executor.last_proof_decline = self.last_proof_decline;
    }
}

impl PredecessorOutputs {
    /// Move every output out of `executor`, leaving the empty slate a primary
    /// dispatch starts on.
    fn take(executor: &mut Executor) -> Self {
        Self {
            last_result: executor.last_result.take(),
            last_unknown_reason: executor.last_unknown_reason.take(),
            last_unknown_origin: executor.last_unknown_origin.take(),
            pending_sat_unknown_reason: executor.pending_sat_unknown_reason.take(),
            last_model: executor.last_model.take(),
            last_model_validated: std::mem::replace(&mut executor.last_model_validated, false),
            last_validation_stats: executor.last_validation_stats.take(),
            last_sat_certificate: executor.last_sat_certificate.take(),
            model_validation_delegated_assertions: std::mem::take(
                &mut executor.model_validation_delegated_assertions,
            ),
            dt_solver_added_axiom_terms: std::mem::take(&mut executor.dt_solver_added_axiom_terms),
            nra_algebraic_model: std::mem::take(&mut executor.nra_algebraic_model),
            dt_theory_model: executor.dt_theory_model.take(),
            dt_validation_wants_egraph: std::mem::replace(
                &mut executor.dt_validation_wants_egraph,
                false,
            ),
            dt_egraph_assignment: executor.dt_egraph_assignment.take(),
            last_negations: executor.last_negations.take(),
            last_unsat_certificate: executor.last_unsat_certificate.take(),
            last_assumption_core: executor.last_assumption_core.take(),
            last_proof: executor.last_proof.take(),
            last_finite_enum_pigeonhole: executor.last_finite_enum_pigeonhole.take(),
            last_checked_finite_enum_pigeonhole: executor
                .last_checked_finite_enum_pigeonhole
                .take(),
            last_unsat_proof_reconstruction_suppressed: std::mem::replace(
                &mut executor.last_unsat_proof_reconstruction_suppressed,
                false,
            ),
            last_lrat_certificate: executor.last_lrat_certificate.take(),
            last_proof_term_overrides: executor.last_proof_term_overrides.take(),
            last_proof_quality: executor.last_proof_quality.take(),
            last_clause_trace: executor.last_clause_trace.take(),
            last_checked_sat_refutation: executor.last_checked_sat_refutation.take(),
            last_var_to_term: executor.last_var_to_term.take(),
            last_trail_provenance: executor.last_trail_provenance.take(),
            last_clausification_proofs: executor.last_clausification_proofs.take(),
            last_original_clause_theory_proofs: executor.last_original_clause_theory_proofs.take(),
            proof_check_result: executor.proof_check_result.take(),
            proof_check_ok: std::mem::replace(&mut executor.proof_check_ok, false),
            quantified_model_confirmation: executor.quantified_model_confirmation.take(),
            dt_cert_grant_active: std::mem::replace(&mut executor.dt_cert_grant_active, false),
            dt_cert_query_grant: executor.dt_cert_query_grant.take(),
            finite_table_cert_grant_active: std::mem::replace(
                &mut executor.finite_table_cert_grant_active,
                false,
            ),
            const_interp_cert_grant_active: std::mem::replace(
                &mut executor.const_interp_cert_grant_active,
                false,
            ),
            mbqi_sat_cert_grant_active: std::mem::replace(
                &mut executor.mbqi_sat_cert_grant_active,
                false,
            ),
            mbqi_sat_cert_query_grant: executor.mbqi_sat_cert_query_grant.take(),
            cegqi_uf_recompletion_grant: executor.cegqi_uf_recompletion_grant.take(),
            bv_quantifier_full_domain_proof: std::mem::replace(
                &mut executor.bv_quantifier_full_domain_proof,
                false,
            ),
            bv_quantifier_full_domain_pending_evidence: executor
                .bv_quantifier_full_domain_pending_evidence
                .take(),
            bv_quantifier_full_domain_query_grant: executor
                .bv_quantifier_full_domain_query_grant
                .take(),
            finite_table_cert_witness_state: executor.finite_table_cert_witness_state.take(),
            const_interp_cert_witness_state: executor.const_interp_cert_witness_state.take(),
            latches: LaneLatches::take(executor),
        }
    }

    /// Move every output back, overwriting whatever the probe wrote.
    fn restore(self, executor: &mut Executor) {
        executor.last_result = self.last_result;
        executor.last_unknown_reason = self.last_unknown_reason;
        executor.last_unknown_origin = self.last_unknown_origin;
        executor.pending_sat_unknown_reason = self.pending_sat_unknown_reason;
        executor.last_model = self.last_model;
        executor.last_model_validated = self.last_model_validated;
        executor.last_validation_stats = self.last_validation_stats;
        executor.last_sat_certificate = self.last_sat_certificate;
        executor.model_validation_delegated_assertions = self.model_validation_delegated_assertions;
        executor.dt_solver_added_axiom_terms = self.dt_solver_added_axiom_terms;
        executor.nra_algebraic_model = self.nra_algebraic_model;
        executor.dt_theory_model = self.dt_theory_model;
        executor.dt_validation_wants_egraph = self.dt_validation_wants_egraph;
        executor
            .dt_egraph_assignment
            .replace(self.dt_egraph_assignment);
        executor.last_negations = self.last_negations;
        executor.last_unsat_certificate = self.last_unsat_certificate;
        executor.last_assumption_core = self.last_assumption_core;
        executor.last_proof = self.last_proof;
        executor.last_finite_enum_pigeonhole = self.last_finite_enum_pigeonhole;
        executor.last_checked_finite_enum_pigeonhole = self.last_checked_finite_enum_pigeonhole;
        executor.last_unsat_proof_reconstruction_suppressed =
            self.last_unsat_proof_reconstruction_suppressed;
        executor.last_lrat_certificate = self.last_lrat_certificate;
        executor.last_proof_term_overrides = self.last_proof_term_overrides;
        executor.last_proof_quality = self.last_proof_quality;
        executor.last_clause_trace = self.last_clause_trace;
        executor.last_checked_sat_refutation = self.last_checked_sat_refutation;
        executor.last_var_to_term = self.last_var_to_term;
        executor.last_trail_provenance = self.last_trail_provenance;
        executor.last_clausification_proofs = self.last_clausification_proofs;
        executor.last_original_clause_theory_proofs = self.last_original_clause_theory_proofs;
        executor.proof_check_result = self.proof_check_result;
        executor.proof_check_ok = self.proof_check_ok;
        executor.quantified_model_confirmation = self.quantified_model_confirmation;
        executor.dt_cert_grant_active = self.dt_cert_grant_active;
        executor.dt_cert_query_grant = self.dt_cert_query_grant;
        executor.finite_table_cert_grant_active = self.finite_table_cert_grant_active;
        executor.const_interp_cert_grant_active = self.const_interp_cert_grant_active;
        executor.mbqi_sat_cert_grant_active = self.mbqi_sat_cert_grant_active;
        executor.mbqi_sat_cert_query_grant = self.mbqi_sat_cert_query_grant;
        executor.cegqi_uf_recompletion_grant = self.cegqi_uf_recompletion_grant;
        executor.bv_quantifier_full_domain_proof = self.bv_quantifier_full_domain_proof;
        executor.bv_quantifier_full_domain_pending_evidence =
            self.bv_quantifier_full_domain_pending_evidence;
        executor.bv_quantifier_full_domain_query_grant = self.bv_quantifier_full_domain_query_grant;
        executor.finite_table_cert_witness_state = self.finite_table_cert_witness_state;
        executor.const_interp_cert_witness_state = self.const_interp_cert_witness_state;
        self.latches.restore(executor);
        // The evaluator memoises against the installed model's identity; the
        // probe's model was the installed one for the duration.
        crate::executor::model::eval_memo_clear();
    }
}

impl Executor {
    /// The snapshot stage 4 may later rebuild from, or `None` when the
    /// dispatched vector cannot satisfy [`ce_free_vector_invariant_holds`]
    /// whatever support axioms are added to it: a counterexample conjunct the
    /// pre-dispatch passes rewrote away (so the identity list is not exact for
    /// this vector, and nothing proves the rewritten form a consequence), or a
    /// surviving member that carries a quantifier or mentions a
    /// counterexample constant. Such a vector is a legitimate
    /// dispatch, not a rebuild defect, so it is not armed at all -- the same
    /// fail-closed `unknown` the invariant's decline gives in release, without
    /// tripping its `debug_assert!`, which stays the detector for the rebuild
    /// itself ([`Self::ce_free_vector`]).
    pub(in crate::executor) fn ce_free_resolve_snapshot(
        &self,
        pre_dispatch: &[TermId],
        ce_lemma_ids: &[TermId],
    ) -> Option<Vec<TermId>> {
        let conjuncts: DetHashSet<TermId> = ce_lemma_ids.iter().copied().collect();
        let survivors: Vec<TermId> = pre_dispatch
            .iter()
            .copied()
            .filter(|member| !conjuncts.contains(member))
            .collect();
        if ce_free_vector_invariant_holds(&self.ctx.terms, pre_dispatch, &conjuncts, &survivors) {
            return Some(pre_dispatch.to_vec());
        }
        if ay_core::misc_cli_flags().debug_cert {
            let present: DetHashSet<TermId> = pre_dispatch.iter().copied().collect();
            let rewritten = conjuncts.iter().filter(|&c| !present.contains(c)).count();
            let quantified = survivors
                .iter()
                .filter(|&&member| contains_quantifier(&self.ctx.terms, member))
                .count();
            eprintln!(
                "CERT/ce-free-resolve: not armed, the dispatched vector is not \
                 counterexample-separable (conjuncts rewritten away={rewritten}, \
                 quantified members={quantified})"
            );
        }
        None
    }

    /// The vector the probe solves: every member of `snapshot` except the
    /// counterexample `conjuncts`, verbatim and in order, then the support
    /// axioms recorded since the snapshot (instances of entailed universals
    /// from the interleaved rounds — consequences by the support set's
    /// write-side contract). A support axiom that carries a quantifier, or
    /// that mentions a counterexample constant, is dropped rather than
    /// solved: the primary dispatch never saw a quantified member either, and
    /// a CE-mentioning one is exactly what
    /// [`ce_free_vector_invariant_holds`] refuses at the point of
    /// consumption. Both drops only SHRINK the re-solved vector, so an UNSAT
    /// of it is still an UNSAT of the authored problem. Returns the vector
    /// with the number of conjuncts dropped and support axioms added.
    fn ce_free_vector(
        &self,
        snapshot: &[TermId],
        conjuncts: &DetHashSet<TermId>,
    ) -> (Vec<TermId>, usize, usize) {
        let mut vector: Vec<TermId> = snapshot
            .iter()
            .copied()
            .filter(|member| !conjuncts.contains(member))
            .collect();
        let dropped = snapshot.len() - vector.len();
        let mut present: DetHashSet<TermId> = vector.iter().copied().collect();
        let mut support_added = 0usize;
        // One scan budget for the whole support set, as
        // `ce_free_vector_invariant_holds` keeps one for the whole vector, so
        // a pathological support set declines members instead of paying an
        // unbounded walk per root.
        let mut ce_scan_work = 0usize;
        let mut ce_scan_seen: DetHashSet<TermId> = DetHashSet::default();
        for lit in &self.active_support_axioms {
            let term = lit.term;
            if !lit.value
                || present.contains(&term)
                || conjuncts.contains(&term)
                || contains_quantifier(&self.ctx.terms, term)
            {
                continue;
            }
            // The invariant's THIRD per-member clause, mirrored here; the two
            // above it already were. An instance E-matched AT the
            // counterexample constant is the ordinary product of a CEGQI
            // round and a legitimate `active_support_axioms` member — its
            // write-side contract (`push_active_support_axiom`) asks only for
            // a ground instance of an unconditionally asserted universal, and
            // the set's other two consumers read it in the CE-augmented
            // context where those constants are meaningful. Only THIS
            // consumer needs CE-freeness, so only this producer may filter
            // for it. Appending such a member made
            // `ce_free_vector_invariant_holds` fail at the point of
            // consumption, which panics its `debug_assert!` in debug/test
            // builds and silently declines stage 4 for the whole class in
            // release. Dropping the member is sound for the same reason
            // dropping a quantified one is: the re-solved vector only
            // SHRINKS, and an UNSAT of a subset of the consequences is an
            // UNSAT of the problem.
            //
            // `ce_scan_seen` is a clean-subterm cache that is only valid
            // after a walk that COMPLETED. `mentions_counterexample` returns
            // the moment it meets a counterexample variable, and again on the
            // budget exit, leaving nodes marked whose children it never
            // visited. The invariant never reuses it (it returns `false` on
            // the spot); this loop continues, so the cache is dropped on any
            // answer that is not `Some(false)`.
            if mentions_counterexample(&self.ctx.terms, term, &mut ce_scan_seen, &mut ce_scan_work)
                != Some(false)
            {
                ce_scan_seen.clear();
                continue;
            }
            present.insert(term);
            vector.push(term);
            support_added += 1;
        }
        (vector, dropped, support_added)
    }

    /// Stage 4, the last resort before `unknown`: re-solve the pre-dispatch
    /// vector without its counterexample conjuncts. Returns `Some(Ok(Unsat))`
    /// only when the re-solve refuted; every other outcome restores the
    /// predecessor state and returns `None` so the caller's fail-closed
    /// `unknown` stands. Never returns `Sat`. Called from exactly one site,
    /// [`Executor::fire_stashed_ce_free_resolve`], which `check_sat_guarded`
    /// calls after every verdict-producing arm of the solve -- the loop's own
    /// and the five executor-level passes behind it -- has declined.
    pub(super) fn try_ce_free_resolve(
        &mut self,
        snapshot: Option<&[TermId]>,
        ce_lemma_ids: &[TermId],
        category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        let trace = ay_core::misc_cli_flags().debug_cert;
        if !crate::quant_unit_authority::quantifier_ce_free_resolve_enabled() {
            return None;
        }
        let snapshot = snapshot?;
        if ce_lemma_ids.is_empty() || snapshot.is_empty() {
            return None;
        }
        if self.should_abort_theory_loop() {
            return None;
        }
        let conjuncts: DetHashSet<TermId> = ce_lemma_ids.iter().copied().collect();
        let (vector, dropped, support_added) = self.ce_free_vector(snapshot, &conjuncts);

        // THE INVARIANT, at the point of consumption.
        let holds = ce_free_vector_invariant_holds(&self.ctx.terms, snapshot, &conjuncts, &vector);
        debug_assert!(
            holds,
            "BUG (#quantifier-ce-free-resolve): the rebuilt vector violates the counterexample-free invariant"
        );
        if !holds {
            if trace {
                eprintln!("CERT/ce-free-resolve: declined, invariant does not hold");
            }
            return None;
        }
        if trace {
            eprintln!(
                "CERT/ce-free-resolve: re-solving dropped={dropped} support_added={support_added} total={}",
                vector.len()
            );
        }
        self.cegqi_ce_free_resolves += 1;

        // Live re-solve, the same way a refinement round re-solves. The
        // predecessor's outputs are moved out so the lane starts on the slate
        // a primary dispatch starts on, and so a non-refuting outcome can put
        // every one of them back — restore, don't clear (module docs).
        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, vector);
        let predecessor = PredecessorOutputs::take(self);
        // THE WINDOW, structural at the probe for every category: a fresh
        // incremental theory/BV state, so the lane encodes exactly this
        // vector and not the primary dispatch's counterexample hypothesis
        // ("The window" in the module documentation).
        let probe_started_at = std::time::Instant::now();
        let outcome =
            self.with_isolated_incremental_state(None, |probe| probe.solve_for_category(category));
        // Cumulative like the two counters: the price of a non-refuting probe
        // is its own wall, and nothing else -- it is the last thing the loop
        // runs, so no certificate is waiting behind it.
        self.add_phase_seconds(
            "time.quantifier.ce_free_resolve_seconds",
            probe_started_at.elapsed().as_secs_f64(),
        );
        let refuted =
            matches!(outcome, Ok(SolveResult::Unsat(_))) && !self.should_abort_theory_loop();
        if trace {
            let kind = match &outcome {
                Ok(SolveResult::Sat) => "Sat",
                Ok(SolveResult::Unsat(_)) => "Unsat",
                Ok(SolveResult::Unknown) => "Unknown",
                Err(_) => "Err",
            };
            eprintln!("CERT/ce-free-resolve: result={kind} refuted={refuted}");
        }
        if !refuted {
            // Restore the predecessor state exactly: the assertion vector,
            // then every solve output the probe could have written, moved
            // back over whatever the probe left. Nothing this probe produced
            // survives as a model, an authority, or proof state for anything.
            self.ctx.assertions = saved_assertions;
            predecessor.restore(self);
            // The one field not restored verbatim: a stop that fired DURING
            // the probe is the reason this query publishes. Otherwise the
            // predecessor's reason stands, defaulting to the CEGQI
            // fail-closed reason it was produced under.
            self.last_unknown_reason = if let Some(reason) = self.external_stop_reason() {
                Some(reason)
            } else {
                self.last_unknown_reason
                    .or(Some(UnknownReason::QuantifierCegqiIncomplete))
            };
            return None;
        }
        // Refuted: the probe's outputs stand and the predecessor's are
        // dropped. The CE-free refutation is classified with the artifacts
        // ITS lane produced, never with a stale one of the CE-augmented solve.
        drop(predecessor);
        self.cegqi_ce_free_refutations += 1;
        self.last_unknown_reason = None;
        Some(outcome)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{Sort, Symbol};

    /// A three-member vector: a ground fact, a counterexample conjunct over a
    /// registered `__ay_ce_` constant, and a genuine fact that mentions no
    /// counterexample.
    fn fixture() -> (TermStore, Vec<TermId>, TermId) {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x".to_string(), Sort::Int);
        let zero = terms.mk_int(0.into());
        let ground = terms.mk_app(Symbol::named("<"), [zero, x], Sort::Bool);
        let ce_name = terms.mk_internal_symbol("ce_x");
        assert!(ce_name.starts_with(COUNTEREXAMPLE_SYMBOL_PREFIX));
        let ce = terms.mk_var(ce_name, Sort::Int);
        let conjunct = terms.mk_app(Symbol::named("<"), [ce, zero], Sort::Bool);
        let p = terms.mk_var("p".to_string(), Sort::Bool);
        (terms, vec![ground, conjunct, p], conjunct)
    }

    #[test]
    fn invariant_holds_when_every_conjunct_is_dropped() {
        let (terms, source, conjunct) = fixture();
        let conjuncts: DetHashSet<TermId> = [conjunct].into_iter().collect();
        let vector: Vec<TermId> = source
            .iter()
            .copied()
            .filter(|m| !conjuncts.contains(m))
            .collect();
        assert_eq!(vector.len(), 2);
        assert!(ce_free_vector_invariant_holds(
            &terms, &source, &conjuncts, &vector
        ));
    }

    #[test]
    fn invariant_refuses_a_surviving_conjunct() {
        let (terms, source, conjunct) = fixture();
        let conjuncts: DetHashSet<TermId> = [conjunct].into_iter().collect();
        assert!(!ce_free_vector_invariant_holds(
            &terms, &source, &conjuncts, &source
        ));
    }

    #[test]
    fn invariant_refuses_a_counterexample_residue_under_a_new_identity() {
        let (mut terms, source, conjunct) = fixture();
        let conjuncts: DetHashSet<TermId> = [conjunct].into_iter().collect();
        let mut vector: Vec<TermId> = source
            .iter()
            .copied()
            .filter(|m| !conjuncts.contains(m))
            .collect();
        // The same counterexample constant, in a term the id list does not
        // name — the in-place-rewrite shape that retired identity filtering.
        let TermData::App(_, args) = terms.get(conjunct).clone() else {
            panic!("fixture conjunct is an application");
        };
        let one = terms.mk_int(1.into());
        let residue = terms.mk_app(Symbol::named("<"), [args[0], one], Sort::Bool);
        vector.push(residue);
        assert!(!ce_free_vector_invariant_holds(
            &terms, &source, &conjuncts, &vector
        ));
    }

    #[test]
    fn invariant_refuses_a_conjunct_the_source_never_held() {
        let (mut terms, source, conjunct) = fixture();
        let q = terms.mk_var("q".to_string(), Sort::Bool);
        let conjuncts: DetHashSet<TermId> = [conjunct, q].into_iter().collect();
        let vector: Vec<TermId> = source
            .iter()
            .copied()
            .filter(|m| !conjuncts.contains(m))
            .collect();
        assert!(!ce_free_vector_invariant_holds(
            &terms, &source, &conjuncts, &vector
        ));
    }

    #[test]
    fn invariant_refuses_a_quantified_member() {
        let (mut terms, source, conjunct) = fixture();
        let conjuncts: DetHashSet<TermId> = [conjunct].into_iter().collect();
        let mut vector: Vec<TermId> = source
            .iter()
            .copied()
            .filter(|m| !conjuncts.contains(m))
            .collect();
        let y = terms.mk_var("y".to_string(), Sort::Int);
        let zero = terms.mk_int(0.into());
        let body = terms.mk_app(Symbol::named("<"), [zero, y], Sort::Bool);
        let forall = terms.mk_forall(vec![("y".to_string(), Sort::Int)], body);
        vector.push(forall);
        assert!(!ce_free_vector_invariant_holds(
            &terms, &source, &conjuncts, &vector
        ));
    }
}
