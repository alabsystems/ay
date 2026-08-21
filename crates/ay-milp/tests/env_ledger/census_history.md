# Environment-ledger census history

This chronology was moved out of `the_census_matches_the_survey` so the
executable invariant remains readable. The assertions still live in
`census_history.rs`; this file preserves the rationale for each census change.

Regression guard on the two numbers the debt triage rests on: if either
moves, the triage needs re-reading, not silently updating.

325 -> 332 (2026-07-26, separation-screen merge). The tripwire fired on
its first real merge and caught seven unregistered names, which is what
it is for. Re-read rather than bumped: all seven come from the c-MIR /
strong-CG violation screen and its measurement scaffolding, and each was
bucketed individually --
  AY_MILP_NO_SEP_SCREEN        KillSwitch  (the A/B arm for the screen)
  AY_MILP_SEP_SCREEN_AUDIT     Diagnostic
  AY_MILP_SEP_SCREEN_EXPLAIN   Diagnostic
  AY_MILP_SEPSTAT / AY_SEPSTAT Diagnostic  (separation census dump)
  AY_MILP_ALLOCSTAT / AY_ALLOCSTAT Diagnostic (allocation census dump)
No name was retired and the dead count is unchanged, so the triage's
conclusion (nothing deletable without losing a journal arm) still holds.

332 -> 337, every name re-read rather than the count bumped:
  AY_MILP_SETPART_SHARE   Arm         restores the set-partition constructor's old
                                      pure-fraction-of-the-time-limit ceiling
  AY_MILP_COND_TIGHTEN    Arm         opt-in for conditional (probing) coefficient
                                      tightening (`tighten_coefficients_conditional`)
  AY_MILP_NO_COND_SCOUT   KillSwitch  its float advice lane's A/B arm
  AY_MILP_PREFIX_COLS     Product     PRE-EXISTING GAP, not new: examples/milp_profile.rs
                                      has read it since the shared/family profile modes
                                      landed and it was never registered
  AY_MILP_PREFIX_WORKERS  Diagnostic  same profiler's worker count, same pre-existing gap
Nothing retired and the dead count is unchanged, so the triage's conclusion --
that nothing is deletable without losing a journal arm -- still holds.
337 -> 338: `AY_MILP_NO_COND_TIGHTEN`, the kill switch added when conditional
(probing) coefficient tightening was promoted to a DEFAULT. Per the repo's own
rule, a shipped optimisation keeps an A/B arm: the NO_ switch restores the prior
behaviour byte-identically.
338 -> 340, both from the Aardal-Hurkens-Lenstra kernel reformulation, each re-read
rather than the count bumped:
  AY_MILP_NO_KERNEL_REFORM   KillSwitch  the A/B arm for the reformulation. Per the
                                         repo's rule a shipped reduction keeps its
                                         arm, and this one is load-bearing: the
                                         reformulation is the difference between ej
                                         proving in 5 nodes and not proving at all,
                                         so an arm that restores the old behaviour is
                                         exactly what a regression hunt would need.
  AY_MILP_KERNEL_SCAN_DIR    Diagnostic  points the gate's corpus census at a model
                                         directory, so the gate's real firing rate is
                                         a MEASUREMENT rather than an assertion. The
                                         census self-skips when unset, so it is inert
                                         in CI.
Nothing retired; the dead count is unchanged, so the triage's conclusion still holds.
340 -> 341: `AY_MILP_CUT_FRAC_PENALTY` (Arm), the W2 fractionality-penalised cut rank
from the development design notes. It is registered as an ARM and not
as tuning because it was MEASURED LOSING and ships default-off: the value of the name
is that the negative result stays re-checkable. `0` (the default) is bit-identical to
the pre-W2 depth rank, so it costs the default path nothing.
341 -> 342: `AY_MILP_ITER_LEDGER` (Diagnostic), the per-PHASE iteration ledger.
Registered rather than the count bumped silently, and it is a genuinely new
measurement surface rather than an arm: `AY_MILP_ITER_PROFILE` normalises every
figure it prints BY PIVOT and so can only answer what one pivot costs, while the
measured LP gap is 4.87x too many pivots. This name turns on the `ITERLEDGER`
line, which attributes iterations AND solves to root LP / root cut re-solve /
node / cold retry / node cut / strong branching / each heuristic / in-solve
recovery, split dual vs primal-phase-I vs primal-phase-II. It counts only —
never time — so the line is byte-identical on an idle and a contended box, and
it self-checks: the reported `unattributed` residual against `stats::work()` is
0 exactly when the partition is still exhaustive.
342 -> 343: `AY_MILP_CUT_WARM` (Arm), the warm-started root cut round. The ledger
located the work it removes: the `root-cut` phase reports 0.0% DUAL pivots on all 60
measured instances and ~50/50 primal phase-I / phase-II — the cold root LP's own
mixture — because every round rebuilds the model and crashes a fresh basis, at a
median 0.99x the price of a full cold root solve. Adding rows to an optimal LP is the
textbook dual-simplex warm start, and the mapped basis is dual feasible with no
tolerance in the argument (see `cut_round_warm_basis`). It is an ARM and not tuning
because the loop separates FROM the vertex each round's LP returns: a different but
equally optimal vertex yields different cuts, so the whole measured root trajectory
moves. Default-off keeps that trajectory byte-identical.
343 -> 344: `AY_MILP_RINS_DRYCAP` (Arm), the onset of the WIDE-gap dry-ladder backoff.
The narrow-gap arm has had a multiplicative dry-pull backoff since mas76; the wide-gap
arm had none, and the 38-instance root-closure ledger priced that hole at 27.5M of 97.3M
simplex iterations for 59 incumbents — the whole of opt1217's 6.4M-iteration RINS spend
(67.9% of that instance) landing on an incumbent that was ALREADY OPTIMAL at the root.
Registered as an ARM and not as Tuning for the same reason `AY_MILP_CUT_FRAC_PENALTY` is:
it was MEASURED LOSING and ships default-off, and the value of the name is that the
negative stays re-checkable. `=7` is the measured arm; the default and `=0` are the tuned
schedule bit-for-bit. What it bought is the finding — 18.7% of the RINS lane recovered,
+6.6% pooled nodes (opt1217 +53%), and the dual bound bit-identical on both arms, 0
verdicts gained anywhere, and two reproducible primal losses (mas74, timtab1).
See `rins_drycap` in bab.rs.
344 -> 345: `AY_MILP_NO_TREE_BOUND_OUTCOME` (KillSwitch), the A/B arm for the
no-incumbent dual-bound report. `solve_milp_in` has always computed the tree's
rigorous global bound and has always shipped it on the `Feasible` (incumbent)
arm; on the NO-incumbent arms it computed the identical number and then threw it
away, reporting `Unknown{Timeout}`. Now it reports `Outcome::Bound{rigorous:true}`.
Registered as a kill switch, not an arm, because the change is a shipped DEFAULT
and the repo's rule is that a shipped default keeps an arm that restores the prior
behaviour byte-identically -- which this one does exactly, since the switch is read
only at outcome-construction time and cannot touch the search. It is also the arm
the measurement rests on: one binary, two runs, no rebuild between them.
345 -> 346: `AY_MILP_NO_ROOT_FLOOR` (KillSwitch), the A/B arm for flooring the
root node with the rigorous bound its own root LP certifies. The root node
carried no bound of any kind ("keep this construction byte-for-byte"), and since
the root is the ancestor of every node, the `NO_BOUND_COVER` entry below had
nothing to carry down: `tree_bound` forfeits outright when one open node has no
inherited bound, so an interrupt AT the root -- including every instance whose
root LP eats the whole budget, because the deadline break pushes that node back
onto the open set -- threw the bound away. The sibling
`shared_binary_prefix_frontier` has always derived exactly this number from
exactly this dual. It is written to `Node::cover`, NOT to `bound`, and that is
load-bearing: the first cut of this change wrote `bound` and MOVED THE SEARCH --
neos-787933 went 2643 nodes / incumbent 128 to 936 nodes / incumbent 149 at the
same 60s budget, a worse answer bought with a reporting fix. In `cover` the
trajectory is byte-identical and the bound still reaches the claim.
346 -> 347: `AY_MILP_NO_BOUND_COVER` (KillSwitch), the A/B arm for the node
BOUND COVER. The two entries above make the tree's global dual bound reportable;
this one is why there was usually no bound there to report. A node's `bound` is
re-derived from its own LP duals and can decline, and both children were then
pushed with `bound: None` -- one such node anywhere in the open set forfeits the
whole tree's claim. Measured over 216 MIPLIB mid/large at 60s: 166 unproved runs
held NO rigorous bound, 165 of them with nodes already explored. 50v-10 threw
away a 9301-node tree because 4100 of its nodes had declined their own bound.
`Node::cover` carries the nearest ancestor bound down those chains, which is
rigorous because a child's box is a SUBSET of its parent's -- the same argument
the rim's `lost_bank` already runs on. Registered as a kill switch because the
fix is a shipped default; and unlike `NO_ROOT_FLOOR` it CANNOT move the tree,
since `cover` is read only by the dual-bound claim and never by the heap `Ord`,
the cutoff prune, the plateau tracker or the pseudocosts. That is what makes the
one-binary A/B a measurement of REPORTING with the search held fixed.
347 -> 350: the COLD-ROOT LU BAND (`FloatLp::cold_root_lu`) —
`AY_MILP_NO_COLD_LU` (KillSwitch) plus `AY_MILP_COLD_LU_ROWS` and
`AY_MILP_COLD_LU_MAX_ROWS` (Tuning, the window's floor and ceiling).
`plain_cold` pins the VERTEX-SEEDING cold root LP to the product-form eta
file, and on tall models that pin was the whole defect: every WARM node
re-solve already ran on the Forrest-Tomlin engine via `node_lu`, so the
cold root was the last solve paying O(m·nnz) eta rebuilds, and it was
paying 38-76% of its LP budget for them. Measured A/B against
`AY_MILP_NO_COLD_LU` over 61 pairs at 60s: 11 in-band models now finish a
root LP the eta lane cannot finish at all (peg-solitaire-a3 7,034
rebuilds/36.71s -> 66/0.70s, 41,732 -> 219,065 pivots; hypothyroid-k1's
root LP goes from Stopped to Optimal at -2902.852586), +7 verdicts / -1,
158,126 -> 88,116 eta rebuilds across the sweep. Registered as a kill
switch because it is a shipped DEFAULT and every number above is a
one-binary A/B against exactly this arm. The two row bounds are Tuning,
not Arm: 3,000 and 8,192 are a measured crossover (below 3,000 the FT
engine costs 1.4-2.7x wall and MOVES THE VERTEX; at 8,192 the code hands
the model to the w5/cifar regime, and above it `LuEngine::update`'s O(m)
sweeps merely replace the refactorisation wall), and they exist so the
follow-up experiment can move the window without a rebuild.
350 -> 351: `AY_MILP_FT_SPIKE` (KillSwitch), the arm selector for the
Forrest-Tomlin SPIKE BUILD in `LuEngine::update_nz`. The dense build
pays a fixed ~7 full `0..m` sweeps per update no matter how few
nonzeros the FTRAN has, which measures as a FLAT 5.2-5.9 ns/row floor
invariant over a 35x range of m (4,744 -> 168,336) -- the signature of
nothing but the sweeps. The sparse arm derives the spike's support from
the caller's pattern via a one-step closure over `ucols`, and the two
arms leave BYTE-IDENTICAL engine state (asserted directly, at every
step of a 200-update chain, by `long_sparse_spike_chain_matches_fresh_factor`),
so `dense` is the exact pre-change path and this is a pure one-binary
A/B on cost. It is a kill switch and not Tuning because the sparse arm
is the shipped default and every timing below is measured against
`AY_MILP_FT_SPIKE=dense`.
351 -> 352: `AY_MILP_DUAL_CUTOFF` (Arm), an EXTERNAL dual bound delivered as a
CUTOFF instead of as a ROW. Registered rather than the count bumped because it is
the control the row-form experiment lacked. Handing ay Gurobi's own root bound as a
ROW closed the median root deficit (5.046% -> 0.000% over 45 instances) and still
made the tree 1.720x bigger and proved 5 FEWER instances -- and the vacuous-row
control, a bound exactly tight at ay's own root LP, cost 1.209x of that by itself,
which means the ROW and not the NUMBER was doing much of the damage. A row moves the
LP's optimal vertex and every branching decision downstream; this name delivers the
identical number with no row, so the root LP bound, the cut-round bounds and the
whole node trajectory stay bit-identical to the unset arm right up to the moment the
incumbent reaches the injected bound. It is an ARM, not Product: nothing in the
crate can validate the injected number, and an invalid one silently deletes the
optimum (the row form fails loudly instead, by making the LP infeasible). Unset --
the default -- is bit-identical to a build without it.
352 -> 353: `AY_MILP_COLD_LU_ETA_REBUILDS` (Arm), the MEASURED companion to the
cold-root LU band. Registered rather than the count bumped because it answers a
question the band's own profile raised and could not settle. The band is keyed on
`m`, and `m` does not predict what the Forrest-Tomlin engine costs: over 39 corpus
models with deterministic `LU_FTRAN_REACH`/`LUFACT` counters, Spearman against ns
per update per row is 0.841 for SPIKE DENSITY, 0.598 for factor fill and -0.045 for
`m` -- and `m` vs spike density is -0.429, i.e. bigger models have SPARSER spikes.
uccase12 (m=121,161, spike 0.0004) costs 0.56 ns/update/row against ex9's 39.50
(m=40,962, spike 0.57): 70x more per row at a third of the rows, so the ceiling
excludes the cheapest models in the corpus and the floor excludes the downstream optimization consumer's entire
sub-3,000-row corpus.

It is keyed on the ETA BILL rather than on that better predictor for a reason that
is structural, not a preference. Spike density is a property of `B^-1` UNDER the FT
engine -- `LU_FTRAN_REACH` only exists once the LU lane runs -- so a solve on the
eta file cannot read the very quantity that predicts what leaving it would cost.
Statically it is no better: out-of-sample over 1,000 random 2/3-1/3 splits, the best
MPS-derived predictor of spike density scores mean R2 = +0.018 (raw density) and `m`
alone scores -0.090, worse than predicting the corpus mean; even a Gilbert-Peierls
symbolic FTRAN reach computed on the greedy triangular CRASH basis -- this quantity
with the crash basis substituted for the optimal one -- classifies dense-vs-sparse
at AUC 0.621, BELOW the plain ratio `n/m` at 0.755. The crash basis does not carry
the optimal basis's fill, which is the negative result that forces the trigger to be
a measured one.

So it counts what the band was actually buying. The band's win came from the
O(m*nnz) refactorisation bill it removes (in-band 89,220 -> 21,264 eta rebuilds,
861.2s -> 99.3s of REFAC), and rebuilds are countable while they are being paid.
The unit is a plain COUNT, and that is a result rather than a shortcut: THREE cost
units were tried against the eta-arm census first and all three rank the corpus
backwards. `m * nnz` charges aflow40b 19x less than drayage-100-23 for 1.35x more
time; measured fill `entries + m` charges uccase12 11,200 for a 0.17s rebuild and
ex9 605,154 -- 54x more -- for 0.05s, 3.4x FASTER; `m` alone spans 0.12 vs 13.7
us/row between drayage and nursesched-sprint02 at nearly equal m. What a rebuild
costs is a property of the BASIS, recoverable only from the clock, and the clock is
disqualified because this decision moves the vertex and a load-dependent trigger
would make node counts irreproducible. The count needs no cost model: it is the
MULTIPLIER on a per-event difference measured favourable on 13 of 14 paired models
(median 9.97x, min 0.82x). A row floor survives, but it is the crate's existing
`tall_lu()` rather than a new number -- a pure count would promote gt2 (m=29) and
air05 (m=426), which is exactly what the band's floor-of-0 experiment measured as a
lost proof and two lost OPTIMALs.

The switch fires only inside `refactorize`, where `B^-1` is being re-derived from
`self.basis` anyway and the two representations never compose
(`apply_inverse_parts` short-circuits on an installed engine), so it costs the
DIFFERENCE between the two rebuild kinds rather than a rebuild on top of one.
DEFAULT 0 = OFF, so unset is bit-identical to a build without it; it shares
`AY_MILP_NO_COLD_LU` rather than adding a second kill switch because it moves the
seeding vertex by exactly the mechanism that band already accepted.

IT IS DEFAULT-OFF BECAUSE IT WAS MEASURED AND DID NOT WIN, which is the reason the
name is registered at all -- an arm nobody can re-run is a result nobody can check.
52 models, 60s, one frozen binary, both arms: over the 18 promoted models eta
rebuilds fall 29,338 -> 2,383 (12.3x) and REFAC time 271.3s -> 59.7s, and one root
LP goes Stopped -> Optimal. The verdict ledger is still NET NEGATIVE, +3 / -6, with
ZERO ref_obj disagreements -- the losses are tightness and throughput, never a wrong
answer. The cause is the finding the knob was built on, now visible at the decision:
the promotion trades a rebuild bill for an FT UPDATE bill whose size is set by spike
density, and the trigger cannot see spike density. In the promoted arm uccase12 runs
0.1% dense at 71,690 ns/update while ex9 runs 67.6% at 4,787,213 -- 4.8ms per update
-- and the dense-spike models' partial root bounds get WORSE for the switch (ex9
7.459 -> 6.218, atlanta-ip 2522.74 -> 1998.49). Closing it needs the DEMOTION half,
which is the one direction where the predictor exists, because `LU_FTRAN_REACH` only
becomes readable once the LU lane is already running.
7 -> 10 dead, and this one was NOT a new name: it is three OLD names that the
hand-typed `read_sites` column had been hiding. `read_site_counts_are_derived`
now derives the column from the source, and on its first run 23 of 353 entries
disagreed. Three of them read NOTHING, so they were never live:
  AY_MILP_COND_TIGHTEN  was Arm         `presolve.rs` documents it as "kept as the
                                        explicit-on A/B arm" and no code reads it.
                                        Setting it measures the DEFAULT arm — the
                                        `AY_MILP_NO_CUTZ` defect, inside the ledger
                                        built to catch it. Nothing is lost by the
                                        re-bucket: conditional tightening ships ON
                                        and `AY_MILP_NO_COND_TIGHTEN` (live, 1 site)
                                        is its real arm.
  AY_ALLOCSTAT          was Diagnostic  only ever an OUTPUT LABEL, in
                                        `eprintln!("AY_ALLOCSTAT allocs=...")`.
  AY_SEPSTAT            was Diagnostic  same shape, in `sepstat.rs`'s dump lines.
                                        The live switch is `AY_MILP_SEPSTAT`.
Per the Dead-bucket policy the prose stays and only the claim of a read site goes.
The triage's conclusion is unchanged: nothing is deletable without losing an arm.
353 -> 354: `AY_ALLOW_UNKNOWN_ENV` (Product), the documented way through the
now-FATAL environment audit. The audit used to print a WARNING and continue,
which is not a guard inside a harness that emits hundreds of lines per
instance; it now refuses the run. A check with no escape hatch is a check
people delete, so the hatch is part of the change rather than a concession.
It reads INDIRECTLY (via the `ALLOW_UNKNOWN_ENV` const), so it is ROUTED.
354 -> 356: two KillSwitches, both A/B arms for reporting-only fixes to the
global dual bound. `AY_MILP_NO_TREE_FLOOR` restores the pre-fix
min-over-open-nodes (the tree's claim is now floored by the root's own
bound, which a min over re-derived node duals does not respect).
`AY_MILP_NO_RC_CAP_GUARD` restores reduced-cost caps that close an OPEN
column side at any magnitude at all — measured up to 5.8e20 on a model
whose largest bound is 673.5.
356 -> 357: `AY_MILP_IMPLIED_COL_BOUNDS`, the OPT-IN arm for the
implied-column-bound rescue in `safe_bound` — a column open on the side its
exact reduced cost charges asks the ROWS for a corner (exact rationals, one
pass, no write-back) instead of forfeiting the node's whole bound. Default
OFF: measured, it closes zero root declines and costs 2.6x node throughput.
357 -> 358: `AY_MILP_NO_CERT_DECOUPLE` (KillSwitch), the A/B arm for
DECOUPLING the root reductions from tree-certificate capture. The kernel
reformulation and duplicate-column dedup were gated on
`opts.tree_cert_leaves == 0` because neither one's reduced TREE lifts into the
caller's frame — and `SolveOpts` DEFAULTS that field to 256, so both
reductions were off on default options. The trade was one-sided by
construction: `tree_cert` exists on `Outcome::Infeasible` and on no other
variant, so every OPTIMAL / FEASIBLE / BOUND / UNKNOWN solve surrendered a
reduction for an artifact it could never receive. The reductions now run
unconditionally and the artifact is bought only where it is possible, by ONE
re-solve of the caller's own model (`bab::harvest_tree_cert_by_resolve`) — the
same move the symmetry lane has always made at its `Infeasible` exit.
Registered as a kill switch, not an arm, because the decoupling is a shipped
DEFAULT and the repo's rule is that a shipped default keeps an arm restoring
the prior behaviour byte-identically: with it set, both gates collapse back to
`tree_cert_leaves == 0` and the harvest becomes unreachable, so one name
restores the whole prior path rather than half of it.
358 -> 359: `AY_MILP_NO_MIR_GENINT` (KillSwitch), the A/B arm for NARROWING the
MIR-class self-gate (`cuts::mir_family_inert`) from all-INTEGRAL to all-BINARY.
Registered as a kill switch, not an arm, because the narrowing is a shipped DEFAULT
and the repo's rule is that a shipped default keeps an arm restoring the prior
behaviour byte-identically -- which this one does exactly: the switch is read once
per process into a `OnceLock` and simply swaps `is_integral()` back in for
`== ColKind::Binary`, so with it set every separation decision is the historical
one, INCLUDING the MIR class's per-round wall budget, which is scoped to the models the
narrowing admits. It is also the arm the measurement rests on -- one binary, two runs,
no rebuild between them -- and the measurement is large: haprp goes from a 300s BOUND
3666028.211734 at 640,876 nodes with NO INCUMBENT AT ALL to OPTIMAL 3673280.681685 in
63.2s at 357,624 nodes, on a root closure that moves 0% -> 96.2%. Serial root-closure
A/B over the 62 admitted instances: 16 BETTER, 0 WORSE, 30 same on the 46 non-large
members; 0 verdicts gained or lost and 0 soundness violations at a 30s solve budget.
359 -> 360: `AY_MILP_ADOPT_FT_MAX_ROWS` (Tuning). Not a new lever -- a name for
an EXISTING one. A gate audit found the FT-adoption row ceiling reading
`REFACTOR_TALL_ROWS` directly with no override, while its cold-root sibling has
`AY_MILP_COLD_LU_MAX_ROWS`. 106 of 379 corpus instances sit above that ceiling
and there was no way to run ANY of them with adoption on, so the ceiling's own
premise could not be checked even in principle. The DEFAULT IS UNCHANGED:
making a gate measurable and moving it are different acts, and re-tuning an
unmeasurable gate by guess is how the original size-gate defects were
introduced. Each top-level solve that actually reaches the excluded branch
is now charged once to the forgone-cost census.
360 -> 362: FEASIBILITY-MODE DETECTION — the objective-≡0 model class
(`Model::objective_is_identically_zero`) and its two consumers. One name per
behaviour, each in the bucket its DEFAULT earns:

  AY_MILP_NO_FEAS_CONFLICT  KillSwitch. The conflict levers, re-gated on the
    class instead of on SIZE, and SHIPPED ON. Nogood unit propagation and
    nogood-guided branching required 1,000+ LP rows or an assembled
    orbitope, propagation-conflict learning required the orbitope, and VSIDS
    was default-off although its own comment names this regime by name. All
    three arm on BIG models and go dark on SMALL ones — backwards for a
    class whose difficulty is tree SIZE at a few hundred rows and whose dual
    bound is permanently 0. Measured on 46 ny W1 captures at 30s, serial,
    one binary: nodes-to-proof over the 25 instances both arms decide fall
    112,124 -> 10,234 (10.96x), over the 15 UNSAT among them 111,778 ->
    9,888 (11.30x) and their wall 44.9s -> 23.7s, with zero verdict changes
    anywhere. A shipped default keeps an arm that restores the prior
    behaviour byte-identically, and this one does exactly that.

  AY_MILP_AUTO_MARGIN  Arm, DEFAULT OFF. The margin reframe's AUTO-DETECTED
    row. The `margin` module was written for this exact class ("a relational
    whole-net verifier emits an objective-≡0 FEASIBILITY MILP ... a single
    one-sided violation row") and was UNREACHABLE from a plain `check()`:
    `mark_margin_row`'s only non-test callers require the CALLER to name the
    row, so every model that arrives as a file — every ny W1 model — never
    saw it. Registered as an ARM and not a kill switch for the same reason
    `AY_MILP_CUT_FRAC_PENALTY` and `AY_MILP_RINS_DRYCAP` are: it was
    measured and it LOST, and the value of the name is that the negative
    stays re-checkable. Same 46 captures, same binary: 25/46 -> 22/46
    decided, sat roots 8/10 -> 10/10, unsat roots 2/13 -> 1/13, and 379 ->
    41,867 nodes over the commonly decided set. A margin objective is a
    PRIMAL driver, so it finds witnesses and cannot close the refutation ny
    actually wants. Unset is bit-identical to a build without it.

Neither can reach a model with a real objective, so off-class byte-identity
is by CONSTRUCTION rather than by a corpus sweep — the criterion `7b439b9b0`
records as the one that hid rout's 30/30 -> 0/30 regression for ten days.
The corpus sample and the four slow provers were re-measured regardless, the
latter as a proof RATE.
362 -> 364: DUAL FIXING BY LOCK COUNTING (`dualfix.rs`), the crate's first
reduction that is allowed to cut off feasible points. Two names, each
re-read rather than the count bumped:

  AY_MILP_NO_DUALFIX  KillSwitch. The A/B arm for the reduction, which
    ships ON for objective-≡0 models. Per the repo's rule a shipped default
    keeps an arm that restores the prior behaviour byte-identically, and
    this one does exactly that: the switch is read at the single entry
    point of `dualfix::dual_fix`, which returns `None`, which hands the
    caller's model on untouched. It is also the arm every measurement in
    the journal for this reduction rests on — one binary, two runs, no
    rebuild between them.

  AY_MILP_DUALFIX_ALL  Arm, DEFAULT OFF. Widens the reduction from
    objective-≡0 models to every model. An ARM and not tuning because what
    it trades is the ARTIFACT and not the speed: the reduction strips
    certificates, the `Infeasible` lane buys its tree back with one
    re-solve, and the OPTIMAL lane has nothing that buys a dual bound back.
    The rule itself is sound with an objective (the sign test is
    implemented, sense-aware, and covered by
    `the_objective_sign_test_is_read_in_the_models_sense` plus the 4,000-
    model brute-force campaign), so what the default encodes is evidence
    economics, not doubt about the algebra.

Off-class byte-identity is by CONSTRUCTION, not by a corpus sweep: a model
with a nonzero objective coefficient anywhere never reaches `dual_fix` at
all on default settings, so no bound moves and no work is done. That is the
criterion `7b439b9b0` records as the one that hid rout's 30/30 -> 0/30
regression, so the corpus sample and the slow provers were re-measured
anyway.
364 -> 369 (2026-08-01), five names, each named and bucketed:
  AY_MILP_BINARY_COMPLEMENT_SUB   Arm         binary-complement substitution
  AY_MILP_OBJECTIVE_SINGLETON_SUB Arm         objective-singleton substitution
  AY_MILP_AMO_MULTIWAY            Arm         default-off multiway AMO branching
  AY_MILP_HYBRID_PB_LP            Arm         hybrid PB/LP route selector
  AY_MILP_NO_STRUCTURE_ROUTE      KillSwitch  the A/B arm for the exact
                                              structure-recognition routes.
                                              Added deliberately: those routes
                                              had NO kill switch, so there was
                                              no way to measure what they cost
                                              or to pin a test on the native
                                              proof-producing lane they now
                                              claim first.
369 -> 371, both from the FILL-RATE TRIP (`Simplex::maybe_trip_bump_fill`),
which arms the Markowitz bump lane on MEASURED fill rather than on the
`AY_MILP_BUMP_LU_MIN` column count. The floor's premise -- "the crash-walk
bases (~160-column bumps, already near-zero-fill) keep the measured PFI path"
-- is falsified by arithmetic: the census charged >= 326 eta entries per bump
column on exactly that branch.
  (bump-fill-trip)        Arm         opt-in; DEFAULT OFF because the shipped
                                      predicate is known biased (it compares
                                      the bump against the singleton peel,
                                      which is fill-free BY SELECTION)
  AY_MILP_NO_FILL_TRIP    KillSwitch  restores the pure column floor
Both inert at the default, so the shipped lane is byte-identical.

372 -> 374, both from making the GMI basis factorization SPARSE, and both
re-read rather than the count bumped:

  AY_MILP_DENSE_GMI_LU    KillSwitch. Restores the DENSE `m × m` `Bᵀ` and
    `ExactLu`. A shipped default keeps an arm that restores the prior
    behaviour byte-identically, and this one does exactly that -- the switch
    rebuilds the same dense matrix from the same rows (last write wins, stored
    zeros included) and factors it with the untouched `ExactLu`. It is also the
    arm the whole claim rests on: "identical cuts, 43x less peak RSS at
    m=10765" is one binary, two runs, no rebuild between them. (43x is the
    figure in `certify.rs`'s measured table -- 3329 MB dense against 78 MB
    sparse on `decomp2`; an earlier draft of this note said 72x, which no
    measurement in the tree supports.)

  AY_MILP_GMI_CUT_TRACE   Diagnostic. Per-cut identity fingerprints
    (`sepstat::gmi_cut`). Deliberately NOT folded into `AY_MILP_TRACE`: the
    general trace's output volume is itself a cost, and it perturbs which A/B
    arm runs out of round budget first -- which is the exact confounder these
    lines exist to remove. Measured: on `bg512142` the dense arm separated 4
    cuts to the sparse arm's 8, and the 4 were hash-for-hash the first 4, so
    the whole-run digest disagreed where no cut did.

Nothing retired; the dead count is unchanged.

374 -> 375: AY_MILP_MIN_VIOLATION (Tuning). The measurement arm for the
cut-admission efficacy floor, added while adjudicating cause 6 of
the development design notes. It ships
DEFAULT-IDENTICAL (`unwrap_or(MIN_VIOLATION)`, one `OnceLock` read primed at
solve entry) and exists because the result it carries is NEGATIVE: over 101
instances the floor refuses 163 violated cuts of which only 3 clear the pool's
own DEPTH floor, and turning it off moves root closure on ZERO instances (one
is worse). A negative result is only re-checkable while its arm still exists,
which is this ledger's own stated reason for inventorying names rather than
purging them.
375 -> 376 (2026-08-02): `AY_MILP_COLD_DUAL_ALL`, a measurement arm that drops the
`wide_tall()` shape gate so the cold dual start is tried on square-ish models too.
It exists because the gate means `try_cold_dual` NEVER RUNS on the square corpus --
the corpus the headline LP numbers were measured on -- so the "5x too many simplex
steps" result never had the dual start in it. The arm is a MEASURED NEGATIVE at MIP
level (blend2 2.1s -> 8.7s, misc07 9.8s -> 12.4s), which is exactly why the name
stays: the negative is only re-checkable while its arm exists.
376 -> 377 (2026-08-02): `AY_MILP_CUT_SHADOW`, the PERTURBATION-MATCHED CUT
CONTROL. Re-read rather than bumped: it is an Arm, and it is the denominator the
whole cut record has been missing. Every cut arm on file is scored `nodes(cuts) /
nodes(no cuts)`, while this campaign's own controls put the cost of adding an
information-free ROW at 1.209x nodes and a pure vertex change at 1.122x -- larger
than most cut arms' reported effect. This name runs the shipped cut loop unchanged
and then replaces every row it installed with a row of the same shape and no
information (a non-negative combination of the model's own column bounds, tight at
the cut-free root vertex), so `nodes(cuts) / nodes(control)` is measurable at last.
`=slack` selects the weaker construction the report specified, kept because the
comparison between the two is what shows the binding property is load-bearing.
377 -> 378 (2026-08-03): `AY_MILP_PUMP_WORK_MULT`, the multiplier on the feasibility pump's
new budget cap. The pump's window was `ROOT_HEURISTIC_SHARE x PUMP_SHARE` = 18% of the
CALLER'S REMAINING WALL with no model term at all, so at a 120s limit it handed out 21.6s to
models whose whole heuristic appetite is under a second; `pump_window` now caps it at
`PUMP_WORK_MULT x root_lp`. The name exists because the multiplier is the one fitted number
in the rule and a re-sweep must be possible without a rebuild — the same reason
`AY_MILP_SETPART_SHARE` exists for the constructor's window. Measured at 3.0: gen
1.141 -> 0.567s, air03 5.958 -> 4.557s, mod010 2.140 -> 1.647s, 0 worse over 15 instances.
378 -> 379 (2026-08-05): `AY_MILP_NO_SHAPE_CPR`, the kill switch on the shape-gated
per-round cut budget. `AY_MILP_CUTS_PER_ROUND=8` was measured on 16 corpus instances with
BOTH arms seeded, and the sign separates cleanly on `cols/rows >= 4` -- the same predicate
`default_root_cut_eff_floor` already uses: narrow models sum -3.746s (qnet1 -2.053, qiu
-1.009, misc07 -0.665), wide models sum +2.645s (mas76 +1.994, khb05250 +0.546), with a 4x
margin between the classes (narrow tops out at 3.06, wide starts at 10.33). Applied
globally the knob is a WASH (-1.10s, one win cancelling one loss); gated it keeps the win
and declines the loss. The switch exists because the gate is a DEFAULT change and the
corpus guard needs a byte-identical way back to the flat four.
379 -> 278 (2026-08-12): batches B6-B11 of the env-flag retirement
(user directive: auto-on defaults + CLI opt-outs, stale env vars
deleted; the development design notes) deleted the read
sites for 101 names — mechanical constant conversions (B6/B7), the
milp_profile CLI-arg moves (B9), and the typed `EngineEconomics`
carriers (B11). A name with no read is not an arm: its measurements live in history,
while B12/B13's typed-carrier retirements survive in retired_env_names.txt.
B18 retired four reads; B19 auto-decided FLIP_NZ, folded LATTICE_THREADS into --threads, and moved OBBT_OUT to argv.
B20 moved more carriers to CLI; B22 retired 24 names (224 -> 200), restoring NODE_CUTS/DEVEX after teaching the audit their dict-literal setters.
200 -> 186 (2026-08-13): B25 — fourteen value knobs became their named
constants (the measurement arms live on as editable literals).
186 -> 188 (2026-08-13): reclaiming two stranded measurement fronts from
their worktrees. AY_MILP_DIVE_BACKTRACKS (Tuning, default 0 = inert) and
AY_MILP_ACENSUS (Diagnostic, inert without the counting allocator). Both
are registered rather than folded into literals because both are MEASURED
NEGATIVES whose value is that the negative stays re-checkable.
188 -> 192 (2026-08-13): the c-MIR complementation campaign, reclaimed.
  AY_MILP_MIR_KNAP / AY_MILP_NO_MIR_KNAP  Arm + KillSwitch — the knapsack-form
    complementation search. Ships OFF: it separates nothing on 16 of the 17
    corpus instances and displaces one cut on `gen`.
  AY_MILP_MIR_AGG_ROOT                    Arm — ships OFF: qnet1's root falls
    14,857.59 -> 14,805.06.
  AY_MILP_KNAP_DBG                        Diagnostic — per-row policy trace.
AY_MILP_PREFIX_COLS was in the original front too; main has since closed
that gap independently, so it is NOT re-counted here.
192 -> 196 (2026-08-13): the hybrid-branching front, reclaimed. AY_MILP_HYBRID
(Arm) plus three weights (HYBRID_W, HYBRID_INF, HYBRID_CUT). ALL SHIP OFF: the
campaign measured a WASH (-0.4% nodes) and the inference term was a regression.
The names exist so that wash stays re-checkable rather than retold.
196 -> 197 (2026-08-13): AY_MILP_RENS_WINDOW (Diagnostic, default 0 =
byte-identical). The front it came from ALSO re-read AY_MILP_RENS_WIDEN,
which B6 deliberately deleted; that read was NOT reinstated, so the name
count moves by one and not by two.
197 -> 198 (2026-08-13): AY_MILP_STRUCT_ELIM (Arm) — the structural
elimination pass (fixed columns, redundant rows). SHIPS OFF: it is
correct and it finds real structure, and it MEASURED NEGATIVE anyway.
AY_MILP_TRACE also gains a read site (77 -> 78) for that pass's census.
198 -> 199 (2026-08-13): AY_MILP_ATTRIB (Diagnostic) — the attribution
instrument (per-phase wall, allocation regions, rounding-kernel call and
yield counts). It is the tool the attribution findings were derived WITH,
so it ships to keep them re-derivable.
199 -> 200 (2026-08-13): AY_MILP_NO_ROOT_WARM (KillSwitch) — restores the
COLD re-solve of the root relaxation at the first tree node. Default OFF:
that node's LP IS the root LP, so it is handed the root Candidate itself
(box-rechecked at the consumption boundary) instead of paying a second
cold solve. The kill switch is what makes that substitution falsifiable.
200 -> 201 (2026-08-13): AY_MILP_RLT (Arm) — level-1 reformulation-
linearization with a binary bound factor. Ships OFF; the family carries
its own mutation check (an inverted substitution direction must be caught
by the integer sweep), so the arm is falsifiable rather than merely present.
201 -> 202 (2026-08-13): AY_MILP_RELAX_LIFT (Arm), relaxation lifting of a
separated row against its non-integral support. Ships OFF. The snapshot it
came from also carried AY_MILP_RENS_WIDEN, which stays retired (B6).
202 -> 203 (2026-08-13): AY_MILP_CHAIN_AGG (Arm) — chain aggregation for
the c-MIR family on the qiu fixed-charge shape. Ships OFF. AY_MILP_TRACE
also gains that family's trace site (78 -> 79).
203 -> 205 (2026-08-13): the feasibility-pump iteration cap, reclaimed.
AY_MILP_NO_PUMP_ITER_CAP (KillSwitch, default off = cap ON) and
AY_MILP_PUMP_ITER_MULT (Tuning). Without the cap a single pump call can
spend the whole heuristic budget on one model.
10 -> 9 (2026-07-29): `AY_MILP_COND_TIGHTEN` is READ again. It was marked Dead when
conditional big-M tightening became a default and the opt-in name stopped being
consulted; reverting that default (it measured 3.1x WORSE on dcmulti under later
changes) makes the opt-in the live read site once more, so it returns to Arm.
(no count change, 2026-08-20): Knob::AffineAgg (Arm, typed-only — no env
spelling, per the B49 contract). Exact fixed-column / implied-free equality
aggregation with the affine replay-certificate lane, salvaged from the
June-era local branch perf/implied-free-aggregation-1785664248 and re-wired
from its retired AY_MILP_NO_EQUALITY_AGGREGATION default-ON env gate into a
DEFAULT-OFF caller-flag arm. Ships OFF until the corpus A/B is run; the
structure-elimination journal's own conclusion ("the reductions that pay
are the ones that change what the relaxation can see") names this family
as the candidate that substitutes rather than deletes.
