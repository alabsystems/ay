# Cut and tree feature history

These notes were moved out of `bab.rs` so the executable control-flow spans stay reviewable. They preserve the detailed rationale and measurements referenced by the corresponding source comments.

## Node-level fixed-slot cut block

NODE-LEVEL CUTTING VIA A FIXED-SLOT CUT BLOCK — OFF BY DEFAULT. Opt in with
`AY_MILP_NODE_CUTS=1` (structural pool size) or `the node-cut-slots knob=<k>` (forces the size,
the guard test's lever); `AY_MILP_NO_NODE_CUTS` also forces it off.

THIRD-VISIT VERDICT (2026-07-17, branch-and-cut CUT-MANAGEMENT arm) — the wall is CLOSED.
The 2026-07-16 verdict blamed missing MANAGEMENT: cuts admitted without selection, never
aged at the right cadence, entering at deep nodes the subtree cannot amortize. This arm
BUILT that management — all four prescriptions, each measurable independently:
  (a) SHALLOW-ONLY separation (`AY_MILP_NODE_CUT_DEPTH`, default 8): rounds fire only at
      depth <= cap, where the remaining subtree amortizes a permanent row;
  (b) ADMISSION BY THROWAWAY TRIAL (`AY_MILP_NODE_CUT_EPS`): every candidate is written,
      the node re-solved warm, and the cut kept only if THIS node's bound moved >= eps —
      a rejected cut is rolled back byte-for-byte;
  (c) AGGRESSIVE AGING (`AY_MILP_NODE_CUT_STREAK`): a cut idle (slack basic) at 3
      consecutive checks is evicted outright, not merely recycled on demand;
  (d) LOCAL CUTS (`the node-cut-local knob`): bound-substituted MIR on the NODE BOX —
      strictly stronger derivations, subtree-only validity managed by per-node activation
      (`slot_local`); plus per-visit GMI re-separation ladders (`the node-gmi knob_ROUNDS`).
MEASURED, rout @60s SEEDED with the optimum (primal variance killed; the decisive frame):
cut-free 1052.1 vs the best-of-sweep managed engine (slots=16, GMI, nnz 60, 3-6 rounds)
1046.8-1047.1 — STILL NEGATIVE (−5), though management shrank the old −15.6 (k=64) loss
3x. The control that settles attribution: 16 FREE slots, depth cap 4, ZERO cuts ever
admitted (writes=0) scored 1055.3 — i.e. +3 of pure tree-shape lottery from carrying free
rows, LARGER than any cut effect. Unseeded 60s A/Bs (+0.7 to +3.6) sit inside that noise.
WHY NOTHING CAN PAY HERE: the admission trials measured the supply directly — at rout's
shallow nodes 33 of 34 violated global MIR/clique/zero-half cuts move the node bound
< 0.01 (LOCAL box-MIR: 105 of 127; GMI keeps ~5-27 of 136-232 derived across 60s), total
admitted gain 2.3-7.0 against a root-to-optimum gap of ~33, and aging then finds nearly
every admitted cut idle within 3 checks (18-29 evictions of 21-32 writes): the frontier
that owns rout's bound is ~10^3-10^4 nodes at depth 13-16 whose LP bounds tie, so a
per-node lift of 0.01-1.3 evaporates at the min over the frontier. rout's wall is
enumeration cardinality, not cut supply or cut management — no admission rule can admit
cuts that do not exist. air05: the engine is a STRUCTURAL NO-OP as the tree actually runs
(the zero-pin projection restart plus ~100ms-1s node LPs leave the cadence 0-1 rounds per
60s at ANY depth cap; the one observed firing round admitted 3 zero-half cuts, +46 dual —
real but unreachable as a lever). Kept exact, guard-tested, opt-in, and better-managed
than it has ever been; do not reopen without a materially cheaper bound device (non-LP
bounding or a frontier-wide cut family), not another management scheme.

MEASURED VERDICT (2026-07-16 branch-and-cut arm): this engine is a NET NEGATIVE on rout — the
one model it was built for — at every pool size, and a STRUCTURAL NO-OP on air05 (pure-binary,
zero continuous columns, so `cut_slot_count` returns 0 and no slot is ever reserved). It is
therefore off by default. The cut MECHANISM is real and the cuts are exact: a probe confirmed
rout has ~4 MIR cuts violated at nearly EVERY node while it has NONE at the root (a node's
tighter box gives a different fractional vertex), and `separate`/`separate_mir` derive
globally-valid cuts from the ORIGINAL rows and GLOBAL bounds, so a cut found at a node is valid
model-wide. But the ARITHMETIC does not pay. Each landed cut lifts the node bound by ~0.06
(gain/writes) while the up-to-`slot_k` PERMANENT cut rows roughly double every subsequent node
LP, and rout's bound needs +22 units (root ~1042, optimum 1077.56). Seeded with the exact
optimum, at 60s the tree reaches dual 1055.4 in 88.6k nodes with NO node cuts, 1046.3 in 50.8k
nodes at slot_k=8, and only 1039.8 in 11.3k nodes at the default slot_k=64: fewer cuts is
strictly better and the limit (zero cuts) wins, because the node-LP throughput tax exceeds the
bound benefit at EVERY pool size. The pool is already capped, aged, cadence-backed-off, and
evicts idle rows, so no cut-management tuning of THIS family rescues it — rout's bound wall
wants a cheaper or materially stronger cut (or a non-LP bound), and air05's wall is primal, not
bound. On the mixed proven corpus the engine is a wash (all values still exact either way;
qnet1 11.6→9.5s and gen 1.4→1.2s FASTER with it off, blend2/dcmulti a hair slower), and the
all-binary ladder never reserves a slot, so turning it off is bit-identical there. Kept, exact
and guard-tested, behind the opt-in for the structured families that may yet pay.

Every naive form of in-tree cutting was built and MEASURED NET-NEGATIVE, for three mechanical
reasons the fixed-slot design removes BY CONSTRUCTION:
  (a) growing the model rebuilt `lp` via `from_model`, discarding cross-solve caches -- here
      the row count is fixed once, before the root solve, and a cut lands by REWRITING a
      reserved slot row in place (`Model::set_row` + `FloatLp::reload_rows`), keeping the
      pooled solver state;
  (b) accumulated rows (up to 400) made node LPs 6.7x slower -- here at most `slot_k` cut
      rows ever exist, and a stale cut is EVICTED by recycling its slot;
  (c) every stored warm basis had the wrong row count after a growth and cold-started -- here
      `m` NEVER CHANGES, so every basis anywhere in the tree stays dimension-valid forever.

SLOT-REWRITE VALIDITY: a reserved slot is a row with zero coefficients and ±inf bounds -- it
constrains nothing, in the float lane and in every rigorous consumer (`safe_bound`/
`exact_bound` clamp any dual whose bound side is infinite to 0; `box_infeasible` skips free
rows; a basic slack's dual is identically 0). Writing a cut into a slot whose SLACK IS BASIC
in the incumbent basis preserves that basis's nonsingularity: B contains the slack's ±e_i
column, and expanding det(B) along it deletes row i, so the determinant does not depend on
row i's other entries. A free slot's slack is always basic (a row that constrains nothing
never pivots out), and eviction picks only slots whose slack is basic at the current node,
so the node's own warm re-solve after a swap starts from a provably nonsingular basis.
Any OTHER stored basis may reference the rewritten row arbitrarily -- `warm_start`
unconditionally refactorizes against the CURRENT matrix and repairs a singular basis, so
staleness costs pivots, never correctness.

SOUNDNESS: every cut is separated from the ORIGINAL rows and GLOBAL bounds (brute-force
guarded families in `cuts.rs`), so it is valid for the whole model at every node. All exact
adjudication over the augmented model -- node bounds, Farkas emptiness, no-goods -- therefore
remains sound, and a bound BANKED while a cut was in its slot stays valid after the slot is
recycled (the cut is still a true statement about the model; only the LP stopped carrying
it). Guarded end-to-end by `node_cut_slots_preserve_the_optimum`.
OFF BY DEFAULT (see the block header): the engine is opt-in. `AY_MILP_NODE_CUTS` enables it at
the structural pool size; `the node-cut-slots knob` enables it AND pins the size (so the guard
test, which sets that variable, still exercises the machinery). `AY_MILP_NO_NODE_CUTS` wins as
a hard off-switch, and a cheap sub-MIP finder never separates.
(B22 briefly retired AY_MILP_NODE_CUTS as "never set" — WRONG: the
milp_portfolio.py "nodecuts" arm sets it through a dict literal no
audit pattern saw. Both spellings stay.)

## No-good unit propagation

NOGOOD UNIT PROPAGATION (the check site). Class-gated to the tall-LU
regime like node-prop retirement — the deep-enumeration trees where the
store saturates — PLUS the implication class (the conflict-clause
revival tranche of the noswot lever: on orbitope-carrying mixed models
the same check-site engine turns each stored Farkas conflict into unit
tightenings that seed the implication x lex fixpoint, the "conflict
analysis generalizing every lex infeasibility" arm of the SCIP
arithmetic). OFF everywhere else, so every other ladder/corpus instance
keeps its trajectory byte-identical. `the ng-up knob=0` kills, `=2`
forces it everywhere (measurement lever).

⚠ "CORPUS BYTE-IDENTICAL" IS NOT EVIDENCE FOR THIS GATE, and the
introducing commit's justification (5a6ad38fa, "class-gated to tall_lu —
corpus byte-identical") is the same criterion that let rout regress
30/30 -> 0/30 unnoticed for ten days (see 7b439b9b0). Byte-identity on a
class the gate EXCLUDES says nothing whatever about that class. Compare
`lb_on` twenty lines below, which carries a five-instance measured-miss
anatomy; this gate carried none until now.

MEASURED 2026-07-31 on the excluded class (mixed, short, no orbitope):
the capability is NOT inert there. Of 102 excluded instances, 37 build a
non-empty nogood store and 24 build >= 19 boxes; forcing UP fires
heavily on models the in-source belief says are too small for it —
ic97_tension 684,725 unit fixes, pigeon-08 315,372, timtab1 141,318,
rout 79,315, all on a few hundred rows. On the slow-prover control
(rout, 291 rows, excluded), 3 byte-identical reps per arm at 60s:
  base                    17,616 nodes / 15.25s   OPTIMAL 1077.56
  NG_UP=2, NG_BRANCH=0    15,098 nodes / 13.99s   (-14.3% nodes)
  NG_UP=2 (as shipped)    16,408 nodes / 15.08s   (-6.9%)
Equal-work dual bounds improved on prod1, neos17, coxs and beavma under
UP-only, and got worse nowhere.

⛔ AND IT IS STILL NOT WORTH OPENING, which is why this is a comment and
not a change. It produced ZERO new verdicts anywhere; it is inert on 65
of the 102 excluded instances; timtab1 LOST its incumbent under UP-only;
the shipped coupling is not even the best arm (rout wants UP without the
branch tie-break, blend2 wants the tie-break); and opening it perturbs
the tree of every mixed model — the exact failure mode that cost rout its
proof. The neighbouring lane already measured a `tall_lu()` floor dropped
to 0 as HARMFUL (simplex.rs:1893-97: air05's proven bound became a bare
incumbent; gt2 and qiu fell OPTIMAL -> FEASIBLE). Correct severity: a
tree-size / dual-bound lever, NOT a verdict lever.

If it is ever revisited, the two changes worth testing are (a) give
`ng_branch_band` its own default instead of riding `ng_up`, so the two
levers can arm independently, and (b) re-gate on the property the comment
above actually claims — STORE SATURATION — rather than LP height, which
is a factorisation-engine boundary that already moved under this gate's
feet when TALL_LU_ROWS went 1,200 -> 1,000 for an unrelated LP-speed
reason, silently changing who gets nogood UP.

`feas_class` joins the default for the reason the paragraph above asks for
in its own words: "re-gate on the property the comment actually claims —
STORE SATURATION — rather than LP height, which is a factorisation-engine
boundary". An objective-≡0 decision MILP is the one class where the store
is guaranteed to be the whole search: every fathomed subtree is a conflict
and none of them is a bound prune, because there is no bound. See
`feas_class` for why this cannot reach any of the 102 instances the
measured refusal above is about.

## Root-LP frontier floor

FLOOR THE TREE WITH THE ROOT LP IT JUST SOLVED.

The root node carried NO bound of any kind, and that hole cost the
whole tree its dual report: `tree_bound` forfeits (`lost_subtree`) the
instant ONE open node has no inherited bound, and the two `lost_bank`
sites say so in as many words — "A node with NO inherited bound still
forfeits — there is nothing to bank." The root is the ancestor of
EVERY node, so with it unfloored `Node::cover` has nothing to carry
down and an interrupt at or near the root threw away a bound the
solver was already holding. That is the whole of the group whose
signature is `nodes=1, stopped=1, tb=0` — including every instance
whose root LP consumed the entire budget, since the deadline break
pushes that node back onto the open set with whatever bound it has.

The number is exactly the one the SIBLING branch below already derives
and ships — `shared_binary_prefix_frontier` computes `safe_bound` over
this same root dual and the same root box, then rounds it on the
objective granularity — so this is that branch's licence applied to the
one-region case, not a new claim.

WHY IT IS RIGOROUS, AND WHY THE ROOT'S STATUS DOES NOT ENTER IT:
`safe_bound` is Neumaier–Shcherbina, and weak duality holds for ANY
dual vector `y` — the function says so at its head, `probe_child_quick`
already rests on it for a deliberately STOPPED dual walk, and the
objective-cutoff early stop rests on it for a basis that is not even
primal feasible. So an interrupted or degenerate root LP yields a
weaker bound, never an invalid one, and `None` (unbounded direction)
fails closed to exactly the old `bound: None`.

The box is `root_lower`/`root_upper` AFTER reduced-cost fixing, same as
the sibling branch. That narrowing is licensed by the incumbent, and
`tree_bound` takes the MIN of this bound and that same incumbent, so
the pair covers every feasible point: inside the narrowed box by this
bound, outside it by the cutoff that fixed it. (With no incumbent
`reduced_cost_fix` returns 0 without touching a bound, so the box is
the unnarrowed one and the question does not arise.)
IT GOES IN `cover`, NOT `bound`, AND THAT IS THE WHOLE POINT.
`bound` is read by the best-bound heap `Ord`, the pop-time cutoff
prune, the plateau tracker and the pseudocost gain, so filling it in
CHANGES THE SEARCH — measured, on the first cut of this change: with
the floor written to `bound`, neos-787933 went 2643 nodes / incumbent
128 to 936 nodes / incumbent 149 at the same 60s budget. A WORSE
answer, bought with a reporting fix. `cover` is the reporting-only
channel `Node::cover` exists for; the search never reads it, so the
trajectory stays byte-identical and the bound still reaches
`tree_bound`. `bound` therefore keeps its historical `None`.

`the no-root-floor knob` restores that historical unfloored root. The
whole computation sits inside the arm so the off-config does not even
pay the one `safe_bound` pass.

## MAS74-class gate

MAS74-CLASS gate — MEASURED NEGATIVE, kept as an env-gated repro (default OFF,
`the mas74-plunge knob`; row cap `AY_MILP_MAS74_ROWS`, default 40 to cover the
cut-extended 13->~29-row model). mas74/mas76 share qiu's distinct-fractional-
bounds pathology (non-integral objective => every node bound a distinct real,
so the best-bound heap's deepest-first tie-break never fires and the shallow
tree is a cold frontier jump), but are tiny (12-13 rows) so `tall_lu` — and
thus the shipped gate — never arms for them. The gate below fires on exactly
this class: fractional objective AND a tiny row count, which excludes the
large fractional-objective instances (blend2 274, gen 780, qnet1 503) and the
small INTEGRAL-objective ones (flugpl, gt2, pk1) whose bounds tie-break.

Why it stays OFF: node ORDERING cannot make mas74 prove @60s. Its proof tree
is millions of nodes (600s best-bound: 3.27M nodes, rigorous dual 11548.67,
still 252 below the optimum 11801.19, UNPROVEN) — the LP relaxation of this
knapsack is weak, so a huge band of nodes sits between the root bound (~10483)
and the optimum, and ALL of them must be expanded to raise the dual, whatever
the order. The plunge DOES engage and help at the margin — at matched node
counts it reaches a higher dual (deterministic), and an AGGRESSIVE dive
(`AY_MILP_PLUNGE_CAP` large) even finds the TRUE optimum incumbent 11801.185729
that best-bound never reaches — but it stays FEASIBLE, never OPTIMAL, because
the dual-bound closure is order-invariant. Contrast qiu, whose plunge win was
WALL-TIME-PER-NODE (warm-basis reuse on 1192-row LU LPs at ~15 ms/node); mas74's
13-row LPs run at ~2.4k nodes/s, so there is no per-node cost to reclaim — the
bottleneck is node COUNT, which ordering does not touch. (mas76, the easier
sibling, DOES prove faster under the plunge: 13.3s vs 20.9s — verified no
regression.)

RIGOROUS BOUNDARY (2026-07-22, measured on this build via AY_MILP_GUB_MEAS_EVERY
— a full dual-bound-vs-nodes trajectory + a budget sweep; the last peek_bound
internal↔unscaled scale 781.2 was validated by the 1.56M-node exit where the
last MEAS peek 9059219/781.2 = 11596.35 EQUALS the exit rigorous dual exactly).
The dual climbs CONCAVELY in nodes and its marginal rate collapses monotonically:
  142k n → dual 11213.49 (gap 587.7)   [≈60s @2.4k n/s]
  1.56M n → dual 11596.35 (gap 204.8)   [300s wall here, load-slowed]
clean post-1M tail (no restarts) marginal rate 2.74e-4 → 1.47e-4 /node and still
decelerating; a gap=C·N^-α fit on that tail gives α≈0.99 (gap ≈ 2.76e8 / N). So
the *remaining* ~205-unit gap at 1.56M costs, at the last observed rate, another
~1.4M nodes (total ~3M, OPTIMISTIC linear floor) and, under the measured
deceleration (α≈1), 1e7–1e8 nodes to actually close — i.e. HOURS at 2.4k n/s.
NOT astronomical: the tree is FINITE and field-provable (Gurobi-16T proves in
12.2s with stronger cuts + 16 threads). But @60s SINGLE-THREAD it is out of reach
for ANY current solver — AY-1T reaches only ~1.44e5 nodes / gap ~587, and
GUROBI-1T ALSO FAILS @60s (gap ~2.95%). The blocker is COMPOUND — a weak knapsack
relaxation (large tree; SCIP's full cut arsenal closes only +43 of the ~1318
root gap, and AY's dual already beats SCIP's root, so no known cut family shrinks
it) × single-thread throughput (~13x slower per node than Gurobi) × no parallelism.
No single lever brings it to 60s-1T: the bound lever is documented-hard and the
throughput/parallelism lever (13x/thread + ~16 threads to match Gurobi-16T) still
exceeds a 60s single-thread budget. Aggressive diving reaches the exact known
optimum 11801.185729; the remaining failure is purely dual. This is the honest
negative, now with the extrapolation curve.

## Root reductions versus tree-certificate capture

ROOT REDUCTIONS AND TREE-CERTIFICATE CAPTURE ARE DECOUPLED HERE.

They used to be COUPLED, and the coupling ran the wrong way. A
reduced-frame TREE mostly does not lift (per-reduction notes below), so
the kernel reformulation and dedup were both gated on
`opts.tree_cert_leaves == 0` — and that field DEFAULTS TO 256
(`opts.rs`), which arms capture on every solve that does not explicitly
opt out. Two root reductions were therefore OFF BY DEFAULT, and off in
exchange for a benefit `Outcome` can deliver on exactly ONE variant:
`tree_cert` exists on `Outcome::Infeasible` and nowhere else
(`outcome.rs`). Every OPTIMAL, FEASIBLE, BOUND and UNKNOWN solve in the
corpus was paying for a certificate slot it could never be handed.
MEASURED over 65 corpus instances, running them anyway is +2 verdicts and
0 lost: `ej` 271,642 nodes -> 3 (kernel reformulation) and `decomp2` ->
OPTIMAL (dedup).

So the order is inverted. Run the reduction; buy the certificate only
where a certificate is possible at all:

  reduce -> solve reduced -> lift the outcome
    |
    +-- not Infeasible              -> done, ZERO certificate cost paid
    +-- Infeasible, lift SUCCEEDED  -> done, evidence in the caller's frame
    +-- Infeasible, lift DECLINED   -> ONE re-solve of the CALLER's own
                                       model with capture armed, and
                                       harvest that tree
                                       (`harvest_tree_cert_by_resolve`)

That last arm is not a new mechanism. It is the SAME move the symmetry
lane already makes at the `Infeasible` exit of `solve_milp_in`: a
symmetric solve poisons its own capture (its tree is exhaustive only up to
an automorphism), so on Infeasible + armed it re-solves once with `no_sym`
purely to harvest the artifact. Evidence posture is unchanged and
fail-closed in both: a retry that does not come back Infeasible leaves
`tree_cert: None`, and nothing partial or unverified is ever emitted.

Which reduction lifts what, and why:

* KERNEL — the tree does not lift, and there is not even a
  `KernelPostsolve::lift_tree_cert` to decline (`cert_lift.rs`): the
  reduced tree splits on `z` columns, and `z_t <= k` pulled back through
  `x_C = x_p + B z` is a general lattice disjunction over `x_C` that
  `TreeNode` cannot express. Root Farkas/optimality DO lift, through
  `expand_kernel_outcome`. Infeasible + armed therefore always harvests.
* SINGLETON — YES, the tree lifts. It eliminates only CONTINUOUS columns,
  so every splittable column survives with its box copied verbatim and a
  reduced split IS a caller split at the same integer cut.
  `expand_singleton_outcome` lifts leaf by leaf and strips on any decline.
  This one was never gated on `tree_cert_leaves` and is untouched here.
* DEDUP — `DedupLift::lift_tree_cert` exists and IS attempted, but its own
  doc says declining is the EXPECTED answer: the reduced model is the FACE
  `x_removed = 0`, so a tree that splits only kept columns says nothing
  about the removed twins unless every leaf happens to lean on lower
  bounds. Root certificates lift through `expand_dedup_outcome_certified`.

Kill switch: `AY_MILP_NO_CERT_DECOUPLE` restores the old coupling exactly.

## Root cut carrying-cost guard

A CUT THE LP CANNOT CARRY IS NOT A CUT, IT IS A TAX.

Every row in the pool is a row in every LP of the loop AND of every node under it, so a
cut's cost is not what it takes to SEPARATE but what it takes to CARRY. qnet1's GMI rows
come out at 569 nonzeros on a 1541-column model -- a third of the matrix, each -- and
`clean` can pay to drop almost none of it. Sixty-six of them and the loop manages two
rounds in 150 seconds.

Measured on qnet1's root bound (optimum 16029.7, root LP 14274.1): uncapped the loop gets
to 14952 and stalls at round 7, because each round's LP is dragging 569-nonzero rows.
Capped at a tenth of the columns it runs twenty rounds and reaches 15408. The cuts it
throws away are not the ones that were paying.

(Keeping the SLACK cuts as well, so the pool accumulates the way HiGHS's 880-cut pool
does, was tried here and is worse -- 15356 against 15408. A bigger pool buys fewer rounds
and the rounds were what was paying. B18: the `AY_MILP_KEEP_SLACK_CUTS` re-check lever
is retired; this record and the Dead ledger row are what survive.)
A FRACTION ALONE IS THE WRONG RULE, because it scales the wrong way on a small model.
mas74 has 151 columns, so a tenth of them is FIFTEEN nonzeros -- and a knapsack cut on a
knapsack model is dense by nature, it touches most of the row. The cap threw away every
cut mas74 had and its incumbent went from 12052.2 (which beats HiGHS) to 12233.6.

⚠ WHAT THE CODE ACTUALLY DOES, because the sentence that used to end this paragraph
("so take the looser of the two: a fraction for the wide models, a floor for the narrow
ones") described a rule that IS NOT IMPLEMENTED and sent one reader off to build it.
Only the absolute `MAX_CUT_NNZ` cap is applied. B1 deleted the former fractional cap
along with its inert environment override; both had been parsed and discarded rather
than participating in this decision.

Measured 2026-08-01 before restoring the fraction: DON'T. Taking the looser of the two
widens the cap only on models with many columns per row, and the one instance on this
corpus where the absolute number is demonstrably mis-scaled -- neos-860300, whose OWN
rows average 453.8 nonzeros against a cap of 200 -- gains nothing when its cuts are let
in (zero cuts adopted either way, verdict unmoved at 60 s). See the adjudication in
[`MAX_CUT_NNZ`]'s comment: the absolute unit survived its own test and the relative one
has no instance to justify it.

## Root cut bound-driven adoption

ADOPTION IS BOUND-DRIVEN IN THE ROUNDS MIR ALONE PAID FOR. The base rounds keep
their NON-WORSENING test (a materiality bar there broke the synthetic ladder -- see
`CUT_BOUND_MATERIAL`), and so do rounds another family's economy already bought.
But a MIR-only extended round exists ONLY because it claims to move the bound, so
a hair of movement may not buy its rows into the model the whole tree carries --
that hair is exactly how rout once bought a 60x node-LP tax. An extension that
never pays materially therefore returns the base-budget model BIT-IDENTICALLY.

A FLAT BOUND IS AN ADOPTION, NOT A REJECTION -- and it used to be a rejection, which
threw away every row a quarter of the corpus separated. Round 0 solves an EMPTY
pool, so its cut-free bound is what `best_bound` holds when round 1 arrives with real
rows; on a degenerate root those rows move the f64 objective by EXACTLY 0.0 and a
strict `>` then refused every row the loop ever separated. That is the exact case
the comment above says must be adopted: "a GMI round that moves the root bound by
nothing still shapes the relaxation the tree prunes against". Measured 2026-07-27
over the 90 smallest MIPLIB instances in ~/ay-bench/milp at a 10s cut share, this
gate plus the post-loop evaluation below take the count that ships ZERO cuts from
50 to 28 (glass4 0 -> 9 rows, noswot 0 -> 10, markshare1 0 -> 8, pk1 0 -> 3) and
improve the root gain on 22 with NONE worsened (beavma +768.9 -> +5038.7,
ic97_tension +0.157 -> +3.312, timtab1 +17016 -> +23893 on 14 rows where the old
loop needed 27, mas74 +53.07 -> +79.51, graphdraw-gemcutter +20.8 -> +36.6).

EXACTLY `>=`, WITH NO TOLERANCE UNDER IT -- and that is measured, not fastidiousness.
A tolerance is tempting here (the final retention one screen below carries a
`1e-9 * (1 + |b|)` one) because a re-solve of a FATTER model can land on a different
vertex of the same optimal face. But adding VALID rows cannot lower a relaxation's
true optimum, so a bound that comes back lower is the LP telling you something about
the pool, and 1e-9-relative is an enormous licence on a bound of 1.9e6. Measured at
`1e-9 * (1 + |best_bound|)`: dsbmip adopts one row for a bound 3.8e-12 WORSE and goes
from FEASIBLE -305.198175 (259 nodes) to UNKNOWN at the 30s limit, and neos859080 --
an infeasible 164x160 all-integer model, root bound FLAT at 1.0 for four rounds --
takes eight rows and goes from INFEASIBLE in 0.64s/189 nodes to still searching at
60s/200k nodes. At a bare `>=` both come back (cuts=0 on each, verdicts and node
counts restored to the digit) and EVERY gain above survives unchanged: glass4 9,
noswot 10, markshare1 8, markshare2 8, pk1 3 rows adopted where the strict `>` shipped
none, and mas74 +79.51 / qnet1 +638.1 / timtab1 +23893 / air05 +90.6 / misc07 +10 /
nw04 +0.76 root closure. The tie -- an EXACTLY equal bound -- is the case the corpus
is full of and the case this gate exists to adopt; a decrease is not a tie.

THE COMPARISON IS SENSE-FREE. `obj_bound` reads `lp.cost`, and `FloatLp::from_model`
solves a MAXIMIZE model as the MINIMIZE of the negated objective (see the `flip`
there), so the loop always works in the minimising frame: `bound` is a LOWER bound on
the normalised objective and rises as valid rows are added, whatever the model's own
`Sense`. Higher is tighter here in both senses, and there is nothing to branch on.

## Root lifted odd-hole gate

LIFTED ODD HOLES — DEFAULT-ON for the WIDE set-partition class (air05: 426 × 7,195). On
such an instance the {0,1/2} family is inert (the equality rows are
GF(2)-independent in the far wider column space, so no odd row-combination exists) and the
pairwise cliques saturate the root; the odd-hole facets AND their wheel lifts are the
set-packing strength the cliques miss. Gated to the structure so the corpus and ladder are
untouched. `AY_MILP_ODD_CYCLE` keeps the historical opt-in everywhere else;
`AY_MILP_NO_ODD_CYCLE` is the kill switch.

THE GATE USED TO BE ALL-OR-NOTHING, AND THAT IS WHAT KEPT IT OFF
(2026-07-28). It read `num_cols >= 10*num_rows && num_rows >= 200 &&
is_pure_set_partitioning`, and BOTH extra clauses were proxies for "air05
and nothing else" rather than statements about odd holes:

 * `num_rows >= 200` is not a structural claim at all. What makes the
   conflict graph carry chordless odd cycles is WIDTH — many columns per
   sum-to-1 row — and a short set-partition model has that structure at a
   smaller scale. nw04 (36 × 87,482) is the extreme case.
 * `is_pure_set_partitioning` demands that EVERY row be a sum-to-1
   equality, so TWO side rows disqualify a model made of 144 of them.
   That is what excluded mod010 (146 rows: 144 sum-to-1 equalities, one
   equality with RHS 46, one `<=` row with coefficients up to 20) — and
   forcing the family on there separates 9 odd holes and moves the
   presolved root gain 2.9167 → 3.1667, +8.6% over the entire rest of the
   arsenal. The separator never looks at the side rows: it builds its
   conflict graph from packing rows only, so their presence cannot make
   an emitted hole wrong, only make the model less uniformly "the class".

`cuts::is_wide_set_partition` therefore keeps the two clauses that are
about the SEPARATOR — all-binary columns (the conflict graph is a 0/1
object) and a wide sum-to-1 majority — and drops the two that were about
one instance. See `wide_set_partition_gate_matches_structure`.

## Root zero-half gate

ZERO-HALF ({0,1/2}-CG) — DEFAULT-ON for PURE SET PARTITIONING (see
`cuts::is_pure_set_partitioning` — every row an all-binary sum-to-1
equality). Everything else keeps the historical opt-in
(`AY_MILP_ZERO_HALF`); `AY_MILP_NO_ZERO_HALF` is the kill switch. Gated
on the BASE model, so the answer is stable across rounds (cut rows are
inequalities and would flip it off mid-loop).

⚠ THE AUTO-ARM IS INERT, AND BROADENING IT IS MEASURED-NEGATIVE
(2026-07-28). Two facts, both from the shipped default arsenal, presolved
root-closure regime:

 1. On the class this gate admits, the separator returns NOTHING. air05
    arms the family and emits ZERO zero-half cuts at every root vertex;
    killing it with `AY_MILP_NO_ZERO_HALF=1` reproduces the root gain
    96.165248656 BIT-IDENTICALLY. (The reason is the one already recorded
    at the odd-hole header in `cuts.rs`: sum-to-1 equality rows are
    GF(2)-independent in a far wider column space, so no odd
    row-combination with even column parity exists.) The header's older
    "air05: 25936 → 26018 over four rounds" claim does not reproduce.
 2. Arming it wherever a violated combination could EXIST — ≥ 2
    all-integer rows with integer data and a finite integer bound, one of
    them with odd RHS, which is exactly the separator's own row filter
    minus the LP-dependent part — makes 7 of 49 gurobi-tier instances
    newly separate (stein9inf 5 cuts, enlight4 3, stein45inf 9, neos16
    120, graphdraw-domain 37, graphdraw-gemcutter 40, neos-1430701 1) and
    LOSES root closure on net: graphdraw-domain 36.2458 → 31.2217,
    enlight4 1.1667 → 0, against graphdraw-gemcutter 46.82731 → 46.82926.
    The tree is unharmed (26 terminating instances: 24 bit-identical node
    counts, stein9inf 56 → 52 and stein45inf 903 → 889 BETTER, none
    worse; 17 OPTIMAL + 9 INFEASIBLE in both arms, no verdict moved), so
    the loss is bound-only and lands where the pool is full: the zero-half
    rows outrank and EVICT the cuts that were carrying the bound
    (stein45inf adopts 4 cuts before, 0 after; enlight4 2 before, 0
    after). That is cut SELECTION, which this campaign has already
    refuted as a lever, so the family stays opt-in.
