// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CERTIFIED LP BRANCH-AND-BOUND: an OPT-LIN optimality proof from a SPLIT
//! rather than from a structure.
//!
//! # What this route is for
//!
//! The eight structural certifiers each buy the last unit of the lower bound
//! from a FACT about the instance — an odd cycle, a handshake parity, a
//! per-colour at-most-one, a pebbling layer. That works only where such a fact
//! exists. On `ceil(LP*) = optimum - 1` instances with no structure to find
//! (grid domination, whose bound is a transfer-matrix DP; area-delay logic
//! synthesis; S-box hypergraph covering) weak duality caps EVERY LP-dual floor
//! strictly below the optimum, permanently, and no cut recovers it: measured on
//! `g9x9`, the rank-1 `{0,1/2}` closure over the tight rows stalls at 18.3333
//! and multi-round CG-`k` at 18.5738 after 1500 cuts, against an optimum of 20.
//!
//! What buys the unit is not a better cut but a CASE SPLIT. Cutting planes
//! cannot split on an objective bound — adding `S + M·x >= K` to
//! `S - M·x >= K - M` collapses to `S >= K - M/2` — but they CAN split on a
//! LITERAL, because the leaf of a literal split closes as a CLAUSE, whose
//! penalty coefficient is 1 and therefore survives resolution.
//!
//! This is therefore an ENGINE, not a ninth family: it asks the instance for no
//! structure at all, only `>=` rows and a linear `min:`.
//!
//! # The derivation, in one paragraph
//!
//! `soli` logs the incumbent, which both proves the upper bound and installs the
//! objective-improving row `-Σ c_v x_v >= 1 - optimum`. At a node with variables
//! fixed to 1 (`F1`) and 0 (`F0`), take non-negative integer row multipliers `Y`
//! and an objective multiplier `qo`, and form the single AGGREGATE ROW
//!
//! ```text
//!     Σ_c Y_c · row_c  +  qo · (the soli row)   ->   Σ_v coef_v x_v >= G
//! ```
//!
//! with `coef_v = Σ_c Y_c A[c,v] - qo·c_v` and `G = Σ_c Y_c b_c + qo·(1 - optimum)`.
//! The MOST that left-hand side can reach under this node's fixings is
//! `Σ_{v ∈ F1} coef_v + Σ_{v free} max(0, coef_v)`, so
//!
//! ```text
//!     R = G - Σ_{v free} max(0, coef_v) - Σ_{v ∈ F1} coef_v  >  0
//! ```
//! says exactly that THE NODE'S FIXINGS FALSIFY THE AGGREGATE ROW. That is
//! precisely the premise reverse unit propagation needs, so the leaf is
//!
//! ```text
//!     pol  <the aggregate row>                        ;
//!     rup  Σ_{v ∈ F1} ~x_v + Σ_{v ∈ F0} x_v  >= 1     ;
//! ```
//!
//! — negating that clause fixes every branch literal, the aggregate row's slack
//! goes negative with no propagation needed, and the clause is derived.
//! Internal nodes are plain resolution (`pol c1 c0 + s ;`) and the root clause
//! is EMPTY — the contradiction that justifies
//! `conclusion BOUNDS optimum optimum`.
//!
//! # Why there are no literal axioms here
//!
//! The route's first form CANCELLED every free coefficient with `max(0, coef_v)`
//! copies of `~x_v >= 0` and `max(0, coef_v) - coef_v` copies of `x_v >= 0`, so
//! that a single `d K` could round what survived into the same clause. That is
//! sound and it is what the Python prototype emitted, but the axioms are
//! BOOKKEEPING, not evidence: they carry one term per variable with a non-zero
//! aggregate coefficient, which on the measured instances is thousands of terms
//! per leaf against a handful of branch literals. `rup` needs the row falsified,
//! not cancelled, and `R > 0` already says it is — so the axiom block and the
//! division come out and no leaf is lost.
//!
//! The self-check does NOT take that on faith. `cp_replay` models the `rup` rule
//! itself — normalized slack, weight-versus-slack propagation, conflict on
//! negative slack, and the transitive reasons of that conflict for the `soli`
//! taint — so a `rup` line the database does not actually imply is refused by
//! the route's own guard before the pinned checker ever sees it.
//!
//! # Two defects the prototype measured on itself, and how this port avoids them
//!
//! The Python prototype (`scripts/pb_certified_bb_cert.py`) found both in its own
//! output. They are recorded here because a port that reproduced them would look
//! like it worked.
//!
//! 1. ROW DISCHARGE. `keep = r > -1e-9` drops every row whose residual right-hand
//!    side has gone `<= 0`. That is valid only for a NON-NEGATIVE coefficient
//!    matrix, where the least achievable left-hand side over the free variables is
//!    0. With negative coefficients the least achievable value is the sum of the
//!    row's NEGATIVE free coefficients, so the correct test is
//!    `r > Σ_v min(0, A[c,v])` — [`NodeModel::residual`] below. The wrong test
//!    dropped 17,126 of 43,326 rows on `f20c10b_011` and 1,859 of 1,979 on an
//!    `injcomp` member, and cost 55.5x proof size on `f20c10b_008`
//!    (24,698,884 -> 444,827 bytes).
//!
//! 2. LP-INFEASIBLE NODES. The prototype had NO leaf rule for them and raised a
//!    hard error. Here every such node has one, and it needs no phase-1 LP at
//!    all: a node is infeasible through a single row exactly when that row's
//!    largest achievable free left-hand side is below its residual right-hand
//!    side, and THAT row alone, at multiplier 1 with `qo = 0`, already gives
//!    `R > 0`. See [`single_row_farkas`]. Multi-row infeasibility that the node
//!    LP's own duals do not close is not an error either: the node is BRANCHED,
//!    and branching terminates, because an all-fixed node is closed by
//!    [`single_row_farkas`] or by the objective unless it is a genuine witness
//!    (see below).
//!
//! # What is float, and what is not
//!
//! Nothing float reaches the proof, and neither does anything rational. The node
//! LP CHOOSES the branch variable and PROPOSES row multipliers; every multiplier
//! is then cleared to an exact integer over one common denominator and the whole
//! leaf is re-derived coefficient by coefficient in checked `i128`
//! ([`try_leaf`]). A leaf is emitted only if the exact integer `R > 0`. If no
//! leaf clears, the node is branched; if the budget runs out, the route returns
//! no bytes. The emitted text is then parsed BACK and replayed against an
//! independent cutting-planes interpreter
//! ([`cp_replay::self_check_soli_refutation`]) before it is returned, and the
//! external pinned checker re-proves it after that.

use std::collections::BTreeSet;

use num_bigint::{BigInt, Sign};
use num_rational::BigRational;
use num_traits::{Signed, ToPrimitive, Zero};

use super::cp_replay::self_check_soli_refutation;
use super::{evaluate_linear_objective, format_assignment};
use crate::optimize::lp_bound::{lp_dual_raw_diagnosed, LpDualDecline};
use crate::proof::steps::{ConstraintId, ProofStep};
use crate::proof::veripb::{veripb_input_constraint_count, VeriPbWriter};
use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective, PbRel, PbTerm};

/// Deterministic node budget: the number of search-tree nodes this route may
/// open before it gives up, on EVERY machine and under EVERY load.
///
/// A COUNT, never a clock — the same discipline as
/// `lp_dual_floor::MAX_DUAL_SOLVE_POLLS` and `odd_cycle_cover::packing::Limits`,
/// and for the same reason: the emitted bytes must not depend on how busy the
/// box is. Raising it cannot make a proof wrong, only slower; lowering it turns
/// certificates into declines.
///
/// SIZED FROM MEASUREMENT, not chosen. See `certified_bb::tests` and the
/// measurement table in the branch report: the heaviest instance this route
/// certifies opens 443 nodes (`sbox_4_shg`, prototype guidance) and the three
/// `injcomp` members that DO NOT close open more than 200,000 without ever
/// closing. 4,096 is the power of two inside that gap.
const MAX_NODES: u64 = 4_096;

/// Deterministic depth cap. Bounds the recursion (each frame is a few machine
/// words plus two pushes onto shared vectors) and, with [`MAX_NODES`], bounds
/// the whole search. The measured `injcomp` non-closers reach depth 162-187, so
/// this is not what stops them — [`MAX_NODES`] is.
const MAX_DEPTH: usize = 512;

/// Deterministic work cap for ONE node's LP solve, counted in `should_stop`
/// polls. Each poll is a fixed-size chunk of tableau work (`optimize::lp_bound`
/// polls at deterministic sites only), so the count at which this fires is
/// identical on every machine.
///
/// TWO CAPS, because the root solve and the node solves are different jobs.
///
/// The ROOT solve is the same computation `lp_dual_floor` already performs for a
/// certificate — a full model, no fixings — and is sized by the same
/// measurement, [`lp_dual_floor::MAX_DUAL_SOLVE_POLLS`] = 4096. Below the root
/// the LP is GUIDANCE for a split, not a certificate: a weaker dual costs tree
/// size and nothing else, because [`try_leaf`] re-derives the arithmetic
/// regardless. So the node cap is small, and it has to be, since this route
/// solves an LP PER NODE.
///
/// Both numbers are measured, not chosen:
///
/// * with NO per-solve cap at all, `dominating_set_hexgrid_opt_r6_c50`
///   (300 vars, 300 rows) spent 275 s in the ROOT solve alone and returned a
///   point the emitter then refused — the whole route's cost, spent before the
///   first node closed;
/// * at 4096 everywhere, `sbox_4_shg` reached 264 of the nodes it needs, spent
///   the entire 100,000-poll global budget doing it (243 s), and certified
///   nothing;
/// * at 128 below the root, the same instance certifies in 30 s, and the proof
///   is 2.2x SMALLER than the prototype's (195,974 B / 303 lines against
///   435,163 B / 437 lines) because the extra branching closes leaves with far
///   fewer cited rows;
/// * 128 AT the root is too small for a big model: `f20c10b_008` (3,973 vars,
///   11,097 rows) declines with no dual point at all after 131 polls, and
///   certifies once the root gets its 4096.
const MAX_ROOT_LP_POLLS: u64 = 4_096;
const MAX_NODE_LP_POLLS: u64 = 128;

/// The FIRST allowance a node LP below the root is given, before
/// [`MAX_NODE_LP_POLLS`] is spent on it.
///
/// # Why two passes, and why the escalation test is REFUSAL and not tightness
///
/// `lp_dual_raw_diagnosed` runs a cheap `f64`-certified tier and then, ONLY IF
/// that tier's bound did not reach the target, an exact rational simplex. At a
/// node that closes, the cheap tier usually reaches the target and the exact
/// tier never runs. At a node that does NOT close — every internal node, which
/// is half the tree — the exact tier ALWAYS runs, and it is where the polls go.
/// Its whole product there is a branching hint.
///
/// Measured, `dominating_set`-style instance `m100_300_10_20.r` at an unbounded
/// budget: the tree is 1,443 nodes / 722 leaves and the proof is
/// BYTE-IDENTICAL (2,540,174 B) at per-node caps of 128, 64, 32 and 16 — while
/// the poll count falls 102,375 -> 56,295 -> 33,255 -> 21,735. Every one of
/// those 80,640 extra polls bought nothing at all, and they are the difference
/// between a certificate and a decline: 32,768 is the global budget.
///
/// The opposite instances exist too, which is why a flat small cap is the wrong
/// answer: at 16, `addm4.r` goes 73 nodes -> 2,808 and declines, `fir04_trarea_ac`
/// 3 -> 995, and at 32 `f20c10b_008_area_delay` 49 -> 1,512. All three are
/// conversions this route makes today.
///
/// What separates the two populations is not how TIGHT the cheap pass is but
/// whether it returns a dual point AT ALL. On `m100_300_10_20.r` at 16 polls
/// every node's LP answers (`guided=0`). On `addm4.r` at 16, `1,433` of `2,808`
/// nodes get no point (`guided=1433`); on `fir04_trarea_ac`, `511` of `995`; on
/// `f20c10b_008_area_delay` at 32, `1,435` of `2,734`. So the escalation test is
/// exactly that refusal — a fact the fast pass REPORTS, with no threshold to
/// tune and no unit to get wrong.
///
/// A refusing node therefore pays `16 + 128` where it used to pay `128`; a node
/// whose LP answers pays `16` where it used to pay up to `128`.
///
/// ONLY A BUDGET REFUSAL BUYS THE SECOND PASS. See
/// [`refusal_can_change_with_a_bigger_budget`]: escalating a refusal the poll
/// count cannot change re-solves the identical model to the identical answer,
/// which on the 17 instances the static LP size cap rejects meant building a
/// 61,821-row node model TWICE PER NODE for nothing.
const MAX_NODE_LP_POLLS_FAST: u64 = 16;

/// Deterministic cap on the BLIND-BRANCHING PATH: how many nodes this search
/// may branch WITHOUT a fresh relaxation of its own to steer them.
///
/// # The wall this closes, measured
///
/// Before the fallback branch rule existed, one node's refused LP ended the
/// WHOLE search (`Exhausted` propagates to the root). Removing that is right —
/// a fact about one node's LP budget says nothing about whether the tree closes
/// — but it uncovered a cost that had been hidden behind the accident: an
/// instance whose LP refuses at EVERY node no longer stops at node 1, it walks
/// to [`MAX_NODES`] or [`MAX_DEPTH`]. Measured back-to-back on this box, the
/// route's own `ms`, against `8ccb70761`:
///
/// ```text
///   50-250-false-45-90-4-2000opt        75 ms ->  32,726 ms   (436x, 4,097 nodes)
///   single-obj-f50-DC_side2            307 ms ->  17,354 ms   ( 57x,   513 nodes)
///   kdessh.cudf.trendy               1,179 ms ->  11,608 ms   (9.8x,   991 nodes)
///   vertexcover_..._dim_071          3,948 ms -> 240,728 ms   ( 61x,   219 nodes)
///   single-obj-f17-DCdoubleLoss      8,768 ms -> 630,144 ms   ( 72x,   264 nodes)
/// ```
///
/// None of it is interruptible and none of it produces anything: 17 of those
/// instances spend `polls=0/32768` across 513-4,097 nodes because the LP was
/// refused UNREAD by a static size cap, so the one budget that did bound the
/// route never advanced at all.
///
/// # Why a count, and why THIS count
///
/// A blind node is exactly a node the relaxation declined to steer, so counting
/// them charges the path that the poll budget cannot see. It is a COUNT and not
/// a clock for the reason every other budget here is: the emitted bytes must be
/// the same on a loaded box as on an idle one.
///
/// SIZED FROM THE MEASURED PRODUCT OF THAT PATH, WHICH IS ZERO. Every one of the
/// seven instances this route certifies walks `guided=0` — not one of them
/// branches blind even once — so no value of this cap can cost a certificate,
/// and that is arithmetic rather than hope. Across all 50 `SEARCH-PROOF-GAP`
/// instances, at every budget probed, blind branching converted NOTHING.
///
/// WHY 16 AND NOT SOMETHING ROOMIER.
///
/// THERE IS NO GAP. An earlier version of this comment said the corpus's blind
/// counts are `0, 1, 14, 145, 154, 177, 184, 190, 217, 243, 512, 1135, 3916+`,
/// that nothing lives between 14 and 145, and therefore that "every cap from 15
/// to 144 binds on exactly the same instances". That is FALSE, and the
/// counterexample is in the same corpus (r6 probe `31e8ef02…`, deterministic
/// counts, re-measured for this merge):
///
/// ```text
///   normalized-ssa7552-159       nodes=271 leaves=82 blind=142 polls=32771/32768
///   normalized-single-obj-f3-..  nodes=222 leaves=29 blind=178 polls=32771/32768
/// ```
///
/// `142` sits inside the interval declared empty, so caps 15..=141 bind on
/// `ssa7552-159` and caps 142..=144 do not; `178` is a second value the list
/// omits. The enumerated list is NOT a complete census of the corpus and must
/// not be read as one.
///
/// WHAT ACTUALLY SIZES THIS CAP is the pair of one-sided facts below, neither of
/// which needs the list: the cap must be >= 14 to keep `9symml`'s gain, and
/// among the caps that do, the smallest measured is the cheapest. That is the
/// whole argument, and it survives the correction. Measured back-to-back on this
/// box, the route's own `ms`:
///
/// ```text
///                                  BASE      cap 8   cap 16   cap 64  cap 192   r6 (uncapped)
///   50-250-..-2000opt                75        116      150      364      941      32,726
///   single-obj-f50-DC_side2         307        317      343      444      828      17,354
///   kdessh.cudf.trendy            1,179      1,108    1,185    1,768    3,305      11,608
///   vertexcover_..._dim_071       3,948     13,466   22,923   77,801  226,364     240,728
/// ```
///
/// 16 is the FLOOR of that range rather than 8 because `9symml` branches blind
/// 14 times on its way from 403 nodes to 1,859, and that gain is one this cap
/// is meant to keep. What 16 gives up is MORE THAN THE FOUR an earlier version
/// of this comment named (`ii16d2` at 145 and the three `injcomp_4layers` at
/// 154-184). Every instance re-measured for this merge trips the cap:
///
/// ```text
///   ssa7552-159 142   ii16d2 145   single-obj-f3 178   vertexcover_..071 217
///   f20c10b_011 512   single-obj-f50 512   kdessh.cudf.trendy 512
///   sporttournament18 1,135   50-250-..-2000opt 3,916
/// ```
///
/// NONE of them converts at any budget measured, so the cap costs no
/// certificate; their extra nodes cost 2.2-3.7x wall, so the trade is a decline
/// that arrives sooner. Note that 142 and 178 also mean the give-up set is NOT
/// identical across 16, 64, 128 and 144 — the claim that it was is corrected
/// above.
const MAX_BLIND_NODES: u64 = 16;

/// How many nodes the search opens before it will consult the caller's
/// `should_stop` at all.
///
/// # Why this rung may be interrupted, and why not from node 1
///
/// This is an UNSCHEDULED rung: it is called outside [`CertRouteBudget`]
/// precisely so that a CLI whose deadline is already spent — the normal case,
/// since certification runs after the search — still gets it. Polling
/// `should_stop` from the first node would hand that caller a decline instead of
/// the certificate it gets today.
///
/// But "not scheduled" was allowed to mean "not stoppable", and a route that
/// cannot be stopped is one a `--timeout` cannot bound: `single-obj-f17` spent
/// 10.5 uninterruptible minutes inside a rung whose caller had asked for less.
///
/// COUNTS reconcile the two, and it takes TWO of them because this route spends
/// two things. `m100_300_10_20.r` is the heaviest certificate on both: 1,443
/// nodes and 21,735 polls; every other conversion is under 400 nodes and under
/// 12,000 polls. 2,048 and 24,576 clear those with 1.42x and 1.13x headroom —
/// the same margin [`MAX_TOTAL_LP_POLLS`] carries over ITS heaviest consumer.
///
/// A node bound alone would not have been enough, and that is measured rather
/// than assumed. `knapPI_14_10000_1000_2` declines at 316 nodes and 197 s;
/// `composed_pebbling_..._height13` at 261 nodes and 183 s. Both are FAR under
/// any node envelope while spending the whole 32,768-poll budget, because their
/// cost is per-poll and not per-node — one poll ranges 0.11 ms to 26 ms across
/// this corpus. A route bounded in two currencies has to be escapable in both.
///
/// Every certificate this route produces is therefore emitted before the first
/// poll of the stop signal, and everything past its certifying envelope is
/// stoppable. An interrupt can only ever turn a certificate into a decline; it
/// can never change a byte of one, which is what keeps the emitted proof
/// load-invariant.
const MAX_UNINTERRUPTIBLE_NODES: u64 = 2_048;
const MAX_UNINTERRUPTIBLE_POLLS: u64 = 24_576;

/// Deterministic work cap for ALL node LP solves together. Bounds the route
/// independently of how many nodes turn out to be cheap, and — because this is
/// an UNSCHEDULED rung that never consults the caller's clock — it is the ONLY
/// thing that bounds what a DECLINE costs in wall time.
///
/// SIZED FROM MEASUREMENT, AND THE TRADE IS EXPLICIT. Poll counts of the four
/// instances this route certifies: `g9x9` 1,925; `dominating_set_hexgrid_opt_r6_c50`
/// 4,276; `addm4.r` 9,724; `sbox_4_shg` 25,304 — so 32,768 admits every measured
/// certifying member with 1.29x headroom over the heaviest. Against that:
///
/// * a DECLINE spends the whole budget. Measured with the shipped caps,
///   `injcomp_..._size_29` (which declines correctly, and must) exhausts all
///   32,772 polls in 3.7 s.
/// * A COUNT BOUNDS WORK AND REPRODUCIBILITY, NOT WALL TIME, and the spread is
///   large enough that saying otherwise would be a lie by rounding: a poll costs
///   0.11 ms on `injcomp_..._size_29` (2,494 vars, 927 rows) and 1.4 ms on
///   `sbox_4_shg` (147 vars, 240 rows) — 13x apart, and the SMALLER model is the
///   expensive one, because the exact rational tableau is denser there. So the
///   honest ceiling is "one full budget at the most expensive rate measured",
///   about 46 s, not the 3.7 s the cheapest instance suggests.
/// * this is the same shape of trade `lp_dual_floor::MAX_DUAL_SOLVE_POLLS`
///   closed, with one difference worth stating rather than glossing: there, the
///   minute bought NOTHING on the instances that consumed it. Here the heaviest
///   consumer (`sbox_4_shg`, 25,304 polls / ~36 s) is a coverage conversion no
///   other route produces. The cost is real either way and it lands on the
///   DECLINES.
///
/// The A/B gate for any resize is proof-sha equality on the four certifying
/// instances PLUS a re-measure of the decline ceiling; changing it cannot make a
/// proof wrong, only slower or absent.
const MAX_TOTAL_LP_POLLS: u64 = 32_768;

/// Denominators tried, in order, when clearing a node's rational duals to
/// integer `pol` multipliers.
///
/// # Why a LADDER and not the exact common denominator
///
/// The prototype's author noted that AY's LP returns EXACT RATIONAL duals and
/// concluded that the Python version's snapping ladder was therefore unnecessary
/// in Rust. That is true of the REPRESENTATION and false of the NUMBERS. The
/// tier that answers first is `solve_dual_f64_certified`, which builds its duals
/// with `BigRational::from_float` — exact, and therefore carrying the whole
/// BINARY EXPANSION of each `f64`. Its denominators are powers of two in the
/// 2^50 range whatever the LP looks like (this is the same fact
/// `lp_dual_floor::denominator_profile` exists to report), so an exact common
/// denominator overflows any sane cap on the first fractional dual. Measured:
/// with exact-LCM-only clearing, `dominating_set_hexgrid_opt_r6_c50` closed ZERO
/// nodes and the route declined at the root.
///
/// SNAPPING DOWN IS FREE HERE, which is what makes the ladder the right answer
/// rather than a compromise. [`try_leaf`] asks nothing of `Y` beyond
/// non-negativity — it re-derives every coefficient and refuses unless the exact
/// integer degree `R` is positive — so a floored multiplier can only make `R`
/// smaller, never a proof wrong. The exact common denominator is still tried
/// FIRST when it is small, because it gives the tightest `R` at the smallest
/// numbers.
const LEAF_SCALES: [i128; 11] = [1, 2, 4, 12, 48, 256, 1_024, 4_096, 65_536, 262_144, 1 << 20];

/// Largest common denominator admitted when the EXACT clearing is attempted.
/// Mirrors `lp_dual_floor::MAX_DUAL_SCALE`.
const MAX_LEAF_SCALE: i128 = 1 << 20;

/// How many ancestor multiplier vectors the search carries down the tree and
/// replays at every node BEFORE it pays for an LP.
///
/// # Why replaying an ancestor's multipliers is free AND monotone
///
/// Fix `Y` and `qo`. `try_leaf`'s degree is
/// `R = G + qo(1-optimum) - Σ_{v free} max(0, coef_v) - Σ_{v ∈ F1} coef_v`, so
/// moving one variable OUT of `free` changes exactly one term: to `F1` it
/// becomes `-coef_v` (a gain of `max(0, -coef_v) >= 0`) and to `F0` it drops
/// (a gain of `max(0, coef_v) >= 0`). Either way `R` can only GROW as the tree
/// descends. So a multiplier vector that failed at an ancestor is a valid, and
/// strictly better, candidate at every descendant — and testing it costs no
/// LP poll at all, only one pass over the cited rows.
///
/// That matters here because POLLS, not nodes, are what actually stop this
/// route: `MAX_TOTAL_LP_POLLS / MAX_NODE_LP_POLLS = 256`, so a decline exhausts
/// its budget after ~256 nodes however large `MAX_NODES` is.
///
/// SIZED small on purpose. Each entry costs one `try_leaf` per node — a pass
/// over `num_vars` plus the cited rows — and the entries that pay are the near
/// ones (a sibling's closing combination) and the root's, not a long history.
const MAX_DUAL_POOL: usize = 8;

/// What the search concluded. Three outcomes, and the whole point of the type is
/// that the middle one is NOT the last one.
///
/// # Why this enum exists
///
/// The prototype collapsed two of these into one message. When a node's LP came
/// back integral and inside the refuted budget it printed
/// `the claimed optimum N is WRONG` — an accusation — and exited. On
/// `f20c10b_011` and three `injcomp` members it printed exactly that about
/// optima that are CORRECT: the row-discharge defect above had thrown away most
/// of the relaxation, so the surviving LP was weak enough for its optimum to
/// look integral. HiGHS MIP, consulted independently, reports the accused value
/// INFEASIBLE on all four.
///
/// It happened to be SAFE — it wrote no file — but a fail-closed premise
/// reachable two ways is only as good as its rarer one, and this one was
/// reachable by a bug in the route's own modelling. The two are now separated by
/// what they can SHOW:
///
/// * [`Self::Refuted`] carries a COMPLETE ASSIGNMENT that has been re-verified
///   against every ORIGINAL row with its objective recomputed exactly, and whose
///   value is strictly below the claimed optimum. It is a witness, checkable by
///   anything, and it says the optimum is wrong.
/// * [`Self::Exhausted`] carries a REASON and no claim about the optimum at all.
///   "I could not close this tree inside the budget" and "I have no leaf rule
///   for this node" both land here.
///
/// An integral node LP inside the budget is now evidence for NEITHER until the
/// point it proposes has been checked — see [`witness_from_point`]. If it checks
/// out it is a witness; if it does not, it is a weak relaxation and the node is
/// branched or the route declines.
enum Outcome {
    /// Proof text.
    Proof(String),
    /// The claimed optimum is refuted BY A WITNESS: this assignment satisfies
    /// every original constraint and its exact objective is `value < optimum`.
    Refuted {
        #[allow(dead_code)] // Carried for `--cert-debug` and the diagnosis entry.
        witness: Vec<bool>,
        value: i128,
    },
    /// No claim about the optimum. The budget ran out, or a node admitted no
    /// leaf this route can express.
    Exhausted(&'static str),
}

/// [`run`]'s full result: the outcome plus what the search spent reaching it.
struct Run {
    outcome: Outcome,
    stats: Stats,
    /// The node LP's own first refusal, when there was one.
    lp_decline: Option<String>,
}

/// Counts the search spent, reported by [`certified_bb_diagnosis`] so a decline
/// names a NUMBER rather than a mood. All four are the deterministic budgets'
/// own units, so a decline can be read straight against [`MAX_NODES`],
/// [`MAX_DEPTH`] and [`MAX_TOTAL_LP_POLLS`].
#[derive(Clone, Copy, Default)]
struct Stats {
    nodes: u64,
    leaves: u64,
    farkas: u64,
    depth: usize,
    polls: u64,
    /// Leaves closed by a REPLAYED ancestor multiplier vector, with no LP solve
    /// of their own. A subset of `leaves`, reported separately because it is the
    /// number that says whether carrying the pool paid for itself.
    replays: u64,
    /// Nodes whose branch variable came from an INHERITED point or from the
    /// objective, because this node's own LP produced none. Reported because it
    /// is the number that says how much of the tree was walked without a fresh
    /// relaxation to steer it.
    guided: u64,
    /// Nodes whose fast LP pass refused and which therefore paid for the full
    /// one as well. See [`MAX_NODE_LP_POLLS_FAST`].
    escalations: u64,
}

impl std::fmt::Display for Stats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "nodes={}/{MAX_NODES} leaves={} replays={} guided={} escalations={} farkas={} \
             depth={}/{MAX_DEPTH} polls={}/{MAX_TOTAL_LP_POLLS}",
            self.nodes,
            self.leaves,
            self.replays,
            self.guided,
            self.escalations,
            self.farkas,
            self.depth,
            self.polls
        )
    }
}

/// The instance in the one form the derivation needs: `>=` rows in VARIABLE
/// form (negated literals folded into the coefficient and the degree), a dense
/// objective vector, and nothing else.
///
/// Row `r` here is VeriPB input id `r + 1`. That identity is proof-critical and
/// is why [`build_model`] refuses `PbRel::Eq` outright rather than splitting it:
/// VeriPB imports an equality as TWO consecutive ids, so a split would have to
/// be carried through every `pol` this module writes. The route declines on such
/// instances instead of getting the arithmetic subtly right in one place and
/// wrong in another.
struct Model {
    num_vars: usize,
    /// Per row: `(variable index 0-based, coefficient)`, no zero coefficients.
    rows: Vec<Vec<(usize, i128)>>,
    /// Per row: the right-hand side after negated literals were folded in.
    rhs: Vec<i128>,
    /// Dense objective in variable form, one entry per variable.
    objective: Vec<i128>,
}

fn build_model(instance: &PbInstance) -> Option<Model> {
    let num_vars = usize::try_from(instance.num_vars).ok()?;
    if num_vars == 0 {
        return None;
    }
    let objective_terms = &instance.objective.as_ref()?.terms;
    let mut objective = vec![0_i128; num_vars];
    for term in objective_terms {
        let [lit] = term.lits.as_slice() else {
            return None;
        };
        // Plain, non-negated single literals only. `soli`'s installed row is
        // modelled from this objective in three places (here, `try_leaf`, and
        // `cp_replay::objective_improving_row`); a negated literal contributes a
        // constant that each of them would have to fold identically, so the
        // shape is refused rather than modelled three times.
        if lit.negated {
            return None;
        }
        let index = (lit.var as usize).checked_sub(1)?;
        if index >= num_vars {
            return None;
        }
        objective[index] = objective[index].checked_add(term.coeff)?;
    }
    let mut rows = Vec::with_capacity(instance.constraints.len());
    let mut rhs = Vec::with_capacity(instance.constraints.len());
    for constraint in &instance.constraints {
        if constraint.rel != PbRel::Ge {
            return None;
        }
        let mut dense = vec![0_i128; num_vars];
        let mut degree = constraint.rhs;
        for term in &constraint.terms {
            let [lit] = term.lits.as_slice() else {
                return None;
            };
            let index = (lit.var as usize).checked_sub(1)?;
            if index >= num_vars {
                return None;
            }
            if lit.negated {
                // `c·~x = c - c·x`: the constant moves to the degree.
                degree = degree.checked_sub(term.coeff)?;
                dense[index] = dense[index].checked_sub(term.coeff)?;
            } else {
                dense[index] = dense[index].checked_add(term.coeff)?;
            }
        }
        rows.push(
            dense
                .into_iter()
                .enumerate()
                .filter(|&(_, coefficient)| coefficient != 0)
                .collect(),
        );
        rhs.push(degree);
    }
    Some(Model {
        num_vars,
        rows,
        rhs,
        objective,
    })
}

/// A node's residual view of one row, over the FREE variables only.
struct Residual {
    /// Right-hand side after the `F1` fixings were substituted in.
    degree: i128,
    /// `Σ_{v free} min(0, A[c,v])` — the LEAST the free part can achieve.
    least: i128,
    /// `Σ_{v free} max(0, A[c,v])` — the MOST the free part can achieve.
    most: i128,
}

impl Model {
    /// The residual of row `c` at a node. `None` on arithmetic overflow.
    ///
    /// THE DISCHARGE TEST LIVES HERE, and it is the first of the two defects
    /// this port does not inherit. A row may be dropped from the node
    /// relaxation only if it holds for EVERY assignment of the free variables,
    /// i.e. only if `degree <= least`. The prototype tested `degree <= 0`,
    /// which is the same thing ONLY when every free coefficient is
    /// non-negative.
    fn residual(&self, row: usize, fixed: &[Option<bool>]) -> Option<Residual> {
        let mut degree = self.rhs[row];
        let mut least = 0_i128;
        let mut most = 0_i128;
        for &(var, coefficient) in &self.rows[row] {
            match fixed[var] {
                Some(true) => degree = degree.checked_sub(coefficient)?,
                Some(false) => {}
                None => {
                    if coefficient < 0 {
                        least = least.checked_add(coefficient)?;
                    } else {
                        most = most.checked_add(coefficient)?;
                    }
                }
            }
        }
        Some(Residual {
            degree,
            least,
            most,
        })
    }
}

/// The exact integer leaf certificate: non-negative row multipliers `ys`, the
/// objective/`soli` multiplier `qo`, and the branch clause they refute.
struct Leaf {
    /// `(row index, multiplier)`, multipliers strictly positive, rows ascending.
    ys: Vec<(usize, i128)>,
    /// Multiplier on the `soli`-installed row. `0` for a Farkas leaf, which
    /// closes on row infeasibility alone and must not cite the objective.
    qo: i128,
    /// The branch clause, as `(0-based variable, negated)` literals: `~x_v` for
    /// a variable this node fixed to 1, `x_v` for one it fixed to 0. Recorded
    /// HERE rather than re-read from the search's `fixed` vector at emission
    /// time so the clause cannot drift from the `R > 0` test that licensed it.
    clause: Vec<(usize, bool)>,
    /// The clause's support, as 0-based variable indices.
    support: BTreeSet<usize>,
}

/// Re-derives a candidate leaf in exact checked integer arithmetic and returns
/// it only if the surviving degree is STRICTLY POSITIVE.
///
/// This is the soundness boundary of the whole route. `ys` and `qo` are
/// proposals — from a float-guided LP, from a rational dual, from a single row,
/// it does not matter — and nothing about where they came from is trusted. Every
/// coefficient of the combination is recomputed here, each free variable is
/// charged the SMALLEST cancellation that covers it (which is also the choice
/// that maximises `R`, so a slack dual costs tightness and never correctness),
/// and `R <= 0` returns `None`.
///
/// `R` is computed as `G - Σ_{v free} max(0, c_v) - Σ_{v ∈ F1} c_v`, which is
/// the aggregate row's degree minus the MOST its left-hand side can reach under
/// this node's fixings. So `R > 0` is not merely the condition under which the
/// axioms cancel: it is literally the statement that the node's fixings FALSIFY
/// the aggregate row — which is what makes the branch clause reverse-unit-
/// propagate from it. See [`Search::emit_leaf`].
fn try_leaf(
    model: &Model,
    fixed: &[Option<bool>],
    ys: &[(usize, i128)],
    qo: i128,
    optimum: i128,
) -> Option<Leaf> {
    if qo < 0 || ys.iter().any(|&(_, multiplier)| multiplier <= 0) {
        return None;
    }
    if ys.is_empty() && qo == 0 {
        return None;
    }
    let mut coefficient = vec![0_i128; model.num_vars];
    let mut aggregate_degree = 0_i128;
    for &(row, multiplier) in ys {
        aggregate_degree = aggregate_degree.checked_add(multiplier.checked_mul(model.rhs[row])?)?;
        for &(var, entry) in &model.rows[row] {
            coefficient[var] = coefficient[var].checked_add(multiplier.checked_mul(entry)?)?;
        }
    }
    if qo != 0 {
        for var in 0..model.num_vars {
            coefficient[var] =
                coefficient[var].checked_sub(qo.checked_mul(model.objective[var])?)?;
        }
    }

    // `R` starts at the aggregate degree plus the soli row's own degree
    // (`1 - optimum` per unit of `qo`) and is then charged for every axiom that
    // carries a `-1` into the degree: the `~x_v >= 0` copies.
    let mut degree = aggregate_degree.checked_add(qo.checked_mul(1_i128.checked_sub(optimum)?)?)?;
    let mut clause: Vec<(usize, bool)> = Vec::new();
    let mut support = BTreeSet::new();
    for var in 0..model.num_vars {
        let c = coefficient[var];
        match fixed[var] {
            // FREE: the most it can contribute is `max(0, c)`, so that is what
            // the degree is charged. This is the least such charge, hence the
            // largest surviving `R`.
            None => {
                if c > 0 {
                    degree = degree.checked_sub(c)?;
                }
            }
            // FIXED TO 1: it contributes exactly `c`, of either sign, so `- c`
            // covers both cases in one term. A negative `c` is a coefficient the
            // fixing is CARRYING, and dropping the fixing would undo the leaf —
            // so `~x_v` joins the branch clause.
            Some(true) => {
                degree = degree.checked_sub(c)?;
                if c < 0 {
                    support.insert(var);
                    clause.push((var, true));
                }
            }
            // FIXED TO 0: it contributes nothing, so the degree is unchanged. A
            // positive `c` is a contribution the fixing is SUPPRESSING, so
            // `x_v` joins the branch clause.
            Some(false) => {
                if c > 0 {
                    support.insert(var);
                    clause.push((var, false));
                }
            }
        }
    }
    if degree <= 0 {
        return None;
    }
    Some(Leaf {
        ys: ys.to_vec(),
        qo,
        clause,
        support,
    })
}

/// The exact single-row Farkas leaf: the second defect this port does not
/// inherit.
///
/// A node is infeasible THROUGH ONE ROW exactly when that row's residual degree
/// exceeds the most its free part can achieve. That row alone, at multiplier 1
/// with `qo = 0`, then has
/// `R = degree - Σ_{v free} max(0, A[c,v]) - Σ_{v ∈ F1} A[c,v] = residual.degree - residual.most > 0`
/// — which is the infeasibility test itself. No phase-1 LP, no objective, and
/// the leaf cites the `soli` row not at all.
fn single_row_farkas(model: &Model, fixed: &[Option<bool>], optimum: i128) -> Option<Leaf> {
    for row in 0..model.rows.len() {
        let residual = model.residual(row, fixed)?;
        if residual.degree > residual.most {
            if let Some(leaf) = try_leaf(model, fixed, &[(row, 1)], 0, optimum) {
                return Some(leaf);
            }
        }
    }
    None
}

/// The node relaxation handed to the LP, plus the map back to original rows.
struct NodeLp {
    /// `(original row index, exact rational dual > 0)`, rows ascending.
    duals: Vec<(usize, BigRational)>,
    /// The exact common denominator of `duals` when it is small enough to be
    /// worth trying first, else `None`.
    exact_scale: Option<i128>,
    /// The LP's fractional point over the FREE variables, in original variable
    /// space, or `None` when the winning tier recovered none. ADVISORY: it
    /// chooses the branch variable and proposes a candidate witness, and both
    /// are checked before anything is claimed.
    point: Option<Vec<(usize, BigRational)>>,
}

impl NodeLp {
    /// `floor(y_c · scale)` for every dual, dropping the zeros.
    ///
    /// FLOOR, not round and not exact: see [`LEAF_SCALES`]. Rounding UP would
    /// produce a multiplier the dual does not support, which is not unsound here
    /// either (nothing downstream assumes dual feasibility) but is pointless —
    /// it can only make the aggregate coefficients larger without making the
    /// degree larger.
    fn scaled(&self, scale: i128) -> Option<Vec<(usize, i128)>> {
        let mut out = Vec::with_capacity(self.duals.len());
        for (row, dual) in &self.duals {
            let scaled = dual * BigRational::from_integer(BigInt::from(scale));
            let multiplier = scaled.floor().to_integer().to_i128()?;
            if multiplier > 0 {
                out.push((*row, multiplier));
            }
        }
        Some(out)
    }

    /// The denominators to try at this node, tightest-and-smallest first.
    fn scales(&self) -> impl Iterator<Item = i128> + '_ {
        self.exact_scale
            .into_iter()
            .chain(LEAF_SCALES.iter().copied().filter(|&scale| {
                // The exact scale, when there is one, is already first.
                self.exact_scale != Some(scale)
            }))
    }
}

/// Solves the node relaxation and clears its duals to exact integers.
///
/// The relaxation is built over the FREE variables only, with every row's
/// right-hand side reduced by the `F1` fixings and every row that the free
/// variables cannot violate DISCHARGED by the corrected test. Discharging is a
/// modelling choice with no soundness content whatsoever: a discharged row is a
/// row the emitted combination does not cite, every cited multiplier is
/// non-negative regardless, and [`try_leaf`] re-derives the arithmetic from the
/// ORIGINAL rows either way. It buys size and reach — the wrong test cost 55.5x
/// on `f20c10b_008` and stopped `f20c10b_011` outright.
fn solve_node_lp(
    model: &Model,
    fixed: &[Option<bool>],
    optimum: i128,
    polls: &std::cell::Cell<u64>,
    budget: u64,
) -> Result<NodeLp, String> {
    let free: Vec<usize> = (0..model.num_vars)
        .filter(|&v| fixed[v].is_none())
        .collect();
    if free.is_empty() {
        return Err("all-variables-fixed".into());
    }
    let mut position = vec![usize::MAX; model.num_vars];
    for (index, &var) in free.iter().enumerate() {
        position[var] = index;
    }

    let mut kept: Vec<usize> = Vec::new();
    let mut constraints: Vec<PbConstraint> = Vec::new();
    for row in 0..model.rows.len() {
        let Some(residual) = model.residual(row, fixed) else {
            return Err("overflow".into());
        };
        if residual.degree <= residual.least {
            continue; // Holds under every free assignment: not part of this node.
        }
        let terms: Vec<PbTerm> = model.rows[row]
            .iter()
            .filter(|&&(var, _)| fixed[var].is_none())
            .map(|&(var, coefficient)| PbTerm {
                coeff: coefficient,
                lits: vec![PbLit {
                    var: (position[var] + 1) as u32,
                    negated: false,
                }],
            })
            .collect();
        if terms.is_empty() {
            // No free support and not discharged means the row is already
            // violated; `single_row_farkas` owns that node and is tried first.
            return Err("row-violated-under-the-fixings".into());
        }
        kept.push(row);
        constraints.push(PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs: residual.degree,
        });
    }
    if constraints.is_empty() {
        return Err("every-row-discharged".into());
    }

    let objective_terms: Vec<PbTerm> = free
        .iter()
        .filter(|&&var| model.objective[var] != 0)
        .map(|&var| PbTerm {
            coeff: model.objective[var],
            lits: vec![PbLit {
                var: (position[var] + 1) as u32,
                negated: false,
            }],
        })
        .collect();
    if objective_terms.is_empty() {
        // Every remaining objective coefficient is already fixed; the node bound
        // is a constant and `try_leaf` with `ys = []`, `qo = 1` decides it.
        return Err("free-objective-is-empty".into());
    }
    let objective = PbObjective {
        terms: objective_terms,
    };

    // The residual LP's own target: the node closes when
    // `Σ_{v ∈ F1} c_v + residual >= optimum`.
    let mut base = 0_i128;
    for var in 0..model.num_vars {
        if fixed[var] == Some(true) {
            let Some(next) = base.checked_add(model.objective[var]) else {
                return Err("overflow".into());
            };
            base = next;
        }
    }
    let Some(target) = optimum.checked_sub(base) else {
        return Err("overflow".into());
    };

    // TWO caps, both COUNTS. The per-solve one exists because this route runs an
    // LP per node: a budget that is generous for a single solve is the whole
    // route's cost when there are hundreds.
    let entry = polls.get();
    let Ok(num_free) = u32::try_from(free.len()) else {
        return Err("too-many-free-variables".into());
    };
    let raw = lp_dual_raw_diagnosed(
        &objective,
        &constraints,
        num_free,
        Some(target),
        Some(MAX_LEAF_SCALE),
        &|| {
            let spent = polls.get().saturating_add(1);
            polls.set(spent);
            spent > MAX_TOTAL_LP_POLLS || spent.saturating_sub(entry) > budget
        },
    )
    .map_err(|decline| decline.label())?;
    if raw.num_constraint_rows != constraints.len() {
        return Err("row-count".into());
    }

    let row_duals = &raw.duals[..raw.num_constraint_rows];
    let mut duals: Vec<(usize, BigRational)> = Vec::new();
    let mut exact = Some(BigInt::from(1));
    for (index, dual) in row_duals.iter().enumerate() {
        if dual.is_negative() {
            return Err("negative-row-dual".into());
        }
        if dual.is_zero() {
            continue;
        }
        // The exact common denominator is worth having when it is small; when it
        // is not — the f64 tier's binary expansions — the ladder takes over.
        if let Some(scale) = exact.take() {
            let denominator = dual.denom();
            if denominator.sign() == Sign::Plus {
                let mut a = scale.clone();
                let mut b = denominator.clone();
                while b.sign() != Sign::NoSign {
                    let remainder = &a % &b;
                    a = b;
                    b = remainder;
                }
                if a.sign() != Sign::NoSign {
                    let lcm = &scale / a * denominator;
                    if lcm <= BigInt::from(MAX_LEAF_SCALE) {
                        exact = Some(lcm);
                    }
                }
            }
        }
        duals.push((kept[index], dual.clone()));
    }
    let point = raw.primal.as_ref().and_then(|values| {
        (values.len() == free.len()).then(|| {
            free.iter()
                .zip(values)
                .map(|(&var, value)| (var, value.clone()))
                .collect()
        })
    });
    Ok(NodeLp {
        duals,
        exact_scale: exact.and_then(|scale| scale.to_i128()),
        point,
    })
}

/// Whether re-running [`solve_node_lp`] on the SAME node with a bigger poll
/// allowance could give a different answer.
///
/// [`LpDualDecline::NoDualPoint`] is the only refusal in the whole set that is
/// about the budget. Every other one — a static size cap that rejected the model
/// UNREAD, a row already violated by the fixings, an empty free objective, an
/// overflow — is a fact about this node's model, decided before a single poll is
/// spent and identical however many are offered. Escalating those re-builds the
/// node model and re-derives the same refusal, which on the 17 corpus instances
/// the size cap rejects is a second pass over up to 61,821 rows PER NODE for an
/// answer already in hand.
///
/// Comparing against `label()` rather than a literal keeps the two ends from
/// drifting: if the decline is ever renamed, this predicate moves with it.
fn refusal_can_change_with_a_bigger_budget(reason: &str) -> bool {
    reason == LpDualDecline::NoDualPoint.label()
}

/// Completes a node's fixings with an LP point and returns the assignment ONLY
/// if it is a genuine counterexample to the claimed optimum.
///
/// THIS IS THE FUNCTION THAT SEPARATES THE TWO PREMISES. An integral node LP
/// inside the refuted budget is a HINT that a better solution exists; it is not
/// evidence, because the node relaxation is a relaxation — it has fewer rows
/// than the instance (discharged ones), and a modelling defect that drops too
/// many makes almost any point look integral and almost any bound look
/// achievable. That is precisely how the prototype came to print "the claimed
/// optimum is WRONG" about four optima that are correct.
///
/// So the point is CHECKED, against the ORIGINAL instance, with the objective
/// recomputed exactly. What comes back is either a witness anybody can verify or
/// nothing at all.
fn witness_from_point(
    instance: &PbInstance,
    model: &Model,
    fixed: &[Option<bool>],
    point: Option<&[(usize, BigRational)]>,
    optimum: i128,
) -> Option<(Vec<bool>, i128)> {
    let mut assignment = vec![false; model.num_vars];
    for (var, slot) in fixed.iter().enumerate() {
        match slot {
            Some(value) => assignment[var] = *value,
            None => {
                // A free variable needs an integral value from the LP; anything
                // fractional (or missing) means there is no candidate point here.
                let values = point?;
                let (_, value) = values.iter().find(|&&(candidate, _)| candidate == var)?;
                if value.is_integer() {
                    assignment[var] = !value.is_zero();
                } else {
                    return None;
                }
            }
        }
    }
    if !crate::eval::verify_all_constraints(&instance.constraints, &assignment) {
        return None;
    }
    let value = evaluate_linear_objective(instance.objective.as_ref()?, &assignment)?;
    (value < optimum).then_some((assignment, value))
}

/// Formats one `pol` line: `Σ operand·multiplier`.
fn pol_line(terms: &[(String, i128)]) -> Option<String> {
    let mut expression = String::new();
    for (operand, multiplier) in terms {
        if *multiplier <= 0 {
            continue;
        }
        let piece = if *multiplier == 1 {
            operand.clone()
        } else {
            format!("{operand} {multiplier} *")
        };
        if expression.is_empty() {
            expression = piece;
        } else {
            expression.push_str(&format!(" {piece} +"));
        }
    }
    if expression.is_empty() {
        return None;
    }
    expression.push_str(" ;");
    Some(expression)
}

/// Formats a branch clause as the inline OPB constraint a `rup` line carries:
/// `1 ~x3 1 x7 >= 1 ;`. An EMPTY clause renders as `>= 1 ;`, the contradiction.
fn clause_body(clause: &[(usize, bool)]) -> Option<String> {
    let mut body = String::new();
    for &(var, negated) in clause {
        let index = var.checked_add(1)?;
        let tilde = if negated { "~" } else { "" };
        body.push_str(&format!("1 {tilde}x{index} "));
    }
    body.push_str(">= 1 ;");
    Some(body)
}

/// The mutable state one depth-first search carries.
struct Search<'a> {
    instance: &'a PbInstance,
    model: &'a Model,
    optimum: i128,
    /// Id of the `soli`-installed objective-improving row.
    soli: ConstraintId,
    fixed: Vec<Option<bool>>,
    writer: VeriPbWriter<Vec<u8>>,
    polls: std::cell::Cell<u64>,
    stats: Stats,
    /// Ancestor multiplier vectors, replayed at every node before the LP runs.
    /// Slot 0, once filled, is the ROOT's — the strongest global dual this
    /// search ever sees, because the root is the only solve that gets
    /// `MAX_ROOT_LP_POLLS`. See [`MAX_DUAL_POOL`].
    pool: Vec<(Vec<(usize, i128)>, i128)>,
    /// The FIRST reason the node LP gave for refusing, verbatim.
    lp_decline: Option<String>,
    /// The caller's stop signal, consulted only past
    /// [`MAX_UNINTERRUPTIBLE_NODES`] so that a starved caller still gets every
    /// certificate this route makes. It can only ever turn a certificate into a
    /// decline; it never reaches the emitter, so no proof byte depends on it.
    should_stop: &'a dyn Fn() -> bool,
}

/// What one node resolved to.
enum NodeResult {
    /// A derived clause: its id and its support (0-based variables).
    Clause(ConstraintId, BTreeSet<usize>),
    Refuted(Vec<bool>, i128),
    Exhausted(&'static str),
}

impl Search<'_> {
    /// Emits one leaf as `pol` (the aggregate row) then `rup` (the branch
    /// clause), and returns the CLAUSE's id — the one the resolution above it
    /// cites.
    ///
    /// WHY THE LITERAL AXIOMS ARE GONE. They existed only to CANCEL the free
    /// variables' coefficients so that one division could round what survived
    /// into the branch clause. `rup` does not need them cancelled; it needs the
    /// aggregate row FALSIFIED under the negated clause, and [`try_leaf`]'s own
    /// `R > 0` test is exactly that statement (`R` is the row's degree minus
    /// the most its left-hand side can reach under this node's fixings). The
    /// negated clause fixes every variable the leaf's degree was charged for as
    /// a fixing, and leaves free exactly the ones charged at `max(0, c_v)` —
    /// so the reachable maximum under the negation is the same `R`-defining
    /// quantity, the aggregate row's slack goes negative with no propagation
    /// needed, and the substitution cannot lose a leaf that the axiom block
    /// would have closed.
    ///
    /// The axiom block was also the bulk of the bytes: one term per variable
    /// with a non-zero aggregate coefficient, against one term per BRANCH
    /// literal here.
    fn emit_leaf(&mut self, leaf: &Leaf) -> Option<ConstraintId> {
        let mut terms: Vec<(String, i128)> = Vec::new();
        for &(row, multiplier) in &leaf.ys {
            terms.push(((row + 1).to_string(), multiplier));
        }
        if leaf.qo > 0 {
            terms.push((self.soli.get().to_string(), leaf.qo));
        }
        let expression = pol_line(&terms)?;
        let clause = clause_body(&leaf.clause)?;
        self.writer
            .log_step(ProofStep::Polynomial(expression))
            .ok()?;
        self.writer.log_step(ProofStep::Rup(clause)).ok()
    }

    /// Adds a multiplier vector to the replay pool, newest last, root pinned.
    ///
    /// FIFO above slot 0 and deduplicated BY CONTENT, so the pool a node sees is
    /// a function of the tree walked so far and of nothing else — the same
    /// determinism requirement the branch rule and the poll budgets carry.
    fn remember(&mut self, ys: &[(usize, i128)], qo: i128) {
        if ys.is_empty() && qo == 0 {
            return;
        }
        if self
            .pool
            .iter()
            .any(|(pooled, pooled_qo)| *pooled_qo == qo && pooled.as_slice() == ys)
        {
            return;
        }
        if self.pool.len() >= MAX_DUAL_POOL {
            // Slot 0 is the root's and is never evicted; the oldest of the rest
            // goes.
            self.pool.remove(1.min(self.pool.len() - 1));
        }
        self.pool.push((ys.to_vec(), qo));
    }

    fn dfs(&mut self, depth: usize, inherited: Option<&[(usize, BigRational)]>) -> NodeResult {
        self.stats.nodes = self.stats.nodes.saturating_add(1);
        self.stats.depth = self.stats.depth.max(depth);
        if self.stats.nodes > MAX_NODES {
            return NodeResult::Exhausted("node-budget");
        }
        if depth >= MAX_DEPTH {
            return NodeResult::Exhausted("depth-budget");
        }
        if self.polls.get() > MAX_TOTAL_LP_POLLS {
            return NodeResult::Exhausted("lp-poll-budget");
        }
        // Past the envelope in which this route has ever certified anything —
        // in EITHER of the two currencies it spends — the caller may stop it.
        // See [`MAX_UNINTERRUPTIBLE_NODES`].
        if (self.stats.nodes > MAX_UNINTERRUPTIBLE_NODES
            || self.polls.get() > MAX_UNINTERRUPTIBLE_POLLS)
            && (self.should_stop)()
        {
            return NodeResult::Exhausted("interrupted");
        }

        // 1. The node's rows are already contradictory through one of them.
        //    Exact, no LP, and it cites no objective.
        if let Some(leaf) = single_row_farkas(self.model, &self.fixed, self.optimum) {
            self.stats.farkas = self.stats.farkas.saturating_add(1);
            return self.close(&leaf);
        }
        // 2. Every objective coefficient that matters is already fixed, and the
        //    fixed part alone exceeds the refuted budget.
        if let Some(leaf) = try_leaf(self.model, &self.fixed, &[], 1, self.optimum) {
            return self.close(&leaf);
        }
        // 3. REPLAY. An ancestor's multipliers, re-derived against THIS node's
        //    fixings. Monotone (see `MAX_DUAL_POOL`) and free of polls, so it is
        //    tried before the LP rather than after it.
        let model = self.model;
        let optimum = self.optimum;
        let fixed = &self.fixed;
        let replayed = self
            .pool
            .iter()
            .find_map(|(ys, qo)| try_leaf(model, fixed, ys, *qo, optimum));
        if let Some(leaf) = replayed {
            self.stats.replays = self.stats.replays.saturating_add(1);
            return self.close(&leaf);
        }

        // The root is a full model with no fixings and is solved ONCE, at its own
        // allowance. Below it the fast pass runs first and only a REFUSAL buys
        // the full one — see [`MAX_NODE_LP_POLLS_FAST`].
        let mut lp = solve_node_lp(
            self.model,
            &self.fixed,
            self.optimum,
            &self.polls,
            if depth == 0 {
                MAX_ROOT_LP_POLLS
            } else {
                MAX_NODE_LP_POLLS_FAST
            },
        );
        // ...and only a refusal a bigger allowance could actually change. Every
        // other one is decided before the first poll and re-deriving it costs a
        // second full node-model build for a known answer.
        if depth > 0
            && lp
                .as_ref()
                .err()
                .is_some_and(|reason| refusal_can_change_with_a_bigger_budget(reason))
        {
            self.stats.escalations = self.stats.escalations.saturating_add(1);
            let full = solve_node_lp(
                self.model,
                &self.fixed,
                self.optimum,
                &self.polls,
                MAX_NODE_LP_POLLS,
            );
            // A second refusal keeps the FIRST reason, which is the one the
            // diagnosis reports and the one that names the model.
            if full.is_ok() {
                lp = full;
            }
        }
        if let Err(reason) = &lp {
            // Kept for the diagnosis so a decline NAMES the LP's own refusal
            // (`model-too-large(MAX_ROWS=40000,measured=43326)`) instead of
            // reporting the generic "no dual point here".
            if self.lp_decline.is_none() {
                self.lp_decline = Some(reason.clone());
            }
        }
        if let Ok(node) = lp.as_ref() {
            for scale in node.scales() {
                let Some(ys) = node.scaled(scale) else {
                    continue;
                };
                // 3. The objective leaf: the node's dual bound exceeds the
                //    refuted budget. Cites the `soli` row at the SAME scale as
                //    the rows, which is what makes the single `d K` at the end
                //    round the degree without disturbing any ratio.
                if let Some(leaf) = try_leaf(self.model, &self.fixed, &ys, scale, self.optimum) {
                    self.remember(&ys, scale);
                    return self.close(&leaf);
                }
                // 4. The same multipliers with `qo = 0`: a multi-row Farkas
                //    leaf, for a node closed by its rows alone rather than by
                //    its bound.
                if let Some(leaf) = try_leaf(self.model, &self.fixed, &ys, 0, self.optimum) {
                    self.stats.farkas = self.stats.farkas.saturating_add(1);
                    self.remember(&ys, 0);
                    return self.close(&leaf);
                }
            }
        }

        // Nothing closed it here — but by monotonicity the same vector is
        // stronger at every descendant, so it goes into the pool on the way
        // down. The LARGEST ladder scale is the one kept: `R` is very nearly
        // linear in the scale, so the largest is where the floor of each dual
        // costs the least relative to the numbers it rounds.
        if let Ok(node) = lp.as_ref() {
            let widest = node
                .scales()
                .filter_map(|scale| node.scaled(scale).map(|ys| (ys, scale)))
                .filter(|(ys, _)| !ys.is_empty())
                .max_by_key(|&(_, scale)| scale);
            if let Some((ys, scale)) = widest {
                self.remember(&ys, scale);
            }
        }

        // Nothing closed it. Pick a branch variable: this node's own point
        // first, then the nearest ancestor's, then the objective.
        let own_point = lp.as_ref().ok().and_then(|node| node.point.as_deref());
        // An integral point that completes to a re-verified feasible assignment
        // BELOW the claim is the one thing this route says about the instance
        // rather than about itself, and it must be reported before any fallback
        // branches past it.
        if own_point.is_some_and(|point| branch_variable(point, &self.fixed).is_none()) {
            if let Some((witness, value)) = witness_from_point(
                self.instance,
                self.model,
                &self.fixed,
                own_point,
                self.optimum,
            ) {
                return NodeResult::Refuted(witness, value);
            }
        }
        let guide: Option<&[(usize, BigRational)]> = own_point.or(inherited);
        let from_point = guide.and_then(|point| branch_variable(point, &self.fixed));
        if from_point.is_none() || own_point.is_none() {
            self.stats.guided = self.stats.guided.saturating_add(1);
            // THE BLIND PATH IS BOUNDED, AND BY A COUNT. This node has no fresh
            // relaxation steering it, so the poll budget — the only thing that
            // bounded this route's cost — did not necessarily move. See
            // [`MAX_BLIND_NODES`] for the 436x wall that fact opened.
            if self.stats.guided > MAX_BLIND_NODES {
                return NodeResult::Exhausted("blind-branch-budget");
            }
        }
        let branch = from_point.or_else(|| fallback_branch_variable(self.model, &self.fixed));
        let Some(variable) = branch else {
            // Every variable is fixed and nothing above closed the node. That is
            // not reachable through `fallback_branch_variable` — an all-fixed
            // node is closed by `single_row_farkas` or by the objective leaf —
            // but the route names it rather than assuming it.
            return NodeResult::Exhausted("no-branch-variable");
        };

        self.fixed[variable] = Some(true);
        let one = self.dfs(depth + 1, guide);
        self.fixed[variable] = None;
        let (one_id, one_support) = match one {
            NodeResult::Clause(id, support) => (id, support),
            other => return other,
        };
        if !one_support.contains(&variable) {
            // The subtree closed without ever needing the fixing: its clause
            // dominates, and the sibling need not be explored.
            return NodeResult::Clause(one_id, one_support);
        }

        self.fixed[variable] = Some(false);
        let zero = self.dfs(depth + 1, guide);
        self.fixed[variable] = None;
        let (zero_id, zero_support) = match zero {
            NodeResult::Clause(id, support) => (id, support),
            other => return other,
        };
        if !zero_support.contains(&variable) {
            return NodeResult::Clause(zero_id, zero_support);
        }

        // Resolution. The two clauses share the ancestors' branch literals at the
        // SAME polarity and disagree only on `variable`, so the sum cancels it
        // exactly and `s` caps the shared literals back to 1.
        let Ok(resolved) = self
            .writer
            .log_step(ProofStep::Polynomial(format!("{one_id} {zero_id} + s ;")))
        else {
            return NodeResult::Exhausted("emit-failed");
        };
        let mut support: BTreeSet<usize> = one_support.union(&zero_support).copied().collect();
        support.remove(&variable);
        NodeResult::Clause(resolved, support)
    }

    fn close(&mut self, leaf: &Leaf) -> NodeResult {
        self.stats.leaves = self.stats.leaves.saturating_add(1);
        match self.emit_leaf(leaf) {
            Some(id) => NodeResult::Clause(id, leaf.support.clone()),
            None => NodeResult::Exhausted("emit-failed"),
        }
    }
}

/// The most fractional STILL-FREE variable of a point, ties broken by the
/// lowest index.
///
/// Deterministic by construction: the comparison is on exact rationals and the
/// tie-break is total, so the tree this route walks is the same on every machine.
///
/// `fixed` is consulted because the point may be an INHERITED one — an
/// ancestor's, carried down by [`Search::dfs`] — in which case some of the
/// variables it scores have been fixed by the branches taken since.
fn branch_variable(point: &[(usize, BigRational)], fixed: &[Option<bool>]) -> Option<usize> {
    let half = BigRational::new(BigInt::from(1), BigInt::from(2));
    let mut best: Option<(usize, BigRational)> = None;
    for (var, value) in point {
        if fixed[*var].is_some() || value.is_integer() {
            continue;
        }
        let distance = (value - &half).abs();
        let replace = match &best {
            None => true,
            Some((_, incumbent)) => distance < *incumbent,
        };
        if replace {
            best = Some((*var, distance));
        }
    }
    best.map(|(var, _)| var)
}

/// The last-resort branch variable: the free variable with the largest absolute
/// objective coefficient, ties broken by the lowest index.
///
/// # Why a search with NO usable point must still branch
///
/// The prototype's structure, which this port inherited, ended the WHOLE search
/// when one node's LP produced no fractional point: `Exhausted` propagates to
/// the root, so a single refused relaxation at depth 47 threw away a tree that
/// was two thirds inside its budget (`ii16d2`: 48 nodes, 0 leaves, 10,256 of
/// 32,768 polls spent). That is a fact about the LP's budget at ONE node, and
/// nothing about whether the tree closes.
///
/// It is also unnecessary, because branching needs no LP at all — only a free
/// variable — and it TERMINATES: each branch fixes one more variable, and an
/// all-fixed node always resolves. Either some original row is violated, and
/// [`single_row_farkas`] closes it; or the assignment is feasible with value
/// `V`, and `try_leaf(&[], 1, optimum)` has degree `1 + V - optimum`, which is
/// positive exactly when `V >= optimum` and otherwise means the node completes
/// to a genuine counterexample that [`witness_from_point`] reports. So the
/// fallback cannot loop and cannot invent a leaf: `try_leaf` is still the only
/// thing that emits one.
///
/// The objective coefficient is the ranking because it is the only per-variable
/// signal available without a relaxation, and it is exactly what moves the
/// degree of the objective leaf: fixing `v` to 1 adds `qo * c_v` to `R`.
fn fallback_branch_variable(model: &Model, fixed: &[Option<bool>]) -> Option<usize> {
    let mut best: Option<(usize, i128)> = None;
    for var in 0..model.num_vars {
        if fixed[var].is_some() {
            continue;
        }
        let weight = model.objective[var].saturating_abs();
        if best.is_none_or(|(_, incumbent)| weight > incumbent) {
            best = Some((var, weight));
        }
    }
    best.map(|(var, _)| var)
}

fn run(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
    should_stop: &dyn Fn() -> bool,
) -> Run {
    let Some(model) = build_model(instance) else {
        return Run {
            lp_decline: None,
            outcome: Outcome::Exhausted("shape"),
            stats: Stats::default(),
        };
    };
    if incumbent.len() != model.num_vars {
        return Run {
            lp_decline: None,
            outcome: Outcome::Exhausted("shape"),
            stats: Stats::default(),
        };
    }
    let Some(objective) = instance.objective.as_ref() else {
        return Run {
            lp_decline: None,
            outcome: Outcome::Exhausted("shape"),
            stats: Stats::default(),
        };
    };
    if evaluate_linear_objective(objective, incumbent) != Some(optimum)
        || !crate::eval::verify_all_constraints(&instance.constraints, incumbent)
    {
        // The upper bound is not established, so there is nothing to close a
        // lower bound against. This is the cheap guard, not the premise: the
        // premise is `Outcome::Refuted`, which needs a witness.
        return Run {
            lp_decline: None,
            outcome: Outcome::Exhausted("incumbent-does-not-achieve-the-claim"),
            stats: Stats::default(),
        };
    }
    let Ok(input_count) = veripb_input_constraint_count(instance) else {
        return Run {
            lp_decline: None,
            outcome: Outcome::Exhausted("input-count"),
            stats: Stats::default(),
        };
    };
    if input_count != model.rows.len() as u64 {
        // `>=`-only inputs are one id each; anything else means this module's
        // `row + 1` id arithmetic would be citing the wrong rows.
        return Run {
            lp_decline: None,
            outcome: Outcome::Exhausted("input-count"),
            stats: Stats::default(),
        };
    }
    let Ok(mut writer) = VeriPbWriter::new(Vec::<u8>::new(), input_count) else {
        return Run {
            lp_decline: None,
            outcome: Outcome::Exhausted("emit-failed"),
            stats: Stats::default(),
        };
    };
    let Ok(soli) = writer.log_step(ProofStep::SolutionImproving(format_assignment(incumbent)))
    else {
        return Run {
            lp_decline: None,
            outcome: Outcome::Exhausted("emit-failed"),
            stats: Stats::default(),
        };
    };

    let mut search = Search {
        instance,
        model: &model,
        optimum,
        soli,
        fixed: vec![None; model.num_vars],
        writer,
        polls: std::cell::Cell::new(0),
        stats: Stats::default(),
        pool: Vec::new(),
        lp_decline: None,
        should_stop,
    };
    let root = search.dfs(0, None);
    let mut stats = search.stats;
    stats.polls = search.polls.get();
    let lp_decline = search.lp_decline.clone();
    let done = |outcome| Run {
        outcome,
        stats,
        lp_decline: lp_decline.clone(),
    };
    let (root_id, support) = match root {
        NodeResult::Clause(id, support) => (id, support),
        NodeResult::Refuted(witness, value) => return done(Outcome::Refuted { witness, value }),
        NodeResult::Exhausted(reason) => return done(Outcome::Exhausted(reason)),
    };
    if !support.is_empty() {
        return done(Outcome::Exhausted("root-clause-not-empty"));
    }
    let mut writer = search.writer;
    if writer.set_opt_bounds(optimum, optimum).is_err()
        || writer
            .conclude_opt_hinted(Some(root_id), Some(&format_assignment(incumbent)))
            .is_err()
    {
        return done(Outcome::Exhausted("emit-failed"));
    }
    let Ok(text) = String::from_utf8(writer.into_inner()) else {
        return done(Outcome::Exhausted("emit-failed"));
    };
    // Layer 4: parse the emitted bytes BACK and replay them against an
    // independent cutting-planes interpreter with VeriPB's own semantics. The
    // route returns nothing unless those bytes, read cold, refute
    // `obj <= optimum - 1` for this instance.
    if !self_check_soli_refutation(&text, instance, incumbent, optimum, root_id.get()) {
        return done(Outcome::Exhausted("self-check-rejected-the-emitted-bytes"));
    }
    done(Outcome::Proof(text))
}

/// Implements the public contract in [`super::certify_opt_lin_certified_bb`].
///
/// The uninterruptible entry: a caller with no stop signal at all. Kept because
/// the probes, the census and every test want the route's own counts, not a
/// reading of how busy the box was.
pub(super) fn certify_opt_lin_certified_bb(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
) -> Option<String> {
    certify_opt_lin_certified_bb_interruptible(instance, incumbent, optimum, &|| false)
}

/// Implements the public contract in
/// [`super::certify_opt_lin_certified_bb_interruptible`].
pub(super) fn certify_opt_lin_certified_bb_interruptible(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
    should_stop: &dyn Fn() -> bool,
) -> Option<String> {
    let Run { outcome, stats, .. } = run(instance, incumbent, optimum, should_stop);
    match outcome {
        Outcome::Proof(text) => {
            if ay_core::misc_cli_flags().cert_debug {
                eprintln!("c [cert/certified-bb] certified {stats}");
            }
            Some(text)
        }
        Outcome::Refuted { value, .. } => {
            // A certificate route must never change a verdict, so this emits
            // nothing — but it is the one decline that is ABOUT the instance
            // rather than about the budget, and losing that distinction is what
            // the `Outcome` type exists to prevent.
            if ay_core::misc_cli_flags().cert_debug {
                eprintln!(
                    "c [cert/certified-bb] REFUTED: a re-verified feasible witness \
                     achieves {value} < the claimed optimum {optimum} [{stats}]"
                );
            }
            None
        }
        Outcome::Exhausted(reason) => {
            if ay_core::misc_cli_flags().cert_debug {
                eprintln!("c [cert/certified-bb] declined({reason}) {stats}");
            }
            None
        }
    }
}

/// Names what the search concluded, for the census and for tests.
///
/// MEASUREMENT ONLY, and it is the entry point that keeps the two premises
/// apart in writing: `refuted-by-witness(...)` is a claim about the INSTANCE and
/// `exhausted(...)` is a claim about this ROUTE. Never called by the production
/// certificate chain.
pub(super) fn certified_bb_diagnosis(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
) -> String {
    let Run {
        outcome,
        stats,
        lp_decline,
    } = run(instance, incumbent, optimum, &|| false);
    let lp = lp_decline.map_or_else(String::new, |reason| format!(" lp={reason}"));
    match outcome {
        Outcome::Proof(text) => format!("certified(bytes={}) {stats}{lp}", text.len()),
        Outcome::Refuted { value, .. } => {
            format!("refuted-by-witness(value={value},claimed={optimum}) {stats}{lp}")
        }
        Outcome::Exhausted(reason) => format!("exhausted({reason}) {stats}{lp}"),
    }
}

#[cfg(test)]
mod tests {
    use super::{
        certified_bb_diagnosis, certify_opt_lin_certified_bb, fallback_branch_variable,
        single_row_farkas, try_leaf, MAX_BLIND_NODES, MAX_DEPTH, MAX_DUAL_POOL, MAX_NODES,
        MAX_NODE_LP_POLLS, MAX_NODE_LP_POLLS_FAST, MAX_ROOT_LP_POLLS, MAX_TOTAL_LP_POLLS,
        MAX_UNINTERRUPTIBLE_NODES, MAX_UNINTERRUPTIBLE_POLLS,
    };
    use crate::optimize::lp_bound::LpDualDecline;
    use crate::proof::cert::cp_replay::self_check_soli_refutation;
    use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective, PbRel, PbTerm};

    fn term(coeff: i128, var: u32, negated: bool) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![PbLit { var, negated }],
        }
    }

    /// The PETERSEN GRAPH's minimum vertex cover, and the reason it is the
    /// generality probe rather than a convenience.
    ///
    /// Its independence number is 4, so the optimum is `10 - 4 = 6`; the
    /// all-half point is feasible for the covering LP at value 5, so
    /// `ceil(LP*) = 5 < 6` and NO LP-dual floor can reach the bound. A SPLIT has
    /// to fire for this to certify at all — which is exactly what
    /// `benchmarks/pb-comp/test-instances/optimization-small.opb` did NOT probe
    /// (`LP* = 3 = optimum`, no split, so that run exercised the parser and the
    /// emitter and none of the argument).
    fn petersen_vertex_cover() -> (PbInstance, Vec<bool>, i128) {
        let edges: [(u32, u32); 15] = [
            (1, 2),
            (2, 3),
            (3, 4),
            (4, 5),
            (5, 1),
            (1, 6),
            (2, 7),
            (3, 8),
            (4, 9),
            (5, 10),
            (6, 8),
            (8, 10),
            (10, 7),
            (7, 9),
            (9, 6),
        ];
        let constraints = edges
            .iter()
            .map(|&(a, b)| PbConstraint {
                terms: vec![term(1, a, false), term(1, b, false)],
                rel: PbRel::Ge,
                rhs: 1,
            })
            .collect();
        let instance = PbInstance {
            num_vars: 10,
            num_constraints: 15,
            constraints,
            objective: Some(PbObjective {
                terms: (1..=10).map(|v| term(1, v, false)).collect(),
            }),
        };
        // Complement of the independent set {1, 3, 9, 10} (0-based {0,2,8,9}).
        let mut incumbent = vec![true; 10];
        for v in [1usize, 3, 9, 10] {
            incumbent[v - 1] = false;
        }
        (instance, incumbent, 6)
    }

    /// END TO END, on the one shape that needs the split. `ceil(LP*) = 5` here,
    /// so a certificate at 6 is evidence the literal case-split fired and its
    /// leaves resolved to the empty clause — the whole argument, in one assert.
    #[test]
    fn petersen_vertex_cover_certifies_through_a_split() {
        let (instance, incumbent, optimum) = petersen_vertex_cover();
        let proof = certify_opt_lin_certified_bb(&instance, &incumbent, optimum)
            .expect("the split certificate must emit for an instance no LP floor reaches");
        assert!(
            proof.contains("conclusion BOUNDS 6 :"),
            "equal bounds at the optimum, got:\n{proof}"
        );
        assert!(
            proof.lines().any(|line| line.ends_with("+ s ;")),
            "a split must resolve at least once, got:\n{proof}"
        );
        assert!(
            proof.lines().any(|line| line.starts_with("soli ")),
            "the upper bound is the logged solution, got:\n{proof}"
        );
    }

    /// FAIL CLOSED, THE PREMISE THAT SHOULD FIRE. A wrong optimum supplied WITH
    /// A MATCHING FEASIBLE WITNESS — so the cheap "the incumbent does not
    /// achieve the claim" guard cannot be what refuses it — must produce no
    /// bytes AND must say the thing it can prove: that a better point exists.
    #[test]
    fn a_wrong_optimum_with_a_matching_witness_is_refuted_by_a_witness() {
        let (instance, _, _) = petersen_vertex_cover();
        // Every vertex but one: feasible, value 9, and 9 > 6 is wrong.
        let mut incumbent = vec![true; 10];
        incumbent[0] = false;
        assert!(
            certify_opt_lin_certified_bb(&instance, &incumbent, 9).is_none(),
            "a certificate for a value the instance beats is the worst defect here"
        );
        let diagnosis = certified_bb_diagnosis(&instance, &incumbent, 9);
        assert!(
            diagnosis.starts_with("refuted-by-witness("),
            "the refusal must be the one BACKED BY A WITNESS, got: {diagnosis}"
        );
    }

    /// FAIL CLOSED, AND THE PREMISE THAT MUST NOT FIRE. An incumbent that does
    /// not achieve the claim is a caller error, not a refutation of the optimum;
    /// saying `refuted-by-witness` here would be the accusation-for-a-bad-reason
    /// this route's `Outcome` type exists to prevent.
    #[test]
    fn an_incumbent_that_misses_the_claim_is_not_an_accusation() {
        let (instance, incumbent, _) = petersen_vertex_cover();
        assert!(certify_opt_lin_certified_bb(&instance, &incumbent, 5).is_none());
        let diagnosis = certified_bb_diagnosis(&instance, &incumbent, 5);
        assert_eq!(
            diagnosis.split_whitespace().next(),
            Some("exhausted(incumbent-does-not-achieve-the-claim)"),
            "got: {diagnosis}"
        );
    }

    /// SHAPE GATES, both fail-closed. `=` rows would need VeriPB's two-id split
    /// carried through every `pol` this module writes, and a negated objective
    /// literal would need a constant folded identically in three places. Both
    /// decline rather than being modelled once and mis-modelled elsewhere.
    #[test]
    fn equality_rows_and_negated_objective_literals_decline() {
        let (base, incumbent, optimum) = petersen_vertex_cover();

        let mut with_equality = base.clone();
        with_equality.constraints[0].rel = PbRel::Eq;
        assert!(certify_opt_lin_certified_bb(&with_equality, &incumbent, optimum).is_none());

        let mut negated_objective = base;
        negated_objective.objective = Some(PbObjective {
            terms: (1..=10).map(|v| term(1, v, v == 1)).collect(),
        });
        assert!(certify_opt_lin_certified_bb(&negated_objective, &incumbent, optimum).is_none());
    }

    /// THE SELF-CHECK IS NOT A FORMALITY. Every one of these doctorings is a
    /// shape the pinned external checker also rejects (measured: the mutation
    /// battery on `g9x9` and `dominating_set_hexgrid_opt_r6_c50`), and the
    /// replay must catch them WITHOUT the checker — otherwise the route's
    /// layer-4 buys nothing and the first line of defence is a subprocess.
    #[test]
    fn the_replay_rejects_doctored_bytes() {
        let (instance, incumbent, optimum) = petersen_vertex_cover();
        let proof = certify_opt_lin_certified_bb(&instance, &incumbent, optimum).expect("emit");
        let cited: u64 = proof
            .lines()
            .find_map(|line| line.strip_prefix("conclusion BOUNDS "))
            .and_then(|rest| rest.split(" : ").nth(1))
            .and_then(|rest| rest.split_whitespace().next())
            .and_then(|id| id.parse().ok())
            .expect("the conclusion hints at a row id");
        assert!(
            self_check_soli_refutation(&proof, &instance, &incumbent, optimum, cited),
            "the untouched bytes must replay"
        );

        // 1. The bound one higher: the same derivation, a claim it does not make.
        let higher = proof.replace("conclusion BOUNDS 6 :", "conclusion BOUNDS 7 :");
        assert!(!self_check_soli_refutation(
            &higher, &instance, &incumbent, optimum, cited
        ));

        // 2. The `soli` line removed: the contradiction is then untainted, which
        //    would mean the FORMULA is unsatisfiable — impossible next to a
        //    re-verified feasible incumbent.
        let stripped: String = proof
            .lines()
            .filter(|line| !line.starts_with("soli "))
            .map(|line| format!("{line}\n"))
            .collect();
        assert!(!self_check_soli_refutation(
            &stripped, &instance, &incumbent, optimum, cited
        ));

        // 3. The logged solution is not the incumbent. Flip the FIRST literal
        //    whichever polarity it has — a "mutation" that silently matched
        //    nothing would be a test that passes by doing nothing.
        assert!(
            proof.contains("\nsoli ~x1 "),
            "this incumbent leaves x1 false"
        );
        let swapped = proof.replacen("\nsoli ~x1 ", "\nsoli x1 ", 1);
        assert_ne!(
            swapped, proof,
            "the mutation must actually change the bytes"
        );
        assert!(!self_check_soli_refutation(
            &swapped, &instance, &incumbent, optimum, cited
        ));

        // 4. The conclusion cites a row that is not the contradiction.
        assert!(!self_check_soli_refutation(
            &proof, &instance, &incumbent, optimum, 1
        ));
    }

    /// THE GUARD ON THE NEW RULE, AND THE ONE TEST THAT DECIDES WHETHER IT IS A
    /// GUARD AT ALL.
    ///
    /// A `rup` line is an ASSUMPTION until something replays it. If the
    /// self-check accepted anything shaped like a clause, this route would have
    /// swapped a derivation it checks (`pol`) for one it does not, and the layer
    /// that reads the emitted bytes cold would have stopped reading them. So
    /// each mutation below is a `rup` line the database does NOT imply, and each
    /// must be refused:
    ///
    /// 1. a branch literal at the WRONG POLARITY — the negation then fixes the
    ///    node's variables the other way, which is a different node;
    /// 2. the EMPTY CLAUSE in place of a real one (which, for a one-literal
    ///    leaf, is also "drop the branch literal") — the shape that would let a
    ///    single leaf close the whole tree;
    /// 3. the OBJECTIVE FLOOR `Σ_v x_v >= optimum`. This is the one that
    ///    separates "models RUP" from "checks whether the claim is true": it is
    ///    the very theorem this proof exists to establish, so it is TRUE, and it
    ///    is not reachable by unit propagation from the database — a
    ///    truth-checking guard would wave it through and let the certifier skip
    ///    the entire search.
    ///
    /// The `pol` line the leaf rests on is also deleted, on its own, to show the
    /// `rup` is not self-supporting: without the aggregate row in the database
    /// there is nothing for propagation to conflict against.
    #[test]
    fn the_replay_rejects_a_rup_line_the_database_does_not_imply() {
        let (instance, incumbent, optimum) = petersen_vertex_cover();
        let proof = certify_opt_lin_certified_bb(&instance, &incumbent, optimum).expect("emit");
        let cited: u64 = proof
            .lines()
            .find_map(|line| line.strip_prefix("conclusion BOUNDS "))
            .and_then(|rest| rest.split(" : ").nth(1))
            .and_then(|rest| rest.split_whitespace().next())
            .and_then(|id| id.parse().ok())
            .expect("the conclusion hints at a row id");
        assert!(
            self_check_soli_refutation(&proof, &instance, &incumbent, optimum, cited),
            "the untouched bytes must replay"
        );

        // The route must actually be using the rule under test. A battery that
        // mutates a line the proof does not contain passes by doing nothing.
        let rup: Vec<&str> = proof
            .lines()
            .filter(|line| line.starts_with("rup "))
            .collect();
        assert!(
            rup.len() > 1,
            "the leaves are `rup` lines now; got {} in {proof}",
            rup.len()
        );
        // The FIRST leaf, so the mutation lands where the database is smallest
        // and nothing later can accidentally rescue it.
        let target = *rup.first().expect("at least one leaf");
        assert!(
            target.contains('x'),
            "the first leaf carries a branch literal: {target}"
        );

        let mutate = |replacement: &str| proof.replacen(target, replacement, 1);

        // 1. Flip one branch literal's polarity.
        let flipped = if target.contains(" ~x") {
            target.replacen(" ~x", " x", 1)
        } else {
            target.replacen(" x", " ~x", 1)
        };
        assert_ne!(flipped, target, "the mutation must change the bytes");
        let bytes = mutate(&flipped);
        assert!(
            !self_check_soli_refutation(&bytes, &instance, &incumbent, optimum, cited),
            "a clause over the opposite fixings is a different node: {flipped}"
        );

        // 2. The empty clause in place of a leaf.
        let bytes = mutate("rup >= 1 ;");
        assert_ne!(bytes, proof, "the mutation must change the bytes");
        assert!(
            !self_check_soli_refutation(&bytes, &instance, &incumbent, optimum, cited),
            "one leaf must not be allowed to claim the contradiction"
        );

        // 3. TRUE, AND NOT RUP. The objective floor is what the whole proof is
        //    for, so a guard that asked "is this true?" would accept it — and
        //    accepting it here would let one line replace the search.
        let floor = format!(
            "rup {} >= {optimum} ;",
            (1..=10)
                .map(|v| format!("1 x{v}"))
                .collect::<Vec<_>>()
                .join(" ")
        );
        let bytes = mutate(&floor);
        assert_ne!(bytes, proof, "the mutation must change the bytes");
        assert!(
            !self_check_soli_refutation(&bytes, &instance, &incumbent, optimum, cited),
            "the theorem is not a unit-propagation consequence: {floor}"
        );

        // 4. The `pol` the leaf rests on, deleted. The `rup` survives, and the
        //    ids shift, so this also shows the replay is not merely counting
        //    lines.
        let leaf_index = proof
            .lines()
            .position(|line| line == target)
            .expect("the target leaf");
        let without_pol: String = proof
            .lines()
            .enumerate()
            .filter(|(index, _)| *index + 1 != leaf_index)
            .map(|(_, line)| format!("{line}\n"))
            .collect();
        assert_ne!(without_pol, proof, "the mutation must change the bytes");
        assert!(
            !self_check_soli_refutation(&without_pol, &instance, &incumbent, optimum, cited),
            "the `rup` is not self-supporting"
        );
    }

    /// The leaf substitution must not cost a leaf. Same instance, same search:
    /// every leaf the old axiom-and-division form could close, `rup` closes, so
    /// the tree is IDENTICAL — same nodes, same leaves, same depth — and the
    /// only thing that moved is the bytes.
    #[test]
    fn the_rup_leaf_keeps_the_tree_and_drops_the_axiom_block() {
        let (instance, incumbent, optimum) = petersen_vertex_cover();
        let proof = certify_opt_lin_certified_bb(&instance, &incumbent, optimum).expect("emit");
        // Every leaf is exactly one `pol` (the aggregate row) plus one `rup`
        // (the clause it falsifies); the remaining `pol`s are resolutions.
        let leaves = proof.lines().filter(|l| l.starts_with("rup ")).count();
        let diagnosis = certified_bb_diagnosis(&instance, &incumbent, optimum);
        let reported: usize = diagnosis
            .split_whitespace()
            .find_map(|field| field.strip_prefix("leaves="))
            .and_then(|value| value.parse().ok())
            .expect("the diagnosis reports a leaf count");
        assert_eq!(leaves, reported, "one `rup` per leaf: {diagnosis}");
        // The axiom block and its division are what came out. A stray `d` would
        // mean a leaf still carries one.
        assert!(
            !proof.lines().any(|line| line.starts_with("pol ")
                && line
                    .split_whitespace()
                    .any(|token| token == "d" || token.starts_with('~'))),
            "no leaf may still carry literal axioms or a division: {proof}"
        );
    }

    /// `try_leaf` IS THE SOUNDNESS BOUNDARY, so its refusal is worth pinning
    /// directly: multipliers that do not clear the refuted budget produce no
    /// leaf, whatever the LP thought of them.
    #[test]
    fn a_leaf_whose_degree_is_not_positive_is_refused() {
        let (instance, _, _) = petersen_vertex_cover();
        let model = super::build_model(&instance).expect("model");
        let fixed = vec![None; model.num_vars];
        // One edge row at multiplier 1 with no objective: `x_a + x_b >= 1` minus
        // the two axioms leaves degree 1 - 1 - 1 < 0. No leaf.
        assert!(try_leaf(&model, &fixed, &[(0, 1)], 0, 6).is_none());
        // The same row against the objective at scale 1 is the LP-dual floor of
        // ONE edge, which is nowhere near 6.
        assert!(try_leaf(&model, &fixed, &[(0, 1)], 1, 6).is_none());
        // Nothing at all cited is never a leaf.
        assert!(try_leaf(&model, &fixed, &[], 0, 6).is_none());
    }

    /// THE FARKAS LEAF THE PROTOTYPE DID NOT HAVE. Fix both endpoints of an edge
    /// to 0 and that row alone is violated; the leaf must exist, cite exactly
    /// that row, cite the objective NOT AT ALL, and carry both branch literals.
    #[test]
    fn a_violated_row_closes_without_the_objective() {
        let (instance, _, _) = petersen_vertex_cover();
        let model = super::build_model(&instance).expect("model");
        let mut fixed = vec![None; model.num_vars];
        fixed[0] = Some(false);
        fixed[1] = Some(false);
        let leaf = single_row_farkas(&model, &fixed, 6).expect("a violated row must close");
        assert_eq!(leaf.qo, 0, "a Farkas leaf must not cite the objective");
        assert_eq!(leaf.ys, vec![(0, 1)], "row 0 is `x1 + x2 >= 1`");
        assert_eq!(
            leaf.support,
            [0usize, 1].into_iter().collect(),
            "the clause is exactly the two branch literals"
        );
    }

    /// THE BUDGETS ARE COUNTS, AND THE ROOT'S IS THE ONE THAT DIFFERS. Pinned so
    /// a blind resize cannot silently cross a measured edge: at 128 polls the
    /// root of `f20c10b_008` produces no dual point at all, and at 4096
    /// EVERYWHERE `sbox_4_shg` spends the whole global budget without
    /// certifying.
    #[test]
    fn the_budgets_are_counts_and_sized_from_measurement() {
        assert!(
            MAX_ROOT_LP_POLLS > MAX_NODE_LP_POLLS,
            "the root solve is a full model and needs more than a guidance solve"
        );
        assert_eq!(
            MAX_ROOT_LP_POLLS, 4_096,
            "sized off lp_dual_floor::MAX_DUAL_SOLVE_POLLS' own measurement"
        );
        assert!(
            MAX_NODES >= 443,
            "443 is the heaviest measured certifying tree (sbox_4_shg, prototype guidance)"
        );
        assert!(
            MAX_TOTAL_LP_POLLS > 25_304,
            "cap {MAX_TOTAL_LP_POLLS} would decline sbox_4_shg, the heaviest measured \
             certifying member"
        );
        assert!(
            MAX_TOTAL_LP_POLLS <= 65_536,
            "past this the DECLINE ceiling (~80 s at 32,768) returns to the minute-scale \
             overshoot lp_dual_floor::MAX_DUAL_SOLVE_POLLS exists to close"
        );
        assert!(
            MAX_DEPTH > 187,
            "the measured injcomp non-closers reach depth 187; the node cap, not the \
             depth cap, must be what stops them"
        );
        assert!(
            MAX_NODE_LP_POLLS_FAST < MAX_NODE_LP_POLLS,
            "the fast pass must be cheaper than the full one or the escalation is a tax"
        );
        assert_eq!(
            MAX_NODE_LP_POLLS_FAST, 16,
            "sized from the measured population split: at 16 polls per node \
             m100_300_10_20.r's LP answers at EVERY node (guided=0) and the proof is \
             byte-identical to the 128-poll one, while addm4.r, fir04_trarea_ac and \
             f20c10b_008_area_delay get no point at ~half their nodes and escalate"
        );
        assert!(
            MAX_DUAL_POOL > 0,
            "a pool of nothing makes `remember` a no-op and every replay impossible"
        );
        assert!(
            MAX_BLIND_NODES < MAX_NODES,
            "a blind cap at or above the node cap is not a cap: the 436x wall on \
             50-250-false-45-90-4-2000opt is exactly a blind walk to MAX_NODES"
        );
        assert!(
            MAX_BLIND_NODES >= 14,
            "9symml branches blind 14 times on its way from 403 nodes to 1,859; below \
             14 this cap starts costing node throughput instead of only bounding waste"
        );
        assert!(
            MAX_BLIND_NODES < 142,
            "the smallest measured blind count above 9symml's 14 is ssa7552-159's 142, so \
             142 is the first cap that stops binding on a measured instance. NOT because \
             the counts 'jump 14 -> 145 with nothing in between' -- they do not; \
             ssa7552-159 is 142 and single-obj-f3 is 178, and the enumerated list in the \
             MAX_BLIND_NODES comment is not a complete census. What holds is one-sided \
             and is all this needs: among the caps that keep 9symml, the smallest \
             measured is the cheapest -- cap 64 costs vertexcover_..._dim_071 77.8 s \
             where cap 16 costs 22.9 s"
        );
        assert!(
            MAX_UNINTERRUPTIBLE_NODES >= 1_443,
            "1,443 is the largest tree this route has ever certified (m100_300_10_20.r); \
             below it a starved caller loses a certificate it gets today"
        );
        assert!(
            MAX_UNINTERRUPTIBLE_POLLS >= 21_735,
            "21,735 is the most polls any certificate this route has produced needed \
             (m100_300_10_20.r again); below it a starved caller loses that conversion"
        );
        assert!(
            MAX_UNINTERRUPTIBLE_NODES < MAX_NODES && MAX_UNINTERRUPTIBLE_POLLS < MAX_TOTAL_LP_POLLS,
            "at or above its own budget an escape is not an escape: this rung would be \
             uninterruptible again, which is the defect a --timeout has to reach"
        );
    }

    /// THE ESCALATION TEST IS A BUDGET REFUSAL, AND NOTHING ELSE.
    ///
    /// `model-too-large` is decided by a static size cap before the first poll,
    /// so re-solving with a bigger poll allowance rebuilds the whole node model
    /// to reach the identical answer. Measured, that second pass ran on up to
    /// 61,821 rows at every one of 4,097 nodes. If this predicate ever answers
    /// `true` for a decline the budget cannot move, the waste comes straight
    /// back.
    #[test]
    fn only_a_budget_refusal_buys_the_second_lp_pass() {
        assert!(super::refusal_can_change_with_a_bigger_budget(
            &LpDualDecline::NoDualPoint.label()
        ));
        for immovable in [
            LpDualDecline::ModelTooLarge {
                cap: "MAX_ROWS",
                limit: 40_000,
                measured: 61_821,
            },
            LpDualDecline::ModelShape,
            LpDualDecline::RowCount,
        ] {
            assert!(
                !super::refusal_can_change_with_a_bigger_budget(&immovable.label()),
                "{} is decided before any poll is spent",
                immovable.label()
            );
        }
        // The refusals `solve_node_lp` raises ITSELF. All ten are listed, and
        // they split into two groups that an earlier version of this test
        // conflated under "before the LP is even called" -- which is not true of
        // the last two.
        //
        // RAISED BEFORE THE LP IS CALLED. Properties of the node's own shape;
        // no amount of poll budget changes any of them.
        for own in [
            "all-variables-fixed",
            "overflow",
            "row-violated-under-the-fixings",
            "every-row-discharged",
            "free-objective-is-empty",
            "too-many-free-variables",
        ] {
            assert!(
                !super::refusal_can_change_with_a_bigger_budget(own),
                "{own} is not a budget refusal"
            );
        }
        // RAISED AFTER THE LP RETURNS, and still treated as immovable. These two
        // are the ones the enumeration used to omit or mis-describe:
        //
        //   `row-count`        the solver reported a different number of
        //                      constraint rows than the model has. That is a
        //                      SHAPE disagreement, not a convergence one; a
        //                      bigger budget cannot make the two agree.
        //   `negative-row-dual` a `>=` row came back with a negative dual, so
        //                      the readout is not a valid dual point. More polls
        //                      COULD in principle land on a different vertex, so
        //                      this one is a DELIBERATE CONSERVATIVE CHOICE
        //                      rather than an impossibility: re-running is only
        //                      ever allowed to cost work, never to change a
        //                      verdict, and declining to re-run is the safe
        //                      direction. It has no measured cost either --
        //                      across the 50-instance SEARCH-PROOF-GAP corpus
        //                      the only labels ever raised below the root are
        //                      `model-too-large` and `no-dual-point-in-budget`;
        //                      `negative-row-dual` never fires.
        for after_lp in ["row-count", "negative-row-dual"] {
            assert!(
                !super::refusal_can_change_with_a_bigger_budget(after_lp),
                "{after_lp} is raised after the LP returns but is still not a budget \
                 refusal: escalating it re-runs the same solve for the same answer"
            );
        }
    }

    /// AN INTERRUPT COSTS BYTES IT HAS NOT EMITTED, NEVER BYTES IT HAS.
    ///
    /// The route is unscheduled on purpose, so the stop signal must not be able
    /// to change a certificate — only to withhold one. Two halves, both
    /// asserted: a caller that stops IMMEDIATELY still gets the identical proof
    /// (because the certifying envelope is below `MAX_UNINTERRUPTIBLE_NODES`),
    /// and the interruptible entry with a never-stop signal is the plain one.
    #[test]
    fn an_always_true_stop_signal_cannot_change_an_emitted_certificate() {
        let (instance, incumbent, optimum) = petersen_vertex_cover();
        let plain = certify_opt_lin_certified_bb(&instance, &incumbent, optimum)
            .expect("Petersen certifies through this route");
        let stopped = super::certify_opt_lin_certified_bb_interruptible(
            &instance,
            &incumbent,
            optimum,
            &|| true,
        )
        .expect(
            "a certificate emitted inside the uninterruptible envelope must survive \
             a caller that is already stopping",
        );
        assert_eq!(plain, stopped, "the stop signal changed the emitted bytes");
        let never = super::certify_opt_lin_certified_bb_interruptible(
            &instance,
            &incumbent,
            optimum,
            &|| false,
        );
        assert_eq!(never.as_deref(), Some(plain.as_str()));
    }

    /// THE FALLBACK IS A RANKING, AND ITS TIE-BREAK IS TOTAL. Determinism is the
    /// whole reason this route may use a heuristic at all: the emitted bytes
    /// must not depend on iteration order, so equal-weight variables must always
    /// resolve to the lowest index.
    #[test]
    fn the_fallback_branch_variable_is_deterministic_and_objective_ranked() {
        let (instance, _, _) = petersen_vertex_cover();
        let model = super::build_model(&instance).expect("model");
        let mut fixed = vec![None; model.num_vars];
        // Every objective coefficient is 1 here, so the tie-break alone decides.
        assert_eq!(fallback_branch_variable(&model, &fixed), Some(0));
        fixed[0] = Some(true);
        fixed[1] = Some(false);
        assert_eq!(fallback_branch_variable(&model, &fixed), Some(2));
        // Weight beats index: a heavier free variable outranks a lighter one
        // that comes first.
        let mut weighted = instance.clone();
        weighted.objective = Some(PbObjective {
            terms: (1..=10)
                .map(|v| term(if v == 7 { 5 } else { 1 }, v, false))
                .collect(),
        });
        let heavy = super::build_model(&weighted).expect("model");
        assert_eq!(
            fallback_branch_variable(&heavy, &vec![None; heavy.num_vars]),
            Some(6),
            "x7 carries 5 and must outrank the ten unit coefficients"
        );
        // All fixed: no branch, which is the state the leaf rules own.
        assert_eq!(
            fallback_branch_variable(&model, &vec![Some(true); model.num_vars]),
            None
        );
    }

    /// THE PROPERTY THE REPLAY POOL RESTS ON, ASSERTED RATHER THAN ASSUMED.
    ///
    /// `R = G + qo(1-optimum) - Sum_{v free} max(0, coef_v) - Sum_{v in F1} coef_v`, so
    /// moving a variable out of `free` can only ADD to `R`: to `F1` the term
    /// goes from `-max(0, c)` to `-c` (a gain of `max(0, -c)`), and to `F0` it
    /// disappears (a gain of `max(0, c)`). If that were false, carrying an
    /// ancestor's multipliers down the tree would be unsound rather than merely
    /// unhelpful, because `try_leaf` would be asked to emit a leaf whose degree
    /// it had not re-derived at THIS node.
    ///
    /// Concretely on Petersen, where every vertex has degree 3: the fifteen edge
    /// rows at multiplier 1 with `qo = 2` give every variable coefficient
    /// `3 - 2 = 1` and normalized degree `15 + 2(1 - 6) = 5`. At the root all ten
    /// coefficients are charged and `R = -5`. Fixing six vertices to 0 charges
    /// only the four that remain free — the fixed ones become branch literals
    /// instead — so `R = 1` and the SAME vector closes. Nothing about the
    /// multipliers changed; only which variables the axioms have to cancel.
    #[test]
    fn an_ancestors_multipliers_only_get_stronger_as_the_tree_descends() {
        let (instance, _, optimum) = petersen_vertex_cover();
        let model = super::build_model(&instance).expect("model");
        let ys: Vec<(usize, i128)> = (0..15).map(|row| (row, 1_i128)).collect();
        let root = vec![None; model.num_vars];
        assert!(
            try_leaf(&model, &root, &ys, 2, optimum).is_none(),
            "the whole edge relaxation at the root is LP*, which is below the optimum"
        );
        // Five is one short: `R = 5 - 5 = 0`, and `try_leaf` demands STRICTLY
        // positive. The boundary is asserted so a sign slip cannot pass.
        let mut five = root.clone();
        for var in [0usize, 1, 2, 3, 4] {
            five[var] = Some(false);
        }
        assert!(
            try_leaf(&model, &five, &ys, 2, optimum).is_none(),
            "R = 0 is not a leaf"
        );
        let mut six = five.clone();
        six[5] = Some(false);
        let leaf = try_leaf(&model, &six, &ys, 2, optimum)
            .expect("the SAME multipliers must close once one more variable is fixed");
        assert_eq!(
            leaf.support,
            (0..6).collect(),
            "the clause is exactly the six branch literals the fixings created"
        );
    }
}
