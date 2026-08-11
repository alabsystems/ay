//! MaxSAT proof emission: an OPB restatement of the WCNF input, plus a VeriPB
//! certificate of the answer AY reports for it.
//!
//! # THE RULE: the proof log is WRITE-ONLY from the engine's perspective
//!
//! Nothing in this module may feed back into the verdict. There is no
//! `if certificate_closed_the_gap { report OPTIMUM }` and there must never be
//! one. AY's one historical wrong answer came from bound reasoning reaching the
//! answer path; a certificate writer that can promote an answer would be the
//! same defect wearing a badge.
//!
//! This is enforced structurally rather than by convention: emission lives in
//! the `ay` binary, DOWNSTREAM of `ay-maxsat` (which does not even depend on
//! `ay-pb`). The emitter is handed a finished `(model, cost)` and returns
//! `Result<()>`; its output is a pair of files that no AY code path reads back.
//! The only way emission can influence a run is by refusing to certify, which
//! raises an alarm — it can never manufacture a stronger claim.
//!
//! # What gets emitted
//!
//! Two files, `<stem>.opb` and `<stem>.opb.pbp`:
//!
//! * **`.opb`** — the WCNF as a pseudo-Boolean optimisation instance. Hard
//!   clause `(l1 … lk)` becomes `+1 L1 … +1 Lk >= 1`. Soft clause `[w] (l1 … lk)`
//!   gets a fresh relaxation variable `r_j` and becomes `+1 L1 … +1 Lk +1 r_j >= 1`
//!   with objective term `+w r_j`: paying `w` is exactly the licence to falsify
//!   the clause. Minimising `Σ w_j r_j` is therefore literally the MaxSAT problem.
//!
//! * **`.opb.pbp`** — a VeriPB v3 proof. A `sol` line logs the model with its
//!   claimed objective value (the checker recomputes it), and a
//!   `conclusion BOUNDS lo <= obj <= hi` states the interval AY is willing to
//!   defend.
//!
//! We emit OPB rather than handing the checker the `.wcnf` directly because the
//! checker's own WCNF→PB variable mapping is an implementation detail we would
//! be guessing at. Emitting OPB puts AY in control of every variable index and
//! every constraint id, and lands on the same path `ci/cert-instances/manifest.tsv`
//! already exercises.
//!
//! # The two bounds
//!
//! The upper bound is the honest part and always available: `sol` forces the
//! checker to verify the model against every hard constraint and to recompute
//! the objective. A cost AY misreports cannot survive it.
//!
//! The lower bound is emitted only when it can be *derived*. The base case is
//! the `#core-mine` floor. A mined core is a hard clause all of whose
//! literals negate a unit soft's literal; in PB that same row is
//! `Σ_i ~L_ji >= 1`. Summing it with each member's relaxation row
//! `L_ji + r_ji >= 1` cancels the `k` literal pairs (`L + ~L = 1`), dropping the
//! degree from `1+k` to `1` and leaving `Σ_i r_ji >= 1` — the core, as cutting
//! planes over input rows only. Scaling by `w_min` and summing over paid cores
//! gives `Σ_j c_j r_j >= lb`; a final pass of literal axioms (`r_j >= 0`) lifts
//! each `c_j` to the objective's own `w_j`, so the derived row IS `obj >= lb`.
//!
//! When no derivation is available the lower bound is `0`, which is sound for
//! non-negative weights and — crucially — `BOUNDS 0 <= obj <= k` does not entail
//! optimality. This increment cannot produce a premature optimum claim by
//! construction.
//!
//! # SAT-derived cores, and why they need their own check
//!
//! A mined core IS an input hard clause, so the paragraph above derives it with
//! nothing but `pol` over rows the checker already has. A core that came back
//! from a SAT CALL is a different animal: it is a REFUTATION. The solver ran
//! search — with inprocessing, and over totalizer variables that exist nowhere
//! in the OPB — to establish that `Σ_{i∈K} r_i >= 1`. In general that row is
//! NOT RUP over the input, and a `rup` step the checker cannot replay fails the
//! ENTIRE proof, taking the mined-core bound down with it. All-or-nothing is
//! not an acceptable trade for a bound improvement.
//!
//! So the emitter does not take the engine's word for it. Before stating a
//! SAT-derived core it runs the checker's own test itself:
//!
//! 1. negate the claim — every `r_i`, `i ∈ K`, is `0`;
//! 2. each member's soft row `+1 l_i +1 r_i >= 1` then forces `l_i`;
//! 3. unit-propagate over the hard rows;
//! 4. the core is RUP exactly when that conflicts.
//!
//! Cores that pass are emitted as `rup`; cores that fail are SILENTLY OMITTED,
//! which weakens the bound and is therefore always sound. Because step 3 is a
//! SUBSET of what VeriPB propagates (it also propagates every non-member soft
//! row and every previously derived row, none of which can remove a conflict),
//! a core that passes here passes there. This feature cannot fail a
//! certificate that would otherwise have verified.
//!
//! Only cores over UNIT softs are considered at all — for a unit soft the OLL
//! selector IS the soft's own literal, which is the one case where the core is
//! expressible over the OPB's variables.
//!
//! That the filter is doing real work, and not being merely timid, is MEASURED
//! rather than assumed. Emitting the engine's cores verbatim on
//! `warehouses_wt-warehouse0.wcsp` claims `328 <= obj <= 328` — the exact
//! optimum, and a lie the checker will not accept: VeriPB fails the proof at
//! the first unreplayable `rup`, which costs not just the extra 3 but the whole
//! 325, including the 226 the mined cores had already earned. The two offending
//! cores are the UNIT cores `{¬x16}` and `{¬x31}`, failed literals the solver
//! established by search. With the filter, the same run certifies `325 <= obj
//! <= 328` and verifies. `auctions_wt-cat_paths_60_70_0007.txt` is the same
//! story with nothing to lose but the anytime interval: verbatim emission
//! claims `lb = 6` and is rejected outright; filtered, it correctly states
//! nothing and keeps its `0 <= obj <= 43384`.
//!
//! The propagation structure is built lazily, from one extra streaming pass,
//! and is dropped before the OPB is written. It is capped by
//! [`UP_LITERAL_BUDGET`]: this workspace's instances reach 1,035,351 hard
//! clauses on a 24GB machine that has kernel-panicked under memory pressure,
//! and a bound improvement is never worth a swap death. Over budget, the whole
//! feature is skipped and the `c proof:` line says so.
//!
//! # Preprocessing bounds, DERIVED BY THE EMITTER
//!
//! OLL reaches a large part of its lower bound before it ever calls the SAT
//! solver, and charges it to `preproc_cost`. On `spot5_wt-8.wcsp.log` and the
//! `MaxSATQueriesinInterpretableClassifiers` family that is the ENTIRE bound
//! (`cores_found = 0`), so the certificate used to say `0 <= obj <= k` while AY
//! privately knew better.
//!
//! The emitter does not ask the engine for those numbers. `preproc_cost` is not
//! plumbed here and must not be: everything below is rediscovered from the
//! `.wcnf` the emitter already streams, which is a strict improvement under THE
//! RULE — the claim is emitter-derived and checker-verified, and the emitter
//! never compares it with anything the engine said. Three sources, in ascending
//! order of what they cost the checker:
//!
//! **P1 — a soft every one of whose literals is false at the root.** Its
//! relaxation variable is forced, so the soft's whole weight is unavoidable.
//!
//! * *P1a*, every literal negated by a UNIT HARD row: pure `pol`. Summing the
//!   soft row `L_1 + … + L_k + r_j >= 1` with the `k` unit rows `¬L_i >= 1`
//!   cancels every literal pair and leaves `r_j >= 1`. This is exactly the
//!   `#core-mine` derivation with unit hards in place of the mined row, so it
//!   inherits everything already argued for it — no propagation, nothing to
//!   replay, and it survives the [`UP_LITERAL_BUDGET`] skip. The `k = 0` case
//!   (an EMPTY soft clause, whose row already IS `+1 r_j >= 1`) falls out of the
//!   same code.
//! * *P1b*, literals falsified by a propagation CHAIN: `rup +1 r_j >= 1`.
//!   Negating it sets `r_j = 0`, degenerating the soft row to `Σ L_i >= 1`,
//!   which the hard rows root-falsify. Budget-gated exactly like SAT cores.
//!
//! **P2/AM1 — at-most-one cliques over unit softs.** If unit softs
//! `l_1 … l_k` are pairwise exclusive then at most one is satisfied, so `k-1` of
//! them must be paid. The emitter builds the conflict graph itself, from two
//! kinds of edge:
//!
//! * *free*, when `l_b = ¬l_a` — two unit softs on complementary literals. No
//!   input row is needed at all: `(l + r_a >= 1) + (¬l + r_b >= 1)` is already
//!   `r_a + r_b >= 1`. This is the complementary-pair rule, and because a
//!   clique is peeled layer by layer over SOFT ROWS (not merged literals),
//!   duplicate unit softs on the same literal are handled by peeling several
//!   layers, which recovers the full `min(ΣW⁺, ΣW⁻)` without a special case.
//! * *hard*, witnessed by a binary hard row `¬l_a + ¬l_b >= 1`.
//!
//! `k-1` does NOT follow from summing the `C(k,2)` pair rows — that caps at
//! `⌈k/2⌉`, and VeriPB refuses the difference. It follows by INDUCTION, one
//! division per step, with the pair rows expanded inline so the checker's
//! constraint database stays linear in `k`:
//!
//! ```text
//! T_2      : pol h(1,2) s(1) + s(2) + ;
//! T_{m+1}  : pol h(1,m+1) s(1) + … h(m,m+1) s(m) + +
//!                s(m+1) m * + T_m (m-1) * + m d ;
//! ```
//!
//! Each step sums `m` pair rows (leaving `m·¬l_{m+1} + Σ_{i≤m} r_i >= m`), adds
//! `m` copies of `s(m+1)` so the `l_{m+1}` pairs cancel, adds `m-1` copies of
//! `T_m`, and divides by `m`: the coefficients land on 1 and the degree on
//! `⌈(m²-m+1)/m⌉ = m`. VeriPB's `d` rounds BOTH up, which is what makes it
//! exact rather than lucky. A `free` edge needs no `h(i,j)` term: `s(i)` IS
//! already `¬l_j + r_i >= 1`.
//!
//! # Charge accounting is the last line of defence, and it now spans five sources
//!
//! Every source — mined cores, SAT cores, P1, and each AM1 layer — adds a
//! coefficient to some `r_j`, and the final lift can only ADD to a coefficient.
//! So if the sources together charge a soft more than its weight, the derived
//! row's coefficient exceeds the objective's and VeriPB refuses the conclusion
//! outright ("Expected constraint is not syntactically implied by the constraint
//! at the hint"). One shared `charged` map guards all five.
//!
//! The ORDER matters. `charged` is computed from mined and accepted SAT cores
//! FIRST; P1 and AM1 are then handed the RESIDUAL `w_j - charged_j` as their
//! cap. With that, a preprocessing charge can never trip
//! [`LbDeclined::OverCharged`] and so can never knock out the core floor. Within
//! preprocessing, P1 runs before AM1 and zeroes the residual of every soft it
//! claims: a root-false unit soft is worth its FULL weight to P1 but only the
//! peel depth to a clique, and charging both is rejected.
//!
//! # A tripwire this deliberately leaves armed
//!
//! `Oll::root_up_implied` caps at 32 rounds; the emitter's [`HardUp`]
//! propagates to fixpoint, and the emitter's clique cover is not the engine's.
//! So the derived floor can legitimately EXCEED `preproc_cost`. If it ever
//! exceeds the reported `cost`, VeriPB answers "The lower bound claimed for
//! `conclusion BOUNDS` is larger than the best logged objective value" and
//! refuses the whole proof — a genuine new wrong-answer detector obtained with
//! zero feedback into the verdict. The floor is therefore NOT clamped to the
//! reported cost; clamping would disarm it.

use std::collections::HashMap;
use std::fs;
use std::io::{BufWriter, Write};
use std::path::Path;

use anyhow::{Context, Result};

/// One `#core-mine` core that OLL actually paid, in the terms the proof needs.
///
/// Reported by the engine purely as evidence; see THE RULE above.
#[derive(Clone, Debug)]
pub(crate) struct PaidCore {
    /// 1-based index of the mined hard clause among the instance's hard
    /// clauses, which is exactly its constraint id in the emitted OPB.
    pub hard_row: u64,
    /// The weight OLL charged for this core.
    pub w_min: u64,
    /// The core's members, as DIMACS unit-soft literals.
    pub members: Vec<i32>,
}

/// One core a SAT CALL returned and OLL paid for, in the terms the proof needs.
///
/// Reported by the engine purely as evidence; see THE RULE above. Unlike
/// [`PaidCore`] this names no input row — it is a refutation, and the emitter
/// must verify it for itself before it may be stated (see the module docs).
#[derive(Clone, Debug)]
pub(crate) struct SatCore {
    /// The weight OLL charged for this core.
    pub w_min: u64,
    /// The core's members, as DIMACS unit-soft literals.
    pub members: Vec<i32>,
}

/// A SAT-derived core the emitter has verified and will state as `rup`.
#[derive(Clone, Debug)]
struct AcceptedSatCore {
    w_min: u64,
    /// 0-based soft indices of the members, resolved against the WCNF.
    softs: Vec<usize>,
}

/// Budget for the SAT-derived-core propagation structure, counted in hard
/// clause literals plus two per variable (the occurrence index is per literal,
/// so it scales with both).
///
/// At the cap the structure costs roughly 80MB and is dropped before the OPB is
/// written. Over it, the feature is skipped entirely — a weaker bound, never a
/// failed proof and never a swap death.
const UP_LITERAL_BUDGET: u64 = 8_000_000;

/// Why a lower bound was not certified. Emission continues with `lb = 0`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum LbDeclined {
    /// A core member is not a unit soft of this instance.
    MemberNotUnitSoft { lit: i32 },
    /// The mined row is not a hard clause id in range.
    RowOutOfRange { row: u64 },
    /// Cores together charge a soft more than its weight — the over-pay that
    /// drives `lb` past the optimum. This is the wrong-answer mode.
    OverCharged {
        lit: i32,
        weight: u64,
        charged: u128,
    },
    /// Arithmetic would overflow.
    Overflow,
}

impl std::fmt::Display for LbDeclined {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MemberNotUnitSoft { lit } => {
                write!(f, "core member {lit} is not a unit soft of this instance")
            }
            Self::RowOutOfRange { row } => write!(f, "mined hard row {row} out of range"),
            Self::OverCharged {
                lit,
                weight,
                charged,
            } => write!(
                f,
                "unit soft {lit} has weight {weight} but paid cores charge it {charged}"
            ),
            Self::Overflow => write!(f, "bound arithmetic overflow"),
        }
    }
}

/// What emission produced, for logging.
#[derive(Clone, Debug)]
pub(crate) struct Emitted {
    pub num_constraints: u64,
    pub num_vars: u64,
    pub lower_bound: u64,
    /// `Some` when a lower bound was requested but could not be derived.
    pub lb_declined: Option<LbDeclined>,
    /// SAT-derived cores the engine offered as evidence.
    pub sat_cores_offered: usize,
    /// …of which the emitter verified as RUP itself and stated. The rest were
    /// silently omitted, which only weakens the bound.
    pub sat_cores_certified: usize,
    /// The propagation structure would have exceeded [`UP_LITERAL_BUDGET`], so
    /// no SAT-derived core was even considered.
    pub sat_cores_over_budget: bool,
    /// Root-falsified softs (P1) charged in full, rediscovered by the emitter.
    pub p1_softs_certified: usize,
    /// …of which needed a `rup` (P1b) rather than pure `pol` (P1a).
    pub p1b_softs_certified: usize,
    /// At-most-one layers peeled and stated as induction ladders.
    pub am1_layers_certified: usize,
    /// The part of `lower_bound` that came from preprocessing rather than from
    /// the engine's cores.
    pub preproc_lower_bound: u64,
    /// The propagation structure was over budget, so P1b stated nothing. P1a
    /// and the at-most-one ladders are pure `pol` and survive it — a bound that
    /// is weaker because the machine was small must be distinguishable from one
    /// that was never provable.
    pub p1b_over_budget: bool,
    /// The at-most-one conflict graph hit [`AM1_EDGE_BUDGET`] and later edges
    /// were dropped, so the peel saw a smaller graph than the instance has.
    pub am1_graph_truncated: bool,
}

/// Per-instance facts gathered in one streaming pass.
struct Shape {
    max_var: u32,
    n_hard: u64,
    /// Total literal occurrences across all hard clauses, before dedup. Sizes
    /// (and caps) the unit-propagation structure without a second file pass.
    hard_lits: u64,
    /// Weight of each soft clause, in file order.
    soft_weights: Vec<u64>,
    /// Whether the model falsifies each soft clause, in file order.
    soft_falsified: Vec<bool>,
    /// For each unit soft literal: its 0-based soft index. Later softs win the
    /// same way the engine's own install does not merge them here — a duplicate
    /// unit soft simply makes one of the two uncertifiable, and we decline
    /// rather than guess.
    unit_soft: HashMap<i32, usize>,
    /// Unit soft literals that appear more than once; never certifiable.
    ambiguous_unit: Vec<i32>,
    /// For each literal held by a UNIT HARD clause: that clause's 1-based hard
    /// index, which is its constraint id in the emitted OPB. First occurrence
    /// wins; a duplicate unit hard states the same thing, so either row works.
    ///
    /// This is what makes P1a pure `pol` — no propagator, no budget.
    unit_hard: HashMap<i32, u64>,
    /// Some soft clause has NO literals. Its row is already `r_j >= 1`, so P1
    /// pays it in full needing nothing from the hard formula — which is why the
    /// P1 gate cannot be conditioned on `unit_hard` alone.
    has_empty_soft: bool,
    /// The hard clauses alone are contradictory: an empty hard clause, or a
    /// literal held as a unit alongside its negation. Then every row is
    /// vacuously derivable, AY has no model, and emission is not on this path —
    /// so preprocessing is skipped defensively rather than allowed to claim
    /// everything.
    hard_root_conflict: bool,
    /// Every UNIT soft, as `(literal, 0-based soft index)` in file order.
    ///
    /// Unlike [`Shape::unit_soft`] this keeps DUPLICATES: the mined-core and
    /// SAT-core paths need a single unambiguous relaxation variable, but an
    /// at-most-one clique is peeled over soft ROWS and genuinely does not.
    unit_rows: Vec<(i32, usize)>,
}

fn lit_value(model: &[bool], lit: i32) -> bool {
    // OLL uses RAW variable ids (id 0 unused), so DIMACS n indexes model[n].
    // Getting this wrong is not hypothetical: an n-vs-n-1 slip in a witness
    // oracle cost hours and produced two false results.
    let assigned = model
        .get(lit.unsigned_abs() as usize)
        .copied()
        .unwrap_or(false);
    if lit > 0 {
        assigned
    } else {
        !assigned
    }
}

/// Render a DIMACS literal as an OPB literal over the instance's own variables.
fn opb_lit(lit: i32) -> String {
    if lit > 0 {
        format!("x{lit}")
    } else {
        format!("~x{}", -lit)
    }
}

/// Deduplicate a clause's literals, preserving order. `x` alongside `~x` is
/// kept: the row is then trivially true, which is what the clause means.
fn dedup_lits(lits: &[i32]) -> Vec<i32> {
    let mut seen = std::collections::HashSet::new();
    lits.iter().copied().filter(|l| seen.insert(*l)).collect()
}

/// The clause's DEDUPLICATED literals when there are at most two of them, which
/// is exactly when the emitted OPB row is a unit or a binary.
///
/// Allocation-free and identical to `dedup_lits` on that range — which is the
/// point: `unit_hard` and the at-most-one edge set name OPB ROWS, so they must
/// agree with what the OPB writer put on disk, literal for literal. A clause
/// written `(x1 x1 x1)` IS a unit row and must be seen as one.
fn small_dedup(lits: &[i32]) -> Option<Vec<i32>> {
    let mut out = [0i32; 2];
    let mut n = 0usize;
    for &l in lits {
        if out[..n].contains(&l) {
            continue;
        }
        if n == 2 {
            return None;
        }
        out[n] = l;
        n += 1;
    }
    Some(out[..n].to_vec())
}

impl Shape {
    /// OPB variable id of soft clause `j`'s relaxation variable.
    fn relax_var(&self, j: usize) -> u64 {
        self.max_var as u64 + 1 + j as u64
    }

    /// 1-based OPB constraint id of soft clause `j`'s row.
    fn soft_row(&self, j: usize) -> u64 {
        self.n_hard + 1 + j as u64
    }

    fn num_vars(&self) -> u64 {
        self.max_var as u64 + self.soft_weights.len() as u64
    }

    fn num_constraints(&self) -> u64 {
        self.n_hard + self.soft_weights.len() as u64
    }
}

fn scan_shape(
    wcnf: &Path,
    model: &[bool],
    stream: &dyn Fn(&Path, &mut dyn FnMut(Option<u64>, &[i32]) -> Result<()>) -> Result<()>,
) -> Result<Shape> {
    let mut shape = Shape {
        max_var: 0,
        n_hard: 0,
        hard_lits: 0,
        soft_weights: Vec::new(),
        soft_falsified: Vec::new(),
        unit_soft: HashMap::new(),
        ambiguous_unit: Vec::new(),
        unit_hard: HashMap::new(),
        has_empty_soft: false,
        hard_root_conflict: false,
        unit_rows: Vec::new(),
    };
    stream(wcnf, &mut |weight, lits| {
        for &l in lits {
            shape.max_var = shape.max_var.max(l.unsigned_abs());
        }
        match weight {
            None => {
                shape.n_hard += 1;
                shape.hard_lits += lits.len() as u64;
                // Unit hard rows, by the OPB's own notion of "unit".
                match small_dedup(lits).as_deref() {
                    Some([]) => shape.hard_root_conflict = true,
                    Some(&[l]) => {
                        if shape.unit_hard.contains_key(&-l) {
                            shape.hard_root_conflict = true;
                        }
                        shape.unit_hard.entry(l).or_insert(shape.n_hard);
                    }
                    _ => {}
                }
            }
            Some(w) => {
                let j = shape.soft_weights.len();
                if w > 0 {
                    if let Some(&[l]) = small_dedup(lits).as_deref() {
                        if shape.unit_soft.insert(l, j).is_some() {
                            shape.ambiguous_unit.push(l);
                        }
                        shape.unit_rows.push((l, j));
                    }
                }
                if w > 0 && lits.is_empty() {
                    shape.has_empty_soft = true;
                }
                shape.soft_weights.push(w);
                shape
                    .soft_falsified
                    .push(!lits.iter().any(|&l| lit_value(model, l)));
            }
        }
        Ok(())
    })?;
    Ok(shape)
}

// ---------------------------------------------------------------------------
// Unit propagation over the hard clauses — the emitter's own RUP check.
// ---------------------------------------------------------------------------

const UNASSIGNED: u8 = 0;
const TRUE: u8 = 1;
const FALSE: u8 = 2;

/// Index a DIMACS literal into the per-literal occurrence table.
#[inline]
fn lit_code(lit: i32) -> usize {
    (lit.unsigned_abs() as usize) * 2 + usize::from(lit < 0)
}

#[inline]
fn value_of(assign: &[u8], lit: i32) -> u8 {
    let v = assign[lit.unsigned_abs() as usize];
    if v == UNASSIGNED || lit > 0 {
        v
    } else if v == TRUE {
        FALSE
    } else {
        TRUE
    }
}

/// A falsified-literal-counting unit propagator over the instance's hard
/// clauses, sized exactly once from [`Shape`] and dropped as soon as the last
/// core has been checked.
///
/// Counting FALSIFIED literals (rather than watching two) is deliberate: it
/// needs no satisfaction bookkeeping, because "every literal false" — count
/// zero — is precisely a conflict, and "one literal not false" is precisely the
/// unit case whether or not that literal is already true. The per-clause
/// counters are restored by an undo log after each core, so one core's cost is
/// proportional to the propagation it actually caused, not to the formula size.
struct HardUp {
    /// Deduplicated hard clause literals, concatenated. Clause `c` occupies
    /// `lits[starts[c] .. starts[c + 1]]`.
    lits: Vec<i32>,
    starts: Vec<u32>,
    /// CSR occurrence index: clauses containing literal code `k` are
    /// `occ[occ_start[k] .. occ_start[k + 1]]`.
    occ_start: Vec<u32>,
    occ: Vec<u32>,
    /// Per clause: how many of its literals are not (yet) false.
    unfalsified: Vec<u32>,
    /// Per variable: [`UNASSIGNED`] / [`TRUE`] / [`FALSE`].
    assign: Vec<u8>,
    trail: Vec<i32>,
    /// Clauses whose counter was decremented, for undo.
    undo: Vec<u32>,
    /// Trail / undo lengths after root propagation; never rolled back past.
    root_trail: usize,
    root_undo: usize,
    /// The hard clauses alone are already contradictory (an empty hard clause,
    /// or conflicting units). Then EVERY row is RUP — which is exactly what
    /// VeriPB would also conclude, so it stays faithful rather than convenient.
    root_conflict: bool,
}

impl HardUp {
    /// Would the structure for `shape` fit in `budget`?
    ///
    /// Counted in hard literals plus two per variable: the flat clause array
    /// and the occurrence array both scale with the former, the occurrence
    /// offsets with the latter.
    fn fits(shape: &Shape, budget: u64) -> bool {
        shape
            .hard_lits
            .saturating_add(2u64.saturating_mul(shape.max_var as u64 + 1))
            <= budget
            && shape.hard_lits <= u32::MAX as u64
    }

    /// One extra streaming pass over the WCNF. The hard clauses are held ONCE:
    /// the occurrence index is computed from the in-memory copy, not from a
    /// second read.
    fn build(
        wcnf: &Path,
        shape: &Shape,
        stream: &dyn Fn(&Path, &mut dyn FnMut(Option<u64>, &[i32]) -> Result<()>) -> Result<()>,
    ) -> Result<Self> {
        let mut lits: Vec<i32> = Vec::with_capacity(shape.hard_lits as usize);
        let mut starts: Vec<u32> = Vec::with_capacity(shape.n_hard as usize + 1);
        starts.push(0);
        stream(wcnf, &mut |weight, raw| {
            if weight.is_none() {
                // Deduplicated so the propagator sees exactly the rows the OPB
                // states, literal for literal.
                lits.extend(dedup_lits(raw));
                starts.push(lits.len() as u32);
            }
            Ok(())
        })?;

        let n_codes = (shape.max_var as usize + 1) * 2;
        let mut occ_start = vec![0u32; n_codes + 1];
        for &l in &lits {
            occ_start[lit_code(l) + 1] += 1;
        }
        for k in 0..n_codes {
            occ_start[k + 1] += occ_start[k];
        }
        let mut cursor = occ_start.clone();
        let mut occ = vec![0u32; lits.len()];
        for c in 0..starts.len() - 1 {
            for k in starts[c]..starts[c + 1] {
                let code = lit_code(lits[k as usize]);
                occ[cursor[code] as usize] = c as u32;
                cursor[code] += 1;
            }
        }
        drop(cursor);

        let unfalsified: Vec<u32> = (0..starts.len() - 1)
            .map(|c| starts[c + 1] - starts[c])
            .collect();
        let mut up = HardUp {
            lits,
            starts,
            occ_start,
            occ,
            unfalsified,
            assign: vec![UNASSIGNED; shape.max_var as usize + 1],
            trail: Vec::new(),
            undo: Vec::new(),
            root_trail: 0,
            root_undo: 0,
            root_conflict: false,
        };

        // Root propagation: unit hard clauses hold unconditionally, so assert
        // them once and never roll back. Skipping this would silently make
        // every core over a unit-implied literal look non-RUP.
        let mut units: Vec<i32> = Vec::new();
        for c in 0..up.unfalsified.len() {
            match up.starts[c + 1] - up.starts[c] {
                0 => up.root_conflict = true,
                1 => units.push(up.lits[up.starts[c] as usize]),
                _ => {}
            }
        }
        if !up.root_conflict && up.propagate(&units) {
            up.root_conflict = true;
        }
        up.root_trail = up.trail.len();
        up.root_undo = up.undo.len();
        Ok(up)
    }

    /// Assert `seeds` and propagate to fixpoint. Returns `true` on conflict.
    /// Leaves the assignment in place; the caller rolls back.
    fn propagate(&mut self, seeds: &[i32]) -> bool {
        let mut head = self.trail.len();
        for &l in seeds {
            match value_of(&self.assign, l) {
                FALSE => return true,
                TRUE => continue,
                _ => {
                    self.assign[l.unsigned_abs() as usize] = if l > 0 { TRUE } else { FALSE };
                    self.trail.push(l);
                }
            }
        }
        while head < self.trail.len() {
            let p = self.trail[head];
            head += 1;
            // Clauses holding ¬p just lost a literal.
            let code = lit_code(-p);
            let (from, to) = (self.occ_start[code], self.occ_start[code + 1]);
            for i in from..to {
                let c = self.occ[i as usize] as usize;
                self.unfalsified[c] -= 1;
                self.undo.push(c as u32);
                if self.unfalsified[c] == 0 {
                    return true;
                }
                if self.unfalsified[c] != 1 {
                    continue;
                }
                // Exactly one literal is not false. If it is unassigned the
                // clause is unit on it; if it is true the clause is satisfied
                // and there is nothing to do.
                for k in self.starts[c]..self.starts[c + 1] {
                    let l = self.lits[k as usize];
                    match value_of(&self.assign, l) {
                        FALSE => continue,
                        TRUE => break,
                        _ => {
                            self.assign[l.unsigned_abs() as usize] =
                                if l > 0 { TRUE } else { FALSE };
                            self.trail.push(l);
                            break;
                        }
                    }
                }
            }
        }
        false
    }

    fn rollback(&mut self) {
        for &c in &self.undo[self.root_undo..] {
            self.unfalsified[c as usize] += 1;
        }
        self.undo.truncate(self.root_undo);
        for &l in &self.trail[self.root_trail..] {
            self.assign[l.unsigned_abs() as usize] = UNASSIGNED;
        }
        self.trail.truncate(self.root_trail);
    }

    /// Is `Σ_{i} r_i >= 1` over the softs whose unit literals are `members`
    /// derivable by reverse unit propagation from the input rows?
    ///
    /// Negating that row sets every `r_i` to 0; each member's soft row
    /// `+1 l_i +1 r_i >= 1` then forces `l_i`. So the whole test is: assert the
    /// member literals, propagate the hard rows, look for a conflict.
    fn core_is_rup(&mut self, members: &[i32]) -> bool {
        if self.root_conflict {
            return true;
        }
        let conflict = self.propagate(members);
        self.rollback();
        conflict
    }
}

// ---------------------------------------------------------------------------
// Preprocessing bounds the emitter rediscovers from the `.wcnf` — see the
// module docs. Nothing here consults the engine.
// ---------------------------------------------------------------------------

/// Cap on the at-most-one conflict graph, in edges. Both the row map and the
/// adjacency lists scale with it; at the cap they cost roughly 60MB together
/// and are dropped before the OPB is written. Truncation is by FILE ORDER, so
/// it is deterministic, and it only shrinks the cliques — a weaker bound, never
/// a failed proof.
const AM1_EDGE_BUDGET: usize = 1_000_000;

/// Largest clique the induction ladder is emitted for. The schedule costs
/// `2k² + 7k - 14` RPN tokens, so one layer at the cap is ~530k tokens / 2.3MB
/// — measured, and verified by the checker in 0.15s.
const AM1_MAX_CLIQUE: usize = 512;

/// Total RPN tokens all at-most-one ladders together may spend. ~20MB of
/// `.pbp`. Past it, later layers are dropped: a weaker bound, never a bigger
/// file than this.
const AM1_TOKEN_BUDGET: usize = 4_000_000;

/// Overlapping-peel passes over the seed order.
///
/// One pass usually reaches fixpoint on its own: a peel zeroes at least one
/// member, and any partner that still has residual gets its OWN seed turn in the
/// same pass. The extra passes matter only when a clique was capped by
/// [`AM1_MAX_CLIQUE`] or [`AM1_MAX_CANDIDATES`], which needs a conflict graph far
/// denser than a unit test builds. The `!peeled` break makes them free otherwise.
const AM1_MAX_PASSES: usize = 32;

/// Neighbours examined when growing ONE clique. Bounds the greedy extension on
/// a pathologically dense conflict graph.
const AM1_MAX_CANDIDATES: usize = 4096;

/// Why two unit softs cannot both be satisfied.
#[derive(Clone, Copy, Debug)]
enum Mutex {
    /// `l_b = ¬l_a`. No input row is needed: `s(a)` IS already `¬l_b + r_a >= 1`.
    Free,
    /// A binary hard row `+1 ¬l_a +1 ¬l_b >= 1` witnesses it. The value is that
    /// row's OPB constraint id.
    Hard(u64),
}

/// The at-most-one conflict graph over UNIT SOFT LITERALS, built by the emitter
/// from the `.wcnf` alone.
#[derive(Default)]
struct ConflictGraph {
    /// Per unit-soft literal, its mutually-exclusive neighbours. Sorted and
    /// deduplicated, so membership is a binary search and iteration order is
    /// stable.
    adj: HashMap<i32, Vec<i32>>,
    /// The witnessing binary hard row per excluded pair, keyed `(min, max)`.
    /// Free (complementary) edges are absent — they need no row.
    rows: HashMap<(i32, i32), u64>,
    /// [`AM1_EDGE_BUDGET`] was reached and later edges were dropped.
    truncated: bool,
}

impl ConflictGraph {
    fn mutex(&self, a: i32, b: i32) -> Option<Mutex> {
        if a == b {
            return None;
        }
        if a == -b {
            return Some(Mutex::Free);
        }
        let key = if a < b { (a, b) } else { (b, a) };
        self.rows.get(&key).copied().map(Mutex::Hard)
    }

    fn degree(&self, l: i32) -> usize {
        self.adj.get(&l).map_or(0, Vec::len)
    }

    fn is_empty(&self) -> bool {
        self.adj.is_empty()
    }
}

/// A soft whose relaxation variable is FORCED because every one of its
/// literals is false at the root.
struct P1Soft {
    /// 0-based soft index.
    j: usize,
    /// `Some(rows)` when every literal is negated by a UNIT HARD row — the
    /// derivation is then pure `pol` over input rows, needs no propagator, and
    /// survives the [`UP_LITERAL_BUDGET`] skip. `None` needs one `rup`.
    ///
    /// `Some(vec![])` is the EMPTY soft clause, whose row already IS
    /// `+1 r_j >= 1`.
    unit_rows: Option<Vec<u64>>,
}

/// Everything the emitter rediscovered about preprocessing, in one pass.
#[derive(Default)]
struct Preproc {
    p1: Vec<P1Soft>,
    graph: ConflictGraph,
}

/// ONE extra streaming pass that classifies root-falsified softs and collects
/// the at-most-one conflict graph.
///
/// It cannot be folded into [`HardUp::build`]'s pass: the root assignment is
/// only complete once every hard clause has been read, and hards and softs are
/// interleaved in the file. It stores nothing beyond the hits.
fn scan_preproc(
    wcnf: &Path,
    shape: &Shape,
    up: Option<&HardUp>,
    stream: &dyn Fn(&Path, &mut dyn FnMut(Option<u64>, &[i32]) -> Result<()>) -> Result<()>,
    edge_budget: usize,
) -> Result<Preproc> {
    let mut out = Preproc::default();
    // With contradictory hards every row is vacuously derivable. AY has no
    // model on that path and emission never runs, but claiming the whole
    // objective on the strength of it would be exactly the wrong instinct.
    if shape.hard_root_conflict || up.is_some_and(|u| u.root_conflict) {
        return Ok(out);
    }

    let unit_lits: std::collections::HashSet<i32> =
        shape.unit_rows.iter().map(|&(l, _)| l).collect();
    let want_graph = shape.unit_rows.len() >= 2 && !unit_lits.is_empty();
    // P1 covers TWO shapes and the gate must admit both. `unit_hard` non-empty
    // is what P1a needs (a soft every literal of which a unit hard negates), but
    // the k=0 case — a soft with NO literals at all, which oll.rs:2305 pays in
    // full — needs nothing from the hard formula: an empty soft row is just
    // `r_j >= 1` already. Gating the whole of P1 on `unit_hard` silently dropped
    // that case on any instance without a unit hard clause.
    let want_p1 = !shape.unit_hard.is_empty() || shape.has_empty_soft;

    let mut hard_row: u64 = 0;
    let mut j: usize = 0;
    stream(wcnf, &mut |weight, lits| {
        match weight {
            None => {
                hard_row += 1;
                if !want_graph || out.graph.truncated {
                    return Ok(());
                }
                // A binary hard `(¬a ∨ ¬b)` is the mutex between unit softs
                // `(a)` and `(b)`.
                let Some(two) = small_dedup(lits) else {
                    return Ok(());
                };
                if two.len() != 2 || two[0].unsigned_abs() == two[1].unsigned_abs() {
                    return Ok(());
                }
                let (a, b) = (-two[0], -two[1]);
                if !unit_lits.contains(&a) || !unit_lits.contains(&b) {
                    return Ok(());
                }
                if out.graph.rows.len() >= edge_budget {
                    out.graph.truncated = true;
                    return Ok(());
                }
                let key = if a < b { (a, b) } else { (b, a) };
                if out.graph.rows.insert(key, hard_row).is_none() {
                    out.graph.adj.entry(a).or_default().push(b);
                    out.graph.adj.entry(b).or_default().push(a);
                }
            }
            Some(w) => {
                let idx = j;
                j += 1;
                if w == 0 || !want_p1 {
                    // A weight-0 soft contributes no objective term, so
                    // charging it would break the lift arithmetic.
                    return Ok(());
                }
                // P1a: every literal negated by a unit hard. Purely syntactic,
                // so it holds with or without the propagator. An EMPTY clause
                // passes vacuously, which is the right answer — its row is
                // already `+1 r_j >= 1`.
                if lits.iter().all(|&l| shape.unit_hard.contains_key(&-l)) {
                    let rows = dedup_lits(lits)
                        .iter()
                        .map(|&l| shape.unit_hard[&-l])
                        .collect();
                    out.p1.push(P1Soft {
                        j: idx,
                        unit_rows: Some(rows),
                    });
                } else if let Some(up) = up {
                    // P1b: falsified by a propagation chain. Our propagator
                    // sees a SUBSET of what VeriPB propagates (hard rows only,
                    // at the root), so a falsification we find, it finds.
                    if !lits.is_empty() && lits.iter().all(|&l| value_of(&up.assign, l) == FALSE) {
                        out.p1.push(P1Soft {
                            j: idx,
                            unit_rows: None,
                        });
                    }
                }
            }
        }
        Ok(())
    })?;

    for ns in out.graph.adj.values_mut() {
        ns.sort_unstable();
        ns.dedup();
    }
    // Complementary unit softs are mutually exclusive with no input row at all,
    // so they are edges too — and the seed order must be able to see them.
    if want_graph {
        let mut free: Vec<(i32, i32)> = Vec::new();
        for &l in &unit_lits {
            if l > 0 && unit_lits.contains(&-l) {
                free.push((l, -l));
            }
        }
        free.sort_unstable();
        for (a, b) in free {
            for (x, y) in [(a, b), (b, a)] {
                let ns = out.graph.adj.entry(x).or_default();
                if let Err(pos) = ns.binary_search(&y) {
                    ns.insert(pos, y);
                }
            }
        }
    }
    Ok(out)
}

/// One peeled at-most-one layer: a clique of unit soft ROWS, and the depth the
/// peel charges each of them.
struct Am1Layer {
    /// Members in ladder order, as `(0-based soft index, DIMACS literal)`.
    members: Vec<(usize, i32)>,
    /// Peel depth. The layer proves `Σ r >= k - 1`, contributing `d·(k-1)` to
    /// the bound and `d` to each member's coefficient.
    d: u64,
}

/// Peel overlapping at-most-one layers out of `residual`, deterministically.
///
/// `residual[j]` is what soft `j` may still be charged; it is DECREMENTED in
/// place, so a layer can never take a soft past its weight and the caller's
/// over-charge guard cannot fire on our account.
///
/// Ordering, seeding and candidate growth are all fixed (degree, then literal,
/// then soft index) because the emitted proof must be reproducible byte for
/// byte from the same input.
fn plan_am1(shape: &Shape, graph: &ConflictGraph, residual: &mut [u64]) -> Vec<Am1Layer> {
    let mut layers: Vec<Am1Layer> = Vec::new();
    if graph.is_empty() {
        return layers;
    }
    // Nodes are soft ROWS, not merged literals. Two rows on the SAME literal
    // are not adjacent (both can be satisfied at once), so a clique picks at
    // most one row per literal — and duplicates are recovered by peeling
    // another layer against the other row, which is what makes the
    // complementary-pair rule reach the full `min(ΣW⁺, ΣW⁻)`.
    let nodes: Vec<(i32, usize)> = shape
        .unit_rows
        .iter()
        .copied()
        .filter(|&(l, j)| residual[j] > 0 && graph.degree(l) > 0)
        .collect();
    if nodes.len() < 2 {
        return layers;
    }
    let mut by_lit: HashMap<i32, Vec<usize>> = HashMap::new();
    for (n, &(l, _)) in nodes.iter().enumerate() {
        by_lit.entry(l).or_default().push(n);
    }
    let key = |n: usize| {
        let (l, j) = nodes[n];
        (std::cmp::Reverse(graph.degree(l)), l, j)
    };
    let mut order: Vec<usize> = (0..nodes.len()).collect();
    order.sort_unstable_by_key(|&n| key(n));

    let mut tokens: usize = 0;
    for _ in 0..AM1_MAX_PASSES {
        let mut peeled = false;
        for &seed in &order {
            if residual[nodes[seed].1] == 0 {
                continue;
            }
            let seed_lit = nodes[seed].0;
            let mut cands: Vec<usize> = Vec::new();
            'gather: for &nl in graph.adj.get(&seed_lit).into_iter().flatten() {
                for &n in by_lit.get(&nl).into_iter().flatten() {
                    if residual[nodes[n].1] == 0 {
                        continue;
                    }
                    cands.push(n);
                    if cands.len() >= AM1_MAX_CANDIDATES {
                        break 'gather;
                    }
                }
            }
            if cands.is_empty() {
                continue;
            }
            cands.sort_unstable_by_key(|&n| key(n));
            let mut clique = vec![seed];
            for &c in &cands {
                if clique.len() >= AM1_MAX_CLIQUE {
                    break;
                }
                if clique
                    .iter()
                    .all(|&m| graph.mutex(nodes[m].0, nodes[c].0).is_some())
                {
                    clique.push(c);
                }
            }
            if clique.len() < 2 {
                continue;
            }
            // Every member was filtered on `residual > 0`, so this is positive;
            // the guard is what keeps a zero-depth layer from being emitted as a
            // `0 *` term if that ever stops being true.
            let d = clique
                .iter()
                .map(|&m| residual[nodes[m].1])
                .min()
                .unwrap_or(0);
            if d == 0 {
                continue;
            }
            let k = clique.len();
            let cost = 2 * k * k + 7 * k;
            if tokens + cost > AM1_TOKEN_BUDGET {
                return layers;
            }
            tokens += cost;
            for &m in &clique {
                residual[nodes[m].1] -= d;
            }
            layers.push(Am1Layer {
                members: clique.iter().map(|&m| (nodes[m].1, nodes[m].0)).collect(),
                d,
            });
            peeled = true;
        }
        if !peeled {
            break;
        }
    }
    layers
}

/// The `pol` lines that derive `Σ_{i} r_i >= k - 1` for one clique, by
/// induction on the clique size — see the module docs for the arithmetic.
///
/// Returns one line per derived row `T_2 … T_k`, where the FIRST line takes
/// constraint id `base_id` and each later one the next — so `T_k` lands on
/// `base_id + k - 2`, which is what the caller lifts against.
///
/// `None` means some pair is not actually a mutex. The planner only builds real
/// cliques, so it must never happen; it is refused rather than guessed at
/// because an unwitnessed pair is exactly the mutation VeriPB rejects, and
/// refusing costs a bound where emitting costs the whole certificate.
fn am1_layer_steps(
    shape: &Shape,
    graph: &ConflictGraph,
    layer: &Am1Layer,
    base_id: u64,
) -> Option<Vec<String>> {
    let m = &layer.members;
    let k = m.len();
    if k < 2 {
        return None;
    }
    let soft_row = |i: usize| shape.soft_row(m[i].0);
    // Member `i`'s contribution to the pair row against member `t`, i.e.
    // `¬l_t + r_i >= 1`. Over a free edge `s(i)` already IS that row.
    let contrib = |i: usize, t: usize| -> Option<String> {
        match graph.mutex(m[i].1, m[t].1)? {
            Mutex::Free => Some(format!("{}", soft_row(i))),
            Mutex::Hard(h) => Some(format!("{h} {} +", soft_row(i))),
        }
    };

    let mut steps = Vec::with_capacity(k - 1);
    // T_2 : r_1 + r_2 >= 1.
    steps.push(format!("pol {} {} + ;", contrib(0, 1)?, soft_row(1)));
    // T_{step+1} from T_step, one division per step.
    for step in 2..k {
        // `step` is `m` in the module docs: members `0..step` pair against
        // member `step`, and the sum is `step·¬l_step + Σ_{i<step} r_i >= step`.
        let mut rpn = contrib(0, step)?;
        for i in 1..step {
            rpn.push_str(&format!(" {} +", contrib(i, step)?));
        }
        // `step` copies of s(step) cancel the `l_step` pairs …
        rpn.push_str(&format!(" {} {step} * +", soft_row(step)));
        // … then `step - 1` copies of T_step (id `base_id + step - 2`) and one
        // division by `step` land the degree on `⌈(step² - step + 1)/step⌉`,
        // which is `step` for every `step >= 1`.
        rpn.push_str(&format!(" {} {} * +", base_id + step as u64 - 2, step - 1));
        rpn.push_str(&format!(" {step} d"));
        steps.push(format!("pol {rpn} ;"));
    }
    Some(steps)
}

/// A complete lower-bound derivation: the proof steps that precede the final
/// `pol`, that `pol`'s own reverse-polish, and what it proves.
struct Derivation {
    /// The bound the final `pol` lands on.
    lb: u64,
    /// Steps to write between `f` and the final `pol`, in id order. The first
    /// takes constraint id `n_constraints + 1`.
    steps: Vec<String>,
    /// Reverse-polish of the final `pol`, which derives `obj >= lb`.
    lift: String,
    /// How many SAT-derived cores this derivation actually states.
    sat_cores: usize,
    /// How many root-falsified softs (P1) it charges.
    p1_softs: usize,
    /// …of which needed a `rup` rather than pure `pol`.
    p1b_softs: usize,
    /// How many at-most-one layers it peels.
    am1_layers: usize,
    /// The part of `lb` that came from preprocessing rather than from cores.
    preproc_lb: u64,
}

/// Build the derivation of `obj >= lb`, or explain why we decline.
///
/// Declining is not a failure: the caller falls back to a weaker SUBSET of the
/// sources, and ultimately to `lb = 0`, which is always sound.
///
/// ORDER IS LOAD-BEARING. Cores are charged first and preprocessing is handed
/// the residual, so a preprocessing charge can never trip
/// [`LbDeclined::OverCharged`] and so can never cost the core floor. Within
/// preprocessing P1 runs before the at-most-one peel and zeroes what it claims:
/// a root-false unit soft is worth its FULL weight to P1 but only the peel
/// depth to a clique, and charging both is rejected by the checker.
fn derive_lower_bound(
    shape: &Shape,
    cores: &[PaidCore],
    sat_cores: &[AcceptedSatCore],
    preproc: Option<&Preproc>,
    base_id: u64,
) -> std::result::Result<Derivation, LbDeclined> {
    // Charge accounting, per soft. This is the invariant OLL must satisfy for
    // its own arithmetic to be sound, restated where an independent checker
    // will see it: a soft may be charged at most its weight, in total, across
    // every source that pays it — mined cores, SAT cores, P1 and every
    // at-most-one layer TOGETHER, since one soft can be claimed by all four.
    let mut charged: HashMap<usize, u128> = HashMap::new();
    let mut lb: u64 = 0;

    for core in cores {
        if core.hard_row == 0 || core.hard_row > shape.n_hard {
            return Err(LbDeclined::RowOutOfRange { row: core.hard_row });
        }
        for &lit in &core.members {
            let Some(&j) = shape.unit_soft.get(&lit) else {
                return Err(LbDeclined::MemberNotUnitSoft { lit });
            };
            if shape.ambiguous_unit.contains(&lit) {
                return Err(LbDeclined::MemberNotUnitSoft { lit });
            }
            *charged.entry(j).or_insert(0) += core.w_min as u128;
        }
        lb = lb.checked_add(core.w_min).ok_or(LbDeclined::Overflow)?;
    }

    // SAT-derived cores. Their members were resolved to unit softs and their
    // rows RUP-verified before they got here (see `certify_sat_cores`), so all
    // that is left is the shared charge accounting.
    for core in sat_cores {
        for &j in &core.softs {
            *charged.entry(j).or_insert(0) += core.w_min as u128;
        }
        lb = lb.checked_add(core.w_min).ok_or(LbDeclined::Overflow)?;
    }

    for (&j, &c) in &charged {
        let w = shape.soft_weights[j] as u128;
        if c > w {
            let lit = shape
                .unit_soft
                .iter()
                .find(|(_, &idx)| idx == j)
                .map(|(&l, _)| l)
                .unwrap_or(0);
            return Err(LbDeclined::OverCharged {
                lit,
                weight: shape.soft_weights[j],
                charged: c,
            });
        }
    }

    // What each soft may still be charged, AFTER the cores. Preprocessing is
    // capped by this, which is what makes it unable to break the core floor.
    let mut residual: Vec<u64> = shape
        .soft_weights
        .iter()
        .enumerate()
        .map(|(j, &w)| {
            let c = charged.get(&j).copied().unwrap_or(0);
            // `c <= w` was just checked.
            (w as u128 - c) as u64
        })
        .collect();

    let mut steps: Vec<String> = Vec::new();
    // Every core contributes one term worth `w_min * (Σ r >= 1)`:
    //
    // * a MINED core reconstructs its `Σ r >= 1` on the spot, by summing the
    //   mined hard row with its members' relaxation rows (the literal pairs
    //   cancel, dropping the degree from `1+k` to `1`);
    // * a SAT-derived core already IS such a row — the `rup` step states it —
    //   so its term is just that row's id.
    //
    // The terms are summed and the whole is lifted to the objective's own
    // weights at the end.
    let mut terms: Vec<String> = Vec::with_capacity(cores.len() + sat_cores.len());
    for core in cores {
        let mut term = format!("{}", core.hard_row);
        for &lit in &core.members {
            let j = shape.unit_soft[&lit];
            term.push_str(&format!(" {} +", shape.soft_row(j)));
        }
        term.push_str(&format!(" {} *", core.w_min));
        terms.push(term);
    }
    for core in sat_cores {
        let mut step = String::from("rup");
        for &j in &core.softs {
            step.push_str(&format!(" +1 x{}", shape.relax_var(j)));
        }
        step.push_str(" >= 1 ;");
        let id = base_id + 1 + steps.len() as u64;
        steps.push(step);
        terms.push(format!("{id} {} *", core.w_min));
    }

    // ---- preprocessing, on the residual ----
    let mut preproc_lb: u64 = 0;
    let mut p1_softs = 0usize;
    let mut p1b_softs = 0usize;
    let mut am1_layers = 0usize;
    if let Some(pre) = preproc {
        // P1: the whole residual weight of a soft whose every literal is false
        // at the root.
        for hit in &pre.p1 {
            let c = residual[hit.j];
            if c == 0 {
                continue;
            }
            match &hit.unit_rows {
                // P1a — pure `pol`: the soft row plus one unit hard row per
                // literal. Every literal pair cancels and the degree falls from
                // `1 + k` to `1`, leaving `r_j >= 1`. With no literals at all
                // (an empty soft) the row already is `r_j >= 1`.
                Some(rows) => {
                    let mut term = format!("{}", shape.soft_row(hit.j));
                    for row in rows {
                        term.push_str(&format!(" {row} +"));
                    }
                    term.push_str(&format!(" {c} *"));
                    terms.push(term);
                }
                // P1b — one `rup`, which the emitter has already replayed for
                // itself against the hard rows.
                None => {
                    let id = base_id + 1 + steps.len() as u64;
                    steps.push(format!("rup +1 x{} >= 1 ;", shape.relax_var(hit.j)));
                    terms.push(format!("{id} {c} *"));
                    p1b_softs += 1;
                }
            }
            *charged.entry(hit.j).or_insert(0) += c as u128;
            residual[hit.j] = 0;
            preproc_lb = preproc_lb.checked_add(c).ok_or(LbDeclined::Overflow)?;
            p1_softs += 1;
        }

        // P2 / AM1: peel at-most-one cliques out of what is left. `plan_am1`
        // decrements `residual` in place, so no layer can take a soft past its
        // weight.
        for layer in plan_am1(shape, &pre.graph, &mut residual) {
            let k = layer.members.len() as u64;
            let base = base_id + 1 + steps.len() as u64;
            // Refuse rather than guess: a ladder we cannot state in full is a
            // ladder that would fail the WHOLE certificate.
            let Some(lines) = am1_layer_steps(shape, &pre.graph, &layer, base) else {
                continue;
            };
            let t_k = base + lines.len() as u64 - 1;
            steps.extend(lines);
            terms.push(format!("{t_k} {} *", layer.d));
            for &(j, _) in &layer.members {
                *charged.entry(j).or_insert(0) += layer.d as u128;
            }
            let gain = layer.d.checked_mul(k - 1).ok_or(LbDeclined::Overflow)?;
            preproc_lb = preproc_lb.checked_add(gain).ok_or(LbDeclined::Overflow)?;
            am1_layers += 1;
        }
        lb = lb.checked_add(preproc_lb).ok_or(LbDeclined::Overflow)?;
    }

    // The residual cap makes this unreachable, which is exactly why it stays:
    // it is the one check that stands between an accounting slip and a
    // certificate claiming more than the instance allows.
    for (&j, &c) in &charged {
        let w = shape.soft_weights[j] as u128;
        if c > w {
            let lit = shape
                .unit_soft
                .iter()
                .find(|(_, &idx)| idx == j)
                .map(|(&l, _)| l)
                .unwrap_or(0);
            return Err(LbDeclined::OverCharged {
                lit,
                weight: shape.soft_weights[j],
                charged: c,
            });
        }
    }

    if terms.is_empty() {
        // Nothing derived anything, so there is no row to point the conclusion
        // at and the literal-axiom lift below would have nothing to add to.
        return Ok(Derivation {
            lb: 0,
            steps: Vec::new(),
            lift: String::new(),
            sat_cores: 0,
            p1_softs: 0,
            p1b_softs: 0,
            am1_layers: 0,
            preproc_lb: 0,
        });
    }

    let mut lift = String::new();
    for (idx, term) in terms.iter().enumerate() {
        if idx > 0 {
            lift.push(' ');
        }
        lift.push_str(term);
        if idx > 0 {
            lift.push_str(" +");
        }
    }

    // Lift every objective coefficient to its exact weight with literal axioms
    // (`r_j >= 0`), so the derived row is syntactically the objective. Softs no
    // source touched are lifted from 0, which is what makes the result
    // `obj >= lb` over the WHOLE objective rather than over a sub-sum.
    for (j, &w) in shape.soft_weights.iter().enumerate() {
        if w == 0 {
            continue; // contributes no objective term
        }
        let c = charged.get(&j).copied().unwrap_or(0);
        let delta = w as u128 - c; // c <= w checked above
        if delta > 0 {
            lift.push_str(&format!(" x{} {} * +", shape.relax_var(j), delta));
        }
    }

    Ok(Derivation {
        lb,
        steps,
        lift,
        sat_cores: sat_cores.len(),
        p1_softs,
        p1b_softs,
        am1_layers,
        preproc_lb,
    })
}

/// Write `<stem>.opb` and `<stem>.opb.pbp` certifying `cost` for `wcnf`.
///
/// `cores` may be empty, in which case the certified interval is
/// `0 <= obj <= cost` — sound, and deliberately not an optimality claim.
///
/// See THE RULE at the top of this module: the return value carries no verdict
/// and no caller may derive one from it.
pub(crate) fn emit_certificate(
    wcnf: &Path,
    stem: &Path,
    model: &[bool],
    cost: u64,
    cores: &[PaidCore],
    sat_cores: &[SatCore],
    stream: &dyn Fn(&Path, &mut dyn FnMut(Option<u64>, &[i32]) -> Result<()>) -> Result<()>,
) -> Result<Emitted> {
    emit_certificate_within(
        wcnf,
        stem,
        model,
        cost,
        cores,
        sat_cores,
        stream,
        UP_LITERAL_BUDGET,
    )
}

/// Decide which SAT-derived cores this emitter is willing to state.
///
/// Two hurdles, both of which SILENTLY DROP a core rather than failing:
///
/// 1. every member must resolve to an unambiguous unit soft of THIS file (the
///    engine works on a merged, preprocessed soft set — a member that merged
///    with a duplicate cannot be pointed at a single relaxation variable);
/// 2. the resulting row must survive the emitter's own RUP check.
///
/// Dropping weakens the bound, which is always sound. With `up` absent — the
/// propagation structure did not fit [`UP_LITERAL_BUDGET`] — NOTHING can be
/// verified and nothing is stated; the caller reports that the feature was
/// skipped rather than that it found nothing.
fn certify_sat_cores(
    shape: &Shape,
    sat_cores: &[SatCore],
    up: Option<&mut HardUp>,
) -> Vec<AcceptedSatCore> {
    if sat_cores.is_empty() {
        return Vec::new();
    }
    // Resolve memberships BEFORE touching the propagation structure: on an
    // instance whose cores are all inexpressible there is nothing to check.
    let resolved: Vec<(&[i32], AcceptedSatCore)> = sat_cores
        .iter()
        .filter_map(|core| {
            if core.members.is_empty() || core.w_min == 0 {
                return None;
            }
            let mut softs = Vec::with_capacity(core.members.len());
            for &lit in &core.members {
                let &j = shape.unit_soft.get(&lit)?;
                if shape.ambiguous_unit.contains(&lit) {
                    return None;
                }
                softs.push(j);
            }
            Some((
                core.members.as_slice(),
                AcceptedSatCore {
                    w_min: core.w_min,
                    softs,
                },
            ))
        })
        .collect();
    // No propagator (over budget) means nothing can be verified, and an
    // unverified core must never be stated.
    let Some(up) = up else {
        return Vec::new();
    };
    let mut accepted = Vec::with_capacity(resolved.len());
    for (members, core) in resolved {
        if up.core_is_rup(members) {
            accepted.push(core);
        }
    }
    accepted
}

#[allow(clippy::too_many_arguments)]
fn emit_certificate_within(
    wcnf: &Path,
    stem: &Path,
    model: &[bool],
    cost: u64,
    cores: &[PaidCore],
    sat_cores: &[SatCore],
    stream: &dyn Fn(&Path, &mut dyn FnMut(Option<u64>, &[i32]) -> Result<()>) -> Result<()>,
    up_budget: u64,
) -> Result<Emitted> {
    let shape = scan_shape(wcnf, model, stream)?;

    // ONE propagation structure, shared by the SAT-core RUP filter and P1b's
    // root-false scan. It is built only if something needs it — root
    // propagation starts from unit hard rows, so with none of those no soft can
    // be root-falsified by a chain and P1b has nothing to find.
    // A SAT core only needs the propagator if it is RESOLVABLE at all — every
    // member has to be a unit soft of this file, or the core is dropped before
    // the RUP filter ever sees it. Checking that first costs a HashMap lookup
    // per member and saves a full extra pass over the .wcnf plus up to ~80MB
    // allocated and immediately dropped, on instances whose cores all live over
    // totalizer selectors (the common case once OLL gets going).
    let any_resolvable_sat_core = sat_cores
        .iter()
        .any(|c| c.members.iter().all(|l| shape.unit_soft.contains_key(l)));
    let wants_up = any_resolvable_sat_core || !shape.unit_hard.is_empty();
    let up_fits = HardUp::fits(&shape, up_budget);
    let mut up = if wants_up && up_fits {
        Some(HardUp::build(wcnf, &shape, stream)?)
    } else {
        None
    };
    let over_budget = wants_up && !up_fits;
    let sat_cores_over_budget = over_budget && !sat_cores.is_empty();
    let accepted = certify_sat_cores(&shape, sat_cores, up.as_mut());

    // Preprocessing the emitter rediscovers for itself. P1a and the
    // at-most-one ladders are pure `pol`, so they run with or without the
    // propagator; only P1b needs it.
    let preproc = scan_preproc(wcnf, &shape, up.as_ref(), stream, AM1_EDGE_BUDGET)?;
    // Free the propagation index — up to ~80MB — before the OPB pass starts
    // writing.
    drop(up);
    let am1_graph_truncated = preproc.graph.truncated;

    let base_id = shape.num_constraints();
    // Fall back to the strongest SUBSET that still derives rather than
    // surrendering to 0. A decline is almost always a SAT-derived core whose
    // charge collides with a mined one; dropping straight to 0 would forfeit
    // the mined floor too, even though it derives from input rows alone and
    // would have verified on its own. Preprocessing is charged on the residual
    // and cannot decline, so it survives every rung.
    let mut lb_declined: Option<LbDeclined> = None;
    let mut derivation: Option<Derivation> = None;
    for (with_sat, with_mined) in [(true, true), (false, true), (false, false)] {
        let sat: &[AcceptedSatCore] = if with_sat { &accepted } else { &[] };
        let mined: &[PaidCore] = if with_mined { cores } else { &[] };
        match derive_lower_bound(&shape, mined, sat, Some(&preproc), base_id) {
            Ok(d) => {
                derivation = Some(d);
                break;
            }
            Err(why) => {
                // Report the FIRST reason, which is the one that names what the
                // engine actually did wrong.
                lb_declined.get_or_insert(why);
            }
        }
    }
    let derivation = derivation.unwrap_or(Derivation {
        lb: 0,
        steps: Vec::new(),
        lift: String::new(),
        sat_cores: 0,
        p1_softs: 0,
        p1b_softs: 0,
        am1_layers: 0,
        preproc_lb: 0,
    });
    let lower_bound = derivation.lb;
    let pol = (!derivation.lift.is_empty()).then_some(&derivation.lift);

    // APPEND `.opb`, never `with_extension`. `with_extension` REPLACES whatever
    // follows the last dot, and MaxSAT instance names are full of dots:
    // `spot5_wt-8.wcsp.log` became `spot5_wt-8.wcsp.opb`, and
    // `auctions_wt-cat_paths_60_70_0007.txt` became
    // `auctions_wt-cat_paths_60_70_0007.opb`. The certificate was written, just
    // not where it was asked for — so a caller that derives the stem from the
    // instance name (which the bench lane does) finds nothing and records the
    // row as "solver reported OPTIMUM but wrote no certificate". Silent, and
    // wrong in the direction that makes a certified sweep look uncertified.
    let opb_path = {
        let mut p = stem.to_path_buf().into_os_string();
        p.push(".opb");
        std::path::PathBuf::from(p)
    };
    let pbp_path = {
        let mut p = opb_path.clone().into_os_string();
        p.push(".pbp");
        std::path::PathBuf::from(p)
    };

    // ---- the OPB restatement ----
    let mut opb = BufWriter::new(
        fs::File::create(&opb_path)
            .with_context(|| format!("failed to create '{}'", opb_path.display()))?,
    );
    writeln!(
        opb,
        "* #variable= {} #constraint= {}",
        shape.num_vars(),
        shape.num_constraints()
    )?;
    write!(opb, "min:")?;
    for (j, &w) in shape.soft_weights.iter().enumerate() {
        if w > 0 {
            write!(opb, " +{w} x{}", shape.relax_var(j))?;
        }
    }
    writeln!(opb, " ;")?;

    // Hard rows first, in file order, so hard clause i has constraint id i+1 —
    // the identity `#core-mine` reports its rows in.
    stream(wcnf, &mut |weight, lits| {
        if weight.is_none() {
            for l in dedup_lits(lits) {
                write!(opb, "+1 {} ", opb_lit(l))?;
            }
            writeln!(opb, ">= 1 ;")?;
        }
        Ok(())
    })?;
    // Then the relaxed soft rows.
    let mut j = 0usize;
    stream(wcnf, &mut |weight, lits| {
        if weight.is_some() {
            for l in dedup_lits(lits) {
                write!(opb, "+1 {} ", opb_lit(l))?;
            }
            writeln!(opb, "+1 x{} >= 1 ;", shape.relax_var(j))?;
            j += 1;
        }
        Ok(())
    })?;
    opb.flush()?;

    // ---- the VeriPB certificate ----
    let mut pbp = BufWriter::new(
        fs::File::create(&pbp_path)
            .with_context(|| format!("failed to create '{}'", pbp_path.display()))?,
    );
    writeln!(pbp, "pseudo-Boolean proof version 3.0")?;
    writeln!(pbp, "f {} ;", shape.num_constraints())?;

    // Every step the derivation needs, in id order: the SAT-derived cores and
    // P1b softs as `rup` (each already replayed by the emitter's own
    // propagation), then the at-most-one induction ladders as `pol`. A declined
    // derivation writes none of them — they would be dead weight in the log.
    for step in &derivation.steps {
        writeln!(pbp, "{step}")?;
    }

    let mut lb_hint: Option<u64> = None;
    if let Some(rpn) = pol {
        writeln!(pbp, "pol {rpn} ;")?;
        // ids 1..=num_constraints are the input rows, then one per step above;
        // this `pol` allocates the next.
        lb_hint = Some(base_id + derivation.steps.len() as u64 + 1);
    }

    // The witness: a COMPLETE assignment over instance variables and relaxation
    // variables. `r_j` is set iff the model falsifies soft `j` — any other
    // choice either violates the soft's row or inflates the objective past the
    // cost we are claiming.
    let witness = {
        let mut w = String::new();
        for v in 1..=shape.max_var {
            if !w.is_empty() {
                w.push(' ');
            }
            if lit_value(model, v as i32) {
                w.push_str(&format!("x{v}"));
            } else {
                w.push_str(&format!("~x{v}"));
            }
        }
        for j in 0..shape.soft_weights.len() {
            if !w.is_empty() {
                w.push(' ');
            }
            if shape.soft_falsified[j] {
                w.push_str(&format!("x{}", shape.relax_var(j)));
            } else {
                w.push_str(&format!("~x{}", shape.relax_var(j)));
            }
        }
        w
    };
    // `: cost` makes the checker recompute the objective and reject a
    // misreported cost, rather than taking our word for it.
    writeln!(pbp, "sol {witness} : {cost} ;")?;
    writeln!(pbp, "output NONE;")?;
    write!(pbp, "conclusion BOUNDS {lower_bound}")?;
    if let Some(id) = lb_hint {
        write!(pbp, " : {id}")?;
    }
    // The upper-bound witness is repeated in the conclusion because VeriPB's
    // unchecked-deletion mode discounts logged solutions and would otherwise
    // fail a finite upper bound outright.
    writeln!(pbp, " {cost} : {witness} ;")?;
    writeln!(pbp, "end pseudo-Boolean proof;")?;
    pbp.flush()?;

    Ok(Emitted {
        num_constraints: shape.num_constraints(),
        num_vars: shape.num_vars(),
        lower_bound,
        lb_declined,
        sat_cores_offered: sat_cores.len(),
        sat_cores_certified: derivation.sat_cores,
        sat_cores_over_budget,
        p1_softs_certified: derivation.p1_softs,
        p1b_softs_certified: derivation.p1b_softs,
        am1_layers_certified: derivation.am1_layers,
        preproc_lower_bound: derivation.preproc_lb,
        p1b_over_budget: over_budget,
        am1_graph_truncated,
    })
}

#[cfg(test)]
#[allow(clippy::panic, clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;
    use ay_test_support::veripb;

    const SUITE: &str = "maxsat-proof";

    /// Two disjoint ternary cores over six unit softs: the shape `#core-mine`
    /// exists for (all-ternary hards, uniform unit softs — the judgment family).
    /// Optimum is 2, and the mined-core floor is also 2, so the certificate is a
    /// full optimality proof.
    const WCNF: &str = "h -1 -2 -3 0\nh -4 -5 -6 0\n1 1 0\n1 2 0\n1 3 0\n1 4 0\n1 5 0\n1 6 0\n";

    fn fixture(dir: &Path) -> std::path::PathBuf {
        let p = dir.join("t.wcnf");
        fs::write(&p, WCNF).unwrap();
        p
    }

    fn streamer() -> impl Fn(&Path, &mut dyn FnMut(Option<u64>, &[i32]) -> Result<()>) -> Result<()>
    {
        |p: &Path, cb: &mut dyn FnMut(Option<u64>, &[i32]) -> Result<()>| {
            crate::cmd_maxsat::stream_wcnf_file(p, cb).map(|_| ())
        }
    }

    /// The model AY reports for `WCNF`: falsify soft 1 and soft 4. RAW ids, so
    /// index 0 is unused.
    fn model() -> Vec<bool> {
        vec![false, false, true, true, false, true, true]
    }

    fn cores() -> Vec<PaidCore> {
        vec![
            PaidCore {
                hard_row: 1,
                w_min: 1,
                members: vec![1, 2, 3],
            },
            PaidCore {
                hard_row: 2,
                w_min: 1,
                members: vec![4, 5, 6],
            },
        ]
    }

    /// THE soundness net, and the one test here that never skips: an engine that
    /// charges a soft more than its weight drives `lb` past the optimum, which
    /// is the wrong-answer mode that disqualified an AY submission. Emission
    /// must refuse to dress that up as a proof.
    #[test]
    fn an_overcharged_core_is_declined_not_certified() {
        let dir = tempfile::tempdir().unwrap();
        let wcnf = fixture(dir.path());
        // Each soft has weight 1, but these cores charge 2 apiece.
        let bad = vec![
            PaidCore {
                hard_row: 1,
                w_min: 2,
                members: vec![1, 2, 3],
            },
            PaidCore {
                hard_row: 2,
                w_min: 2,
                members: vec![4, 5, 6],
            },
        ];
        let out = emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            &model(),
            2,
            &bad,
            &[],
            &streamer(),
        )
        .unwrap();
        assert_eq!(
            out.lower_bound, 0,
            "an unprovable lower bound must not be emitted; got {}",
            out.lower_bound
        );
        assert!(
            matches!(out.lb_declined, Some(LbDeclined::OverCharged { .. })),
            "expected an OverCharged decline, got {:?}",
            out.lb_declined
        );
        // And the file on disk must not claim it either.
        let pbp = fs::read_to_string(dir.path().join("c.opb.pbp")).unwrap();
        assert!(
            pbp.contains("conclusion BOUNDS 0 2"),
            "certificate should have fallen back to lb 0:\n{pbp}"
        );
    }

    /// A dotted stem must produce `<stem>.opb`, not have its last segment eaten.
    ///
    /// Real MSE24 names are dotted (`spot5_wt-8.wcsp.log`,
    /// `auctions_wt-cat_paths_60_70_0007.txt`), and `with_extension` silently
    /// rewrote those to `spot5_wt-8.wcsp.opb`. Caught by running the lane over
    /// the real corpus: 3 of 4 instances looked uncertified because the caller
    /// looked where it asked and the file was somewhere else.
    ///
    /// Kill mutation: put back `stem.with_extension("opb")`.
    #[test]
    fn a_dotted_stem_keeps_every_segment() {
        let dir = tempfile::tempdir().unwrap();
        let wcnf = fixture(dir.path());
        let stem = dir.path().join("spot5_wt-8.wcsp.log");
        emit_certificate(&wcnf, &stem, &model(), 2, &cores(), &[], &streamer()).unwrap();
        assert!(
            dir.path().join("spot5_wt-8.wcsp.log.opb").is_file(),
            "expected `<stem>.opb`; directory holds {:?}",
            fs::read_dir(dir.path())
                .unwrap()
                .filter_map(|e| e.ok().map(|e| e.file_name()))
                .collect::<Vec<_>>()
        );
        assert!(dir.path().join("spot5_wt-8.wcsp.log.opb.pbp").is_file());
        assert!(
            !dir.path().join("spot5_wt-8.wcsp.opb").exists(),
            "the `.log` segment was eaten"
        );
    }

    /// A core naming a literal that is not a unit soft cannot be translated into
    /// the PB derivation, so it must be declined rather than guessed at. This is
    /// what caught a raw-id-vs-DIMACS off-by-one during development.
    #[test]
    fn a_core_over_non_unit_softs_is_declined() {
        let dir = tempfile::tempdir().unwrap();
        let wcnf = fixture(dir.path());
        let bad = vec![PaidCore {
            hard_row: 1,
            w_min: 1,
            members: vec![1, 2, 99],
        }];
        let out = emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            &model(),
            2,
            &bad,
            &[],
            &streamer(),
        )
        .unwrap();
        assert_eq!(out.lower_bound, 0);
        assert!(matches!(
            out.lb_declined,
            Some(LbDeclined::MemberNotUnitSoft { lit: 99 })
        ));
    }

    /// A core pointing past the end of the hard clauses would name a constraint
    /// id that means something else entirely in the emitted OPB.
    #[test]
    fn a_core_row_out_of_range_is_declined() {
        let dir = tempfile::tempdir().unwrap();
        let wcnf = fixture(dir.path());
        let bad = vec![PaidCore {
            hard_row: 99,
            w_min: 1,
            members: vec![1, 2, 3],
        }];
        let out = emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            &model(),
            2,
            &bad,
            &[],
            &streamer(),
        )
        .unwrap();
        assert_eq!(out.lower_bound, 0);
        assert!(matches!(
            out.lb_declined,
            Some(LbDeclined::RowOutOfRange { row: 99 })
        ));
    }

    /// M0: the anytime certificate. `0 <= obj <= cost` deliberately does NOT
    /// entail optimality, so this increment cannot produce a premature optimum
    /// claim — but the upper bound is fully checked, model and cost both.
    #[test]
    fn m0_anytime_certificate_verifies() {
        let Some(checker) = veripb::require_checker(SUITE) else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let wcnf = fixture(dir.path());
        let out = emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            &model(),
            2,
            &[],
            &[],
            &streamer(),
        )
        .unwrap();
        assert_eq!(out.lower_bound, 0);
        veripb::run(
            &checker,
            &dir.path().join("c.opb"),
            &dir.path().join("c.opb.pbp"),
            &["--opb"],
        )
        .assert_verified(&veripb::Expect::bounds("0", "2"), SUITE);
    }

    /// M1: the mined-core floor, derived as cutting planes over input rows only.
    /// Here it closes the gap, so the checker confirms a genuine optimum.
    #[test]
    fn m1_mined_core_lower_bound_verifies() {
        let Some(checker) = veripb::require_checker(SUITE) else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let wcnf = fixture(dir.path());
        let out = emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            &model(),
            2,
            &cores(),
            &[],
            &streamer(),
        )
        .unwrap();
        assert_eq!(out.lower_bound, 2, "both cores should be charged");
        assert!(out.lb_declined.is_none());
        veripb::run(
            &checker,
            &dir.path().join("c.opb"),
            &dir.path().join("c.opb.pbp"),
            &["--opb"],
        )
        .assert_verified(&veripb::Expect::bounds("2", "2"), SUITE);
    }

    /// A passing certificate proves nothing unless it can fail. Each mutation
    /// below is a way AY could be wrong; the checker must reject every one.
    #[test]
    fn the_checker_rejects_a_tampered_certificate() {
        let Some(checker) = veripb::require_checker(SUITE) else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let wcnf = fixture(dir.path());
        emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            &model(),
            2,
            &cores(),
            &[],
            &streamer(),
        )
        .unwrap();
        let opb = dir.path().join("c.opb");
        let good = fs::read_to_string(dir.path().join("c.opb.pbp")).unwrap();

        let mutations: &[(&str, &str, &str)] = &[
            // Understate the cost AY achieved.
            ("misreported cost", ": 2 ;", ": 1 ;"),
            // Claim a lower bound above the optimum: the disqualifying mode.
            ("lower bound above optimum", "BOUNDS 2 :", "BOUNDS 3 :"),
            // Claim an upper bound the model does not achieve.
            ("understated upper bound", " 2 : ~x1", " 1 : ~x1"),
            // Charge a core more than the derivation supports.
            ("over-paid core weight", "5 + 1 *", "5 + 2 *"),
        ];
        for (name, from, to) in mutations {
            let tampered = good.replacen(from, to, 1);
            assert_ne!(
                tampered, good,
                "{SUITE}: mutation '{name}' did not apply — the test is vacuous"
            );
            let path = dir.path().join(format!("m-{}.pbp", name.replace(' ', "-")));
            fs::write(&path, &tampered).unwrap();
            veripb::run(&checker, &opb, &path, &["--opb"])
                .assert_rejected(&format!("{SUITE}: mutation '{name}' must be rejected"));
        }
    }

    // -----------------------------------------------------------------------
    // SAT-derived cores.
    // -----------------------------------------------------------------------

    /// A core the SAT solver could return that IS reachable by unit propagation
    /// over the hard clauses, next to one mined core so the two kinds can be
    /// charged together.
    ///
    /// * hard 1 `(¬x1 ∨ ¬x2 ∨ x3)`, hard 2 `(¬x3 ∨ ¬x4)`: assuming the unit
    ///   softs `x1, x2, x4` propagates `x3` and then conflicts, so `{1,2,4}` is
    ///   a real core AND it is RUP. Crucially it is NOT any single hard clause,
    ///   which is the whole point — `#core-mine` cannot find it.
    /// * hard 3 `(¬x5 ∨ ¬x6)` IS a mined core over `{5,6}`.
    ///
    /// Optimum 2: one of `{x1,x2,x4}` and one of `{x5,x6}` must be paid.
    const RUP_WCNF: &str = "h -1 -2 3 0\nh -3 -4 0\nh -5 -6 0\n\
                            1 1 0\n1 2 0\n1 4 0\n1 5 0\n1 6 0\n";

    fn rup_fixture(dir: &Path) -> std::path::PathBuf {
        let p = dir.join("r.wcnf");
        fs::write(&p, RUP_WCNF).unwrap();
        p
    }

    /// Cost 2: falsify soft `(x4)` and soft `(x6)`. RAW ids, index 0 unused.
    fn rup_model() -> Vec<bool> {
        vec![false, true, true, true, false, true, false]
    }

    /// The SAT-derived core `{x1, x2, x4}` — the one no mining pass can find.
    fn rup_sat_core() -> Vec<SatCore> {
        vec![SatCore {
            w_min: 1,
            members: vec![1, 2, 4],
        }]
    }

    /// The mined core `{x5, x6}`, hard row 3.
    fn rup_mined_core() -> Vec<PaidCore> {
        vec![PaidCore {
            hard_row: 3,
            w_min: 1,
            members: vec![5, 6],
        }]
    }

    /// An instance where the core `{x1, x2}` is genuinely UNSAT but NOT RUP:
    /// assuming both leaves every hard clause with two unassigned literals, so
    /// unit propagation stalls and only a case split on `x5` refutes it.
    ///
    /// This is the shape the whole feature exists to be safe about — an engine
    /// that reports its cores verbatim would emit an unreplayable `rup` here
    /// and lose the entire certificate.
    const NONRUP_WCNF: &str = "h -1 -2 5 6 0\nh -1 -2 5 -6 0\n\
                               h -1 -2 -5 6 0\nh -1 -2 -5 -6 0\n1 1 0\n1 2 0\n";

    fn nonrup_fixture(dir: &Path) -> std::path::PathBuf {
        let p = dir.join("n.wcnf");
        fs::write(&p, NONRUP_WCNF).unwrap();
        p
    }

    /// A SAT-derived core that our own propagation confirms is RUP is stated as
    /// a `rup` step and folded into the bound — reaching past `#core-mine`,
    /// which cannot see `{x1,x2,x4}` at all because it is no single hard clause.
    ///
    /// Kill mutation (APPLIED, confirmed failing, reverted): in
    /// `HardUp::propagate`, `let code = lit_code(-p);` → `lit_code(p)`, i.e.
    /// index the occurrence list by the assigned literal instead of its
    /// negation. Nothing ever propagates, no core is ever accepted, and the
    /// bound falls back to 0.
    #[test]
    fn a_rup_sat_core_is_certified() {
        let Some(checker) = veripb::require_checker(SUITE) else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let wcnf = rup_fixture(dir.path());
        let out = emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            &rup_model(),
            2,
            &[],
            &rup_sat_core(),
            &streamer(),
        )
        .unwrap();
        assert_eq!(out.sat_cores_offered, 1);
        assert_eq!(
            out.sat_cores_certified, 1,
            "a RUP core must be verified and stated"
        );
        assert!(!out.sat_cores_over_budget);
        assert!(out.lb_declined.is_none());
        // The SAT core floors 1; the emitter's own at-most-one peel finds the
        // OTHER 1 for free, because hard 3 `(¬x5 ∨ ¬x6)` excludes the unit
        // softs `(x5)` and `(x6)`. Together they close the gap to the optimum.
        assert_eq!(out.am1_layers_certified, 1, "the {{x5,x6}} mutex is peeled");
        assert_eq!(out.preproc_lower_bound, 1);
        assert_eq!(out.lower_bound, 2, "SAT core 1 + at-most-one layer 1");
        let pbp = fs::read_to_string(dir.path().join("c.opb.pbp")).unwrap();
        assert!(pbp.contains("rup "), "no rup step was written:\n{pbp}");
        veripb::run(
            &checker,
            &dir.path().join("c.opb"),
            &dir.path().join("c.opb.pbp"),
            &["--opb"],
        )
        .assert_verified(&veripb::Expect::bounds("2", "2"), SUITE);
    }

    /// Mined and SAT-derived cores in the same derivation, charging disjoint
    /// softs: the bound is the sum, and it closes the gap. This is the shape
    /// the feature is for — `#core-mine` alone certifies 1 of the optimum 2.
    ///
    /// Kill mutation (APPLIED, confirmed failing, reverted): in
    /// `emit_certificate_within`, drop the `accepted.len()` term from
    /// `lb_hint`, so the conclusion points the checker at the row before the
    /// `pol`. VeriPB then rejects the proof. (That mutation does NOT kill
    /// `a_rup_sat_core_is_certified`: with a single core and unit weights the
    /// `rup` row alone happens to justify the same bound, which is exactly why
    /// the id arithmetic needs a test with two cores of different kinds.)
    #[test]
    fn mined_and_sat_cores_combine_into_one_bound() {
        let Some(checker) = veripb::require_checker(SUITE) else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let wcnf = rup_fixture(dir.path());
        let mined_only = emit_certificate(
            &wcnf,
            &dir.path().join("m"),
            &rup_model(),
            2,
            &rup_mined_core(),
            &[],
            &streamer(),
        )
        .unwrap();
        assert_eq!(
            mined_only.lower_bound, 1,
            "baseline: mining alone reaches half the optimum"
        );

        let both = emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            &rup_model(),
            2,
            &rup_mined_core(),
            &rup_sat_core(),
            &streamer(),
        )
        .unwrap();
        assert_eq!(both.lower_bound, 2, "mined 1 + SAT 1");
        assert!(both.lb_declined.is_none());
        veripb::run(
            &checker,
            &dir.path().join("c.opb"),
            &dir.path().join("c.opb.pbp"),
            &["--opb"],
        )
        .assert_verified(&veripb::Expect::bounds("2", "2"), SUITE);
    }

    /// A core that is UNSAT but NOT RUP is OMITTED, not emitted. The bound is
    /// weaker, which is always sound; emitting it would fail the whole proof.
    ///
    /// The second half proves the omission was necessary rather than timid: the
    /// same certificate with the `rup` step injected by hand is REJECTED by the
    /// checker.
    ///
    /// Kill mutation (APPLIED, confirmed failing, reverted): in
    /// `HardUp::core_is_rup`, replace `let conflict = self.propagate(members);`
    /// with `let conflict = true;` — i.e. trust the engine instead of checking.
    #[test]
    fn a_non_rup_sat_core_is_omitted_not_emitted() {
        let dir = tempfile::tempdir().unwrap();
        let wcnf = nonrup_fixture(dir.path());
        // Cost 1: falsify soft (x1).
        let model = vec![false, false, true, false, false, true, false];
        let out = emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            &model,
            1,
            &[],
            &[SatCore {
                w_min: 1,
                members: vec![1, 2],
            }],
            &streamer(),
        )
        .unwrap();
        assert_eq!(out.sat_cores_offered, 1);
        assert_eq!(
            out.sat_cores_certified, 0,
            "a core needing a case split is not RUP and must not be stated"
        );
        assert_eq!(out.lower_bound, 0);
        let pbp = fs::read_to_string(dir.path().join("c.opb.pbp")).unwrap();
        assert!(
            !pbp.contains("rup"),
            "an unverified core reached the proof log:\n{pbp}"
        );

        let Some(checker) = veripb::require_checker(SUITE) else {
            return;
        };
        // 6 vars + 2 relaxation vars: r_0 = x7, r_1 = x8.
        let injected = pbp.replacen("f 6 ;", "f 6 ;\nrup +1 x7 +1 x8 >= 1 ;", 1);
        assert_ne!(injected, pbp, "{SUITE}: injection did not apply");
        let path = dir.path().join("injected.pbp");
        fs::write(&path, &injected).unwrap();
        veripb::run(&checker, &dir.path().join("c.opb"), &path, &["--opb"]).assert_rejected(
            &format!("{SUITE}: an unreplayable rup step must fail the whole proof"),
        );
    }

    /// The over-charge guard spans BOTH kinds. Here the mined core and the
    /// SAT-derived core are the same soft pair `{x5,x6}` — each valid alone,
    /// together charging weight-1 softs twice over. That is the arithmetic that
    /// drives `lb` past the optimum, so the whole derivation is declined.
    ///
    /// Kill mutation (APPLIED, confirmed failing, reverted): in
    /// `derive_lower_bound`, delete the `for &j in &core.softs` charge loop
    /// over `sat_cores`, so SAT cores raise `lb` without paying into the
    /// accounting. The bound then reads 2 with no decline.
    #[test]
    fn an_overcharged_mined_plus_sat_mix_is_declined() {
        let dir = tempfile::tempdir().unwrap();
        let wcnf = rup_fixture(dir.path());
        let overlapping = vec![SatCore {
            w_min: 1,
            members: vec![5, 6],
        }];
        // Each is fine on its own…
        for (label, mined, sat) in [
            ("mined only", rup_mined_core(), Vec::new()),
            ("sat only", Vec::new(), overlapping.clone()),
        ] {
            let out = emit_certificate(
                &wcnf,
                &dir.path().join("solo"),
                &rup_model(),
                2,
                &mined,
                &sat,
                &streamer(),
            )
            .unwrap();
            assert_eq!(out.lower_bound, 1, "{label} should certify 1");
            assert!(out.lb_declined.is_none(), "{label}: {:?}", out.lb_declined);
        }
        // …but not together.
        let out = emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            &rup_model(),
            2,
            &rup_mined_core(),
            &overlapping,
            &streamer(),
        )
        .unwrap();
        // The over-charged sum (2) must never be certified. But the MINED half
        // derives from input rows alone and would verify on its own, so the
        // fallback drops the SAT cores and keeps it rather than surrendering a
        // bound we can prove — see the retry in `emit_certificate`.
        assert_ne!(
            out.lower_bound, 2,
            "the double-charged bound must never be certified"
        );
        assert_eq!(
            out.lower_bound, 1,
            "the mined half derives from input rows alone and must survive the \
             SAT core being dropped"
        );
        assert!(
            matches!(out.lb_declined, Some(LbDeclined::OverCharged { .. })),
            "the decline must still be REPORTED even though the mined bound \
             survived, or an over-charging engine goes unnoticed; got {:?}",
            out.lb_declined
        );
        let pbp = fs::read_to_string(dir.path().join("c.opb.pbp")).unwrap();
        assert!(
            !pbp.contains("rup"),
            "the dropped SAT cores must not leave their rup steps behind:\n{pbp}"
        );
        assert!(
            pbp.contains("conclusion BOUNDS 1"),
            "the surviving mined bound must be the one concluded:\n{pbp}"
        );
    }

    /// The memory guard. This machine is a 24GB M4 Pro that has kernel-panicked
    /// under memory pressure and the corpus reaches 1,035,351 hard clauses;
    /// above the budget the propagation index is never built and the whole
    /// feature is skipped — a weaker bound, reported as such so it is not
    /// mistaken for "no cores were provable".
    ///
    /// Kill mutation (APPLIED, confirmed failing, reverted): make `HardUp::fits`
    /// return `true` unconditionally.
    #[test]
    fn the_memory_cap_skips_the_whole_feature() {
        let dir = tempfile::tempdir().unwrap();
        let wcnf = rup_fixture(dir.path());
        let out = emit_certificate_within(
            &wcnf,
            &dir.path().join("c"),
            &rup_model(),
            2,
            &rup_mined_core(),
            &rup_sat_core(),
            &streamer(),
            0, // no budget at all
        )
        .unwrap();
        assert!(
            out.sat_cores_over_budget,
            "over budget must be reported, not silently absent"
        );
        assert_eq!(out.sat_cores_certified, 0);
        // The mined bound is untouched: the guard costs the increment, not the
        // certificate.
        assert_eq!(out.lower_bound, 1);
        assert!(out.lb_declined.is_none());
        let pbp = fs::read_to_string(dir.path().join("c.opb.pbp")).unwrap();
        assert!(!pbp.contains("rup"), "no rup step may be written:\n{pbp}");
    }

    // -----------------------------------------------------------------------
    // Preprocessing bounds the emitter derives for itself. On `spot5_wt-8` and
    // the `MaxSATQueries…` family these ARE the whole lower bound, and the
    // certificate used to say `0 <= obj <= k` while AY privately knew better.
    // -----------------------------------------------------------------------

    fn write_fixture(dir: &Path, name: &str, body: &str) -> std::path::PathBuf {
        let p = dir.join(name);
        fs::write(&p, body).unwrap();
        p
    }

    /// P1a: every literal of soft `(x1 ∨ x2)` is negated by a UNIT HARD row, so
    /// its weight is unavoidable and the derivation is PURE `pol` — the soft row
    /// plus the two unit rows, every literal pair cancelling. No propagator, no
    /// `rup`, nothing for the checker to replay.
    ///
    /// Optimum is 5 and the floor is 5, so this is a full optimality proof where
    /// the emitter used to state `0 <= obj <= 5`.
    ///
    /// Kill mutation (APPLIED, confirmed failing, reverted): in `scan_preproc`,
    /// `shape.unit_hard.contains_key(&-l)` → `contains_key(&l)`, i.e. look for a
    /// unit hard ASSERTING the literal instead of negating it. No soft is
    /// classified, `p1_softs_certified` drops to 0 and the bound falls to 0.
    const P1A_WCNF: &str = "h -1 0\nh -2 0\nh 3 4 0\n5 1 2 0\n7 -3 0\n";

    #[test]
    fn p1a_root_falsified_soft_is_pure_pol() {
        let dir = tempfile::tempdir().unwrap();
        let wcnf = write_fixture(dir.path(), "p1a.wcnf", P1A_WCNF);
        // x1 = x2 = false (forced), x3 = false, x4 = true.
        let model = vec![false, false, false, false, true];
        let out = emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            &model,
            5,
            &[],
            &[],
            &streamer(),
        )
        .unwrap();
        assert_eq!(
            out.p1_softs_certified, 1,
            "the falsified soft must be found"
        );
        assert_eq!(out.p1b_softs_certified, 0, "unit hards need no rup");
        assert_eq!(out.lower_bound, 5);
        assert_eq!(out.preproc_lower_bound, 5);
        assert!(out.lb_declined.is_none());
        let pbp = fs::read_to_string(dir.path().join("c.opb.pbp")).unwrap();
        assert!(
            !pbp.contains("rup"),
            "P1a is cutting planes over input rows only:\n{pbp}"
        );

        let Some(checker) = veripb::require_checker(SUITE) else {
            return;
        };
        veripb::run(
            &checker,
            &dir.path().join("c.opb"),
            &dir.path().join("c.opb.pbp"),
            &["--opb"],
        )
        .assert_verified(&veripb::Expect::bounds("5", "5"), SUITE);
    }

    /// …and because P1a needs no propagation, it survives the memory cap that
    /// silences P1b and the SAT-core filter. A 1M-clause instance on a 24GB box
    /// still gets this bound.
    ///
    /// Kill mutation (APPLIED, confirmed failing, reverted): in `scan_preproc`,
    /// wrap the P1a branch in `if up.is_some()`, i.e. make it depend on the
    /// propagator. The bound then falls to 0 under the cap.
    #[test]
    fn p1a_survives_the_memory_cap() {
        let dir = tempfile::tempdir().unwrap();
        let wcnf = write_fixture(dir.path(), "p1a.wcnf", P1A_WCNF);
        let model = vec![false, false, false, false, true];
        let out = emit_certificate_within(
            &wcnf,
            &dir.path().join("c"),
            &model,
            5,
            &[],
            &[],
            &streamer(),
            0, // no budget at all
        )
        .unwrap();
        assert!(out.p1b_over_budget, "the skip must be REPORTED, not silent");
        assert_eq!(
            out.lower_bound, 5,
            "P1a is pure `pol` and must not depend on the propagator"
        );
    }

    /// P1b: soft `(¬x1 ∨ ¬x2)` is falsified only through a propagation CHAIN
    /// (`x1` is a unit hard, which forces `x2` through `(¬x1 ∨ x2)`). No unit
    /// hard negates `¬x2`, so this needs the propagator and one `rup`.
    ///
    /// Kill mutation (APPLIED, confirmed failing, reverted): in `scan_preproc`,
    /// `value_of(&up.assign, l) == FALSE` → `== TRUE`. Nothing is classified and
    /// the bound falls to 0.
    #[test]
    fn p1b_root_falsified_by_a_chain_needs_one_rup() {
        let dir = tempfile::tempdir().unwrap();
        let wcnf = write_fixture(
            dir.path(),
            "p1b.wcnf",
            "h 1 0\nh -1 2 0\nh 3 4 0\n5 -1 -2 0\n7 -3 0\n",
        );
        // x1 = x2 = true (forced), x3 = false, x4 = true.
        let model = vec![false, true, true, false, true];
        let out = emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            &model,
            5,
            &[],
            &[],
            &streamer(),
        )
        .unwrap();
        assert_eq!(out.p1_softs_certified, 1);
        assert_eq!(
            out.p1b_softs_certified, 1,
            "a chain-falsified soft cannot be stated as pure pol"
        );
        assert_eq!(out.lower_bound, 5);
        let pbp = fs::read_to_string(dir.path().join("c.opb.pbp")).unwrap();
        // max_var is 4, so soft 0's relaxation variable is x5.
        assert!(pbp.contains("rup +1 x5 >= 1 ;"), "no rup step:\n{pbp}");

        let Some(checker) = veripb::require_checker(SUITE) else {
            return;
        };
        veripb::run(
            &checker,
            &dir.path().join("c.opb"),
            &dir.path().join("c.opb.pbp"),
            &["--opb"],
        )
        .assert_verified(&veripb::Expect::bounds("5", "5"), SUITE);
    }

    /// An EMPTY soft clause is unavoidable cost by definition, and its OPB row
    /// already IS `+1 r_j >= 1` — the `k = 0` case of P1a, which needs no unit
    /// hard at all.
    ///
    /// Kill mutation (APPLIED, confirmed failing, reverted): in `scan_preproc`,
    /// guard the P1a branch with `!lits.is_empty()`. The empty soft is skipped
    /// and the bound drops from 4 to 0.
    #[test]
    fn an_empty_soft_clause_is_charged_in_full() {
        let dir = tempfile::tempdir().unwrap();
        // `h -1` makes the P1a machinery run at all; the empty soft is the point.
        let wcnf = write_fixture(dir.path(), "e.wcnf", "h -1 0\n4 0\n2 -1 0\n");
        let model = vec![false, false];
        let out = emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            &model,
            4,
            &[],
            &[],
            &streamer(),
        )
        .unwrap();
        assert_eq!(out.lower_bound, 4, "an empty soft is unconditionally paid");
        let Some(checker) = veripb::require_checker(SUITE) else {
            return;
        };
        veripb::run(
            &checker,
            &dir.path().join("c.opb"),
            &dir.path().join("c.opb.pbp"),
            &["--opb"],
        )
        .assert_verified(&veripb::Expect::bounds("4", "4"), SUITE);
    }

    /// P2: unit softs on COMPLEMENTARY literals are mutually exclusive with no
    /// input row at all — `(l + r_p >= 1) + (¬l + r_n >= 1)` already is
    /// `r_p + r_n >= 1`. `min(3,5) = 3` is the floor, and it is the optimum.
    ///
    /// `min`, not `max`: the same `m` on both sides is what makes the `l`/`¬l`
    /// pair cancel completely, and the checker refuses the `max` version.
    ///
    /// Kill mutation (APPLIED, confirmed failing, reverted): in
    /// `ConflictGraph::mutex`, delete the `if a == -b { return Some(Mutex::Free) }`
    /// arm. The pair is no longer an edge and the bound falls to 0.
    #[test]
    fn complementary_unit_softs_are_a_free_at_most_one() {
        let dir = tempfile::tempdir().unwrap();
        let wcnf = write_fixture(dir.path(), "p2.wcnf", "h 1 2 0\n3 1 0\n5 -1 0\n");
        // x1 = false, x2 = true: soft `(x1)` is paid, `(¬x1)` is not.
        let model = vec![false, false, true];
        let out = emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            &model,
            3,
            &[],
            &[],
            &streamer(),
        )
        .unwrap();
        assert_eq!(out.am1_layers_certified, 1);
        assert_eq!(out.lower_bound, 3, "min(3,5), not max");
        let pbp = fs::read_to_string(dir.path().join("c.opb.pbp")).unwrap();
        assert!(
            !pbp.contains("rup"),
            "a complementary pair is pure `pol` over input rows:\n{pbp}"
        );
        let Some(checker) = veripb::require_checker(SUITE) else {
            return;
        };
        veripb::run(
            &checker,
            &dir.path().join("c.opb"),
            &dir.path().join("c.opb.pbp"),
            &["--opb"],
        )
        .assert_verified(&veripb::Expect::bounds("3", "3"), SUITE);
    }

    /// The peel runs over soft ROWS, not merged literals, so DUPLICATE unit
    /// softs on the same literal are handled by peeling another layer against
    /// the other row. `[2](x1) [3](x1) [5](¬x1)` reaches the full
    /// `min(ΣW⁺, ΣW⁻) = 5` — which the single-pair rule would understate as 3.
    ///
    /// Kill mutation (APPLIED, confirmed failing, reverted): in `plan_am1`, add
    /// `&& shape.unit_soft[&l] == j` to the `nodes` filter, i.e. keep ONE row
    /// per literal the way the core paths must. The `[2](x1)` row disappears,
    /// only one layer is peeled, and the bound reads 3 instead of 5.
    #[test]
    fn duplicate_unit_softs_peel_layer_by_layer() {
        let dir = tempfile::tempdir().unwrap();
        let wcnf = write_fixture(dir.path(), "p2c.wcnf", "h 1 2 0\n2 1 0\n3 1 0\n5 -1 0\n");
        let model = vec![false, false, true];
        let out = emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            &model,
            5,
            &[],
            &[],
            &streamer(),
        )
        .unwrap();
        assert_eq!(out.am1_layers_certified, 2, "one layer per backing row");
        assert_eq!(out.lower_bound, 5, "2 + 3, the whole of the smaller side");
        let Some(checker) = veripb::require_checker(SUITE) else {
            return;
        };
        veripb::run(
            &checker,
            &dir.path().join("c.opb"),
            &dir.path().join("c.opb.pbp"),
            &["--opb"],
        )
        .assert_verified(&veripb::Expect::bounds("5", "5"), SUITE);
    }

    /// A k=4 at-most-one clique pays `k - 1 = 3`, and that does NOT follow from
    /// summing the `C(4,2)` pair rows — naive summation caps at `⌈k/2⌉ = 2` and
    /// the checker refuses the difference. It follows by INDUCTION, one division
    /// per step, and this is the smallest k where the two disagree.
    ///
    /// Kill mutation (APPLIED, confirmed failing, reverted): in
    /// `am1_layer_steps`, the divisor `format!(" {step} d")` → `" {} d", step + 1`
    /// — the emitter off-by-one. VeriPB rejects with "Expected constraint is not
    /// equal to the constraint at the hint".
    #[test]
    fn an_at_most_one_clique_of_four_pays_three() {
        let Some(checker) = veripb::require_checker(SUITE) else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let wcnf = write_fixture(
            dir.path(),
            "k4.wcnf",
            "h -1 -2 0\nh -1 -3 0\nh -1 -4 0\nh -2 -3 0\nh -2 -4 0\nh -3 -4 0\n\
             1 1 0\n1 2 0\n1 3 0\n1 4 0\n",
        );
        // x1 true, the rest false: three softs paid.
        let model = vec![false, true, false, false, false];
        let out = emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            &model,
            3,
            &[],
            &[],
            &streamer(),
        )
        .unwrap();
        assert_eq!(out.am1_layers_certified, 1);
        assert_eq!(out.lower_bound, 3, "k - 1, not the pairwise-sum cap of 2");
        veripb::run(
            &checker,
            &dir.path().join("c.opb"),
            &dir.path().join("c.opb.pbp"),
            &["--opb"],
        )
        .assert_verified(&veripb::Expect::bounds("3", "3"), SUITE);

        // The ladder must be stated in full: T_2, T_3, T_4 — one `pol` per step,
        // and the conclusion must point at the LAST of them. Pointing at T_2
        // would claim 3 from a row that only gives 1.
        let pbp = fs::read_to_string(dir.path().join("c.opb.pbp")).unwrap();
        assert_eq!(
            pbp.matches("pol ").count(),
            4,
            "expected 3 ladder steps plus the lift:\n{pbp}"
        );
    }

    /// A preprocessing charge must NEVER cost the core floor. Here the mined
    /// core IS the mutex row, so the clique and the core want the same two
    /// weight-1 softs. Charging both would be an over-charge and would decline
    /// the whole derivation; charging preprocessing on the RESIDUAL means the
    /// clique simply finds nothing left and the core floor stands.
    ///
    /// Kill mutation (APPLIED, confirmed failing, reverted): in
    /// `derive_lower_bound`, build `residual` from `w` alone (drop the
    /// `- charged` term). The at-most-one layer then double-charges,
    /// `LbDeclined::OverCharged` fires, and the bound falls back below 1.
    #[test]
    fn preprocessing_is_charged_on_the_residual_and_cannot_cost_the_core_floor() {
        let dir = tempfile::tempdir().unwrap();
        let wcnf = write_fixture(dir.path(), "mix.wcnf", "h -1 -2 0\n1 1 0\n1 2 0\n");
        let model = vec![false, true, false];
        let mined = vec![PaidCore {
            hard_row: 1,
            w_min: 1,
            members: vec![1, 2],
        }];
        let out = emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            &model,
            1,
            &mined,
            &[],
            &streamer(),
        )
        .unwrap();
        assert!(
            out.lb_declined.is_none(),
            "preprocessing must not be able to decline the derivation: {:?}",
            out.lb_declined
        );
        assert_eq!(out.am1_layers_certified, 0, "no residual weight is left");
        assert_eq!(out.lower_bound, 1);
        let Some(checker) = veripb::require_checker(SUITE) else {
            return;
        };
        veripb::run(
            &checker,
            &dir.path().join("c.opb"),
            &dir.path().join("c.opb.pbp"),
            &["--opb"],
        )
        .assert_verified(&veripb::Expect::bounds("1", "1"), SUITE);
    }

    /// P1 runs BEFORE the at-most-one peel and zeroes what it claims. This is
    /// the p2d collision: `¬x1` is root-false (hard `(x1)`), so P1 wants its
    /// full weight 5 while the complementary pair wants only `min(3,5) = 3`.
    /// Charging both claims 8 against a weight-5 soft and is rejected outright.
    ///
    /// Kill mutation (APPLIED, confirmed failing, reverted): in
    /// `derive_lower_bound`, move the `plan_am1` block ABOVE the P1 loop. The
    /// pair is peeled first, P1 then finds only residual 2, and the bound reads
    /// 5 by a different route — but the CHEAPER route: `am1_layers_certified`
    /// becomes 1, which this test pins at 0.
    #[test]
    fn p1_wins_a_collision_with_the_at_most_one_peel() {
        let dir = tempfile::tempdir().unwrap();
        let wcnf = write_fixture(dir.path(), "p2d.wcnf", "h 1 0\n3 1 0\n5 -1 0\n");
        // x1 is forced true, so the weight-5 soft `(¬x1)` is paid.
        let model = vec![false, true];
        let out = emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            &model,
            5,
            &[],
            &[],
            &streamer(),
        )
        .unwrap();
        assert_eq!(out.p1_softs_certified, 1, "P1 claims the root-false soft");
        assert_eq!(
            out.am1_layers_certified, 0,
            "P1 zeroed the residual, so the pair has nothing to peel"
        );
        assert_eq!(out.lower_bound, 5, "P1's 5 beats the pair's 3");
        let Some(checker) = veripb::require_checker(SUITE) else {
            return;
        };
        veripb::run(
            &checker,
            &dir.path().join("c.opb"),
            &dir.path().join("c.opb.pbp"),
            &["--opb"],
        )
        .assert_verified(&veripb::Expect::bounds("5", "5"), SUITE);
    }

    /// A STAR is not a clique. `x1` excludes `x2` and `x3`, but `x2` and `x3`
    /// are compatible, so only ONE of the three must be paid — not two. The
    /// planner must not grow a clique through an unwitnessed pair, and if it
    /// ever did, `am1_layer_steps` refuses the layer rather than emitting a
    /// ladder the checker would throw the whole certificate out for.
    ///
    /// This is the `mut_not_a_clique` shape, and it is the one place where
    /// being wrong is not merely a weaker bound.
    ///
    /// Kill mutation (APPLIED, confirmed failing, reverted): in `plan_am1`,
    /// weaken the extension test from
    /// `graph.mutex(nodes[m].0, nodes[c].0).is_some()` to
    /// `nodes[m].0 != nodes[c].0`. The greedy then grows `{x1,x2,x3}`,
    /// `am1_layer_steps` finds no row for the `(x2,x3)` pair and drops the
    /// layer whole, and the bound falls from 1 to 0.
    #[test]
    fn a_star_is_not_a_clique_and_pays_only_one() {
        let dir = tempfile::tempdir().unwrap();
        let wcnf = write_fixture(
            dir.path(),
            "star.wcnf",
            "h -1 -2 0\nh -1 -3 0\n1 1 0\n1 2 0\n1 3 0\n",
        );
        // x1 false, x2 and x3 both true: exactly one soft is paid.
        let model = vec![false, false, true, true];
        let out = emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            &model,
            1,
            &[],
            &[],
            &streamer(),
        )
        .unwrap();
        assert_eq!(out.am1_layers_certified, 1, "one pair, not one triangle");
        assert_eq!(out.lower_bound, 1, "a star of 3 pays 1, not 2");
        let Some(checker) = veripb::require_checker(SUITE) else {
            return;
        };
        veripb::run(
            &checker,
            &dir.path().join("c.opb"),
            &dir.path().join("c.opb.pbp"),
            &["--opb"],
        )
        .assert_verified(&veripb::Expect::bounds("1", "1"), SUITE);
    }

    /// A preprocessing-only certificate proves nothing unless it can fail.
    /// These are the ways the derivation could be wrong; the checker must reject
    /// every one. The k=4 clique is the fixture because it is where the
    /// arithmetic is least forgiving.
    #[test]
    fn the_checker_rejects_a_tampered_preprocessing_certificate() {
        let Some(checker) = veripb::require_checker(SUITE) else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let wcnf = write_fixture(
            dir.path(),
            "k4.wcnf",
            "h -1 -2 0\nh -1 -3 0\nh -1 -4 0\nh -2 -3 0\nh -2 -4 0\nh -3 -4 0\n\
             1 1 0\n1 2 0\n1 3 0\n1 4 0\n",
        );
        let model = vec![false, true, false, false, false];
        emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            &model,
            3,
            &[],
            &[],
            &streamer(),
        )
        .unwrap();
        let opb = dir.path().join("c.opb");
        let good = fs::read_to_string(dir.path().join("c.opb.pbp")).unwrap();

        let mutations: &[(&str, &str, &str)] = &[
            // Claim `>= k` where the induction only gives `>= k - 1`.
            ("clique pays k not k-1", "BOUNDS 3 :", "BOUNDS 4 :"),
            // The emitter off-by-one: divide the last step by the wrong divisor.
            ("wrong ladder divisor", " 3 d ;", " 4 d ;"),
            // Lift against T_2 (id 11) instead of T_4 (id 13): a TRUE bound
            // from a row that does not entail it.
            ("conclusion points at T_2", "pol 13 1 * ;", "pol 11 1 * ;"),
            // Over-charge every member past its weight — the coefficient then
            // exceeds the objective's and the lift is impossible.
            (
                "member charged past its weight",
                "pol 13 1 * ;",
                "pol 13 2 * ;",
            ),
        ];
        for (name, from, to) in mutations {
            let tampered = good.replacen(from, to, 1);
            assert_ne!(
                tampered, good,
                "{SUITE}: mutation '{name}' did not apply — the test is vacuous\n{good}"
            );
            let path = dir.path().join(format!("m-{}.pbp", name.replace(' ', "-")));
            fs::write(&path, &tampered).unwrap();
            veripb::run(&checker, &opb, &path, &["--opb"])
                .assert_rejected(&format!("{SUITE}: mutation '{name}' must be rejected"));
        }
    }

    /// Root propagation is not optional: a unit hard clause is asserted before
    /// any core is tried, so a core that conflicts only against those units is
    /// still recognised. Without it such cores look non-RUP and are dropped.
    #[test]
    fn unit_hard_clauses_propagate_at_the_root() {
        let dir = tempfile::tempdir().unwrap();
        // `h -3` is a unit; assuming the softs x1,x2 propagates x3 and only
        // then conflicts with it.
        let wcnf = dir.path().join("u.wcnf");
        fs::write(&wcnf, "h -1 -2 3 0\nh -3 0\n1 1 0\n1 2 0\n").unwrap();
        let out = emit_certificate(
            &wcnf,
            &dir.path().join("c"),
            // Cost 1: falsify soft (x1); x3 must be false.
            &vec![false, false, true, false],
            1,
            &[],
            &[SatCore {
                w_min: 1,
                members: vec![1, 2],
            }],
            &streamer(),
        )
        .unwrap();
        assert_eq!(
            out.sat_cores_certified, 1,
            "a core refuted through a unit hard clause is RUP"
        );
        assert_eq!(out.lower_bound, 1);
    }
}
