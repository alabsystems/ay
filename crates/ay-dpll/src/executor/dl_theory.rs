// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DPLL(T) **difference-logic theory solver** and the `QF_RDL` route that drives
//! it.
//!
//! # Why
//!
//! `QF_RDL` is, in practice, 100% *pure* difference logic: every atom is
//! `x − y ⋈ c`, `x ⋈ c`, or `x ⋈ y`. Routing it through the general LRA simplex
//! pays a large constant per theory query and (measured) yields ~68k SAT
//! decisions against ~62 theory propagations. A dedicated
//! [`IncrementalDiffGraph`] answers each assert in time proportional to the part
//! of the constraint graph the new edge actually disturbs, and needs no work at
//! all to report `Sat` (its potential function *is* a model).
//!
//! # Structure
//!
//! * [`DiffLogicTheory`] — the `TheorySolver` implementation. Holds an
//!   `IncrementalDiffGraph<RStar>` (RDL ⇒ rationals + infinitesimal `ε`), maps
//!   `TermId` variables to graph vertices, and pre-registers **both** edges of
//!   every atom it sees (the one implied by asserting it TRUE and the one
//!   implied by asserting it FALSE).
//! * [`Executor::solve_rdl`] — the route. Taken only when *every* theory atom in
//!   the (preprocessed) problem is a recognised pure difference-logic atom;
//!   anything else falls straight through to the existing `solve_lra()` path.
//!
//! # Soundness posture (load-bearing)
//!
//! * **Fail closed, everywhere.** Atom recognition reuses the existing,
//!   well-tested [`super::diff_logic`] routines (`collect_comparison` /
//!   `linearize` / `try_atomic_leaf`). Any Boolean atom that carries arithmetic
//!   content but is not a pure DL atom marks the solver *unsupported* for the
//!   current scope, and `check()` then answers `Unknown` — never an
//!   approximation. Boolean-only atoms (`(= p q)` over `Bool`, plain Boolean
//!   variables, ITE guards) carry no arithmetic content and are ignored; the
//!   Tseitin encoder constrains them structurally.
//! * **No theory propagation.** `propagate()` returns `vec![]`. The potential
//!   vector returned by `IncrementalDiffGraph::model()` is a *feasible
//!   potential*, NOT a shortest-path distance matrix, so `π(x) − π(y) <= c` is
//!   necessary but **not sufficient** for entailment — testing it to decide an
//!   atom is implied would be unsound. Returning no propagations is always
//!   sound.
//! * **Conflicts are genuine negative cycles.** `assert_edge` returns the tags
//!   of the edges forming the cycle; we map them straight back to the
//!   `TheoryLit`s that activated them. The set is sound (the cycle really is
//!   infeasible) and, by construction, cycle-minimal.
//! * **SAT is re-validated.** The route clears `last_model_validated` so
//!   `check_sat` re-evaluates every ORIGINAL assertion against the extracted
//!   model; a spurious model degrades to `Unknown`, never a wrong SAT.
//! * **Unknown falls back.** If the theory ever answers `Unknown` (an
//!   unmodellable literal was asserted — today only a *negated* arithmetic
//!   equality, which is a disjunction rather than a difference constraint), the
//!   whole route hands the problem back to `solve_lra()`.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{TermData, TermStore};
use ay_core::{Sort, TermId, TheoryLit, TheoryPropagation, TheoryResult, TheorySolver};
use ay_diff_logic::atom::Op;
use ay_diff_logic::rstar::pick_delta_from_slacks;
use ay_diff_logic::DlWeight;
use ay_diff_logic::{AssertOutcome, DiffAtom, Entailment, IncrementalDiffGraph};
use num_rational::BigRational;

use super::diff_logic::{collect_comparison, negate_op, CollectedAtom};

/// Vertex reserved for the implicit zero variable `Z`, so the var-vs-const form
/// `x ⋈ c` can be modelled as `x − Z ⋈ c` exactly as
/// [`ay_diff_logic::atom`] expects.
///
/// The incremental engine never *pins* `π(Z)` (potentials only ever decrease),
/// so a concrete value for `x` is read off as `π(x) − π(Z)`. Every constraint is
/// a difference, so this shift is invisible to feasibility.
const ZERO_VERTEX: usize = 0;

/// The two graph edges of one registered atom: the constraint implied by
/// asserting it TRUE, and the constraint implied by asserting it FALSE.
struct AtomEdges {
    /// Edge ids to activate when the atom is asserted `true`.
    pos: Vec<usize>,
    /// Edge ids to activate when the atom is asserted `false`; `None` when the
    /// negation is not a conjunction of difference constraints (only case
    /// today: `not (x − y = c)`, which is the disjunction `< ∨ >`).
    neg: Option<Vec<usize>>,
}

/// Classification of a Boolean atom the DPLL layer may hand to this theory.
enum AtomKind {
    /// A pure difference-logic atom with its pre-registered edges.
    Dl(AtomEdges),
    /// Carries no arithmetic content (Boolean equality, Boolean variable, ITE
    /// guard, ...). Ignoring it is sound: the Tseitin encoding constrains it.
    Ignored,
    /// Arithmetic-bearing but NOT a pure difference-logic atom. Fail closed.
    Unsupported,
}

/// A conflict found during `assert_literal`, held until `check()` reports it.
struct PendingConflict {
    /// Scope depth at which the conflict was detected. Cleared by any `pop()`
    /// that unwinds below this depth (which retracts the asserting literal).
    level: usize,
    /// The asserted literals whose conjunction is infeasible.
    lits: Vec<TheoryLit>,
}

/// Difference-logic theory solver for DPLL(T).
///
/// See the module documentation for the soundness contract.
pub(crate) struct DiffLogicTheory<'a, W: DlWeight> {
    terms: &'a TermStore,
    /// The incremental Cotton–Maler engine over `ℚ[ε]`.
    graph: IncrementalDiffGraph<W>,
    /// `TermId` of an arithmetic variable → graph vertex (never [`ZERO_VERTEX`]).
    var_index: HashMap<TermId, usize>,
    /// Atom `TermId` → classification + registered edges. Purely structural (a
    /// function of the term shapes), so it deliberately survives `pop`/`reset`.
    atoms: HashMap<TermId, AtomKind>,
    /// Edge tag → the literal whose assertion activates it. Tags are indices
    /// into this vector; the two edges of an `=` share one tag.
    tag_lits: Vec<TheoryLit>,
    /// How many graph edges each tag owns. Only a tag owning EXACTLY ONE edge
    /// may be theory-propagated: an `=` atom activates two edges under one tag,
    /// and entailing one of them does not entail the equality.
    tag_edge_count: Vec<u32>,
    /// Entailments discovered during `assert_literal`, drained by `propagate`.
    pending_props: Vec<TheoryPropagation>,
    /// Vertices each propagation Dijkstra may settle. Tunable via
    /// `AY_RDL_PROP_BUDGET`; 0 disables theory propagation entirely.
    prop_budget: usize,
    /// INTEGER difference logic (QF_IDL) rather than the Real lane (QF_RDL).
    ///
    /// When set, difference variables must all be `Int` and every bound is
    /// integer-TIGHTENED before lowering (see [`tighten_int`]). That is what
    /// makes the lane both sound and integral: after tightening, every edge
    /// weight is an integer with a zero epsilon, so the shortest-path
    /// potentials are integers and the extracted model is integral. Lowering an
    /// Int atom through the rational table instead would only be a RELAXATION.
    int_mode: bool,
    /// Edge ids activated so far (mirrors the engine's own trail so model
    /// extraction can compute exact slacks). Duplicates are harmless.
    active_edges: Vec<usize>,
    /// `active_edges.len()` captured at each `push`.
    active_marks: Vec<usize>,
    /// Number of open scopes.
    scope_depth: usize,
    pending_conflict: Option<PendingConflict>,
    /// Scope depth at which an unmodellable literal was asserted, if any.
    ///
    /// The only such literal today is a NEGATED arithmetic equality:
    /// `not (x − y = c)` is the disjunction `x − y < c ∨ x − y > c`, which a
    /// conjunctive constraint graph cannot hold. `atom_is_routable` keeps
    /// equality-bearing problems out of this lane entirely, so reaching this is
    /// a backstop, not a routine path — and it fails closed to `Unknown`, never
    /// to a guessed disjunct.
    unsupported: Option<usize>,
}

impl<'a, W: DlWeight> DiffLogicTheory<'a, W> {
    /// A fresh solver over `terms` with only the implicit zero vertex.
    pub(crate) fn new(terms: &'a TermStore) -> Self {
        Self {
            terms,
            graph: IncrementalDiffGraph::new(1),
            var_index: HashMap::default(),
            atoms: HashMap::default(),
            tag_lits: Vec::new(),
            tag_edge_count: Vec::new(),
            pending_props: Vec::new(),
            prop_budget: prop_budget_from_env(),
            int_mode: false,
            active_edges: Vec::new(),
            active_marks: Vec::new(),
            scope_depth: 0,
            pending_conflict: None,
            unsupported: None,
        }
    }

    /// QF_IDL constructor: the same engine with integer-tightened lowering.
    ///
    /// Verified but NOT yet wired to a production route — hence the `allow`.
    /// The lowering (the soundness-critical half) is exercised by
    /// `dl_theory_tests::int_lane_*` and `int_tighten_tests::*`. What remains is
    /// plumbing, and it is deliberately not half-done: a `solve_idl` mirroring
    /// `solve_rdl` must fall through to `solve_lia` (NOT `solve_lra`, which
    /// would silently reintroduce the real relaxation this lane exists to
    /// avoid) and must place the extracted model in `TheoryModels::lia` rather
    /// than `lra`, which needs an `LraModel` -> `LiaModel` conversion. Gate it
    /// behind a flag like `--dpll-no-rdl-engine` and run a full-division
    /// differential before default-on. See the development design notes §3a2.
    pub(crate) fn new_int(terms: &'a TermStore) -> Self {
        let mut this = Self::new(terms);
        this.int_mode = true;
        this
    }

    /// Graph vertex for an arithmetic variable term, interning on first use.
    fn vertex(&mut self, term: TermId) -> usize {
        if let Some(&v) = self.var_index.get(&term) {
            return v;
        }
        // Vertex 0 is reserved for `Z`, so dense indices start at 1.
        let v = self.var_index.len() + 1;
        self.var_index.insert(term, v);
        self.graph.ensure_var(v);
        v
    }

    /// Register the edges implied by `atom` under operator `op`, tagged with a
    /// fresh tag bound to `lit`. `None` when the operator has no
    /// conjunction-of-differences form (never happens: every `Op` lowers).
    fn register_polarity(
        &mut self,
        atom: &CollectedAtom,
        op: Op,
        c: &BigRational,
        lit: TheoryLit,
    ) -> Option<Vec<usize>> {
        let x = self.vertex(atom.lhs);
        let y = atom.rhs.map(|r| self.vertex(r));
        let diff = match y {
            Some(y) => DiffAtom::diff(x, y, op, c.clone()),
            None => DiffAtom::var_const(x, op, c.clone()),
        };
        let constraints = W::lower(&diff, ZERO_VERTEX)?;
        let tag = u64::try_from(self.tag_lits.len()).ok()?;
        self.tag_lits.push(lit);
        self.tag_edge_count.push(0);
        let ids: Vec<usize> = constraints
            .into_iter()
            .map(|c| self.graph.register_edge(c.from, c.to, c.weight, tag))
            .collect();
        if let Some(slot) = self.tag_edge_count.last_mut() {
            *slot = u32::try_from(ids.len()).unwrap_or(u32::MAX);
        }
        Some(ids)
    }

    /// Classify `term` (and register its edges when it is a DL atom), caching
    /// the outcome. Never raises the fail-closed flag: classification is a pure
    /// function of the term, and an atom that is never *asserted* costs nothing.
    fn classify(&mut self, term: TermId) {
        if self.atoms.contains_key(&term) {
            return;
        }
        let kind = self.build_atom(term);
        self.atoms.insert(term, kind);
    }

    fn build_atom(&mut self, term: TermId) -> AtomKind {
        let Some(atom) = collect_comparison(self.terms, term) else {
            // Not a recognised comparison. Boolean-only atoms are safely
            // ignored; anything arithmetic-bearing must fail closed.
            return if atom_touches_arithmetic(self.terms, term) {
                AtomKind::Unsupported
            } else {
                AtomKind::Ignored
            };
        };

        // Sort gate. QF_RDL requires every difference variable to be Real;
        // QF_IDL (`int_mode`) requires every one to be Int. NEVER mixed, and
        // never Int through the rational lowering — that is only a relaxation,
        // which is why the Real lane still refuses Int outright.
        let want = if self.int_mode { Sort::Int } else { Sort::Real };
        for v in std::iter::once(atom.lhs).chain(atom.rhs) {
            if *self.terms.sort(v) != want {
                return AtomKind::Unsupported;
            }
        }
        // Over Int a non-integral equality bound is simply unsatisfiable. It is
        // representable only as a contradiction, so refuse rather than encode a
        // bound that is not equivalent to it.
        if self.int_mode && matches!(atom.op, Op::Eq) && !atom.c.is_integer() {
            return AtomKind::Unsupported;
        }

        let pos_lit = TheoryLit::new(term, true);
        let (pos_op, pos_c) = if self.int_mode {
            tighten_int(atom.op, &atom.c)
        } else {
            (atom.op, atom.c.clone())
        };
        let Some(pos) = self.register_polarity(&atom, pos_op, &pos_c, pos_lit) else {
            return AtomKind::Unsupported;
        };

        // NEGATION. Derived from the exact RDL table in `ay_diff_logic::atom`,
        // not guessed:
        //   not (x−y <= c)  ⇔  x−y >  c  ⇒  y−x <= −c − ε   weight (−c, −1)
        //   not (x−y <  c)  ⇔  x−y >= c  ⇒  y−x <= −c       weight (−c,  0)
        //   not (x−y >= c)  ⇔  x−y <  c  ⇒  x−y <= c  − ε   weight ( c, −1)
        //   not (x−y >  c)  ⇔  x−y <= c  ⇒  x−y <= c        weight ( c,  0)
        //   not (x−y  = c)  ⇔  x−y != c  — a DISJUNCTION, not representable.
        // `negate_op` maps Le↔Gt and Lt↔Ge exactly, and `lower_rational_atom`
        // applies the table above, so composing them is the derivation.
        let neg = if matches!(atom.op, Op::Eq) {
            None
        } else {
            let neg_lit = TheoryLit::new(term, false);
            // Tighten the NEGATED operator against the ORIGINAL constant.
            // `negate_op` maps Le↔Gt and Lt↔Ge, so the negation is strict again
            // exactly when the positive form was not — tightening only the
            // positive polarity would leave the negative one as a relaxation
            // and admit models the atom forbids.
            //   ¬(x−y < c) ⇔ x−y ≥ c → ≥ ceil(c)
            //   ¬(x−y ≤ c) ⇔ x−y > c → ≥ floor(c)+1
            let (neg_op, neg_c) = if self.int_mode {
                tighten_int(negate_op(atom.op), &atom.c)
            } else {
                (negate_op(atom.op), atom.c.clone())
            };
            match self.register_polarity(&atom, neg_op, &neg_c, neg_lit) {
                Some(edges) => Some(edges),
                None => return AtomKind::Unsupported,
            }
        };

        AtomKind::Dl(AtomEdges { pos, neg })
    }

    /// Test-only: how this solver classified `term`.
    #[cfg(test)]
    pub(crate) fn debug_kind(&mut self, term: TermId) -> &'static str {
        let (term, _) = strip_negations(self.terms, term, true);
        self.classify(term);
        match self.atoms.get(&term) {
            Some(AtomKind::Dl(_)) => "dl",
            Some(AtomKind::Ignored) => "ignored",
            Some(AtomKind::Unsupported) => "unsupported",
            None => "missing",
        }
    }

    /// Test-only: the `(from, to, weight)` graph edges the literal
    /// `(term, value)` would activate, or `None` when that polarity is refused
    /// (today only `not (x − y = c)`, a disjunction).
    ///
    /// This is what pins the RDL lowering table: the edge `from → to : (q, eps)`
    /// means `π(to) − π(from) <= q + eps·ε`.
    #[cfg(test)]
    pub(crate) fn debug_edges(
        &mut self,
        term: TermId,
        value: bool,
    ) -> Option<Vec<(usize, usize, BigRational, i64)>> {
        let (term, value) = strip_negations(self.terms, term, value);
        self.classify(term);
        let ids = match self.atoms.get(&term)? {
            AtomKind::Dl(e) => {
                if value {
                    e.pos.clone()
                } else {
                    e.neg.clone()?
                }
            }
            _ => return None,
        };
        let edges = self.graph.edges();
        Some(
            ids.iter()
                .map(|&i| {
                    let e = &edges[i];
                    // `parts()` is the weight-generic spelling of the old
                    // `RStar` field access (`.q` / `.eps`): it works for the
                    // `IStar` lane too, which has no such fields.
                    let (q, eps) = e.weight.parts();
                    (e.from, e.to, q, eps)
                })
                .collect(),
        )
    }

    /// Test-only: graph vertex interned for an arithmetic variable term.
    #[cfg(test)]
    pub(crate) fn debug_vertex(&self, term: TermId) -> Option<usize> {
        self.var_index.get(&term).copied()
    }

    /// Test-only: the reserved implicit-zero vertex.
    #[cfg(test)]
    pub(crate) const fn debug_zero_vertex() -> usize {
        ZERO_VERTEX
    }

    /// Turn engine entailments into DPLL theory propagations.
    ///
    /// Sound by construction on the engine's side: `entailed_after_assert`
    /// exhibits a concrete path no longer than the atom's own bound, so
    /// `AND(reason) |= atom`. Two adapter-side guards complete the contract:
    ///
    /// * only a tag owning EXACTLY ONE edge is propagated. An `=` atom registers
    ///   two edges under a single tag, and entailing one of them says nothing
    ///   about the equality;
    /// * the propagated literal is never allowed to appear in its own reason,
    ///   which would make the learned clause a tautology.
    fn collect_entailments(&mut self, edge_id: usize) {
        if self.prop_budget == 0 || self.pending_conflict.is_some() {
            return;
        }
        let found = self.graph.entailed_after_assert(edge_id, self.prop_budget);
        if found.is_empty() {
            return;
        }
        for Entailment { edge_id, reason } in found {
            let Some(edge) = self.graph.edges().get(edge_id) else {
                continue;
            };
            let tag = edge.tag;
            let Ok(idx) = usize::try_from(tag) else {
                continue;
            };
            // Only single-edge tags may be propagated (see the doc above).
            if self.tag_edge_count.get(idx).copied() != Some(1) {
                continue;
            }
            let Some(&lit) = self.tag_lits.get(idx) else {
                continue;
            };
            let mut seen: HashSet<TheoryLit> = HashSet::default();
            let mut reason_lits: Vec<TheoryLit> = Vec::with_capacity(reason.len());
            let mut usable = true;
            for &rtag in &reason {
                let Ok(ridx) = usize::try_from(rtag) else {
                    usable = false;
                    break;
                };
                let Some(&rlit) = self.tag_lits.get(ridx) else {
                    usable = false;
                    break;
                };
                if rlit == lit {
                    // Self-justifying: drop the whole propagation.
                    usable = false;
                    break;
                }
                if seen.insert(rlit) {
                    reason_lits.push(rlit);
                }
            }
            if !usable || reason_lits.is_empty() {
                continue;
            }
            self.pending_props
                .push(TheoryPropagation::eager(lit, reason_lits));
        }
    }

    /// Mark the solver unusable for the current scope (fail closed).
    fn raise_unsupported(&mut self) {
        if self.unsupported.is_none() {
            self.unsupported = Some(self.scope_depth);
        }
    }

    /// Translate engine conflict tags back into asserted literals.
    fn record_conflict(&mut self, tags: &[u64]) {
        if self.pending_conflict.is_some() {
            // Keep the first conflict: it is still valid (its edges stay active
            // for as long as this scope lives) and re-deriving buys nothing.
            return;
        }
        let mut seen: HashSet<TheoryLit> = HashSet::default();
        let mut lits: Vec<TheoryLit> = Vec::with_capacity(tags.len());
        for &tag in tags {
            let Ok(idx) = usize::try_from(tag) else {
                self.raise_unsupported();
                return;
            };
            let Some(&lit) = self.tag_lits.get(idx) else {
                // Unmapped tag: impossible by construction, but never assume.
                self.raise_unsupported();
                return;
            };
            if seen.insert(lit) {
                lits.push(lit);
            }
        }
        if lits.is_empty() {
            // A conflict must name at least one literal; an empty explanation
            // would become an empty (unconditional) blocking clause.
            self.raise_unsupported();
            return;
        }
        self.pending_conflict = Some(PendingConflict {
            level: self.scope_depth,
            lits,
        });
    }

    /// No-op required by the split-loop pipeline: difference logic learns no
    /// cuts (that is a LIA branch-and-bound concept).
    pub(crate) fn replay_learned_cuts(&mut self) {}

    /// Override the per-Dijkstra propagation budget.
    ///
    /// Tests only: the production value comes from a process-wide `OnceLock`
    /// over `AY_RDL_PROP_BUDGET`, which cannot be varied per test, and the
    /// rollback contract for `pending_props` is unobservable at budget 0.
    #[cfg(test)]
    pub(crate) fn set_prop_budget_for_test(&mut self, budget: usize) {
        self.prop_budget = budget;
    }

    /// Extract a concrete rational model from the current feasible potential.
    ///
    /// The potentials live in `ℚ[ε]`; a single positive `δ` smaller than every
    /// active constraint's slack margin realises them as plain rationals with
    /// every strict constraint still strict (see
    /// [`ay_diff_logic::rstar::pick_delta_from_slacks`]).
    pub(crate) fn extract_model(&self) -> ay_lra::LraModel {
        let pot = self.graph.model();
        let edges = self.graph.edges();
        let mut slacks: Vec<(BigRational, i64)> = Vec::with_capacity(self.active_edges.len());
        for &id in &self.active_edges {
            let Some(e) = edges.get(id) else { continue };
            let (Some(from), Some(to)) = (pot.get(e.from), pot.get(e.to)) else {
                continue;
            };
            let slack = from.add(&e.weight).add(&to.negate());
            slacks.push(slack.parts());
        }
        let delta = pick_delta_from_slacks(&slacks);

        let base = pot.get(ZERO_VERTEX).cloned().unwrap_or_else(W::zero);
        let mut values: HashMap<TermId, BigRational> = HashMap::default();
        for (&term, &v) in &self.var_index {
            let Some(p) = pot.get(v) else { continue };
            values.insert(term, p.add(&base.negate()).realize(&delta));
        }
        ay_lra::LraModel { values }
    }
}

impl<W: DlWeight> TheorySolver for DiffLogicTheory<'_, W> {
    /// Pre-parse and pre-register an atom. Purely a warm-up: it never changes
    /// the verdict, because an unasserted atom's edges stay inactive.
    fn register_atom(&mut self, atom: TermId) {
        self.classify(atom);
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        // The DPLL layer may hand us a `not`-wrapped literal; normalise so the
        // atom key is the bare comparison.
        let (term, value) = strip_negations(self.terms, literal, value);
        self.classify(term);

        let edges = match self.atoms.get(&term) {
            Some(AtomKind::Ignored) => return,
            Some(AtomKind::Dl(e)) => {
                if value {
                    e.pos.clone()
                } else {
                    match &e.neg {
                        Some(n) => n.clone(),
                        // `not (x − y = c)` is a DISJUNCTION. Ask DPLL to case
                        // split it rather than failing closed; both disjuncts
                        // are representable once the SAT layer commits to one.
                        // `not (x − y = c)` is the disjunction `< ∨ >`, which a
                        // conjunctive graph cannot hold. FAIL CLOSED — never pick
                        // a disjunct, never drop the constraint. Consistent with
                        // `atom_is_routable`, which keeps equality-bearing
                        // problems out of this lane in the first place, so this
                        // is a backstop rather than a routine path.
                        None => {
                            self.raise_unsupported();
                            return;
                        }
                    }
                }
            }
            // `Unsupported`, or (impossible) a missing entry: fail closed.
            _ => {
                self.raise_unsupported();
                return;
            }
        };

        for id in edges {
            match self.graph.assert_edge(id) {
                AssertOutcome::Consistent => {
                    self.active_edges.push(id);
                    self.collect_entailments(id);
                }
                AssertOutcome::Conflict(tags) => {
                    self.record_conflict(&tags);
                    return;
                }
            }
        }
    }

    fn check(&mut self) -> TheoryResult {
        // A CONFLICT OUTRANKS A REFUSAL, and the order is load-bearing.
        //
        // The conflict is a negative cycle among ACTIVE edges only, so it is
        // derived from a subset of the genuinely asserted constraints. Dropping
        // some other literal as unmodellable cannot invalidate it — a subset of
        // an infeasible set is still infeasible — so reporting `Unsat` here is
        // sound even while `unsupported` is set, and it is strictly better than
        // discarding a completed refutation and re-deriving it in simplex.
        if let Some(pc) = &self.pending_conflict {
            return TheoryResult::Unsat(pc.lits.clone());
        }
        if self.unsupported.is_some() {
            // An asserted literal could not be modelled and no conflict was
            // found, so nothing can be concluded. Honest `Unknown`; the route
            // then falls back to the general simplex path.
            return TheoryResult::Unknown;
        }
        // The engine's potential function is feasible for every active edge, so
        // feasibility needs no extra work: it IS the model.
        TheoryResult::Sat
    }

    /// Entailments found by the engine's shortest-path propagation, gathered
    /// during `assert_literal`.
    ///
    /// Note what is NOT done here: the potential vector is a feasible potential,
    /// not a shortest-path distance, so no entailment may be read off `model()`.
    /// These propagations come from
    /// [`IncrementalDiffGraph::entailed_after_assert`], which computes real
    /// distances and exhibits a concrete justifying path.
    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        std::mem::take(&mut self.pending_props)
    }

    fn push(&mut self) {
        self.graph.push();
        self.active_marks.push(self.active_edges.len());
        self.scope_depth += 1;
    }

    fn pop(&mut self) {
        // An unmatched `pop()` is a NO-OP (trait contract). Nothing may be
        // discarded here: at depth 0 no assertion is being retracted, so a
        // pending split request is still owed to the DPLL layer and dropping it
        // would silently lose the disequality it stands for.
        if self.scope_depth == 0 {
            debug_assert_eq!(self.graph.level(), 0, "graph scope out of sync at depth 0");
            return;
        }
        self.scope_depth -= 1;
        self.graph.pop();
        debug_assert_eq!(
            self.graph.level(),
            self.scope_depth,
            "graph scope out of sync with theory scope"
        );
        if let Some(mark) = self.active_marks.pop() {
            self.active_edges.truncate(mark);
        }
        // Derived state from the popped scope must not leak: a conflict, a split
        // request, or a fail-closed mark raised at a depth we have now unwound
        // below was caused by a literal that this pop just retracted.
        //
        // The test is `level > scope_depth`, NOT unconditional clearing: a
        // record raised at a depth that SURVIVES this pop describes a literal
        // that is still asserted, and the DPLL layer never re-notifies a
        // surviving assignment.
        if self
            .pending_conflict
            .as_ref()
            .is_some_and(|pc| pc.level > self.scope_depth)
        {
            self.pending_conflict = None;
        }
        if self.unsupported.is_some_and(|lvl| lvl > self.scope_depth) {
            self.unsupported = None;
        }
        // Propagations are pure derived state; dropping one only costs pruning,
        // so they are cleared wholesale rather than level-tracked.
        self.pending_props.clear();
    }

    fn reset(&mut self) {
        self.graph.clear_assertions();
        self.active_edges.clear();
        self.active_marks.clear();
        self.scope_depth = 0;
        self.pending_conflict = None;
        self.unsupported = None;
        // Derived, assertion-dependent state. `reset` is the strongest retraction
        // there is (the eager extension calls it through `soft_reset` on every
        // SAT restart), so every buffer keyed to the OLD assertion set must go:
        // a surviving propagation would justify a literal with reasons that are
        // no longer assigned, and a surviving split request would fire against a
        // disequality the new search has not asserted.
        self.pending_props.clear();
        // `atoms` / `var_index` / `tag_lits` are structural caches keyed by term
        // shape, not by the assertion set, and every registered edge is now
        // inactive (constraining nothing), so they are retained.
    }
}

/// Strip any `not` wrappers, flipping the asserted polarity each time.
fn strip_negations(terms: &TermStore, mut term: TermId, mut value: bool) -> (TermId, bool) {
    while let TermData::Not(inner) = terms.get(term) {
        term = *inner;
        value = !value;
    }
    (term, value)
}

/// Per-Dijkstra vertex budget for theory propagation (`AY_RDL_PROP_BUDGET`).
///
/// Propagation costs two Dijkstras per assert, so the budget trades search
/// pruning against theory time. Only SETTLED distances are used, so a smaller
/// budget loses propagations but can never produce an unsound one. `0` disables
/// propagation entirely.
fn prop_budget_from_env() -> usize {
    static V: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *V.get_or_init(|| {
        // Default OFF. Measured on the QF_RDL corpus, propagation at budget
        // 256 costs far more than the search it prunes: on tempo-depth-4 it
        // turned a 13.4s `sat` into a 27s timeout. The machinery is sound;
        // B25: re-arm by editing this constant for an experiment.
        0
    })
}

/// Does this Boolean atom carry ARITHMETIC content?
///
/// Used to decide between "safely ignorable Boolean atom" and "fail closed".
/// An application with an `Int`/`Real` argument is arithmetic-bearing; a
/// Boolean equality, Boolean variable or Boolean ITE is not.
fn atom_touches_arithmetic(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::App(_, args) => args
            .iter()
            .any(|&a| matches!(terms.sort(a), Sort::Int | Sort::Real)),
        _ => false,
    }
}

/// Would [`DiffLogicTheory`] be able to model this atom in BOTH polarities?
///
/// This is the routing gate: the `solve_rdl` lane is taken only when it holds
/// for every theory atom reachable from the assertions.
/// Integer-tightened lowering of a difference bound.
///
/// Over the integers every bound has an EXACT non-strict equivalent, and a
/// non-integral bound tightens to its floor/ceil:
///
/// ```text
///   x − y ≤ c  ⇔  x − y ≤ floor(c)
///   x − y < c  ⇔  x − y ≤ ceil(c) − 1
///   x − y ≥ c  ⇔  x − y ≥ ceil(c)
///   x − y > c  ⇔  x − y ≥ floor(c) + 1
/// ```
///
/// This is an EQUIVALENCE over Int, not a relaxation, which is what makes the
/// integer lane sound. Applying it BEFORE the weight lowering is also what
/// makes the model integral: afterwards every edge weight is an integer with a
/// zero epsilon coefficient, so the engine's shortest-path potentials are
/// integers and the extracted assignment needs no rounding.
///
/// Lowering an Int atom straight through the rational table instead yields
/// `≤ c − ε`, which is only a RELAXATION of `≤ c − 1` — that is precisely why
/// `build_atom` refused Int before this lane existed, and why relabelling a
/// QF_IDL file to `QF_RDL` turns a derivable `unsat` into `unknown`.
///
/// `Eq` is returned unchanged: an integral `c` is already exact, and a
/// non-integral one is handled by the caller (the atom is unsatisfiable over
/// Int and is refused rather than approximated).
fn tighten_int(op: Op, c: &BigRational) -> (Op, BigRational) {
    match op {
        Op::Le => (Op::Le, c.floor()),
        Op::Lt => (Op::Le, c.ceil() - BigRational::from_integer(1.into())),
        Op::Ge => (Op::Ge, c.ceil()),
        Op::Gt => (Op::Ge, c.floor() + BigRational::from_integer(1.into())),
        Op::Eq => (Op::Eq, c.clone()),
    }
}

pub(super) fn atom_is_routable(terms: &TermStore, term: TermId) -> bool {
    let Some(atom) = collect_comparison(terms, term) else {
        return !atom_touches_arithmetic(terms, term);
    };
    // An arithmetic EQUALITY disqualifies the whole problem from this lane.
    //
    // Asserting `x − y = c` TRUE is two difference constraints and is fine; it
    // is the NEGATION that a conjunctive constraint graph cannot hold, because
    // `x − y != c` is the disjunction `< ∨ >`. The theory can ask DPLL to case
    // split that, but the split machinery does not converge on these instances,
    // so the lane ends up answering `Unknown` and handing the problem to
    // `solve_lra` anyway — after having spent a large share of the time budget.
    //
    // Deciding it UP FRONT is strictly better: the `sal` and `skdmxa2` families
    // (92 of 255 instances, every one of which contains equalities) go straight
    // to the simplex lane with their full budget intact, instead of paying for a
    // DL attempt that cannot finish. The equality-free families — `scheduling`
    // and `SMT-Temporal-Planning`, 157 instances — are unaffected and keep the
    // fast lane.
    if matches!(atom.op, Op::Eq) {
        return false;
    }
    // Real-only (QF_RDL): an Int variable would need integer-tightened lowering
    // (`< c` ⇒ `<= c−1`), and the rational lowering is only a relaxation of it,
    // so refuse rather than approximate. The integer lane is
    // [`atom_is_routable_int`].
    std::iter::once(atom.lhs)
        .chain(atom.rhs)
        .all(|v| matches!(terms.sort(v), Sort::Real))
}

/// QF_IDL analogue of [`atom_is_routable`]: identical structural conditions,
/// but every difference variable must be `Int` rather than `Real`.
///
/// The `Op::Eq` refusal is shared and load-bearing for the same reason — the
/// NEGATION of an arithmetic equality is a disjunction a conjunctive constraint
/// graph cannot hold. Kept as a separate function rather than a `Sort`
/// parameter so the Real lane's behaviour is provably untouched by this lane.
pub(super) fn atom_is_routable_int(terms: &TermStore, term: TermId) -> bool {
    let Some(atom) = collect_comparison(terms, term) else {
        return !atom_touches_arithmetic(terms, term);
    };
    if matches!(atom.op, Op::Eq) {
        return false;
    }
    std::iter::once(atom.lhs)
        .chain(atom.rhs)
        .all(|v| matches!(terms.sort(v), Sort::Int))
}

#[cfg(test)]
mod int_tighten_tests {
    use super::{tighten_int, Op};
    use num_rational::BigRational;

    fn r(n: i64, d: i64) -> BigRational {
        BigRational::new(n.into(), d.into())
    }
    fn i(n: i64) -> BigRational {
        BigRational::from_integer(n.into())
    }

    /// Integral bounds: only the STRICT operators move, and they move by
    /// exactly one. `≤ 3` and `≥ 3` are already exact over Int.
    #[test]
    fn integral_bounds_tighten_strict_by_one() {
        assert_eq!(tighten_int(Op::Le, &i(3)), (Op::Le, i(3)));
        assert_eq!(tighten_int(Op::Lt, &i(3)), (Op::Le, i(2)));
        assert_eq!(tighten_int(Op::Ge, &i(3)), (Op::Ge, i(3)));
        assert_eq!(tighten_int(Op::Gt, &i(3)), (Op::Ge, i(4)));
    }

    /// Non-integral bounds collapse to the nearest integer INSIDE the feasible
    /// region. `x−y ≤ 7/2` over Int is `≤ 3`; `x−y ≥ 7/2` is `≥ 4`.
    #[test]
    fn fractional_bounds_collapse_inward() {
        assert_eq!(tighten_int(Op::Le, &r(7, 2)), (Op::Le, i(3)));
        assert_eq!(tighten_int(Op::Lt, &r(7, 2)), (Op::Le, i(3)));
        assert_eq!(tighten_int(Op::Ge, &r(7, 2)), (Op::Ge, i(4)));
        assert_eq!(tighten_int(Op::Gt, &r(7, 2)), (Op::Ge, i(4)));
    }

    /// Negatives must use floor/ceil, not truncation — the classic sign bug.
    /// `x−y < −5/2` over Int is `≤ −3`, NOT `≤ −2`.
    #[test]
    fn negative_bounds_use_floor_ceil_not_truncation() {
        assert_eq!(tighten_int(Op::Lt, &r(-5, 2)), (Op::Le, i(-3)));
        assert_eq!(tighten_int(Op::Le, &r(-5, 2)), (Op::Le, i(-3)));
        assert_eq!(tighten_int(Op::Gt, &r(-5, 2)), (Op::Ge, i(-2)));
        assert_eq!(tighten_int(Op::Ge, &r(-5, 2)), (Op::Ge, i(-2)));
    }

    /// The result is always NON-STRICT, which is the property the lowering
    /// relies on: afterwards every edge weight is an integer with a zero
    /// epsilon, so the engine's potentials — and the model — are integral.
    #[test]
    fn output_is_always_non_strict() {
        for op in [Op::Le, Op::Lt, Op::Ge, Op::Gt] {
            for c in [i(0), i(7), i(-7), r(1, 3), r(-1, 3)] {
                let (o, k) = tighten_int(op, &c);
                assert!(matches!(o, Op::Le | Op::Ge), "{op:?} {c} -> {o:?}");
                assert!(k.is_integer(), "{op:?} {c} -> non-integral {k}");
            }
        }
    }

    /// Tightening a bound and tightening its NEGATION must partition the
    /// integers exactly — no integer satisfies both, and none satisfies
    /// neither. This is what makes registering both polarities sound.
    #[test]
    fn positive_and_negated_tightenings_partition_the_integers() {
        let negate = |op: Op| match op {
            Op::Le => Op::Gt,
            Op::Gt => Op::Le,
            Op::Lt => Op::Ge,
            Op::Ge => Op::Lt,
            Op::Eq => Op::Eq,
        };
        let holds = |op: Op, k: &BigRational, v: i64| {
            let v = BigRational::from_integer(v.into());
            match op {
                Op::Le => v <= *k,
                Op::Ge => v >= *k,
                _ => unreachable!("tightened output is non-strict"),
            }
        };
        for op in [Op::Le, Op::Lt, Op::Ge, Op::Gt] {
            for c in [i(0), i(3), i(-3), r(7, 2), r(-5, 2)] {
                let (po, pk) = tighten_int(op, &c);
                let (no, nk) = tighten_int(negate(op), &c);
                for v in -6..=6 {
                    let p = holds(po, &pk, v);
                    let n = holds(no, &nk, v);
                    assert!(p != n, "{op:?} {c} at {v}: pos={p} neg={n} must differ");
                }
            }
        }
    }
}
