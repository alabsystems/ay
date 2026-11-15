// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Difference logic: the arithmetic plug-in's sub-module for checks whose
//! every arithmetic atom is `x − y ⋈ c` or `x ⋈ c` (design §2 "Arith
//! (LRA/LIA/DL)"; §10.4 stage 3; roadmap AL).
//!
//! The engine is `ay-diff-logic`'s [`IncrementalDiffGraph`] (Cotton–Maler):
//! asserting an edge keeps a feasible potential incrementally, a negative
//! cycle is the conflict and its edges are the explanation, and a feasible
//! potential is the model, so the final check has nothing left to do.
//! Theory propagation is the graph's relevant-set entailment after each
//! consistent assert: an unassigned atom whose edge a concrete path of
//! asserted edges already bounds is propagated with that path as its reason.
//!
//! Integer checks tighten every bound before lowering (`x − y < c` is
//! `x − y ≤ c − 1` over Int), which is an equivalence, keeps every edge
//! weight integral and so makes the potential an integral model: integer
//! difference logic needs no branch and bound.
//!
//! An equality atom `a = b` never reaches the graph. Its negation is a
//! disjunction no conjunctive graph can hold, so the plug-in mints `a ≤ b`
//! and `b ≤ a` and defines the equality by them, in the search, with the
//! three clauses `¬e ∨ a≤b`, `¬e ∨ b≤a`, `e ∨ ¬a≤b ∨ ¬b≤a` (K4: T-valid; K5:
//! `Definitional`, because the plug-in relies on them and never re-derives
//! them).

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{AtomHandle, Effort, TermId, TermStore, TheoryLemmaKind, TheoryLit};
use ay_diff_logic::{AssertOutcome, DiffAtom, DlWeight, Entailment, IncrementalDiffGraph, Op};
use num_rational::BigRational;
use num_traits::One;

use crate::dl_shape::{diff_shape, negate, tighten_int, DiffShape};
use crate::linear::Linearizer;
use crate::plugin::{
    Conflict, Ctx, Explanation, Final, GiveUp, Justification, ProofHint, ThVar, TheoryPlugin,
};
use crate::shared::SharedTerms;

mod clauses;

/// Vertex of the implicit zero variable `Z`: `x ⋈ c` is `x − Z ⋈ c`.
const ZERO_VERTEX: usize = 0;

/// Vertices each propagation Dijkstra may settle: the lane's budget
/// (`executor/dl_theory.rs`, `PROP_BUDGET`). Only settled distances are used,
/// so a cut-short search loses propagations and never makes a wrong one.
const PROP_BUDGET: usize = 256;

#[derive(Debug, Clone, Copy)]
enum DlAtom {
    /// An inequality: the edge its truth activates and the edge its
    /// falsity activates.
    Ineq { pos: usize, neg: usize },
    /// A comparison of constants.
    Ground(bool),
    /// An equality, carried by its definitions.
    Defined,
}

/// The difference-logic plug-in, over reals (`ℚ[ε]` weights) or integers
/// (tightened integral weights).
pub struct DlPlugin<W: DlWeight> {
    integer: bool,
    graph: IncrementalDiffGraph<W>,
    vertex_of: HashMap<TermId, usize>,
    vertex_terms: Vec<Option<TermId>>,
    /// Each atom with its term, by handle (KC3: the handle is the index).
    atoms: Vec<(TermId, DlAtom)>,
    /// The handle of each internalized atom (internalization only).
    handles: HashMap<TermId, AtomHandle>,
    /// The literal whose assertion activates each edge (index: edge id, which
    /// is also the edge's tag in the graph).
    edge_lit: Vec<TheoryLit>,
    /// The other polarity's edge of the same atom.
    twin: Vec<usize>,
    /// `Some(depth)` while the edge's literal has been propagated at a scope
    /// depth still open: the edge is then entailed by the active edges, so
    /// asserting it cannot shorten a path (no propagation round) and it is
    /// not propagated twice (the lane's `propagated_level` invariant).
    propagated: Vec<Option<usize>>,
    propagated_trail: Vec<usize>,
    propagated_marks: Vec<usize>,
    active_edges: Vec<usize>,
    active_marks: Vec<usize>,
    depth: usize,
    lin: Linearizer,
    model: HashMap<TermId, BigRational>,
    /// Terms the hub shares with this plug-in (design H1); each is a leaf
    /// plus a constant (`dl_shape::shared_fits`), so it has a vertex.
    shared: SharedTerms,
}

impl<W: DlWeight> DlPlugin<W> {
    /// An empty graph; `integer` selects integer tightening.
    pub fn new(integer: bool) -> Self {
        Self {
            integer,
            graph: IncrementalDiffGraph::new(1),
            vertex_of: HashMap::default(),
            vertex_terms: vec![None],
            atoms: Vec::new(),
            handles: HashMap::default(),
            edge_lit: Vec::new(),
            twin: Vec::new(),
            propagated: Vec::new(),
            propagated_trail: Vec::new(),
            propagated_marks: Vec::new(),
            active_edges: Vec::new(),
            active_marks: Vec::new(),
            depth: 0,
            lin: Linearizer::default(),
            model: HashMap::default(),
            shared: SharedTerms::default(),
        }
    }

    /// The value of a term in the kept model: its vertex's, or its linear
    /// form's over vertices (a shared `x + c`).
    fn value_of(&mut self, terms: &TermStore, term: TermId) -> Option<BigRational> {
        if let Some(value) = self.model.get(&term) {
            return Some(value.clone());
        }
        let form = self.lin.linearize(terms, term).ok()?;
        let mut value = form.constant.clone();
        for (leaf, coeff) in &form.coeffs {
            value += coeff * self.model.get(leaf)?;
        }
        Some(value)
    }

    fn vertex(&mut self, term: TermId) -> usize {
        if let Some(&v) = self.vertex_of.get(&term) {
            return v;
        }
        let v = self.vertex_terms.len();
        self.vertex_terms.push(Some(term));
        self.vertex_of.insert(term, v);
        self.graph.ensure_var(v);
        v
    }

    /// Register the single edge of `x − y ⋈ c` (never `=`) for `lit`.
    fn register_edge(
        &mut self,
        x: TermId,
        y: Option<TermId>,
        op: Op,
        c: &BigRational,
        lit: TheoryLit,
    ) -> Result<usize, GiveUp> {
        let (op, c) = if self.integer {
            tighten_int(op, c)
        } else {
            (op, c.clone())
        };
        let xv = self.vertex(x);
        let yv = y.map(|y| self.vertex(y));
        let atom = match yv {
            Some(yv) => DiffAtom::diff(xv, yv, op, c),
            None => DiffAtom::var_const(xv, op, c),
        };
        let lowered = W::lower(&atom, ZERO_VERTEX)
            .ok_or_else(|| GiveUp::new("dl: a bound does not fit the weight lane"))?;
        let [edge] = lowered.as_slice() else {
            return Err(GiveUp::new(
                "dl: an inequality lowered to more than one edge",
            ));
        };
        let id = self.graph.edges().len();
        let tag = u64::try_from(id).map_err(|_| GiveUp::new("dl: edge space exhausted"))?;
        let registered = self
            .graph
            .register_edge(edge.from, edge.to, edge.weight.clone(), tag);
        debug_assert_eq!(registered, id);
        self.edge_lit.push(lit);
        self.twin.push(id);
        self.propagated.push(None);
        Ok(id)
    }

    /// Propagate every unassigned atom the new edge's paths now bound.
    fn propagate_entailed(&mut self, ctx: &mut Ctx<'_>, edge: usize) {
        let found = self.graph.entailed_after_assert(edge, PROP_BUDGET);
        for Entailment { edge_id, reason } in found {
            let Some(&twin) = self.twin.get(edge_id) else {
                continue;
            };
            if self.graph.edge_is_active(twin) {
                continue; // the atom is assigned already
            }
            if self.propagated.get(edge_id).copied().flatten().is_some() {
                continue;
            }
            let Some(&lit) = self.edge_lit.get(edge_id) else {
                continue;
            };
            let mut reason_lits: Vec<TheoryLit> = Vec::with_capacity(reason.len());
            let mut usable = true;
            for tag in reason {
                match usize::try_from(tag).ok().and_then(|t| self.edge_lit.get(t)) {
                    Some(&r) if r != lit => {
                        if !reason_lits.contains(&r) {
                            reason_lits.push(r);
                        }
                    }
                    _ => {
                        usable = false;
                        break;
                    }
                }
            }
            if !usable || reason_lits.is_empty() {
                continue;
            }
            if let Some(slot) = self.propagated.get_mut(edge_id) {
                *slot = Some(self.depth);
                self.propagated_trail.push(edge_id);
            }
            let mut clause = Vec::with_capacity(reason_lits.len() + 1);
            clause.push(lit);
            clause.extend(reason_lits.iter().map(|r| TheoryLit::new(r.term, !r.value)));
            let hint = self.hint(ctx, &clause);
            ctx.propagate(
                lit,
                Justification::Eager(Explanation {
                    reason: reason_lits,
                    hint,
                }),
            );
        }
    }

    fn cycle_conflict(&self, ctx: &mut Ctx<'_>, tags: &[u64]) -> Result<(), GiveUp> {
        let mut lits: Vec<TheoryLit> = Vec::with_capacity(tags.len());
        for &tag in tags {
            let lit = usize::try_from(tag)
                .ok()
                .and_then(|t| self.edge_lit.get(t))
                .copied()
                .ok_or_else(|| GiveUp::new("dl: a cycle edge has no literal"))?;
            if !lits.contains(&lit) {
                lits.push(lit);
            }
        }
        if lits.is_empty() {
            return Err(GiveUp::new("dl: an empty negative cycle"));
        }
        let clause: Vec<TheoryLit> = lits
            .iter()
            .map(|l| TheoryLit::new(l.term, !l.value))
            .collect();
        let hint = self.hint(ctx, &clause);
        ctx.conflict(Conflict { lits, hint });
        Ok(())
    }

    fn assert_edge(&mut self, ctx: &mut Ctx<'_>, edge: usize) -> Result<(), GiveUp> {
        let implied = self.propagated.get(edge).copied().flatten().is_some();
        match self.graph.assert_edge(edge) {
            AssertOutcome::Consistent => {
                self.active_edges.push(edge);
                if !implied {
                    self.propagate_entailed(ctx, edge);
                }
                Ok(())
            }
            AssertOutcome::Conflict(tags) => self.cycle_conflict(ctx, &tags),
            AssertOutcome::Refused => Err(GiveUp::new(
                "dl: a potential left the weight lane (no negation in its width)",
            )),
        }
    }

    fn value_term(&self, terms: &mut TermStore, value: &BigRational) -> TermId {
        if self.integer {
            terms.mk_int(value.to_integer())
        } else {
            terms.mk_rational(value.clone())
        }
    }
}

impl<W: DlWeight + Send + 'static> TheoryPlugin for DlPlugin<W> {
    fn name(&self) -> &'static str {
        if self.integer {
            "dl-int"
        } else {
            "dl-real"
        }
    }

    fn internalize_atom(&mut self, ctx: &mut Ctx<'_>, atom: TermId) -> Result<AtomHandle, GiveUp> {
        if let Some(&handle) = self.handles.get(&atom) {
            return Ok(handle);
        }
        let shape = diff_shape(ctx.terms(), &mut self.lin, atom).ok_or_else(|| {
            GiveUp::new(format!(
                "dl: {:.80} is not a difference atom",
                format!("{:?}", ctx.terms().get(atom))
            ))
        })?;
        let entry = match shape {
            DiffShape::Ground(truth) => DlAtom::Ground(truth),
            DiffShape::Equality(a, b, _) => {
                // Over Int a fractional difference can never be met.
                let mut form = self.lin.linearize(ctx.terms(), a)?;
                let rhs = self.lin.linearize(ctx.terms(), b)?;
                form.add_scaled(&rhs, &-BigRational::one());
                if self.integer && !form.constant.is_integer() {
                    DlAtom::Ground(false)
                } else {
                    Self::define_equality(ctx, self.integer, atom, a, b);
                    DlAtom::Defined
                }
            }
            DiffShape::Diff { x, y, op, c } => {
                let pos = self.register_edge(x, y, op, &c, TheoryLit::new(atom, true))?;
                let neg = self.register_edge(x, y, negate(op), &c, TheoryLit::new(atom, false))?;
                self.twin[pos] = neg;
                self.twin[neg] = pos;
                DlAtom::Ineq { pos, neg }
            }
        };
        let handle = u32::try_from(self.atoms.len())
            .map(AtomHandle)
            .map_err(|_| GiveUp::new("dl: atom handle space exhausted"))?;
        self.atoms.push((atom, entry));
        self.handles.insert(atom, handle);
        Ok(handle)
    }

    /// A hub node of this plug-in's sort (design H1): a leaf plus a
    /// constant, whose leaf becomes a vertex so the potential values it.
    fn attach_term(&mut self, ctx: &mut Ctx<'_>, term: TermId) -> Result<Option<ThVar>, GiveUp> {
        let form = self.lin.linearize(ctx.terms(), term)?;
        let mut leaves = form.coeffs.iter();
        match (leaves.next(), leaves.next()) {
            (None, _) => {}
            (Some((&leaf, coeff)), None) if coeff.is_one() => {
                let _ = self.vertex(leaf);
            }
            _ => {
                return Err(GiveUp::new(
                    "dl: a shared term is not a variable plus a constant",
                ))
            }
        }
        self.shared.attach(term).map(Some)
    }

    /// The hub merged two shared terms: the graph learns `a = b` through the
    /// equality atom (defined by its two bounds), with the hub's reason as
    /// the premise.
    fn new_eq(
        &mut self,
        ctx: &mut Ctx<'_>,
        a: ThVar,
        b: ThVar,
        why: &[TheoryLit],
    ) -> Result<(), GiveUp> {
        self.shared.new_eq(ctx, a, b, why)
    }

    /// The hub made two shared terms distinct.
    fn new_diseq(
        &mut self,
        ctx: &mut Ctx<'_>,
        a: ThVar,
        b: ThVar,
        why: &[TheoryLit],
    ) -> Result<(), GiveUp> {
        self.shared.new_diseq(ctx, a, b, why)
    }

    fn assign(&mut self, ctx: &mut Ctx<'_>, h: AtomHandle, value: bool) -> Result<(), GiveUp> {
        let Some(&(atom, entry)) = self.atoms.get(h.index()) else {
            return Err(GiveUp::new("dl: an unknown atom handle was assigned"));
        };
        match entry {
            DlAtom::Ineq { pos, neg } => self.assert_edge(ctx, if value { pos } else { neg }),
            DlAtom::Ground(truth) => {
                if value != truth {
                    ctx.conflict(Conflict {
                        lits: vec![TheoryLit::new(atom, value)],
                        hint: ProofHint::kind(TheoryLemmaKind::ArithClauseTautology),
                    });
                }
                Ok(())
            }
            DlAtom::Defined => Ok(()),
        }
    }

    /// Everything happens when an edge is asserted.
    fn can_propagate(&self) -> bool {
        false
    }

    fn propagate(&mut self, _ctx: &mut Ctx<'_>) -> Result<(), GiveUp> {
        Ok(())
    }

    /// The potential is feasible for every active edge: it is the model.
    fn final_check(&mut self, _ctx: &mut Ctx<'_>, _effort: Effort) -> Result<Final, GiveUp> {
        Ok(Final::Sat)
    }

    fn explain(&mut self, _ctx: &mut Ctx<'_>, _lit: TheoryLit, _token: u64) -> Option<Explanation> {
        None // every propagation carries its reason eagerly
    }

    fn push_scope(&mut self, _ctx: &mut Ctx<'_>) {
        self.graph.push();
        self.active_marks.push(self.active_edges.len());
        self.propagated_marks.push(self.propagated_trail.len());
        self.depth += 1;
    }

    fn pop_scope(&mut self, _ctx: &mut Ctx<'_>, n: u32) {
        for _ in 0..n {
            if self.depth == 0 {
                return;
            }
            self.depth -= 1;
            self.graph.pop();
            if let Some(mark) = self.active_marks.pop() {
                self.active_edges.truncate(mark);
            }
            if let Some(mark) = self.propagated_marks.pop() {
                while self.propagated_trail.len() > mark {
                    if let Some(edge) = self.propagated_trail.pop() {
                        if let Some(slot) = self.propagated.get_mut(edge) {
                            *slot = None;
                        }
                    }
                }
            }
        }
    }

    /// Realize the `ℚ[ε]` potential with one `δ` below every active edge's
    /// slack margin, so strict edges stay strict (the lane's
    /// `extract_model`).
    fn on_sat(&mut self, _ctx: &mut Ctx<'_>) {
        let pot = self.graph.model();
        let edges = self.graph.edges();
        let mut slacks: Vec<(BigRational, i64)> = Vec::with_capacity(self.active_edges.len());
        for &id in &self.active_edges {
            let Some(e) = edges.get(id) else { continue };
            let (Some(from), Some(to)) = (pot.get(e.from), pot.get(e.to)) else {
                continue;
            };
            let Some(neg_to) = to.negate() else { continue };
            slacks.push(from.add(&e.weight).add(&neg_to).parts());
        }
        let delta = ay_diff_logic::rstar::pick_delta_from_slacks(&slacks);
        self.model.clear();
        let Some(neg_base) = pot.get(ZERO_VERTEX).and_then(|b| b.negate()) else {
            return;
        };
        for (v, term) in self.vertex_terms.iter().enumerate() {
            let (Some(term), Some(p)) = (term, pot.get(v)) else {
                continue;
            };
            self.model.insert(*term, p.add(&neg_base).realize(&delta));
        }
    }

    fn model_value(&mut self, ctx: &mut Ctx<'_>, term: TermId) -> Option<TermId> {
        let value = self.value_of(ctx.terms(), term)?;
        if self.integer && !value.is_integer() {
            return None; // tightening makes this impossible; never round
        }
        Some(self.value_term(ctx.terms_mut(), &value))
    }

    fn phase_epoch(&self) -> Option<u64> {
        Some(0) // no phase hints: seeding once is enough
    }
}
