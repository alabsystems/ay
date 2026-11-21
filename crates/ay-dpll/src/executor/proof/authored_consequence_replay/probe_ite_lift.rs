// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Arithmetic-ITE-LIFTED assertion leaves in consequence-replay probes
//! (#probe-ite-lift-promoter).
//!
//! # The leaf, measured
//!
//! Ground preprocessing Shannon-expands every term-level arithmetic `ite`
//! before the SAT layer sees an assertion (`TermStore::lift_arithmetic_ite`:
//! `(<= (ite c a b) k)` becomes `(ite c (<= a k) (<= b k))`, branch atoms
//! constant-fold, `mk_ite` absorbs a `true`/`false` branch, `mk_not` pushes
//! the negation into NNF). The proof tracker therefore assumes the LIFTED
//! term, which is no probe assertion and no `and`-conjunct of one, so export
//! demotes it to a premiseless `trust` unit that the probe's strict check
//! refuses and the whole consequence-replay candidate declines.
//!
//! Measured on AUFDTLIRA `P630-039 bug.ads_32_25_range_check` (the
//! `ground_core` leg's 6-formula core, default posture): the ONLY residual
//! trust step is
//!
//! ```text
//! (cl (or (and (<= F L) (not (<= -2147483648 (+ L (- F) 1))))
//!         (and (<= F L) (not (<= (+ L (- F) 1) 2147483647)))))
//! ```
//!
//! with `F = (integerqtint (first b!rt))`, `L = (integerqtint (last b!rt))`
//! — exactly `¬in_range(ite (<= F L) (+ L (- F) 1) 0)` after the lift folded
//! `(<= -2147483648 0)` and `(<= 0 2147483647)` to `true`. The probe's own
//! assertion is the UNLIFTED `(or (not (<= -2147483648 x)) (not (<= x 2147483647)))`
//! with `x` the `ite` term, and re-running the lifter on it reproduces the
//! trust term byte-for-byte.
//!
//! # The derivation
//!
//! Recognition is the lifter itself: a trust unit `(cl G)` is promotable when
//! some probe assertion `H` (or a positional `and`-conjunct of one) satisfies
//! `lift_arithmetic_ite(H) == G`. That is the exact relation preprocessing
//! established, recomputed with the same interning constructors.
//!
//! The derivation of `(cl G)` from `assume H` never re-implements the lifter's
//! rewrites. It is a CLAUSAL refutation of `H ∧ ¬G`, every leaf a step the
//! strict checker validates on its own:
//!
//! * for each term-level `ite` `x = (ite c u v)` of `H`, the branch equalities
//!   `(cl (not c) (= x u))` and `(cl c (= x v))` through the same
//!   `ite_intro` / `equiv_pos2` / `and_pos` / `ite2` / `ite1` chain the
//!   provenance ITE emitter already ships and carcara accepts;
//! * for each atom `B[x]` of `H` and each branch value `w`, the EUF congruence
//!   transfers `(cl (not (= x w)) (not B[x]) B[w])` and
//!   `(cl (not (= x w)) B[x] (not B[w]))`, planned by
//!   [`Executor::plan_euf_lemma_with_budget`] (`eq_congruent_pred` over the
//!   raw substitution) and emitted by the certified EUF emitter;
//! * for a substituted atom the lift folded away — `(<= -2147483648 0)` —
//!   a Farkas-verified `la_generic` evaluation unit; for one the lift merely
//!   re-spelled, a Farkas-verified `la_generic` bridge to the spelling `G`
//!   uses;
//! * Tseitin tautologies (`and_pos`/`and_neg`/`or_pos`/`or_neg`/`ite_pos`/
//!   `ite_neg`) over every compound Boolean node of `H` and `G`;
//! * and the bounded DPLL(T) closer, run under the assumption `¬G`, which
//!   folds the propositional search into ordinary `resolution` steps ending
//!   at exactly `(cl G)`.
//!
//! Nothing is taken on the producer's word: the closer refuses a
//! trust-proved leaf, every seeded lemma was validated before it was seeded,
//! and the caller's unchanged whole-proof strict check still gates the
//! rebuilt candidate. A declined leaf leaves the trust step byte-identical.
//!
//! The native clausification producer also reuses this checked emitter for
//! individual consequences of an immutable native source. It authenticates
//! every original occurrence against the current query epoch, then independently
//! proves `H => G`; a target need not equal the complete arithmetic-ITE lift.
//! Boolean equality congruence followed by equivalence elimination covers
//! equality predicates when a direct EUF transfer plan does not apply.
//!
//! Why no theory oracle carries the arithmetic here: the closer's LRA oracle
//! asserts only atoms over pure linear terms
//! (`term_is_pure_linear_arith`), and this family's atoms are over
//! uninterpreted applications, so every arithmetic fact must be seeded
//! already checked — which is also what makes the closer's output
//! purely propositional and cheap.

use super::*;
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, TermData};
use ay_core::{FarkasAnnotation, TheoryLemmaKind};
use ay_sat::{Literal, Variable};

use crate::executor::proof_farkas_validation::certificate_valid_for_blocking_clause;
use crate::executor::proof_trust_surgery_provenance::SurgeryPlanningBudget;

/// Term-level `ite`s one assertion may carry. Each costs one `ite_intro`
/// chain and doubles the transfer lemmas of every atom it occurs in.
const MAX_LIFT_ITE_TERMS: usize = 4;
/// Compound Boolean nodes of `H`, `G`, and the `ite` conditions together.
const MAX_LIFT_STRUCTURE_NODES: usize = 512;
/// Substitution-derived atom variants (each yields two EUF transfer lemmas).
const MAX_LIFT_TRANSFERS: usize = 128;
/// Subterm visits any single structural walk may spend.
const MAX_LIFT_TERM_WORK: usize = 8_192;

/// An exact source for a candidate trust unit. Legacy plans require its full
/// arithmetic-ITE lift to match the target; native plans instead authenticate
/// the original source and let the checked emitter prove the consequence.
#[derive(Clone)]
struct LiftPlan {
    root: TermId,
    path: Vec<(TermId, u32, TermId)>,
    source: TermId,
}

/// A term-level `(ite cond then else)` of the source assertion.
#[derive(Clone, Copy)]
struct IteSite {
    term: TermId,
    cond: TermId,
    then_branch: TermId,
    else_branch: TermId,
}

/// Compound Boolean structure the Tseitin tautologies decompose.
enum BoolNode {
    And(Vec<TermId>),
    Or(Vec<TermId>),
    Ite(TermId, TermId, TermId),
    Not(TermId),
    Atom,
}

fn bool_node(terms: &TermStore, term: TermId) -> BoolNode {
    if terms.sort(term) != &Sort::Bool {
        return BoolNode::Atom;
    }
    match terms.get(term) {
        TermData::Not(inner) => BoolNode::Not(*inner),
        TermData::Ite(cond, then_branch, else_branch) => {
            BoolNode::Ite(*cond, *then_branch, *else_branch)
        }
        TermData::App(Symbol::Named(name), args) if name == "and" && !args.is_empty() => {
            BoolNode::And(args.clone())
        }
        TermData::App(Symbol::Named(name), args) if name == "or" && !args.is_empty() => {
            BoolNode::Or(args.clone())
        }
        _ => BoolNode::Atom,
    }
}

/// Every distinct NON-Bool `ite` of `term`, with enclosing sites first.
/// A branch may contain another original site. Replacing its enclosing site
/// before replacing the branch's site avoids minting a new numeric `ite`
/// that no `ite_intro` covers. A condition containing a numeric site, a
/// negated condition, binders, and shapes beyond the site cap still decline.
fn collect_ite_sites(terms: &TermStore, term: TermId) -> Option<Vec<IteSite>> {
    let mut sites: Vec<IteSite> = Vec::new();
    let mut stack = vec![term];
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut work = MAX_LIFT_TERM_WORK;
    while let Some(current) = stack.pop() {
        if !seen.insert(current) {
            continue;
        }
        work = work.checked_sub(1)?;
        match terms.get(current) {
            TermData::Const(_) | TermData::Var(..) => {}
            TermData::Not(inner) => stack.push(*inner),
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Ite(cond, then_branch, else_branch) => {
                let (cond, then_branch, else_branch) = (*cond, *then_branch, *else_branch);
                if terms.sort(current) != &Sort::Bool {
                    if matches!(terms.get(cond), TermData::Not(_)) {
                        return None;
                    }
                    if sites.len() >= MAX_LIFT_ITE_TERMS {
                        return None;
                    }
                    sites.push(IteSite {
                        term: current,
                        cond,
                        then_branch,
                        else_branch,
                    });
                }
                stack.extend([cond, then_branch, else_branch]);
            }
            // Binders, `let`, and any term kind this walk does not model.
            _ => return None,
        }
    }
    // Proper descendants always have fewer descendants than their parents.
    // Stable ordering preserves the previous order for independent sites.
    let mut ranked = Vec::with_capacity(sites.len());
    for site in &sites {
        let mut descendants = 0usize;
        for other in &sites {
            if contains_term(terms, site.cond, other.term) {
                return None;
            }
            if contains_term(terms, site.then_branch, other.term)
                || contains_term(terms, site.else_branch, other.term)
            {
                if site.term == other.term {
                    return None;
                }
                descendants += 1;
            }
        }
        ranked.push((descendants, *site));
    }
    ranked.sort_by_key(|(count, _)| std::cmp::Reverse(*count));
    Some(ranked.into_iter().map(|(_, site)| site).collect())
}

/// Whether `needle` occurs in `haystack` (inclusive), bounded.
fn contains_term(terms: &TermStore, haystack: TermId, needle: TermId) -> bool {
    let mut stack = vec![haystack];
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut work = MAX_LIFT_TERM_WORK;
    while let Some(current) = stack.pop() {
        if current == needle {
            return true;
        }
        if !seen.insert(current) {
            continue;
        }
        if work == 0 {
            return false;
        }
        work -= 1;
        match terms.get(current) {
            TermData::Not(inner) => stack.push(*inner),
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Ite(cond, then_branch, else_branch) => {
                stack.extend([*cond, *then_branch, *else_branch]);
            }
            _ => {}
        }
    }
    false
}

fn contains_non_bool_ite(terms: &TermStore, term: TermId) -> bool {
    let mut stack = vec![term];
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut work = MAX_LIFT_TERM_WORK;
    while let Some(current) = stack.pop() {
        if !seen.insert(current) {
            continue;
        }
        if work == 0 {
            return false;
        }
        work -= 1;
        match terms.get(current) {
            TermData::Not(inner) => stack.push(*inner),
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Ite(cond, then_branch, else_branch) => {
                if terms.sort(current) != &Sort::Bool {
                    return true;
                }
                stack.extend([*cond, *then_branch, *else_branch]);
            }
            _ => {}
        }
    }
    false
}

/// RAW structural substitution `term[from := to]`: every ancestor of an
/// occurrence is re-interned with the raw constructors (`mk_app`,
/// `mk_ite_raw`, `mk_not_raw`), so the result is congruent to `term` under
/// `(= from to)` node for node — the shape the EUF planner closes. `None`
/// on a binder or `let`.
fn substitute_raw(
    terms: &mut TermStore,
    term: TermId,
    from: TermId,
    to: TermId,
    memo: &mut HashMap<TermId, TermId>,
) -> Option<TermId> {
    if term == from {
        return Some(to);
    }
    if let Some(&done) = memo.get(&term) {
        return Some(done);
    }
    let rebuilt = match terms.get(term).clone() {
        TermData::Const(_) | TermData::Var(..) => term,
        TermData::Not(inner) => {
            let inner_sub = substitute_raw(terms, inner, from, to, memo)?;
            if inner_sub == inner {
                term
            } else {
                terms.mk_not_raw(inner_sub)
            }
        }
        TermData::Ite(cond, then_branch, else_branch) => {
            let cond_sub = substitute_raw(terms, cond, from, to, memo)?;
            let then_sub = substitute_raw(terms, then_branch, from, to, memo)?;
            let else_sub = substitute_raw(terms, else_branch, from, to, memo)?;
            if cond_sub == cond && then_sub == then_branch && else_sub == else_branch {
                term
            } else {
                terms.mk_ite_raw(cond_sub, then_sub, else_sub)
            }
        }
        TermData::App(symbol, args) => {
            let mut changed = false;
            let mut new_args = Vec::with_capacity(args.len());
            for &arg in &args {
                let sub = substitute_raw(terms, arg, from, to, memo)?;
                changed |= sub != arg;
                new_args.push(sub);
            }
            if changed {
                let sort = terms.sort(term).clone();
                terms.mk_app(symbol, new_args, sort)
            } else {
                term
            }
        }
        // Binders, `let`, and any term kind the raw rebuild does not model.
        _ => return None,
    };
    memo.insert(term, rebuilt);
    Some(rebuilt)
}

/// A comparison atom over `Int`/`Real` operands.
fn arith_comparison_operands(terms: &TermStore, atom: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(Symbol::Named(name), args) = terms.get(atom) else {
        return None;
    };
    if !matches!(name.as_str(), "<" | "<=" | ">" | ">=" | "=") {
        return None;
    }
    let &[lhs, rhs] = args.as_slice() else {
        return None;
    };
    matches!(terms.sort(lhs), Sort::Int | Sort::Real).then_some((lhs, rhs))
}

/// Numerals combined by `+`/`-`/`*`/`/` only.
fn is_ground_arith(terms: &TermStore, term: TermId) -> bool {
    let mut stack = vec![term];
    let mut work = MAX_LIFT_TERM_WORK;
    while let Some(current) = stack.pop() {
        if work == 0 {
            return false;
        }
        work -= 1;
        match terms.get(current) {
            TermData::Const(Constant::Int(_) | Constant::Rational(_)) => {}
            TermData::App(Symbol::Named(name), args)
                if matches!(name.as_str(), "+" | "-" | "*" | "/") =>
            {
                stack.extend(args.iter().copied());
            }
            _ => return false,
        }
    }
    true
}

/// The clause a proof step proves, for seeding the SAT database from
/// whatever the certified emitters actually recorded.
fn step_clause(proof: &Proof, id: ProofId) -> Option<Vec<TermId>> {
    match proof.steps.get(id.0 as usize)? {
        ProofStep::Assume(term) => Some(vec![*term]),
        ProofStep::Resolution { clause, .. }
        | ProofStep::TheoryLemma { clause, .. }
        | ProofStep::Step { clause, .. } => Some(clause.clone()),
        _ => None,
    }
}

/// Seeded term clauses with the proof step proving each one.
struct LiftDatabase {
    versions: Vec<(Vec<TermId>, ProofId)>,
}

impl LiftDatabase {
    fn push(&mut self, clause: Vec<TermId>, id: ProofId) {
        self.versions.push((clause, id));
    }
}

/// A private cumulative closer-work allowance. Reserving an attempt charges
/// its full ceiling even if it declines; no source/target pair can reset it.
struct LiftClosureBudget {
    remaining: u64,
    per_attempt: u64,
}

impl LiftClosureBudget {
    fn reserve(&mut self) -> Option<u64> {
        let allowance = self.remaining.min(self.per_attempt);
        if allowance == 0 {
            return None;
        }
        self.remaining -= allowance;
        Some(allowance)
    }
}

impl Executor {
    /// Replace every probe-local premiseless `trust` unit whose term is the
    /// arithmetic-ITE LIFT of a probe assertion (or of a positional
    /// `and`-conjunct of one) with a derivation of that unit
    /// (#probe-ite-lift-promoter); see the module documentation.
    ///
    /// Grants no authority of its own: the caller immediately runs the
    /// unchanged whole-proof strict checker, and every leaf this pass seeds
    /// was validated before it was seeded. An unrelated trust leaf, a lift
    /// this pass cannot derive, or a search that does not close leaves the
    /// affected step byte-identical.
    pub(in crate::executor) fn promote_consequence_probe_ite_lift_trust_leaves(
        &mut self,
        proof: &mut Proof,
        assertions: &[TermId],
    ) {
        if !crate::quant_unit_authority::probe_ite_lift_promoter_enabled() {
            return;
        }
        if assertions.is_empty()
            || assertions.len() > MAX_CONSEQUENCES
            || proof.steps.len() > MAX_PROBE_PROOF_STEPS
        {
            return;
        }
        let Some(plans) = self.consequence_probe_ite_lift_plans(proof, assertions) else {
            return;
        };

        self.promote_planned_ite_lift_units(proof, &plans, None);
    }

    /// Common checked emitter; its caller supplies only a bounded source plan.
    /// A plan is a hint: closure and the whole-proof checker still re-prove it.
    fn promote_planned_ite_lift_units(
        &mut self,
        proof: &mut Proof,
        plans: &[Option<LiftPlan>],
        mut closure_budget: Option<&mut LiftClosureBudget>,
    ) -> usize {
        let mut rebuilt = Proof::new();
        let mut root_units: HashMap<TermId, ProofId> = HashMap::default();
        let mut remap: Vec<ProofId> = Vec::with_capacity(proof.steps.len());
        let mut promoted = 0usize;
        for (index, step) in proof.steps.iter().cloned().enumerate() {
            if let (Some(plan), ProofStep::Step { clause, .. }) = (&plans[index], &step) {
                if let Some(&target) = clause.first() {
                    let allowance = match closure_budget.as_deref_mut() {
                        Some(budget) => budget.reserve().map(Some),
                        None => Some(None),
                    };
                    if let Some(step_limit) = allowance {
                        let snapshot = rebuilt.steps.len();
                        if let Some(unit) = self.emit_probe_ite_lift_unit(
                            &mut rebuilt,
                            &mut root_units,
                            plan,
                            target,
                            step_limit,
                        ) {
                            replay_note(|| {
                                format!(
                                    "ite-lift: derived trust unit at probe step {index} from {} steps",
                                    rebuilt.steps.len() - snapshot
                                )
                            });
                            remap.push(unit);
                            promoted += 1;
                            continue;
                        }
                        // Decline for this leaf: roll back everything it added,
                        // including any assume it minted, and copy the step.
                        rebuilt.steps.truncate(snapshot);
                        root_units.retain(|_, id| (id.0 as usize) < snapshot);
                        replay_note(|| format!("ite-lift: decline at probe step {index}"));
                    }
                }
            }

            let remap_id = |id: ProofId| remap.get(id.0 as usize).copied().unwrap_or(id);
            let step = match step {
                ProofStep::Resolution {
                    clause,
                    pivot,
                    clause1,
                    clause2,
                } => ProofStep::Resolution {
                    clause,
                    pivot,
                    clause1: remap_id(clause1),
                    clause2: remap_id(clause2),
                },
                ProofStep::Step {
                    rule,
                    clause,
                    premises,
                    args,
                } => ProofStep::Step {
                    rule,
                    clause,
                    premises: premises.into_iter().map(remap_id).collect(),
                    args,
                },
                other => other,
            };
            remap.push(rebuilt.add_step(step));
        }
        if promoted == 0 {
            return 0;
        }

        let mut remapped_named = proof.named_steps.clone();
        remapped_named.retain(|_, id| {
            let old_index = id.0 as usize;
            let Some(new_id) = remap.get(old_index) else {
                return false;
            };
            *id = *new_id;
            true
        });
        rebuilt.named_steps = remapped_named;
        *proof = rebuilt;
        promoted
    }

    fn consequence_probe_ite_lift_plans(
        &mut self,
        proof: &Proof,
        assertions: &[TermId],
    ) -> Option<Vec<Option<LiftPlan>>> {
        let mut plans: Vec<Option<LiftPlan>> = vec![None; proof.steps.len()];
        let mut planned = 0usize;
        for (index, step) in proof.steps.iter().enumerate() {
            let ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                ..
            } = step
            else {
                continue;
            };
            let [target] = clause.as_slice() else {
                continue;
            };
            if !premises.is_empty() {
                continue;
            }
            let Some(plan) = self.probe_ite_lift_source_for(assertions, *target) else {
                continue;
            };
            planned += 1;
            if planned > MAX_CONSEQUENCES {
                return None;
            }
            plans[index] = Some(plan);
        }
        (planned > 0).then_some(plans)
    }

    /// The probe assertion (or `and`-conjunct) whose lift IS `target`.
    fn probe_ite_lift_source_for(
        &mut self,
        assertions: &[TermId],
        target: TermId,
    ) -> Option<LiftPlan> {
        for &root in assertions {
            let mut candidates = vec![root];
            self.collect_and_descendants(root, &mut candidates);
            for candidate in candidates {
                if candidate == target || !contains_non_bool_ite(&self.ctx.terms, candidate) {
                    continue;
                }
                let lifted = self.ctx.terms.lift_arithmetic_ite(candidate);
                if lifted != target {
                    continue;
                }
                let path = if candidate == root {
                    Vec::new()
                } else {
                    self.and_path_to(root, candidate)?
                };
                return Some(LiftPlan {
                    root,
                    path,
                    source: candidate,
                });
            }
        }
        None
    }

    /// Every positional `and`-descendant of `root`, bounded like
    /// [`Executor::and_path_to`].
    fn collect_and_descendants(&self, root: TermId, out: &mut Vec<TermId>) {
        let mut stack = vec![root];
        let mut work = MAX_AND_PATH_WORK;
        while let Some(node) = stack.pop() {
            if work == 0 {
                return;
            }
            work -= 1;
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(node) else {
                continue;
            };
            if name != "and" {
                continue;
            }
            for &child in args {
                if !out.contains(&child) {
                    out.push(child);
                    stack.push(child);
                }
            }
        }
    }

    /// Emit the whole derivation of `(cl target)` into `rebuilt`, returning
    /// its step, or `None` with steps possibly appended (the caller rolls
    /// back to its snapshot).
    fn emit_probe_ite_lift_unit(
        &mut self,
        rebuilt: &mut Proof,
        root_units: &mut HashMap<TermId, ProofId>,
        plan: &LiftPlan,
        target: TermId,
        step_limit: Option<u64>,
    ) -> Option<ProofId> {
        let source = plan.source;
        let sites = collect_ite_sites(&self.ctx.terms, source)?;
        if sites.is_empty() && !matches!(self.ctx.terms.get(source), TermData::Ite(..)) {
            replay_note(|| format!("ite-lift: source {} has no admitted ITE", source.0));
            return None;
        }
        // A Boolean ITE needs no term-equality lifting. Its own ITE Boolean
        // rules below independently derive branch clauses from the source
        // unit, including the checked AndPos path when it was a conjunct.
        replay_note(|| {
            format!(
                "ite-lift: source={} target={} sites={}",
                source.0,
                target.0,
                sites.len()
            )
        });

        // (1) The source as a unit: the authored assume plus its `and_pos`
        // projection chain, exactly as the conjunct promoter derives it.
        let mut unit = *root_units
            .entry(plan.root)
            .or_insert_with(|| rebuilt.add_assume(plan.root, None));
        for &(parent, position, child) in &plan.path {
            let not_parent = self.ctx.terms.mk_not_raw(parent);
            let projection = rebuilt.add_rule_step(
                AletheRule::AndPos(position),
                vec![not_parent, child],
                Vec::new(),
                vec![parent],
            );
            unit = rebuilt.add_resolution(vec![child], parent, projection, unit);
        }

        let mut database = LiftDatabase {
            versions: Vec::new(),
        };
        database.push(vec![source], unit);

        // (2) Branch equalities per term-level `ite`, through the checked
        // `ite_intro` chain.
        let mut branch_eqs: Vec<(TermId, TermId, TermId)> = Vec::with_capacity(sites.len());
        for site in &sites {
            let (eq_then, eq_else) =
                self.emit_probe_ite_branch_equalities(rebuilt, &mut database, source, unit, site)?;
            branch_eqs.push((site.term, eq_then, eq_else));
        }

        // (3) Boolean structure of the source, the target and every `ite`
        // condition: Tseitin tautologies plus the constant units.
        let mut roots: Vec<TermId> = vec![source, target];
        roots.extend(sites.iter().map(|site| site.cond));
        let (nodes, source_atoms, target_atoms) =
            self.collect_probe_lift_structure(source, target, &roots)?;
        self.emit_probe_lift_tseitin(rebuilt, &mut database, &nodes)?;
        let true_term = self.ctx.terms.true_term();
        let false_term = self.ctx.terms.false_term();
        let mut all_atoms: Vec<TermId> = source_atoms.clone();
        for &atom in &target_atoms {
            if !all_atoms.contains(&atom) {
                all_atoms.push(atom);
            }
        }
        for &atom in &all_atoms {
            if atom == true_term {
                let id = rebuilt.add_rule_step(
                    AletheRule::True,
                    vec![true_term],
                    Vec::new(),
                    Vec::new(),
                );
                database.push(vec![true_term], id);
            } else if atom == false_term {
                let not_false = self.ctx.terms.mk_not_raw(false_term);
                let id = rebuilt.add_rule_step(
                    AletheRule::False,
                    vec![not_false],
                    Vec::new(),
                    Vec::new(),
                );
                database.push(vec![not_false], id);
            }
        }

        // (4) EUF congruence transfers over the raw substitution, closed under
        // every remaining `ite` site of a substituted atom.
        let transferred = self.emit_probe_lift_transfers(
            rebuilt,
            &mut database,
            &sites,
            &branch_eqs,
            &source_atoms,
        );
        if transferred.is_none() {
            replay_note(|| "ite-lift: congruence transfers declined".to_owned());
        }
        let transferred = transferred?;

        // (5) Substituted atoms the lift folded away or re-spelled.
        let bridges = self.emit_probe_lift_bridges(
            rebuilt,
            &mut database,
            &transferred,
            &source_atoms,
            &target_atoms,
        );
        if bridges.is_none() {
            replay_note(|| "ite-lift: checked arithmetic bridges declined".to_owned());
        }
        bridges?;

        // (6) Propositional closure to exactly `(cl target)`.
        let closed = self.close_probe_lift_database(rebuilt, &database, target, step_limit);
        replay_note(|| {
            format!(
                "ite-lift: target={} closure={} seeded_clauses={}",
                target.0,
                closed.is_some(),
                database.versions.len()
            )
        });
        closed
    }

    /// `ite_intro` ⊢ `(= H (and H (ite c (= x u) (= x v))))`, then
    /// `equiv_pos2` and two resolutions to `(cl (and H def))`, `and_pos 1`
    /// to `(cl def)`, and `ite2`/`ite1` to the two branch clauses.
    fn emit_probe_ite_branch_equalities(
        &mut self,
        rebuilt: &mut Proof,
        database: &mut LiftDatabase,
        source: TermId,
        unit: ProofId,
        site: &IteSite,
    ) -> Option<(TermId, TermId)> {
        let (eq_then, eq_else, ite_def, and_term, intro_eq) = self.build_ite_lift_connectives(
            source,
            site.cond,
            site.term,
            site.then_branch,
            site.else_branch,
        )?;
        let not_intro_eq = self.ctx.terms.mk_not_raw(intro_eq);
        let not_source = self.ctx.terms.mk_not_raw(source);
        let intro =
            rebuilt.add_rule_step(AletheRule::IteIntro, vec![intro_eq], Vec::new(), Vec::new());
        let equivalence = rebuilt.add_rule_step(
            AletheRule::EquivPos2,
            vec![not_intro_eq, not_source, and_term],
            Vec::new(),
            Vec::new(),
        );
        let resolved_eq =
            rebuilt.add_resolution(vec![not_source, and_term], intro_eq, equivalence, intro);
        let resolved_source = rebuilt.add_resolution(vec![and_term], source, resolved_eq, unit);
        let not_and = self.ctx.terms.mk_not_raw(and_term);
        let and_pos = rebuilt.add_rule_step(
            AletheRule::AndPos(1),
            vec![not_and, ite_def],
            Vec::new(),
            Vec::new(),
        );
        let def_unit = rebuilt.add_resolution(vec![ite_def], and_term, and_pos, resolved_source);
        let not_cond = self.ctx.terms.mk_not_raw(site.cond);
        let then_id = rebuilt.add_rule_step(
            AletheRule::Ite2,
            vec![not_cond, eq_then],
            vec![def_unit],
            Vec::new(),
        );
        let else_id = rebuilt.add_rule_step(
            AletheRule::Ite1,
            vec![site.cond, eq_else],
            vec![def_unit],
            Vec::new(),
        );
        database.push(vec![not_cond, eq_then], then_id);
        database.push(vec![site.cond, eq_else], else_id);
        Some((eq_then, eq_else))
    }

    /// Compound Boolean nodes reachable from `roots` (deduplicated), plus the
    /// atom sets of `source` and of `target`.
    #[allow(clippy::type_complexity)]
    fn collect_probe_lift_structure(
        &self,
        source: TermId,
        target: TermId,
        roots: &[TermId],
    ) -> Option<(Vec<TermId>, Vec<TermId>, Vec<TermId>)> {
        let terms = &self.ctx.terms;
        let mut nodes: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut source_atoms: Vec<TermId> = Vec::new();
        let mut target_atoms: Vec<TermId> = Vec::new();
        for &root in roots {
            let mut stack = vec![root];
            let mut local_seen: HashSet<TermId> = HashSet::default();
            while let Some(current) = stack.pop() {
                if !local_seen.insert(current) {
                    continue;
                }
                match bool_node(terms, current) {
                    BoolNode::Atom => {
                        if root == source && !source_atoms.contains(&current) {
                            source_atoms.push(current);
                        }
                        if root == target && !target_atoms.contains(&current) {
                            target_atoms.push(current);
                        }
                    }
                    BoolNode::Not(inner) => stack.push(inner),
                    BoolNode::And(args) | BoolNode::Or(args) => {
                        if seen.insert(current) {
                            nodes.push(current);
                        }
                        stack.extend(args);
                    }
                    BoolNode::Ite(cond, then_branch, else_branch) => {
                        if seen.insert(current) {
                            nodes.push(current);
                        }
                        stack.extend([cond, then_branch, else_branch]);
                    }
                }
                if nodes.len() > MAX_LIFT_STRUCTURE_NODES {
                    return None;
                }
            }
        }
        Some((nodes, source_atoms, target_atoms))
    }

    /// The literal `(not t)` in the compact form the checker validates and
    /// the closer renders: a negated term becomes its body, anything else
    /// gets one raw negation shell.
    fn probe_lift_negated_literal(&mut self, term: TermId) -> TermId {
        if let TermData::Not(inner) = self.ctx.terms.get(term) {
            return *inner;
        }
        self.ctx.terms.mk_not_raw(term)
    }

    /// Premise-free Tseitin tautologies for every compound node.
    fn emit_probe_lift_tseitin(
        &mut self,
        rebuilt: &mut Proof,
        database: &mut LiftDatabase,
        nodes: &[TermId],
    ) -> Option<()> {
        for &node in nodes {
            let not_node = self.ctx.terms.mk_not_raw(node);
            match bool_node(&self.ctx.terms, node) {
                BoolNode::And(args) => {
                    for (position, &arg) in args.iter().enumerate() {
                        let position = u32::try_from(position).ok()?;
                        let clause = vec![not_node, arg];
                        let id = rebuilt.add_rule_step(
                            AletheRule::AndPos(position),
                            clause.clone(),
                            Vec::new(),
                            vec![node],
                        );
                        database.push(clause, id);
                    }
                    let mut clause = vec![node];
                    for &arg in &args {
                        clause.push(self.probe_lift_negated_literal(arg));
                    }
                    let id = rebuilt.add_rule_step(
                        AletheRule::AndNeg,
                        clause.clone(),
                        Vec::new(),
                        vec![node],
                    );
                    database.push(clause, id);
                }
                BoolNode::Or(args) => {
                    let mut clause = vec![not_node];
                    clause.extend(args.iter().copied());
                    let id = rebuilt.add_rule_step(
                        AletheRule::OrPos(0),
                        clause.clone(),
                        Vec::new(),
                        Vec::new(),
                    );
                    database.push(clause, id);
                    for &arg in &args {
                        let clause = vec![node, self.probe_lift_negated_literal(arg)];
                        let id = rebuilt.add_rule_step(
                            AletheRule::OrNeg,
                            clause.clone(),
                            Vec::new(),
                            Vec::new(),
                        );
                        database.push(clause, id);
                    }
                }
                BoolNode::Ite(cond, then_branch, else_branch) => {
                    let not_cond = self.probe_lift_negated_literal(cond);
                    let not_then = self.probe_lift_negated_literal(then_branch);
                    let not_else = self.probe_lift_negated_literal(else_branch);
                    for (rule, clause) in [
                        (AletheRule::ItePos1, vec![not_node, cond, else_branch]),
                        (AletheRule::ItePos2, vec![not_node, not_cond, then_branch]),
                        (AletheRule::IteNeg1, vec![node, cond, not_else]),
                        (AletheRule::IteNeg2, vec![node, not_cond, not_then]),
                    ] {
                        let id =
                            rebuilt.add_rule_step(rule, clause.clone(), Vec::new(), Vec::new());
                        database.push(clause, id);
                    }
                }
                BoolNode::Not(_) | BoolNode::Atom => {}
            }
        }
        Some(())
    }

    /// For every source atom mentioning a site and every branch value, the
    /// two EUF congruence transfers between the atom and its raw
    /// substitution; substituted atoms still mentioning another site are
    /// transferred again. Returns every substituted atom minted.
    fn emit_probe_lift_transfers(
        &mut self,
        rebuilt: &mut Proof,
        database: &mut LiftDatabase,
        sites: &[IteSite],
        branch_eqs: &[(TermId, TermId, TermId)],
        source_atoms: &[TermId],
    ) -> Option<Vec<TermId>> {
        let mut planning = SurgeryPlanningBudget::new();
        let mut work: Vec<TermId> = source_atoms
            .iter()
            .copied()
            .filter(|&atom| {
                sites
                    .iter()
                    .any(|site| contains_term(&self.ctx.terms, atom, site.term))
            })
            .collect();
        let mut queued: HashSet<TermId> = work.iter().copied().collect();
        let mut minted: Vec<TermId> = Vec::new();
        let mut transfers = 0usize;
        let mut memo: HashMap<TermId, TermId> = HashMap::default();
        while let Some(atom) = work.pop() {
            let Some(site_index) = sites
                .iter()
                .position(|site| contains_term(&self.ctx.terms, atom, site.term))
            else {
                continue;
            };
            let site = sites[site_index];
            let (_, eq_then, eq_else) = branch_eqs[site_index];
            for (branch, eq) in [(site.then_branch, eq_then), (site.else_branch, eq_else)] {
                transfers += 1;
                if transfers > MAX_LIFT_TRANSFERS {
                    return None;
                }
                memo.clear();
                let substituted =
                    substitute_raw(&mut self.ctx.terms, atom, site.term, branch, &mut memo)?;
                if substituted == atom {
                    return None;
                }
                let not_eq = self.ctx.terms.mk_not_raw(eq);
                let not_atom = self.probe_lift_negated_literal(atom);
                let not_substituted = self.probe_lift_negated_literal(substituted);
                for (direction, clause) in [
                    vec![not_eq, not_atom, substituted],
                    vec![not_eq, atom, not_substituted],
                ]
                .into_iter()
                .enumerate()
                {
                    let id = if let Some(plan) =
                        self.plan_euf_lemma_with_budget(&clause, &mut planning)
                    {
                        self.emit_euf_lemma(rebuilt, &plan)
                    } else {
                        // Equality predicates also obey congruence. The generic
                        // equality-chain planner can decline a direct transfer
                        // which is just one reversed equality hypothesis. Prove
                        // equality of the two Boolean applications instead, then
                        // eliminate it with the ordinary equivalence rule.
                        let equivalent = self.ctx.terms.mk_app(
                            Symbol::named("="),
                            [atom, substituted],
                            Sort::Bool,
                        );
                        let plan =
                            self.plan_euf_lemma_with_budget(&[not_eq, equivalent], &mut planning)?;
                        let congruence = self.emit_euf_lemma(rebuilt, &plan);
                        let not_equivalent = self.ctx.terms.mk_not_raw(equivalent);
                        let mut implication = vec![not_equivalent];
                        implication.extend_from_slice(&clause[1..]);
                        let implication = rebuilt.add_rule_step(
                            if direction == 0 {
                                AletheRule::EquivPos2
                            } else {
                                AletheRule::EquivPos1
                            },
                            implication,
                            Vec::new(),
                            Vec::new(),
                        );
                        replay_note(|| {
                            format!(
                            "ite-lift: Boolean congruence transfer atom={} substituted={} direction={direction}",
                            atom.0, substituted.0,
                        )
                        });
                        rebuilt.add_resolution(clause, equivalent, congruence, implication)
                    };
                    let emitted = step_clause(rebuilt, id)?;
                    database.push(emitted, id);
                }
                if !minted.contains(&substituted) {
                    minted.push(substituted);
                }
                if queued.insert(substituted)
                    && sites
                        .iter()
                        .any(|other| contains_term(&self.ctx.terms, substituted, other.term))
                {
                    work.push(substituted);
                }
            }
        }
        Some(minted)
    }

    /// A substituted atom absent from both the source and the target was
    /// either folded to a constant by the lift (a ground comparison: seed its
    /// Farkas-verified evaluation) or re-spelled (seed a Farkas-verified
    /// two-way bridge to the target atom it is equivalent to, when one
    /// exists). Anything else is left to the closer, which declines if the
    /// atom was load-bearing.
    fn emit_probe_lift_bridges(
        &mut self,
        rebuilt: &mut Proof,
        database: &mut LiftDatabase,
        minted: &[TermId],
        source_atoms: &[TermId],
        target_atoms: &[TermId],
    ) -> Option<()> {
        let unit_farkas = FarkasAnnotation::from_ints(&[1]);
        let pair_farkas = FarkasAnnotation::from_ints(&[1, 1]);
        for &atom in minted {
            if source_atoms.contains(&atom) || target_atoms.contains(&atom) {
                continue;
            }
            let Some((lhs, rhs)) = arith_comparison_operands(&self.ctx.terms, atom) else {
                continue;
            };
            if is_ground_arith(&self.ctx.terms, lhs) && is_ground_arith(&self.ctx.terms, rhs) {
                let not_atom = self.ctx.terms.mk_not_raw(atom);
                let clause = if certificate_valid_for_blocking_clause(
                    &self.ctx.terms,
                    &[atom],
                    &unit_farkas,
                ) {
                    vec![atom]
                } else if certificate_valid_for_blocking_clause(
                    &self.ctx.terms,
                    &[not_atom],
                    &unit_farkas,
                ) {
                    vec![not_atom]
                } else {
                    return None;
                };
                let id =
                    self.add_probe_lift_farkas_lemma(rebuilt, clause.clone(), unit_farkas.clone());
                database.push(clause, id);
                continue;
            }
            for &candidate in target_atoms {
                if candidate == atom
                    || arith_comparison_operands(&self.ctx.terms, candidate).is_none()
                {
                    continue;
                }
                let not_atom = self.ctx.terms.mk_not_raw(atom);
                let not_candidate = self.ctx.terms.mk_not_raw(candidate);
                let forward = vec![not_atom, candidate];
                let backward = vec![atom, not_candidate];
                if certificate_valid_for_blocking_clause(&self.ctx.terms, &forward, &pair_farkas)
                    && certificate_valid_for_blocking_clause(
                        &self.ctx.terms,
                        &backward,
                        &pair_farkas,
                    )
                {
                    let forward_id = self.add_probe_lift_farkas_lemma(
                        rebuilt,
                        forward.clone(),
                        pair_farkas.clone(),
                    );
                    database.push(forward, forward_id);
                    let backward_id = self.add_probe_lift_farkas_lemma(
                        rebuilt,
                        backward.clone(),
                        pair_farkas.clone(),
                    );
                    database.push(backward, backward_id);
                    break;
                }
            }
        }
        Some(())
    }

    /// Record a Farkas-verified arithmetic clause, classified the way the
    /// closer's own oracle classifies its lemmas.
    fn add_probe_lift_farkas_lemma(
        &mut self,
        rebuilt: &mut Proof,
        clause: Vec<TermId>,
        farkas: FarkasAnnotation,
    ) -> ProofId {
        let (classified, _) =
            crate::theory_inference::infer_theory_lemma_kind_from_clause_terms_and_farkas(
                &self.ctx.terms,
                &clause,
                Some(&farkas),
                None,
            );
        let kind = match classified {
            TheoryLemmaKind::LraFarkas | TheoryLemmaKind::LiaGeneric => classified,
            _ => TheoryLemmaKind::LraFarkas,
        };
        rebuilt.add_theory_lemma_with_farkas_and_kind("lra", clause, farkas, kind)
    }

    /// Map the seeded term clauses onto SAT literals and run the bounded
    /// DPLL(T) closer under `¬target`.
    fn close_probe_lift_database(
        &mut self,
        rebuilt: &mut Proof,
        database: &LiftDatabase,
        target: TermId,
        step_limit: Option<u64>,
    ) -> Option<ProofId> {
        let mut atom_to_var: HashMap<TermId, u32> = HashMap::default();
        let mut var_to_term: HashMap<u32, TermId> = HashMap::default();
        let mut literal_of = |terms: &TermStore, literal: TermId| -> Option<Literal> {
            let (atom, positive) = match terms.get(literal) {
                TermData::Not(inner) => (*inner, false),
                _ => (literal, true),
            };
            if matches!(terms.get(atom), TermData::Not(_)) {
                return None;
            }
            let next = u32::try_from(atom_to_var.len()).ok()?;
            let var = *atom_to_var.entry(atom).or_insert_with(|| {
                var_to_term.insert(next, atom);
                next
            });
            let variable = Variable::new(var);
            Some(if positive {
                Literal::positive(variable)
            } else {
                Literal::negative(variable)
            })
        };
        let mut sat_versions: Vec<(Vec<Literal>, ProofId)> =
            Vec::with_capacity(database.versions.len());
        for (clause, id) in &database.versions {
            let mut sat: Vec<Literal> = Vec::with_capacity(clause.len());
            for &literal in clause {
                let lit = literal_of(&self.ctx.terms, literal)?;
                if !sat.contains(&lit) {
                    sat.push(lit);
                }
            }
            sat_versions.push((sat, *id));
        }
        let target_sat = vec![literal_of(&self.ctx.terms, target)?];
        let mut manager = crate::SatProofManager::new(&var_to_term, &mut self.ctx.terms);
        manager.set_step_budget(step_limit);
        manager.close_target_over_seeded_clauses(&sat_versions, &target_sat, rebuilt)
    }
}

#[cfg(test)]
#[path = "probe_ite_lift_tests.rs"]
mod tests;

mod native_clausification;
