// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV-specific Model-Based Quantifier Instantiation (BV-MBQI).
//!
//! Extends the generic MBQI module with bitvector-aware instantiation strategies
//! for quantified BV formulas commonly arising from binary analysis and memory
//! safety properties, e.g.:
//! ```text
//! forall ptr: BV64. (valid_access(ptr) => in_bounds(ptr, obj_size))
//! ```
//!
//! Key techniques:
//! 1. **Boundary value instantiation**: For each BV-sorted bound variable, generate
//!    instances at 0, MAX (2^w - 1), and boundary offsets (size-1, size, size+1)
//!    derived from constants in the formula body.
//! 2. **Model value injection**: When a candidate model assigns a value to a BV
//!    variable, also instantiate with that value +/- 1.
//! 3. **Guard-filtered instantiation**: For `forall x. guard(x) => body(x)`, extract
//!    comparison constants from the guard (e.g., `bvult(x, size)`) and use them as
//!    targeted instantiation candidates.
//!
//! Reference: Z3 `sat/smt/q_mbi.cpp` (model-based instantiation) and
//! Ge & de Moura, "Complete Instantiation for Quantified Formulas in SMT" (CAV 2009).
//! The BV boundary strategy draws on CVC5's BV quantifier elimination
//! (`theory/bv/bv_solver_bitblast.cpp`).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{BitVecSort, Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;

use super::model::EvalValue;
use super::quantifier_loop::result_mapping::CheckedGroundDecision;
use super::Executor;
use crate::ematching::subst_vars;
use crate::executor_types::{Result, SolveResult};
use crate::logic_detection::LogicCategory;

mod false_instance;

/// Maximum BV-MBQI refinement rounds.
const MAX_BV_MBQI_ROUNDS: usize = 5;

/// Maximum candidate substitutions per quantifier per round.
const MAX_BV_CANDIDATES: usize = 512;

/// Maximum BV binder width enumerated EXHAUSTIVELY (all `2^width` values).
/// Width 8 → 256 values/binder; only an exhaustive enumeration can soundly
/// PROVE a `forall` by instantiation, so Sat is concluded only for these.
const BV_EXHAUSTIVE_MAX_WIDTH: u32 = 8;

/// Cap on the exhaustive cartesian product across a forall's binders. Below
/// this, the per-forall budget is raised to the full product so a genuinely
/// true small-domain forall completes; above it, the heuristic budget applies
/// and Sat cannot be concluded (fail-closed).
const BV_EXHAUSTIVE_TOTAL_CAP: u64 = 1 << 16;

/// Verdict of the symbolic entailment check of a single `forall`.
///
/// Enumeration can only prove a `forall` by visiting every value of every
/// binder, so it is confined to narrow binders (`BV_EXHAUSTIVE_MAX_WIDTH`).
/// The symbolic check reaches the same conclusion with ONE ground solve
/// regardless of width — a width-32 binder is 4.3 billion values to enumerate
/// but an ordinary bit-blasted query to refute.
enum BvForallCheck {
    /// The ground premise conjoined with the skolemized negation has a sealed,
    /// strict-proof UNSAT decision, so the premise entails the `forall` over
    /// the binder's entire domain.
    Holds,
    /// Undecided; fail closed to the enumeration path.
    Unknown,
}

/// Linear evidence that BV-MBQI discharged every quantified obligation in one
/// exact authored root window over its complete binder domain.
///
/// Construction is private to this module. The query-authority boundary may
/// consume the token, but no sibling module can mint it from a raw solver
/// result, Boolean proof marker, or caller-selected root slice.
#[must_use = "checked BV full-domain SAT authority must be consumed or discarded"]
#[derive(Debug)]
pub(in crate::executor) struct CheckedBvFullDomainSatAuthority {
    query_epoch: crate::executor::QueryAuthorityEpoch,
    source_context_stamp: ay_frontend::SourceContextStamp,
    roots: Box<[TermId]>,
    root_entries: Box<[Option<ay_core::term::TermEntryStamp>]>,
}

impl CheckedBvFullDomainSatAuthority {
    fn for_current(executor: &Executor, roots: &[TermId]) -> Option<Self> {
        let root_entries: Box<[Option<ay_core::term::TermEntryStamp>]> = roots
            .iter()
            .map(|&root| executor.ctx.terms.entry_stamp(root))
            .collect();
        (!roots.is_empty() && root_entries.iter().all(Option::is_some)).then(|| Self {
            query_epoch: executor.query_authority_epoch.clone(),
            source_context_stamp: executor.ctx.source_context_stamp(),
            roots: roots.into(),
            root_entries,
        })
    }

    pub(in crate::executor) fn into_current_roots(
        self,
        executor: &Executor,
    ) -> Option<Box<[TermId]>> {
        (self
            .query_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self.root_entries.iter().all(Option::is_some)
            && self.root_entries.iter().copied().eq(self
                .roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root))))
        .then_some(self.roots)
    }

    #[cfg(test)]
    pub(in crate::executor) fn for_test(executor: &Executor, roots: &[TermId]) -> Self {
        Self::for_current(executor, roots).expect("test roots must be live and nonempty")
    }
}

/// Mint full-domain SAT authority for a complete-domain proof produced OUTSIDE
/// this module, bundling the root-coverage check with the mint so the two can
/// never be separated at a call site.
///
/// The token's meaning is "every quantified obligation in this exact authored
/// root window was discharged over its binders' COMPLETE domain" — it is not
/// specific to bitvectors, only named for its first producer. The finite-sort
/// model-relative lane (`executor/finite_model_mbqi.rs`) establishes exactly
/// that for `FloatingPoint` binders, by a different but equally complete route:
/// a checked-UNSAT refutation of the skolemized negation under a pinned
/// structure covers the whole binder domain the same way this module's
/// symbolic entailment check does.
///
/// [`CheckedBvFullDomainSatAuthority::for_current`] stays private so no sibling
/// module can mint the token from a raw solver result; this is the only widened
/// entry point, and it cannot be called without passing the coverage check.
/// `certified_nodes` are identified by their QUANTIFIER NODE, so a universal
/// authored as `(not (exists ...))` is named by its `Exists` node — the term
/// that actually occurs in the authored root window the publication gates
/// check. (`authority_roots_exactly_cover_bv_foralls` additionally demands each
/// certified node BE a `Forall`, which only a lane working on the rewritten
/// form can satisfy.)
pub(in crate::executor) fn checked_full_domain_sat_authority(
    executor: &Executor,
    authority_roots: &[TermId],
    certified_nodes: &[TermId],
) -> Option<CheckedBvFullDomainSatAuthority> {
    let terms = &executor.ctx.terms;
    let certified: HashSet<TermId> = certified_nodes.iter().copied().collect();
    (!authority_roots.is_empty()
        && !certified_nodes.is_empty()
        && certified.len() == certified_nodes.len()
        && quantifier_nodes_in(terms, authority_roots) == certified)
        .then(|| CheckedBvFullDomainSatAuthority::for_current(executor, authority_roots))
        .flatten()
}

/// Every `Forall`/`Exists` node reachable from `roots`.
///
/// Shared with the finite-sort lane, which must enumerate exactly the nodes
/// this coverage check will later look for — deriving them by a second,
/// independent walk is how they drift apart.
pub(in crate::executor) fn quantifier_nodes_in(
    terms: &TermStore,
    roots: &[TermId],
) -> HashSet<TermId> {
    let mut found: HashSet<TermId> = HashSet::default();
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut pending = roots.to_vec();
    while let Some(term) = pending.pop() {
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                found.insert(term);
                pending.push(*body);
            }
            TermData::App(_, args) => pending.extend(args.iter().copied()),
            TermData::Not(inner) => pending.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                pending.push(*condition);
                pending.push(*then_term);
                pending.push(*else_term);
            }
            TermData::Let(bindings, body) => {
                pending.extend(bindings.iter().map(|(_, value)| *value));
                pending.push(*body);
            }
            _ => {}
        }
    }
    found
}

/// Check that the roots bound into a BV authority token contain exactly the
/// quantified obligations this refinement pass discharged. Ground siblings
/// are allowed because their SAT/model evidence is checked by the ordinary
/// emission funnel; any additional or missing quantifier prevents authority.
fn authority_roots_exactly_cover_bv_foralls(
    terms: &TermStore,
    roots: &[TermId],
    certified_foralls: &[TermId],
) -> bool {
    if roots.is_empty() || certified_foralls.is_empty() {
        return false;
    }
    let certified: HashSet<TermId> = certified_foralls.iter().copied().collect();
    if certified.len() != certified_foralls.len()
        || certified
            .iter()
            .any(|&term| !matches!(terms.get(term), TermData::Forall(..)))
    {
        return false;
    }

    let mut found: HashSet<TermId> = HashSet::default();
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut pending = roots.to_vec();
    while let Some(term) = pending.pop() {
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                found.insert(term);
                pending.push(*body);
            }
            TermData::App(_, args) => pending.extend(args.iter().copied()),
            TermData::Not(inner) => pending.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                pending.push(*condition);
                pending.push(*then_term);
                pending.push(*else_term);
            }
            TermData::Let(bindings, body) => {
                pending.extend(bindings.iter().map(|(_, value)| *value));
                pending.push(*body);
            }
            _ => {}
        }
    }
    found == certified
}

/// BV boundary candidate generator.
///
/// Given a bitvector width and optional constants from the formula body,
/// produces a set of "interesting" bitvector values for instantiation.
struct BvCandidateGenerator {
    width: u32,
    /// Constants extracted from the formula guard/body.
    body_constants: Vec<BigInt>,
}

impl BvCandidateGenerator {
    fn new(width: u32, body_constants: Vec<BigInt>) -> Self {
        Self {
            width,
            body_constants,
        }
    }

    /// Generate boundary candidates for a BV variable of given width.
    ///
    /// Always includes: 0, MAX (2^w - 1).
    /// Also includes: 1, MAX-1, and for each constant c found in the body:
    /// c-1, c, c+1 (all modulo 2^w).
    fn boundary_candidates(&self) -> Vec<BigInt> {
        let modulus = BigInt::from(1) << self.width;
        let max_val = &modulus - 1;
        let mut candidates: Vec<BigInt> = Vec::new();
        let mut seen: HashSet<BigInt> = HashSet::default();

        let mut add = |val: BigInt| {
            // Normalize to [0, 2^w)
            let normalized = ((val % &modulus) + &modulus) % &modulus;
            if seen.insert(normalized.clone()) {
                candidates.push(normalized);
            }
        };

        // Always: 0, 1, MAX-1, MAX
        add(BigInt::ZERO);
        add(BigInt::from(1));
        if self.width > 1 {
            add(&max_val - 1);
        }
        add(max_val);

        // For each constant in the body, generate c-1, c, c+1
        for c in &self.body_constants {
            add(c - 1);
            add(c.clone());
            add(c + 1);
        }

        candidates
    }

    /// Generate model-derived candidates: model value +/- 1.
    fn model_neighbors(&self, model_val: &BigInt) -> Vec<BigInt> {
        let modulus = BigInt::from(1) << self.width;
        let mut result = Vec::new();
        let mut seen: HashSet<BigInt> = HashSet::default();

        let mut add = |val: BigInt| {
            let normalized = ((val % &modulus) + &modulus) % &modulus;
            if seen.insert(normalized.clone()) {
                result.push(normalized);
            }
        };

        add(model_val.clone());
        add(model_val - 1);
        add(model_val + 1);

        result
    }
}

/// Deterministic BV literal candidates for a checked false-instance search.
///
/// Candidate synthesis is completeness-only: callers must independently
/// evaluate or solve every substituted instance before it can authorize a
/// verdict. Keeping this helper beside BV-MBQI ensures the exact-source
/// closed-forall lane uses the same width-normalized boundaries and
/// body-constant neighbours as ordinary BV instantiation.
pub(in crate::executor) fn synthesize_bv_refutation_candidates(
    terms: &TermStore,
    body: TermId,
    width: u32,
) -> Vec<BigInt> {
    let body_constants = extract_bv_body_constants(terms, body, width);
    BvCandidateGenerator::new(width, body_constants).boundary_candidates()
}

/// Analyze a quantifier body to extract BV constants used in comparisons.
///
/// Traverses the body looking for BV comparison operators (bvult, bvule, bvslt,
/// bvsle, bvugt, bvuge, bvsgt, bvsge) and extracts constant operands. These
/// constants are "interesting" boundary values for instantiation.
fn extract_bv_body_constants(terms: &TermStore, body: TermId, width: u32) -> Vec<BigInt> {
    let mut constants: Vec<BigInt> = Vec::new();
    let mut visited: HashSet<TermId> = HashSet::default();
    extract_bv_constants_recursive(terms, body, width, &mut constants, &mut visited);
    constants
}

/// Red zone size for `stacker::maybe_grow` in BV constant extraction (#8570).
const BV_EXTRACT_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for BV constant extraction recursion.
const BV_EXTRACT_STACK_SIZE: usize = 1024 * 1024;

fn extract_bv_constants_recursive(
    terms: &TermStore,
    term: TermId,
    width: u32,
    constants: &mut Vec<BigInt>,
    visited: &mut HashSet<TermId>,
) {
    stacker::maybe_grow(BV_EXTRACT_STACK_RED_ZONE, BV_EXTRACT_STACK_SIZE, || {
        if !visited.insert(term) {
            return;
        }

        match terms.get(term) {
            TermData::Const(ay_core::term::Constant::BitVec {
                value: val,
                width: w,
            }) if *w == width => {
                constants.push(val.clone());
            }
            TermData::App(sym, args) => {
                // Check if this is a BV comparison or arithmetic op — extract constant args
                let is_bv_op = matches!(sym, Symbol::Named(name)
                    if name == "bvult" || name == "bvule" || name == "bvslt" || name == "bvsle"
                    || name == "bvugt" || name == "bvuge" || name == "bvsgt" || name == "bvsge"
                    || name == "bvadd" || name == "bvsub" || name == "=" || name == "distinct"
                );
                if is_bv_op {
                    for &arg in args {
                        if let TermData::Const(ay_core::term::Constant::BitVec {
                            value: val,
                            width: w,
                        }) = terms.get(arg)
                        {
                            if *w == width {
                                constants.push(val.clone());
                            }
                        }
                    }
                }
                // Recurse into all subterms
                for &arg in args {
                    extract_bv_constants_recursive(terms, arg, width, constants, visited);
                }
            }
            TermData::Not(inner) => {
                extract_bv_constants_recursive(terms, *inner, width, constants, visited);
            }
            TermData::Ite(c, t, e) => {
                extract_bv_constants_recursive(terms, *c, width, constants, visited);
                extract_bv_constants_recursive(terms, *t, width, constants, visited);
                extract_bv_constants_recursive(terms, *e, width, constants, visited);
            }
            TermData::Forall(_, inner, _) | TermData::Exists(_, inner, _) => {
                extract_bv_constants_recursive(terms, *inner, width, constants, visited);
            }
            _ => {}
        }
    }); // stacker::maybe_grow
}

/// Detect if a formula body is a guarded pattern: `guard => body`.
///
/// Returns `Some((guard, body))` if the term is an implication (represented as
/// `(or (not guard) body)` or `(=> guard body)`).
fn detect_guard_pattern(terms: &TermStore, body: TermId) -> Option<(TermId, TermId)> {
    match terms.get(body) {
        TermData::App(Symbol::Named(name), args) if name == "=>" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        // Implication encoded as (or (not guard) body)
        TermData::App(Symbol::Named(name), args) if name == "or" && args.len() == 2 => {
            if let TermData::Not(guard) = terms.get(args[0]) {
                Some((*guard, args[1]))
            } else if let TermData::Not(guard) = terms.get(args[1]) {
                Some((*guard, args[0]))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Check if all bound variables in a forall have BV sort.
fn all_vars_are_bv(vars: &[(String, Sort)]) -> bool {
    vars.iter().all(|(_, sort)| matches!(sort, Sort::BitVec(_)))
}

impl Executor {
    /// Prove one BV `forall` from the current ground consequence set.
    ///
    /// Skolemize the binders and check `G ∧ ¬body[skolems]`, where `G` is the
    /// quantifier-free slice of the current assertions. A sealed strict-proof
    /// UNSAT decision proves `G ⊨ forall binders. body`, over the full BV domain.
    ///
    /// SAT is intentionally non-authoritative here. The old implementation
    /// transported its nested model to extract a counterexample, but that model
    /// was not bound to the enclosing query. SAT therefore falls through to the
    /// ordinary, sound boundary/exhaustive enumeration path.
    fn bv_symbolic_entailment_check(
        &mut self,
        vars: &[(String, Sort)],
        body: TermId,
        fallback_category: LogicCategory,
    ) -> BvForallCheck {
        // A nested quantifier would survive into the "ground" negation and the
        // ground solve cannot decide it.
        if crate::ematching::contains_quantifier(&self.ctx.terms, body) {
            return BvForallCheck::Unknown;
        }

        // Skolemize the binders to fresh, unconstrained constants.
        let mut subst: HashMap<String, TermId> = HashMap::default();
        for (name, sort) in vars {
            let fresh = self
                .ctx
                .terms
                .mk_fresh_var(&format!("bvmbqi!{name}"), sort.clone());
            subst.insert(name.clone(), fresh);
        }
        let skolem_body = subst_vars(&mut self.ctx.terms, body, &subst);
        let neg = self.ctx.terms.mk_not(skolem_body);

        // PREMISE: the GROUND slice of the current assertions.
        //
        // Proving `G AND NOT body[skolem]` UNSAT establishes `G |= forall x.
        // body` — an ENTAILMENT, not a model-relative fact. That distinction is
        // what makes the resulting Sat cashable: the model-relative alternative
        // (pin each symbol to its value in M) is cheaper to refute, but it only
        // shows the forall holds under M, so it needs M to have passed the
        // validation gate — and at this point validation is still DEFERRED
        // (measured: `validated=false defer=true` at the Sat return). The
        // entailment form sidesteps the model entirely.
        //
        // Ground instances added by earlier rounds/E-matching may appear in G.
        // That is sound: each is entailed by an asserted universal, so any model
        // of `G AND (all foralls)` still satisfies the original assertions.
        let assertions = self.ctx.assertions.clone();
        let mut sub_assertions: Vec<TermId> = Vec::with_capacity(assertions.len() + 1);
        for a in assertions {
            if !crate::ematching::contains_quantifier(&self.ctx.terms, a) {
                sub_assertions.push(a);
            }
        }
        sub_assertions.push(neg);

        // Only a strict, sealed UNSAT decision establishes the entailment. The
        // former in-place solve also extracted a SAT counterexample model, but
        // that model had no checked transport back into the enclosing query.
        // A SAT/Unknown probe therefore falls through to sound enumeration.
        if self
            .checked_ground_solve(sub_assertions.clone(), fallback_category, 2_000)
            .is_some_and(|decision| match decision {
                CheckedGroundDecision::Unsat(checked) => checked.consume(self, &sub_assertions),
                CheckedGroundDecision::Sat(_) => false,
            })
        {
            BvForallCheck::Holds
        } else {
            BvForallCheck::Unknown
        }
    }

    pub(in crate::executor) fn try_bv_mbqi_refinement(
        &mut self,
        bv_quantifiers: &[TermId],
        category: LogicCategory,
        authority_roots: &[TermId],
    ) -> Option<Result<SolveResult>> {
        if bv_quantifiers.is_empty() {
            return None;
        }

        let mut seen_instantiations: HashSet<TermId> = HashSet::default();
        let mut refinement_provenance: Vec<crate::ematching::ForallInstantiationProvenance> =
            Vec::new();

        // Empty model for the model-less refute-only mode below: evaluating a
        // ground instance against it constant-folds fully-interpreted subterms
        // and fails closed (`EvalValue::Unknown`) wherever a value would have
        // to come from a model.
        let empty_model = super::model::Model::empty();

        for _round in 0..MAX_BV_MBQI_ROUNDS {
            // MODEL-LESS REFUTE-ONLY MODE (#broadcast-vacuity empty-ground):
            // when the ground slice of the problem is empty (e.g. a lone
            // quantified axiom, as in deductive-checks's broadcast-vacuity precheck)
            // the ground solve returns Sat without producing a model, and this
            // loop used to bail out immediately — leaving even a forall that a
            // boundary candidate like 0 instantly falsifies (`forall x:BV32.
            // bvslt (bvmul x x) 0`) undecided. Boundary candidates do not need
            // a model, so keep going: enumerate them, CONSTANT-FOLD each
            // ground instance (empty model ⇒ every verdict is model-free), and
            // add the instances that fold to a definite `false`.
            //
            // SOUNDNESS: the caller (`try_mbqi_refinement`, gated by
            // `forall_ids_in_conjunctive_position` + `is_no_mbqi` at the
            // result_mapping call site) only passes conjunctive-position
            // foralls, so every added instance is ENTAILED by an asserted
            // universal — asserting it can never turn a satisfiable problem
            // unsatisfiable. The subsequent re-solve produces the verdict; this
            // mode grants NO new SAT-acceptance authority: the exhaustive-Sat
            // conclusion below is explicitly disabled while model-less (a
            // constant-folded "all candidates true" pass is not consulted).
            let model_less = self.last_model.is_none();

            let mut new_instantiations: Vec<TermId> = Vec::new();
            let mut all_satisfied = true;
            // SOUNDNESS: a forall is only PROVEN by instantiation when the
            // candidate set covers its ENTIRE domain. The heuristic candidate
            // set (boundary values + model neighbors) does not, so an
            // "all candidates satisfy" verdict is not a proof — returning Sat
            // from it is unsound (#bug04: `(exists q0 (forall q2 (bvslt q0
            // (bvneg q2))))` is UNSAT — `bvneg` reaches the signed min so no q0
            // works — but the sample missed that witness). Track whether EVERY
            // forall here was enumerated EXHAUSTIVELY; only an exhaustive,
            // counterexample-free pass may conclude Sat.
            let mut all_exhaustive = true;
            // Every forall discharged by the SYMBOLIC entailment check (as
            // opposed to enumeration, which is model-relative). Only an
            // all-entailed pass may emit Sat upstream.
            let mut all_entailed = true;

            for &quant in bv_quantifiers {
                let (vars, body) = match self.ctx.terms.get(quant) {
                    TermData::Forall(v, b, _) => (v.clone(), *b),
                    _ => {
                        // Not a forall we can analyse: it is NOT proven, so the
                        // pass must not claim to have covered every quantifier.
                        // (Before the symbolic path below, a wide binder always
                        // cleared `all_exhaustive` anyway, so these skips could
                        // not reach the Sat conclusion. Now that a proof is
                        // reachable, every unanalysed quantifier must fail
                        // closed explicitly.)
                        all_exhaustive = false;
                        all_entailed = false;
                        continue;
                    }
                };

                if vars.is_empty() || !all_vars_are_bv(&vars) {
                    all_exhaustive = false;
                    all_entailed = false;
                    continue;
                }

                // SYMBOLIC PATH. Enumeration proves a forall only by visiting
                // every value of every binder, so it is confined to widths
                // <= BV_EXHAUSTIVE_MAX_WIDTH; a width-32 binder is 4.3 billion
                // values and one SMT-LIB benchmark binds width 2501. Measured on
                // the official Single-Query Bitvec selection, 51 of 92 binders
                // across the fast-bailing files exceed the width cap, and raising
                // the cartesian cap 64x (2^16 -> 2^22) solved ZERO additional
                // files — the per-binder width is the wall, and no cap reaches it.
                //
                // So when enumeration CANNOT be exhaustive, decide the forall
                // with one ground solve instead. This is a gate on the actual
                // reason (enumeration is infeasible here) rather than on a tuned
                // size, and it is self-adapting: narrow binders keep the cheap
                // enumeration, which needs no sub-solve to prove anything.
                let enumerable = vars.iter().all(|(_, sort)| {
                    matches!(sort, Sort::BitVec(bv) if bv.width <= BV_EXHAUSTIVE_MAX_WIDTH)
                }) && vars
                    .iter()
                    .map(|(_, sort)| match sort {
                        Sort::BitVec(bv) => 1u128 << bv.width,
                        _ => u128::MAX,
                    })
                    .try_fold(1u128, |acc, d| acc.checked_mul(d))
                    .is_some_and(|total| total <= u128::from(BV_EXHAUSTIVE_TOTAL_CAP));

                if !enumerable && !model_less {
                    match self.bv_symbolic_entailment_check(&vars, body, category) {
                        BvForallCheck::Holds => {
                            // Proven over the binders' entire domain — the same
                            // authority an exhaustive enumeration would carry.
                            continue;
                        }
                        BvForallCheck::Unknown => {
                            // Fall through to the heuristic enumeration, which
                            // can still refute even though it cannot prove.
                        }
                    }
                }

                // Reaching the enumeration path means this forall was not
                // discharged by entailment (it was enumerable, model-less, or
                // the sub-solve was undecided), so the pass loses the proof
                // certificate even if enumeration goes on to prove it
                // model-relatively.
                all_entailed = false;

                // Build candidate generators per variable
                let mut generators: Vec<BvCandidateGenerator> = Vec::with_capacity(vars.len());
                for (_, sort) in &vars {
                    if let Sort::BitVec(bv_sort) = sort {
                        let body_constants =
                            extract_bv_body_constants(&self.ctx.terms, body, bv_sort.width);
                        // Also extract guard-specific constants
                        let guard_constants =
                            if let Some((guard, _)) = detect_guard_pattern(&self.ctx.terms, body) {
                                extract_bv_body_constants(&self.ctx.terms, guard, bv_sort.width)
                            } else {
                                Vec::new()
                            };
                        let mut all_constants = body_constants;
                        all_constants.extend(guard_constants);
                        generators.push(BvCandidateGenerator::new(bv_sort.width, all_constants));
                    }
                }

                // Build candidate term IDs per variable
                let mut candidates_per_var: Vec<Vec<TermId>> = Vec::with_capacity(vars.len());
                // This forall is exhaustively enumerated only if every binder's
                // candidate list covers its full 2^width domain.
                let mut quant_exhaustive = true;
                for (i, (_, sort)) in vars.iter().enumerate() {
                    let Sort::BitVec(bv_sort) = sort else {
                        continue;
                    };
                    let width = bv_sort.width;

                    // Small domains: enumerate EXHAUSTIVELY (all 2^width values)
                    // so an "all satisfy" verdict actually proves the forall. The
                    // `MAX_BV_CANDIDATES` budget below still bounds the cartesian
                    // product across binders, so a large product simply fails the
                    // exhaustiveness check and never returns Sat.
                    if width <= BV_EXHAUSTIVE_MAX_WIDTH {
                        let domain = 1u64 << width;
                        let term_candidates: Vec<TermId> = (0..domain)
                            .map(|v| self.ctx.terms.mk_bitvec(BigInt::from(v), width))
                            .collect();
                        candidates_per_var.push(term_candidates);
                        continue;
                    }
                    quant_exhaustive = false;

                    // Start with boundary candidates
                    let mut candidate_values: Vec<BigInt> = generators[i].boundary_candidates();

                    // Add model value + neighbors
                    if let Some(ref model) = self.last_model {
                        if let Some(ref bv_model) = model.bv_model {
                            for (&term_id, val) in &bv_model.values {
                                if self.ctx.terms.sort(term_id)
                                    == &Sort::BitVec(BitVecSort::new(width))
                                {
                                    let neighbors = generators[i].model_neighbors(val);
                                    candidate_values.extend(neighbors);
                                }
                            }
                        }
                    }

                    // Deduplicate and convert to TermIds
                    let mut seen_vals: HashSet<BigInt> = HashSet::default();
                    let mut term_candidates: Vec<TermId> = Vec::new();
                    for val in candidate_values {
                        if seen_vals.insert(val.clone())
                            && term_candidates.len() < MAX_BV_CANDIDATES
                        {
                            term_candidates.push(self.ctx.terms.mk_bitvec(val, width));
                        }
                    }

                    if term_candidates.is_empty() {
                        // Fallback: at least 0 and MAX
                        term_candidates.push(self.ctx.terms.mk_bitvec(BigInt::ZERO, width));
                        let max_val = (BigInt::from(1) << width) - 1;
                        term_candidates.push(self.ctx.terms.mk_bitvec(max_val, width));
                    }

                    candidates_per_var.push(term_candidates);
                }

                if candidates_per_var.len() != vars.len() {
                    all_satisfied = false;
                    all_exhaustive = false;
                    continue;
                }

                all_exhaustive &= quant_exhaustive;

                // When every binder is enumerated exhaustively and the cartesian
                // product is within the cap, raise the per-forall budget to the
                // full product so a genuinely-true forall completes (and a true
                // forall is then PROVEN, while a counterexample is still hit).
                // Otherwise keep the heuristic budget; the enumeration then trips
                // the budget, marks `all_satisfied = false`, and cannot conclude
                // Sat — fail-closed.
                let total_combos: u128 =
                    candidates_per_var.iter().map(|c| c.len() as u128).product();
                let enum_budget =
                    if quant_exhaustive && total_combos <= BV_EXHAUSTIVE_TOTAL_CAP as u128 {
                        total_combos as usize
                    } else {
                        MAX_BV_CANDIDATES
                    };

                let var_names: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();

                // Enumerate substitutions (cartesian product with budget)
                let mut indices: Vec<usize> = vec![0; vars.len()];
                let mut checked = 0usize;

                loop {
                    if checked >= enum_budget {
                        all_satisfied = false;
                        break;
                    }

                    // Build binding
                    let binding: Vec<TermId> = indices
                        .iter()
                        .enumerate()
                        .map(|(var_idx, &term_idx)| candidates_per_var[var_idx][term_idx])
                        .collect();

                    // Create ground instance
                    let subst_map: HashMap<String, TermId> = var_names
                        .iter()
                        .zip(binding.iter())
                        .map(|(name, &t)| (name.clone(), t))
                        .collect();
                    let ground_body = subst_vars(&mut self.ctx.terms, body, &subst_map);

                    if !self.observe_bv_mbqi_instance(
                        quant,
                        body,
                        &subst_map,
                        &binding,
                        ground_body,
                        &empty_model,
                        (
                            &mut seen_instantiations,
                            &mut new_instantiations,
                            &mut refinement_provenance,
                        ),
                    ) {
                        all_satisfied = false;
                    }

                    checked += 1;

                    // Advance to next combination
                    let mut carry = true;
                    for i in (0..vars.len()).rev() {
                        if carry {
                            indices[i] += 1;
                            if indices[i] < candidates_per_var[i].len() {
                                carry = false;
                            } else {
                                indices[i] = 0;
                            }
                        }
                    }
                    if carry {
                        break;
                    }
                }
            }

            if new_instantiations.is_empty() {
                // Only an EXHAUSTIVE, counterexample-free pass proves the
                // forall(s) and may conclude Sat. A heuristic pass that found no
                // counterexample proves nothing — fall through (the caller's
                // fail-closed path turns this into Unknown, not a wrong Sat).
                // Model-less rounds are additionally REFUTE-ONLY: without a
                // ground model there is no validated ground Sat to extend, so
                // even an exhaustive constant-folded pass must not conclude Sat
                // here (fail-closed; no new SAT-acceptance authority).
                // Both proof routes cover the complete binder domain. Symbolic
                // entailment has no candidate set; exhaustive enumeration's
                // candidate set is the carrier itself. Preserve either proof
                // across assertion restoration, while sampled enumeration and
                // model-less passes remain fail-closed.
                let full_domain_proof = all_satisfied
                    && (all_entailed || all_exhaustive)
                    && !model_less
                    && authority_roots_exactly_cover_bv_foralls(
                        &self.ctx.terms,
                        authority_roots,
                        bv_quantifiers,
                    );
                let evidence = full_domain_proof
                    .then(|| CheckedBvFullDomainSatAuthority::for_current(self, authority_roots))
                    .flatten();
                self.bv_quantifier_full_domain_proof = evidence.is_some();
                self.bv_quantifier_full_domain_pending_evidence = evidence;
                if all_satisfied && all_exhaustive && !model_less && full_domain_proof {
                    return Some(Ok(SolveResult::Sat));
                }
                break;
            }

            // Add counterexample instantiations and re-solve
            for inst in &new_instantiations {
                self.ctx.assertions.push(*inst);
            }

            // Re-detect the logic category over the AUGMENTED assertion set
            // (#broadcast-vacuity misroute): when the original ground slice was
            // empty (or BV-free), the caller's `category` was detected without
            // any BV ground term — e.g. `QfUf`, whose solver treats `bvmul` /
            // `bvslt` as uninterpreted symbols and answers Sat on an instance
            // that CONSTANT-FOLDS to false, silently discarding the refutation.
            // The pushed BV instances are ground, so detection over the current
            // assertions routes the re-solve to a solver that actually
            // interprets them; `Other` falls back to the caller's category
            // (same pattern as `closed_universal_validity_precheck_inner`).
            let (detected_category, _) = self.detect_logic_category(&self.ctx.assertions);
            let re_category = if matches!(detected_category, LogicCategory::Other) {
                category
            } else {
                detected_category
            };
            let re_result = self.solve_for_category(re_category);
            match re_result {
                Ok(SolveResult::Sat) => {
                    continue;
                }
                Ok(SolveResult::Unsat(_)) => {
                    // Publish instance provenance for the refutation being
                    // returned, AFTER the re-solve: a nested solve clears the
                    // preprocessing proof records, so publishing earlier
                    // loses them. The ground re-solve decided against these
                    // instances, so the proof layer must be able to derive
                    // each from its authored quantifier — same UNSAT-exit
                    // contract as the generic MBQI path.
                    self.mbqi_refinement_instance_records = refinement_provenance.clone();
                    return Some(Ok(SolveResult::unsat()));
                }
                other => {
                    return Some(other);
                }
            }
        }

        None
    }
}

/// Partition quantifiers into BV-only and mixed/non-BV groups.
///
/// A quantifier is "BV-only" if all its bound variables have BV sort.
/// Returns `(bv_quantifiers, other_quantifiers)`.
pub(in crate::executor) fn partition_bv_quantifiers(
    terms: &TermStore,
    quantifiers: &[TermId],
) -> (Vec<TermId>, Vec<TermId>) {
    let mut bv_quants = Vec::new();
    let mut other_quants = Vec::new();

    for &q in quantifiers {
        match terms.get(q) {
            TermData::Forall(vars, _, _) if all_vars_are_bv(vars) => {
                bv_quants.push(q);
            }
            _ => {
                other_quants.push(q);
            }
        }
    }

    (bv_quants, other_quants)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bv_candidate_generator_boundary_values_8bit() {
        let cand_gen = BvCandidateGenerator::new(8, vec![]);
        let candidates = cand_gen.boundary_candidates();
        // Should contain 0, 1, 254, 255
        assert!(candidates.contains(&BigInt::ZERO));
        assert!(candidates.contains(&BigInt::from(1)));
        assert!(candidates.contains(&BigInt::from(254)));
        assert!(candidates.contains(&BigInt::from(255)));
    }

    #[test]
    fn test_bv_candidate_generator_with_body_constants() {
        let cand_gen = BvCandidateGenerator::new(8, vec![BigInt::from(100)]);
        let candidates = cand_gen.boundary_candidates();
        // Should contain boundary values plus 99, 100, 101
        assert!(candidates.contains(&BigInt::from(99)));
        assert!(candidates.contains(&BigInt::from(100)));
        assert!(candidates.contains(&BigInt::from(101)));
    }

    #[test]
    fn test_bv_candidate_generator_wrapping() {
        // Constant 0 should wrap: c-1 = 255 (for 8-bit)
        let cand_gen = BvCandidateGenerator::new(8, vec![BigInt::ZERO]);
        let candidates = cand_gen.boundary_candidates();
        assert!(candidates.contains(&BigInt::from(255)));
    }

    #[test]
    fn test_bv_candidate_generator_model_neighbors() {
        let cand_gen = BvCandidateGenerator::new(8, vec![]);
        let neighbors = cand_gen.model_neighbors(&BigInt::from(42));
        assert!(neighbors.contains(&BigInt::from(41)));
        assert!(neighbors.contains(&BigInt::from(42)));
        assert!(neighbors.contains(&BigInt::from(43)));
    }

    #[test]
    fn test_bv_candidate_generator_32bit() {
        let cand_gen = BvCandidateGenerator::new(32, vec![BigInt::from(0x1000u32)]);
        let candidates = cand_gen.boundary_candidates();
        let max_32 = (BigInt::from(1u64) << 32) - 1;
        assert!(candidates.contains(&BigInt::ZERO));
        assert!(candidates.contains(&max_32));
        assert!(candidates.contains(&BigInt::from(0x1000u32)));
        assert!(candidates.contains(&BigInt::from(0xFFFu32)));
        assert!(candidates.contains(&BigInt::from(0x1001u32)));
    }

    #[test]
    fn test_all_vars_are_bv() {
        let vars_bv = vec![
            ("x".to_string(), Sort::bitvec(8)),
            ("y".to_string(), Sort::bitvec(16)),
        ];
        assert!(all_vars_are_bv(&vars_bv));

        let vars_mixed = vec![
            ("x".to_string(), Sort::bitvec(8)),
            ("y".to_string(), Sort::Int),
        ];
        assert!(!all_vars_are_bv(&vars_mixed));

        let vars_int = vec![("x".to_string(), Sort::Int)];
        assert!(!all_vars_are_bv(&vars_int));
    }
}
