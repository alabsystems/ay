// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Insert-and-remap surgery for trust-bearing proofs whose RESOLUTION
//! SKELETON is sound: instead of re-proving the contradiction from scratch
//! (the full-rebuild passes in `proof_original_rebuild`), this pass keeps the
//! exported derivation and surgically replaces each defective site with a
//! certified derivation, remapping the downstream consumers onto the new
//! steps.
//!
//! Four site classes are repaired (the "n-ary distinct + Int trichotomy"
//! trust class plus the normalized-assume print defects, which need NO trust
//! anchor: a proof whose every step is checkable can still be invalid because
//! a preprocessing-normalized `assume` prints unlike the problem premise):
//!
//! 1. **Int trichotomy trust steps** — `(cl (or (= x y) (<= x (+ y (- 1)))
//!    (<= (+ y 1) x))) :rule trust` plus its `or`-split consumer. Replaced by
//!    `la_disequality ⊢ (cl (or (= x y) (not (<= x y)) (not (<= y x))))`, an
//!    `or` split, and two `[1, 1]` `la_generic` Int-strengthening bridges
//!    (each independently re-verified by `verify_farkas_conflict_lits_full`,
//!    fail-closed), closed by a resolution chain that reproduces the
//!    3-literal strengthened clause. The trust step's unit `(cl (or ...))`
//!    conclusion is NOT re-derived — the `or`-split consumer is REWIRED to
//!    consume the derived 3-literal clause directly, and the trust step +
//!    split are dropped.
//!
//! 2. **N-ary `distinct` assumes** — the exported proof assumes the EXPANDED
//!    `(and (not (= x1 x2)) ...)` form, which no checker can match to the
//!    problem's `(distinct x1 .. xn)` premise. Replaced by an assume of the
//!    raw n-ary `distinct` bridged via `distinct_elim` (pairwise `i < j`
//!    conjunct order) + `equiv_pos2` + resolution down to the conjunction,
//!    with each downstream `and_pos`/resolution unit extraction re-derived
//!    against the bridged conjunction.
//!
//! 3. **Arithmetic-normalized `and` assumes** — a bounds assertion like
//!    `(and .. (>= a 0) ..)` is exported with normalized conjuncts
//!    (`(<= 0 a)`), again unmatchable to the problem premise. Replaced by an
//!    assume of the RAW surface conjunction, with each unit extraction
//!    re-derived from the raw conjunct and bridged to the canonical literal
//!    by a re-verified `[1, 1]` `la_generic` orientation lemma (the class-2
//!    raw-assume pattern).
//!
//! 4. **Arithmetic-normalized bound-literal assumes** — a plain bound like
//!    `(> a 5)` exported as the canonical `(< 5 a)`. Replaced by an assume of
//!    the raw surface literal bridged to the canonical unit by a re-verified
//!    `[1, 1]` `la_generic` orientation lemma, with every consumer remapped
//!    onto the derived unit. Skipped when the surviving surface overrides
//!    (ite-lift class) already print the literal like the file.
//!
//! The pass rebuilds the step list in one pass (assumes hoisted first, as
//! Alethe requires), remapping every kept step's premises through an
//! old-id → new-id map. It is fail-closed at every site: any unrecognized
//! trust step, unbridgeable assume, dangling premise, or failed certificate
//! verification leaves the proof byte-identical.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{
    AletheRule, FarkasAnnotation, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TheoryLemmaKind,
    TheoryLit,
};
use ay_frontend::command::{Index as FrontendIndex, Term as FrontendTerm};

use super::proof_euf_lemma::EufLemmaPlan;
use super::proof_surface_syntax::strip_frontend_annotations;
use super::Executor;

/// Whether two terms are equal modulo binary-equality argument orientation
/// (recursively). Carcara's default mode tolerates exactly this difference
/// ("implicit reordering of equalities") everywhere, including `assume`
/// premise matching.
fn eq_flip_equivalent(terms: &ay_core::TermStore, a: TermId, b: TermId) -> bool {
    if a == b {
        return true;
    }
    match (terms.get(a), terms.get(b)) {
        (TermData::Not(x), TermData::Not(y)) => {
            let (x, y) = (*x, *y);
            eq_flip_equivalent(terms, x, y)
        }
        (TermData::App(sa, xa), TermData::App(sb, xb)) => {
            if sa != sb || xa.len() != xb.len() {
                return false;
            }
            let (sa, xa, xb) = (sa.clone(), xa.clone(), xb.clone());
            let straight = xa
                .iter()
                .zip(xb.iter())
                .all(|(&x, &y)| eq_flip_equivalent(terms, x, y));
            if straight {
                return true;
            }
            matches!(sa, Symbol::Named(ref n) if n == "=")
                && xa.len() == 2
                && eq_flip_equivalent(terms, xa[0], xb[1])
                && eq_flip_equivalent(terms, xa[1], xb[0])
        }
        _ => false,
    }
}

/// Whether `raw` and `canon` are top-level binary-equality orientation
/// flips of each other, possibly under exactly one matching `not` (the
/// bridgeable per-literal shape of [`AndDistinctKind::OrPerm`]): both
/// `(= a b)` / `(= b a)` and `(not (= a b))` / `(not (= b a))`. Exact
/// equality does NOT qualify (callers handle it separately).
fn eq_top_flip(terms: &ay_core::TermStore, raw: TermId, canon: TermId) -> bool {
    let (raw, canon) = match (terms.get(raw), terms.get(canon)) {
        (TermData::Not(x), TermData::Not(y)) => (*x, *y),
        _ => (raw, canon),
    };
    match (terms.get(raw), terms.get(canon)) {
        (TermData::App(sa, xa), TermData::App(sb, xb)) => {
            matches!(sa, Symbol::Named(n) if n == "=")
                && sa == sb
                && xa.len() == 2
                && xb.len() == 2
                && xa[0] == xb[1]
                && xa[1] == xb[0]
        }
        _ => false,
    }
}

/// Match a raw-interned `or`-conjunct against its canonical export when the
/// canonicalization REORDERED the disjuncts and/or FLIPPED binary-equality
/// orientations (#C2b). Returns the `(raw disjunct, canonical disjunct)`
/// pairing over the UNIQUE raw disjuncts in first-occurrence order — an
/// injective alignment where each pair is either identical or a top-level
/// orientation flip — or `None` when the two terms do not align (fail-open:
/// the caller keeps the assume as-is).
fn or_perm_lits(
    terms: &ay_core::TermStore,
    raw: TermId,
    canon: TermId,
) -> Option<Vec<(TermId, TermId)>> {
    if raw == canon {
        return None;
    }
    let (TermData::App(sr, rdis), TermData::App(sc, cdis)) = (terms.get(raw), terms.get(canon))
    else {
        return None;
    };
    if !matches!(sr, Symbol::Named(n) if n == "or") || sr != sc {
        return None;
    }
    let (rdis, cdis) = (rdis.clone(), cdis.clone());
    // The canonical export DEDUPLICATES repeated disjuncts: align the
    // UNIQUE raw disjuncts (first-occurrence order) against the canonical
    // list (the emitter contracts the raw duplicates away first).
    let mut uniq: Vec<TermId> = Vec::with_capacity(rdis.len());
    for &r in &rdis {
        if !uniq.contains(&r) {
            uniq.push(r);
        }
    }
    if uniq.len() != cdis.len() {
        return None;
    }
    let mut used = vec![false; cdis.len()];
    let mut lits: Vec<(TermId, TermId)> = Vec::with_capacity(uniq.len());
    for &r in &uniq {
        // Exact matches first, orientation flips second: equal raw
        // disjuncts must pair with equal canonical disjuncts, so the
        // preference order cannot mispair an exact literal onto a flip
        // slot another literal needs.
        let slot = cdis
            .iter()
            .enumerate()
            .position(|(j, &c)| !used[j] && c == r)
            .or_else(|| {
                cdis.iter()
                    .enumerate()
                    .position(|(j, &c)| !used[j] && eq_top_flip(terms, r, c))
            })?;
        used[slot] = true;
        lits.push((r, cdis[slot]));
    }
    Some(lits)
}

/// Fully expand `let` bindings in a surface term (SMT-LIB parallel-binding
/// semantics: binding values are expanded in the OUTER environment). Returns
/// `None` fail-closed on any binder that could capture (`forall`/`exists`/
/// `lambda`/`match` under a non-empty environment) so no incorrect
/// substitution is ever produced.
fn expand_surface_lets(
    term: &FrontendTerm,
    env: &std::collections::HashMap<String, FrontendTerm>,
) -> Option<FrontendTerm> {
    match term {
        FrontendTerm::Let(bindings, body) => {
            let mut inner = env.clone();
            for (name, value) in bindings {
                let expanded = expand_surface_lets(value, env)?;
                inner.insert(name.clone(), expanded);
            }
            expand_surface_lets(body, &inner)
        }
        FrontendTerm::Symbol(name) => Some(match env.get(name) {
            Some(bound) => bound.clone(),
            None => term.clone(),
        }),
        FrontendTerm::App(head, args) => {
            let args = args
                .iter()
                .map(|a| expand_surface_lets(a, env))
                .collect::<Option<Vec<_>>>()?;
            Some(FrontendTerm::App(head.clone(), args))
        }
        FrontendTerm::IndexedApp(name, indices, args) => {
            let args = args
                .iter()
                .map(|arg| expand_surface_lets(arg, env))
                .collect::<Option<Vec<_>>>()?;
            Some(FrontendTerm::IndexedApp(
                name.clone(),
                indices.clone(),
                args,
            ))
        }
        FrontendTerm::QualifiedApp(identifier, sort, args) => {
            let args = args
                .iter()
                .map(|arg| expand_surface_lets(arg, env))
                .collect::<Option<Vec<_>>>()?;
            Some(FrontendTerm::QualifiedApp(
                identifier.clone(),
                sort.clone(),
                args,
            ))
        }
        FrontendTerm::Annotated(inner, notes) => {
            let inner = expand_surface_lets(inner, env)?;
            Some(FrontendTerm::Annotated(Box::new(inner), notes.clone()))
        }
        FrontendTerm::Const(_) => Some(term.clone()),
        _ => {
            // Binders (and any future variant) under an active environment
            // could capture: fail closed. Without bindings in scope the term
            // needs no expansion.
            env.is_empty().then(|| term.clone())
        }
    }
}

#[cfg(test)]
mod surface_let_tests {
    use super::*;

    #[test]
    fn expansion_descends_into_structured_indexed_terms() {
        let zero = FrontendTerm::IndexedApp(
            "bv0".to_string(),
            vec![FrontendIndex::Numeral("8".to_string())],
            Vec::new(),
        );
        let term = FrontendTerm::Let(
            vec![("x".to_string(), zero.clone())],
            Box::new(FrontendTerm::App(
                "=".to_string(),
                vec![
                    FrontendTerm::Symbol("x".to_string()),
                    FrontendTerm::IndexedApp(
                        "bv1".to_string(),
                        vec![FrontendIndex::Numeral("8".to_string())],
                        Vec::new(),
                    ),
                ],
            )),
        );
        let expanded = expand_surface_lets(&term, &std::collections::HashMap::new())
            .expect("binder-free indexed term expands");
        assert!(matches!(
            expanded,
            FrontendTerm::App(ref op, ref args)
                if op == "=" && args.first() == Some(&zero)
        ));
    }

    #[test]
    fn raw_intern_accepts_structured_decimal_bitvector_literal() {
        let mut executor = Executor::new();
        let literal = FrontendTerm::IndexedApp(
            "bv3".to_string(),
            vec![FrontendIndex::Numeral("4".to_string())],
            Vec::new(),
        );
        let raw = executor
            .raw_intern_surface(&literal)
            .expect("structured decimal bitvector literal interns");
        assert_eq!(executor.ctx.terms.sort(raw), &Sort::bitvec(4));

        let ordinary = FrontendTerm::Symbol("(_ bv3 4)".to_string());
        assert!(executor.raw_intern_surface(&ordinary).is_none());

        let character = FrontendTerm::IndexedApp(
            "Char".to_string(),
            vec![FrontendIndex::Numeral("65".to_string())],
            Vec::new(),
        );
        assert!(executor.raw_intern_surface(&character).is_none());
    }
}

fn atom_of(terms: &ay_core::TermStore, lit: TermId) -> TermId {
    match terms.get(lit) {
        TermData::Not(inner) => *inner,
        _ => lit,
    }
}

/// Step indices reachable from an empty-clause conclusion (the only steps
/// the printer emits).
fn live_steps(proof: &Proof) -> Vec<bool> {
    let n = proof.steps.len();
    let mut live = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    for (idx, step) in proof.steps.iter().enumerate() {
        let empty = match step {
            ProofStep::Step { clause, .. }
            | ProofStep::Resolution { clause, .. }
            | ProofStep::TheoryLemma { clause, .. } => clause.is_empty(),
            _ => false,
        };
        if empty && !live[idx] {
            live[idx] = true;
            stack.push(idx);
        }
    }
    while let Some(idx) = stack.pop() {
        let mut push = |p: ProofId| {
            let i = p.0 as usize;
            if i < n && !live[i] {
                live[i] = true;
                stack.push(i);
            }
        };
        match &proof.steps[idx] {
            ProofStep::Step { premises, .. } => premises.iter().copied().for_each(&mut push),
            ProofStep::Resolution {
                clause1, clause2, ..
            } => {
                push(*clause1);
                push(*clause2);
            }
            _ => {}
        }
    }
    live
}

/// Whether `t` is a PURE linear-arithmetic term: numerals, arithmetic
/// variables / declared constants, and `+`/`-`/`*` applications thereof.
/// The internal Farkas verifier treats any non-arithmetic atom (e.g. an
/// array `select`) as an opaque linear unknown, but external `la_generic`
/// checking evaluates the linear combination syntactically — so promotions
/// that flip a lemma onto `la_generic` must reject impure atoms.
fn term_is_pure_linear_arith(terms: &ay_core::TermStore, t: TermId) -> bool {
    if !matches!(terms.sort(t), Sort::Int | Sort::Real) {
        return false;
    }
    match terms.get(t) {
        TermData::Const(_) | TermData::Var(..) => true,
        TermData::App(Symbol::Named(op), args) => match op.as_str() {
            "+" | "-" | "*" => args.iter().all(|&a| term_is_pure_linear_arith(terms, a)),
            _ => args.is_empty(),
        },
        _ => false,
    }
}

/// Whether both operands of the equality application `eq` are pure
/// linear-arithmetic terms (see [`term_is_pure_linear_arith`]).
fn equality_is_pure_linear_arith(terms: &ay_core::TermStore, eq: TermId) -> bool {
    match terms.get(eq) {
        TermData::App(Symbol::Named(op), args) if op == "=" && args.len() == 2 => {
            let (a, b) = (args[0], args[1]);
            term_is_pure_linear_arith(terms, a) && term_is_pure_linear_arith(terms, b)
        }
        _ => false,
    }
}

/// Complement of a literal without double negation.
fn complement_of(terms: &mut ay_core::TermStore, lit: TermId) -> TermId {
    match terms.get(lit) {
        TermData::Not(inner) => *inner,
        _ => terms.mk_not_raw(lit),
    }
}

/// How a defective `assume` gets repaired.
enum AssumePlan {
    /// Surface `(distinct x1 .. xn)`, n >= 3, exported as the expanded
    /// pairwise conjunction: assume the raw `distinct`, bridge via
    /// `distinct_elim` + `equiv_pos2` to the conjunction.
    Distinct {
        /// Raw `(distinct x1 .. xn)` application (prints like the file).
        raw: TermId,
        /// The canonical pairwise conjunction (the old assume's term).
        and_term: TermId,
        /// Conjuncts of `and_term`, in order.
        conjs: Vec<TermId>,
    },
    /// Surface `(and c1 .. cn)` whose conjuncts were arithmetic-normalized
    /// (or binary-`distinct` sugar): assume the raw surface conjunction,
    /// bridge each extracted unit where the raw conjunct differs from the
    /// canonical one.
    AndBounds {
        /// Raw `(and raw_1 .. raw_n)` application.
        raw_and: TermId,
        /// Per conjunct: the raw surface literal and, when it differs from
        /// the canonical conjunct, the raw literal's atom (bridge pivot).
        raws: Vec<(TermId, Option<TermId>)>,
        /// Canonical conjuncts (of the old assume's term), in order.
        conjs: Vec<TermId>,
    },
    /// Surface `(and c1 .. cn)` with binary-`distinct` sugar conjuncts
    /// (exported as canonical `(not (= s t))`, whose print no longer matches
    /// the file): assume the raw surface conjunction and RE-DERIVE the
    /// canonical conjunction as a unit — per-conjunct `and_pos` extraction
    /// (bridged via `distinct_elim` + `equiv_pos2` where sugared, or a
    /// certified orientation lemma where arithmetic-normalized) closed by
    /// `and_neg` — onto which EVERY consumer is remapped (unlike the
    /// bounds class, consumers may resolve the assume anywhere).
    AndDistinct {
        /// Raw `(and raw_1 .. raw_n)` application (prints like the file;
        /// folded-away conjuncts like `(= c c)` reappear here raw).
        raw_and: TermId,
        /// The canonical conjunction (the old assume's term).
        and_term: TermId,
        /// The raw conjuncts that supply canonical conjunct units, in
        /// canonical-conjunct order.
        units: Vec<AndDistinctUnit>,
        /// Canonical conjuncts (of the old assume's term), in order.
        conjs: Vec<TermId>,
    },
    /// A single arithmetic-normalized bound literal (e.g. surface `(> a 5)`
    /// exported as the canonical `(< 5 a)`): assume the raw surface literal,
    /// bridge to the canonical literal by a certified `[1, 1]` orientation
    /// lemma, and remap every consumer onto the derived unit.
    Literal {
        /// Raw surface literal (prints like the file).
        raw: TermId,
        /// The raw literal's atom (the bridge resolution pivot).
        atom: TermId,
        /// The canonical literal (the old assume's term).
        canonical: TermId,
    },
    /// A finite-domain quantifier expansion assume (#quant-expansion-proof):
    /// preprocessing replaced a top-level `forall` assertion in place with
    /// the merged ground-instance conjunction, and the exporter assumed the
    /// conjunction — which no external checker can match to the problem's
    /// `forall` premise. Replaced by an assume of the ORIGINAL `forall`;
    /// every consumed conjunct is re-DERIVED from it: `forall_inst`
    /// (positional binder-value args) + `or` + resolution to the raw
    /// substituted body, `implies_pos` + per-atom unit `la_generic` guard
    /// discharge + `and_neg`, and a certified `[1, 1]` strict-Int
    /// orientation bridge onto the canonical conjunct where the tightening
    /// pass rewrote it. All consumers must be recognized unit-extraction
    /// patterns (like [`AssumePlan::AndBounds`]).
    QuantExpansion {
        /// The original `forall` assertion (a genuine problem premise).
        forall_term: TermId,
        /// Its parsed surface form (for raw instance construction).
        parsed: FrontendTerm,
        /// Canonical conjuncts of the expansion (the old assume's term).
        conjs: Vec<TermId>,
        /// Folded instance term -> binder values (in binder order).
        instances: HashMap<TermId, Vec<TermId>>,
    },
}

/// A planned per-instance derivation chain from an original `forall`
/// premise to a single unit clause (#quant-expansion-proof). Every
/// ingredient is validated at plan time: the substituted body is built from
/// the premise's own SURFACE syntax (so the printed `forall_inst`
/// conclusion is exactly the instantiation an external checker recomputes),
/// each guard atom is certified as a ground arithmetic tautology by the
/// independent Farkas checker, and the optional strict-Int bridge is a
/// re-verified `[1, 1]` `la_generic` lemma.
struct QuantInstanceChain {
    /// Binder values, in binder order (the `forall_inst` positional args).
    values: Vec<TermId>,
    /// Raw-interned substituted body (the `forall_inst` instance).
    phi: TermId,
    /// `(guard term, guard atoms)` when `phi` is `(=> g b)`; each atom is a
    /// certified ground arithmetic truth, all atoms distinct.
    guard: Option<(TermId, Vec<TermId>)>,
    /// The consequent literal the chain concludes (`phi` when no guard).
    body_lit: TermId,
    /// The final unit term consumers expect. When it differs from
    /// `body_lit`, the plan-time-validated `[1, 1]` pair lemma
    /// `(cl target (not body_lit))` bridges the two.
    target: TermId,
}

/// A recognized trust unit `(cl L)` that is a preprocessing-folded
/// CONSEQUENCE of a quantifier-expansion instance and up to one original
/// premise (#quant-expansion-proof): e.g. the conjunct
/// `(<= (f 24) (+ (f 25) (- 1)))` folded with the asserted `(= (f 25) 26)`
/// into `(<= (f 24) 25)`. Replaced by the instance derivation chain, an
/// assume per consumed original, and one re-verified `la_generic` lemma
/// `(cl (not inst) (not orig).. L)` closed by resolutions.
struct QuantConsequencePlan {
    /// The original `forall` assertion the instance derives from.
    forall_term: TermId,
    /// The plan-time-built derivation of `(cl chain.target)`.
    chain: QuantInstanceChain,
    /// Original premises consumed by the folding (assumed in the rebuild).
    supports: Vec<TermId>,
    /// The validated lemma clause `(not chain.target) (not s)... L`,
    /// ending in the trust unit `L` the consumers expect.
    lemma: Vec<TermId>,
}

/// Substitute ground surface terms for binder-name symbols in a parsed
/// surface term. Fails closed (`None`) on ANY binding construct
/// (`let`/`forall`/`exists`/`lambda`/`match`) — shadowing or capture would
/// make plain symbol replacement incorrect — so only binder-free bodies are
/// instantiated. Annotations are stripped (external checkers compare the
/// bare term).
fn surface_subst_ground(
    term: &FrontendTerm,
    subst: &HashMap<String, FrontendTerm>,
) -> Option<FrontendTerm> {
    match term {
        FrontendTerm::Annotated(inner, _) => surface_subst_ground(inner, subst),
        FrontendTerm::Const(_) => Some(term.clone()),
        FrontendTerm::Symbol(name) => {
            Some(subst.get(name).cloned().unwrap_or_else(|| term.clone()))
        }
        FrontendTerm::App(head, args) => {
            let new_args = args
                .iter()
                .map(|a| surface_subst_ground(a, subst))
                .collect::<Option<Vec<_>>>()?;
            Some(FrontendTerm::App(head.clone(), new_args))
        }
        FrontendTerm::IndexedApp(name, indices, args) => {
            let new_args = args
                .iter()
                .map(|a| surface_subst_ground(a, subst))
                .collect::<Option<Vec<_>>>()?;
            Some(FrontendTerm::IndexedApp(
                name.clone(),
                indices.clone(),
                new_args,
            ))
        }
        FrontendTerm::QualifiedApp(name, sort, args) => {
            let new_args = args
                .iter()
                .map(|a| surface_subst_ground(a, subst))
                .collect::<Option<Vec<_>>>()?;
            Some(FrontendTerm::QualifiedApp(
                name.clone(),
                sort.clone(),
                new_args,
            ))
        }
        _ => None,
    }
}

/// Surface spelling of a ground binder value (Int and Bool only — the
/// finite-domain sorts whose derivations are validated end-to-end).
/// Negative integers spell as `(- k)`, the SMT-LIB surface form.
fn value_to_surface(terms: &ay_core::TermStore, value: TermId) -> Option<FrontendTerm> {
    use ay_frontend::command::Constant as SurfaceConstant;
    match terms.get(value) {
        TermData::Const(ay_core::term::Constant::Bool(b)) => Some(FrontendTerm::Const(if *b {
            SurfaceConstant::True
        } else {
            SurfaceConstant::False
        })),
        TermData::Const(ay_core::term::Constant::Int(n)) => {
            if n.sign() == num_bigint::Sign::Minus {
                Some(FrontendTerm::App(
                    "-".to_string(),
                    vec![FrontendTerm::Const(SurfaceConstant::Numeral(
                        (-n).to_string(),
                    ))],
                ))
            } else {
                Some(FrontendTerm::Const(SurfaceConstant::Numeral(n.to_string())))
            }
        }
        _ => None,
    }
}

/// One raw conjunct of an [`AssumePlan::AndDistinct`] assume that supplies
/// canonical conjunct unit(s).
#[derive(Clone)]
struct AndDistinctUnit {
    /// Operand position in the raw conjunction (the `and_pos` index).
    pos: u32,
    /// The raw conjunct term.
    raw: TermId,
    kind: AndDistinctKind,
}

/// How an extracted raw conjunct bridges to its canonical conjunct(s).
#[derive(Clone)]
enum AndDistinctKind {
    /// The raw conjunct IS the canonical conjunct.
    Plain,
    /// Arithmetic orientation bridge: certified `[1, 1]` `la_generic` lemma
    /// over the raw literal's atom.
    Arith { atom: TermId },
    /// Binary `(distinct s t)` sugar exported as the canonical
    /// `(not (= s t))`: bridge via `distinct_elim` + `equiv_pos2`.
    DistinctBinary,
    /// N-ary `(distinct ..)` sugar exported as `count` pairwise canonical
    /// conjuncts: `distinct_elim` + `equiv_pos2` to the expansion
    /// conjunction `and_term`, then one `and_pos` per pairwise conjunct.
    DistinctNary { and_term: TermId, count: u32 },
    /// An `or`-conjunct whose canonical export REORDERED the disjuncts
    /// and/or FLIPPED individual binary-equality literals (#C2b): the raw
    /// (file-order, file-orientation) disjunction is re-interned for the
    /// assume, and its unit bridges to the canonical or-term via the `or`
    /// rule, one certified `eq_symmetric` + `equiv_pos1/2` orientation
    /// bridge per flipped literal, and the `or_neg` permutation closure
    /// (the C1 or-split reorder machinery).
    OrPerm {
        /// `(raw disjunct, canonical disjunct)` pairs in RAW disjunct
        /// order; each pair is either identical or a top-level
        /// binary-equality orientation flip (possibly under one `not`).
        lits: Vec<(TermId, TermId)>,
    },
}

/// A recognized ite-lift trust step: a preprocessed input `(cl (ite c A B))`
/// obtained by lifting a term-level ite out of an original assertion
/// `P(ite c u v)` (`A = P[ite/u]`, `B = P[ite/v]`). Replaced by an assume of
/// the original assertion plus a certified `ite_intro` → `equiv_pos2` →
/// `and_pos` → `ite1`/`ite2` → opaque-atom `la_generic` → `ite_neg1`/
/// `ite_neg2` derivation of the lifted clause (validated end-to-end against
/// Carcara).
struct IteLiftPlan {
    /// The original assertion `P(s)` (canonical term; printed via the
    /// surface overrides so the assume matches the problem file). In the
    /// defined-equality variant this is the defining equality
    /// `(= d (ite c u v))` and `bound` carries the second original.
    orig: TermId,
    /// The CANONICAL original assertion whose parsed surface spells `orig`,
    /// when `orig` is a re-interned surface form rather than the canonical
    /// term itself (the defined-equality variant, where elaboration lifts
    /// the defining equality to a formula-level ite). Its surface override
    /// is collected on commit and copied onto `orig` so the re-added assume
    /// prints like the problem file.
    defining_source: Option<TermId>,
    /// Defined-equality substitution variant (TWO originals feed the lifted
    /// clause): the bound original `P(d)` over the defined term `d`, so
    /// `A = P[d/u]`, `B = P[d/v]`. Its literal joins the transfer lemmas
    /// (quads instead of triples) and is discharged by its own assume.
    bound: Option<TermId>,
    /// The lifted-condition / branch formulas of the trust clause.
    cond: TermId,
    lifted_then: TermId,
    lifted_else: TermId,
    /// The trust clause's single literal `(ite cond A B)`.
    goal: TermId,
    /// `(= s u)` / `(= s v)` (the `ite_intro` definition equalities;
    /// `s = (ite cond u v)` is the term-level ite inside `orig`).
    eq_then: TermId,
    eq_else: TermId,
    /// `(ite cond (= s u) (= s v))`.
    ite_def: TermId,
    /// `(and orig ite_def)`.
    and_term: TermId,
    /// `(= orig and_term)` — the `ite_intro` conclusion.
    intro_eq: TermId,
}

/// A recognized preprocessor-derived unit trust step `(cl L)` where an
/// original disjunctive assertion (surface `(or ...)` or De Morgan
/// `(not (and ...))`) contains `L` and every OTHER disjunct is refuted by
/// its complementary original assertion. Replaced by an assume of the
/// disjunction, its `or` decomposition (the printer resugars a De Morgan
/// surface to `not_and`), and one resolution per remaining disjunct against
/// the complementary original's assume.
struct OrUnitPlan {
    /// The original disjunctive assertion (canonical or-term; prints via
    /// the surface overrides).
    orig: TermId,
    /// Its disjuncts, in canonical order (the decomposition step's clause).
    disjuncts: Vec<TermId>,
    /// Per non-`L` disjunct, in decomposition order: (resolution pivot
    /// atom, the complementary ORIGINAL assertion discharging it).
    eliminations: Vec<(TermId, TermId)>,
}

/// How a recognized preprocessor-derived EUF-transitivity TAUTOLOGY unit
/// `(cl T)` gets re-derived (T is an `or`-term with exactly one implied
/// positive equality disjunct). Two routes:
enum TautRoute {
    /// `T = (or .. E .. ¬e1 .. ¬en)` where the `¬e` disjuncts' equalities
    /// form a transitivity chain proving `E`: one `eq_transitive` step
    /// `(cl ¬e1 .. ¬en E)`, each `¬ei` eliminated against the `or_neg`
    /// tautology `(cl T (not ¬ei))`, closed by the `E`-position `or_neg`.
    Plain {
        /// The `¬e` disjuncts, in disjunct order (ALL of them: the chain
        /// check requires every edge on the path, mirroring the checker).
        negs: Vec<TermId>,
    },
    /// `T = (or .. E .. A ..)` where `A = (and D1 .. Dm)` and each
    /// `Dj = (or ¬f1 .. ¬fp)` is a De Morganized conjunction whose
    /// equalities chain to `E` (the eq_diamond family's shape): per `Dj` an
    /// `eq_transitive` + `or_neg` elimination derives `(cl E Dj)`, an
    /// `and_neg` step recombines them into `(cl A E)`, and the outer
    /// `or_neg` pair closes `(cl T)`.
    And {
        /// The `and`-disjunct `A`.
        and_term: TermId,
        /// `A`'s conjuncts `D1 .. Dm`, in order.
        conjs: Vec<TermId>,
        /// Per conjunct: its `¬f` disjuncts, in order (chain-verified).
        per_conj_negs: Vec<Vec<TermId>>,
    },
}

/// A recognized preprocessor-derived EUF-transitivity tautology unit: a
/// mid-proof `assume` (or premiseless unit trust step) of an `or`-term `T`
/// that is valid on its own by equality transitivity. Such leaves are
/// checker-invalid (an `assume` that matches no problem premise / an
/// unchecked trust step); the plan re-derives `(cl T)` from NOTHING with
/// certified `eq_transitive` / `or_neg` / `and_neg` / `contraction` /
/// resolution steps, and every consumer is remapped onto the derived unit
/// (same clause content, so no consumer rewiring is needed).
struct OrTautologyPlan {
    /// The tautological `or`-term `T`.
    term: TermId,
    /// The implied positive equality disjunct `E`.
    eq: TermId,
    route: TautRoute,
}

/// A recognized Int-trichotomy trust step and its `or`-split consumer.
struct TrichotomyPlan {
    /// Index of the `or`-split step consuming the trust step.
    or_split_idx: usize,
    /// `(= x y)`.
    eq: TermId,
    /// `(<= x y)` / `(<= y x)` (raw-interned, `la_disequality` operand order).
    le_xy: TermId,
    le_yx: TermId,
    /// Their negations (the split literals).
    not_le_xy: TermId,
    not_le_yx: TermId,
    /// `(or eq (not le_xy) (not le_yx))` — the `la_disequality` conclusion.
    or_term: TermId,
    /// The strengthened literal implied by `(not (<= y x))`
    /// (i.e. `(<= x (+ y (- 1)))` up to normalization).
    strong_from_yx: TermId,
    /// The strengthened literal implied by `(not (<= x y))`.
    strong_from_xy: TermId,
}

impl Executor {
    /// See the module docs. Returns `true` (proof swapped) only when EVERY
    /// reachable defect was repaired with a certified derivation.
    pub(super) fn try_rebuild_with_trust_surgery(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
    ) -> bool {
        let n = proof.steps.len();
        if n == 0 {
            return false;
        }
        // Subproof anchors are out of scope for index-remap surgery.
        if proof
            .steps
            .iter()
            .any(|s| matches!(s, ProofStep::Anchor { .. }))
        {
            return false;
        }

        // Only steps REACHABLE from an empty-clause step matter: dead steps
        // are never printed, so the surgery neither plans for them nor
        // copies them (a dead defective step must not veto the repair).
        let live = live_steps(proof);

        // Consumer map: step index -> indices of LIVE steps that use it.
        let mut consumers: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (idx, step) in proof.steps.iter().enumerate() {
            if !live[idx] {
                continue;
            }
            match step {
                ProofStep::Step { premises, .. } => {
                    for p in premises {
                        let i = p.0 as usize;
                        if i >= n {
                            return false;
                        }
                        consumers[i].push(idx);
                    }
                }
                ProofStep::Resolution {
                    clause1, clause2, ..
                } => {
                    for p in [clause1, clause2] {
                        let i = p.0 as usize;
                        if i >= n {
                            return false;
                        }
                        consumers[i].push(idx);
                    }
                }
                _ => {}
            }
        }

        // (1) Plan every trust step. Any unrecognizable trust step aborts
        // the surgery (fail-closed). A proof with NO trust step can still be
        // defective — its assumes may be preprocessing-normalized forms no
        // checker can match to the problem premises — so a missing trust
        // anchor does not end the pass: step (2) may still find repairable
        // assumes, and the no-plans-at-all case is rejected after it.
        let mut trichotomies: HashMap<usize, TrichotomyPlan> = HashMap::default();
        let mut ite_lifts: HashMap<usize, IteLiftPlan> = HashMap::default();
        let mut or_units: HashMap<usize, OrUnitPlan> = HashMap::default();
        let mut taut_units: HashMap<usize, OrTautologyPlan> = HashMap::default();
        let mut euf_lemmas: HashMap<usize, EufLemmaPlan> = HashMap::default();
        let mut quant_consequences: HashMap<usize, QuantConsequencePlan> = HashMap::default();
        let mut or_split_of: HashMap<usize, usize> = HashMap::default();
        for idx in 0..n {
            if !live[idx] {
                continue;
            }
            // A defective leaf prints as `:rule trust` from either shape:
            // a generic `Step` with the Trust rule, or a certificate-less
            // `TheoryLemma` whose kind exports as trust (the lazy-EUF lemma
            // export, #C2).
            let clause = match &proof.steps[idx] {
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    ..
                } => clause.clone(),
                ProofStep::TheoryLemma { kind, clause, .. } if kind.is_trust() => clause.clone(),
                _ => continue,
            };
            if let Some(plan) = self.plan_trichotomy(proof, &clause, &consumers[idx], idx) {
                or_split_of.insert(plan.or_split_idx, idx);
                trichotomies.insert(idx, plan);
            } else if let Some(plan) = self.plan_ite_lift(&clause, originals) {
                ite_lifts.insert(idx, plan);
            } else if let Some(plan) = self.plan_or_unit(&clause, originals) {
                or_units.insert(idx, plan);
            } else if let Some(plan) = self.plan_or_transitivity_tautology(&clause) {
                taut_units.insert(idx, plan);
            } else if let Some(plan) = self.plan_euf_lemma(&clause) {
                // EUF congruence/substitution-chain lemma (bare or
                // or-wrapped), re-derived via the eq_congruent /
                // eq_transitive / eq_congruent_pred toolkit (#C2).
                euf_lemmas.insert(idx, plan);
            } else if let Some(plan) = self.plan_quant_consequence(&clause, originals) {
                // A preprocessing-folded consequence of a quantifier-
                // expansion instance (#quant-expansion-proof): re-derived
                // from the ORIGINAL forall premise via forall_inst plus a
                // re-verified la_generic combination with the consumed
                // original premises.
                quant_consequences.insert(idx, plan);
            } else {
                return false;
            }
        }
        // The ite-lift derivation depends on the surface overrides surviving
        // (its new assume must print like the problem file), while the
        // trichotomy / assume-bridge classes purge them to protect their
        // rigid raw-interned shapes. Mixing the two disciplines in one proof
        // is unsupported: fail closed.
        if (!ite_lifts.is_empty() || !or_units.is_empty()) && !trichotomies.is_empty() {
            return false;
        }

        // (2) Plan every assume: originals-faithful assumes are kept; the
        // two repairable classes get bridge plans; anything else that is not
        // an original assertion aborts.
        let mut assume_plans: HashMap<usize, AssumePlan> = HashMap::default();
        for (idx, step) in proof.steps.iter().enumerate() {
            if !live[idx] {
                continue;
            }
            let ProofStep::Assume(term) = step else {
                continue;
            };
            let term = *term;
            let Some((_, parsed)) = originals.iter().find(|(c, _)| *c == term) else {
                // A mid-proof assume of a PREPROCESSOR-DERIVED formula: no
                // checker can match it to a problem premise. Repairable when
                // it is a recorded finite-domain quantifier expansion (the
                // conjuncts re-derive from the ORIGINAL forall premise,
                // #quant-expansion-proof), a self-contained EUF-transitivity
                // tautology (re-derived from nothing), or an or-wrapped EUF
                // lemma; otherwise fail closed.
                if let Some(plan) = self.classify_quant_expansion(term, originals) {
                    assume_plans.insert(idx, plan);
                    continue;
                }
                if let Some(plan) = self.plan_or_transitivity_tautology(&[term]) {
                    taut_units.insert(idx, plan);
                    continue;
                }
                if let Some(plan) = self.plan_euf_lemma(&[term]) {
                    if plan.or_term().is_some() {
                        euf_lemmas.insert(idx, plan);
                        continue;
                    }
                }
                return false;
            };
            let parsed = parsed.clone();
            // Surface overrides survive only the ite-lift surgery: when they
            // are kept, an override-covered bound literal already prints
            // right and must NOT be planned (a plan would trip the ite-lift
            // exclusivity abort); when they are purged, it MUST be bridged
            // (its post-purge canonical print no longer matches the file).
            let overrides_kept = !ite_lifts.is_empty();
            match self.classify_assume(term, &parsed, overrides_kept) {
                Ok(Some(plan)) => {
                    assume_plans.insert(idx, plan);
                }
                Ok(None) => {}
                Err(()) => return false,
            }
        }
        // See the exclusivity note above: assume bridges assume the override
        // purge, ite lifts require the overrides. Fail closed on the mix.
        if !ite_lifts.is_empty() && !assume_plans.is_empty() {
            return false;
        }
        // Quant-expansion plans purge the overrides and re-collect only their
        // own re-added originals; the ite-lift / or-unit classes keep the
        // whole override map. Mixing the two disciplines is unsupported:
        // fail closed.
        let has_quant_plans = !quant_consequences.is_empty()
            || assume_plans
                .values()
                .any(|p| matches!(p, AssumePlan::QuantExpansion { .. }));
        if has_quant_plans && (!ite_lifts.is_empty() || !or_units.is_empty()) {
            return false;
        }
        // Nothing to repair at all: keep the proof byte-identical. (The
        // trust-free defective-assume case — the caller's
        // `reachable_non_original_assume` trigger — lands here with a
        // non-empty `assume_plans` and proceeds.)
        if trichotomies.is_empty()
            && ite_lifts.is_empty()
            && assume_plans.is_empty()
            && taut_units.is_empty()
            && euf_lemmas.is_empty()
            && quant_consequences.is_empty()
        {
            return false;
        }

        // (3) Recognize the unit-extraction patterns downstream of each
        // repaired assume: `and_pos` (premiseless) resolved against the
        // assume into a unit clause. Each such resolution is re-derived; the
        // `and_pos` step itself is dropped.
        //
        // `unit_patterns`: resolution idx -> (assume idx, conjunct position).
        let mut unit_patterns: HashMap<usize, (usize, usize)> = HashMap::default();
        let mut dropped_and_pos: Vec<bool> = vec![false; n];
        for (idx, step) in proof.steps.iter().enumerate() {
            if !live[idx] {
                continue;
            }
            // Unit extraction appears either as a `Resolution` step or as a
            // generic `Step` with the (th_)resolution rule.
            let (clause, i1, i2) = match step {
                ProofStep::Resolution {
                    clause,
                    clause1,
                    clause2,
                    ..
                } => (clause, clause1.0 as usize, clause2.0 as usize),
                ProofStep::Step {
                    rule: AletheRule::ThResolution | AletheRule::Resolution,
                    clause,
                    premises,
                    ..
                } if premises.len() == 2 => {
                    (clause, premises[0].0 as usize, premises[1].0 as usize)
                }
                _ => continue,
            };
            if clause.len() != 1 {
                continue;
            }
            let (a_idx, p_idx) = if assume_plans.contains_key(&i1) {
                (i1, i2)
            } else if assume_plans.contains_key(&i2) {
                (i2, i1)
            } else {
                continue;
            };
            let ProofStep::Step {
                rule: AletheRule::AndPos(pos),
                premises,
                ..
            } = &proof.steps[p_idx]
            else {
                continue;
            };
            if !premises.is_empty() {
                continue;
            }
            let pos = *pos as usize;
            let conjs = match &assume_plans[&a_idx] {
                AssumePlan::Distinct { conjs, .. }
                | AssumePlan::AndBounds { conjs, .. }
                | AssumePlan::QuantExpansion { conjs, .. } => conjs,
                // An `AndDistinct` unit pattern is remapped onto the plan's
                // derived per-conjunct unit — but ONLY when the OLD `and_pos`
                // step's not-and literal is not the genuine `(not (and ...))`
                // term (the exporter's de Morganized or-shape no external
                // checker accepts as `and_pos`). Otherwise the historical
                // behavior — keep the step, remap consumers onto the derived
                // conjunction unit — is preserved byte-for-byte.
                AssumePlan::AndDistinct {
                    and_term, conjs, ..
                } => {
                    let ProofStep::Step { clause: ap, .. } = &proof.steps[p_idx] else {
                        continue;
                    };
                    let genuine_not_and = ap.first().is_some_and(|&l| {
                        matches!(self.ctx.terms.get(l), TermData::Not(inner) if *inner == *and_term)
                    });
                    if genuine_not_and {
                        continue;
                    }
                    conjs
                }
                // A `Literal` assume has no `and_pos` pattern to recognize:
                // consumers are remapped onto the derived unit directly.
                AssumePlan::Literal { .. } => continue,
            };
            if pos >= conjs.len() || conjs[pos] != clause[0] {
                return false;
            }
            unit_patterns.insert(idx, (a_idx, pos));
            dropped_and_pos[p_idx] = true;
        }
        // Every consumer of an `AndBounds` / `QuantExpansion` assume must be
        // a recognized unit pattern: the term the new assume carries differs
        // from the canonical conjunction, so no other consumer can be
        // remapped.
        for (&a_idx, plan) in &assume_plans {
            if matches!(
                plan,
                AssumePlan::AndBounds { .. } | AssumePlan::QuantExpansion { .. }
            ) && !consumers[a_idx]
                .iter()
                .all(|c| unit_patterns.contains_key(c))
            {
                return false;
            }
        }
        // Prepare the certified derivation chain for every quant-expansion
        // unit pattern up front (fail-closed: an unmatched or underivable
        // conjunct aborts the surgery and keeps the proof byte-identical).
        let mut quant_chains: HashMap<(usize, usize), QuantInstanceChain> = HashMap::default();
        {
            let mut pattern_targets: Vec<(usize, usize)> =
                unit_patterns.values().copied().collect();
            pattern_targets.sort_unstable();
            pattern_targets.dedup();
            for (a_idx, pos) in pattern_targets {
                let Some(AssumePlan::QuantExpansion {
                    parsed,
                    conjs,
                    instances,
                    ..
                }) = assume_plans.get(&a_idx)
                else {
                    continue;
                };
                let target = conjs[pos];
                let Some(values) = instances.get(&target).cloned() else {
                    return false;
                };
                let parsed = parsed.clone();
                let Some(chain) = self.build_quant_instance_chain(&parsed, &values, target) else {
                    return false;
                };
                quant_chains.insert((a_idx, pos), chain);
            }
        }
        // A dropped `and_pos` step must have no consumers outside its own
        // unit pattern (its literals reference terms the new proof does not
        // derive).
        for (idx, dropped) in dropped_and_pos.iter().enumerate() {
            if *dropped && !consumers[idx].iter().all(|c| unit_patterns.contains_key(c)) {
                return false;
            }
        }

        // (4) Rebuild: hoisted assumes first, then a single ordered walk
        // emitting replacement subgraphs in place and remapping premises.
        let mut new_proof = Proof::new();
        let mut map: Vec<Option<ProofId>> = vec![None; n];
        let mut assume_new_id: HashMap<usize, ProofId> = HashMap::default();
        for (idx, step) in proof.steps.iter().enumerate() {
            if !live[idx] {
                continue;
            }
            let ProofStep::Assume(term) = step else {
                continue;
            };
            // A tautology-planned assume is re-DERIVED, not assumed: no
            // hoisted assume for it (its unit is emitted in the walk below).
            if taut_units.contains_key(&idx) || euf_lemmas.contains_key(&idx) {
                continue;
            }
            let t = match assume_plans.get(&idx) {
                Some(AssumePlan::Distinct { raw, .. }) => *raw,
                Some(AssumePlan::AndBounds { raw_and, .. })
                | Some(AssumePlan::AndDistinct { raw_and, .. }) => *raw_and,
                Some(AssumePlan::Literal { raw, .. }) => *raw,
                Some(AssumePlan::QuantExpansion { forall_term, .. }) => *forall_term,
                None => *term,
            };
            let id = new_proof.add_assume(t, None);
            assume_new_id.insert(idx, id);
            if !assume_plans.contains_key(&idx) {
                map[idx] = Some(id);
            }
        }
        // The ite-lift plans re-derive from ORIGINAL assertions that the
        // preprocessor consumed: their assumes are absent from the exported
        // proof and must be added to the hoist (deduplicated across plans,
        // reusing an existing assume of the same term when present).
        let mut lift_assume: HashMap<TermId, ProofId> = HashMap::default();
        for (idx, step) in proof.steps.iter().enumerate() {
            if !live[idx] {
                continue;
            }
            if let ProofStep::Assume(term) = step {
                if let Some(&id) = assume_new_id.get(&idx) {
                    lift_assume.entry(*term).or_insert(id);
                }
            }
        }
        for plan in ite_lifts.values() {
            for t in std::iter::once(plan.orig).chain(plan.bound) {
                if !lift_assume.contains_key(&t) {
                    let id = new_proof.add_assume(t, None);
                    lift_assume.insert(t, id);
                }
            }
        }
        for plan in or_units.values() {
            for t in
                std::iter::once(plan.orig).chain(plan.eliminations.iter().map(|&(_, comp)| comp))
            {
                if !lift_assume.contains_key(&t) {
                    let id = new_proof.add_assume(t, None);
                    lift_assume.insert(t, id);
                }
            }
        }
        // Quant-expansion assumes were hoisted as the ORIGINAL forall term:
        // register them under that term so consequence plans can share them,
        // then hoist any forall / support original a consequence plan needs
        // that the proof did not assume (#quant-expansion-proof).
        for (idx, plan) in &assume_plans {
            if let AssumePlan::QuantExpansion { forall_term, .. } = plan {
                if let Some(&id) = assume_new_id.get(idx) {
                    lift_assume.entry(*forall_term).or_insert(id);
                }
            }
        }
        for plan in quant_consequences.values() {
            for t in std::iter::once(plan.forall_term).chain(plan.supports.iter().copied()) {
                if !lift_assume.contains_key(&t) {
                    let id = new_proof.add_assume(t, None);
                    lift_assume.insert(t, id);
                }
            }
        }

        // Derived `(cl <conjunction>)` unit per Distinct assume.
        let mut distinct_unit: HashMap<usize, ProofId> = HashMap::default();
        // Derived per-canonical-conjunct units per AndDistinct assume (the
        // targets of that plan's recognized unit patterns).
        let mut anddistinct_units: HashMap<usize, Vec<ProofId>> = HashMap::default();
        // Derived 3-literal strengthened clause per trust step.
        let mut trichotomy_clause: HashMap<usize, ProofId> = HashMap::default();
        // Derived `(cl T)` tautology unit per tautological or-term (shared
        // when several defective leaves carry the same term).
        let mut taut_unit_of_term: HashMap<TermId, ProofId> = HashMap::default();
        // Same sharing for the or-wrapped EUF-lemma units.
        let mut euf_unit_of_term: HashMap<TermId, ProofId> = HashMap::default();
        // Derived quant-expansion instance units, shared per (assume, pos).
        let mut quant_units_emitted: HashMap<(usize, usize), ProofId> = HashMap::default();

        for idx in 0..n {
            if !live[idx] || dropped_and_pos[idx] {
                continue;
            }
            if let Some(&trust_idx) = or_split_of.get(&idx) {
                // The or-split consumer is rewired onto the derived clause.
                map[idx] = trichotomy_clause.get(&trust_idx).copied();
                if map[idx].is_none() {
                    return false;
                }
                continue;
            }
            if let Some(plan) = trichotomies.get(&idx) {
                // la_disequality -> or -> two certified strengthening
                // lemmas -> the 3-literal strengthened clause.
                let la = new_proof.add_rule_step(
                    AletheRule::LaDisequality,
                    vec![plan.or_term],
                    Vec::new(),
                    Vec::new(),
                );
                let or_step = new_proof.add_rule_step(
                    AletheRule::Or,
                    vec![plan.eq, plan.not_le_xy, plan.not_le_yx],
                    vec![la],
                    Vec::new(),
                );
                let lem_yx = Self::add_pair_lemma(&mut new_proof, plan.strong_from_yx, plan.le_yx);
                let r1 = new_proof.add_resolution(
                    vec![plan.eq, plan.not_le_xy, plan.strong_from_yx],
                    plan.le_yx,
                    or_step,
                    lem_yx,
                );
                let lem_xy = Self::add_pair_lemma(&mut new_proof, plan.strong_from_xy, plan.le_xy);
                let r2 = new_proof.add_resolution(
                    vec![plan.eq, plan.strong_from_yx, plan.strong_from_xy],
                    plan.le_xy,
                    r1,
                    lem_xy,
                );
                trichotomy_clause.insert(idx, r2);
                // The trust step itself is never referenced by anything but
                // its or-split (verified during planning): no mapping.
                continue;
            }
            if let Some(plan) = ite_lifts.get(&idx) {
                let Some(&assume_id) = lift_assume.get(&plan.orig) else {
                    return false;
                };
                let not_intro_eq = self.ctx.terms.mk_not_raw(plan.intro_eq);
                let not_orig = self.ctx.terms.mk_not_raw(plan.orig);
                let not_cond = self.ctx.terms.mk_not_raw(plan.cond);
                let not_eq_then = self.ctx.terms.mk_not_raw(plan.eq_then);
                let not_eq_else = self.ctx.terms.mk_not_raw(plan.eq_else);
                let not_lifted_then = complement_of(&mut self.ctx.terms, plan.lifted_then);
                let not_lifted_else = complement_of(&mut self.ctx.terms, plan.lifted_else);

                // ite_intro ⊢ (cl (= P (and P (ite c (= s u) (= s v)))))
                let intro = new_proof.add_rule_step(
                    AletheRule::IteIntro,
                    vec![plan.intro_eq],
                    Vec::new(),
                    Vec::new(),
                );
                let ep = new_proof.add_rule_step(
                    AletheRule::EquivPos2,
                    vec![not_intro_eq, not_orig, plan.and_term],
                    Vec::new(),
                    Vec::new(),
                );
                let r_eq = new_proof.add_resolution(
                    vec![not_orig, plan.and_term],
                    plan.intro_eq,
                    ep,
                    intro,
                );
                let r_and =
                    new_proof.add_resolution(vec![plan.and_term], plan.orig, r_eq, assume_id);
                let not_and = self.ctx.terms.mk_not_raw(plan.and_term);
                let ap = new_proof.add_rule_step(
                    AletheRule::AndPos(1),
                    vec![not_and, plan.ite_def],
                    Vec::new(),
                    Vec::new(),
                );
                let r_def = new_proof.add_resolution(vec![plan.ite_def], plan.and_term, ap, r_and);
                // ite2 ⊢ (cl (not c) (= s u)); ite1 ⊢ (cl c (= s v))
                let it2 = new_proof.add_rule_step(
                    AletheRule::Ite2,
                    vec![not_cond, plan.eq_then],
                    vec![r_def],
                    Vec::new(),
                );
                let it1 = new_proof.add_rule_step(
                    AletheRule::Ite1,
                    vec![plan.cond, plan.eq_else],
                    vec![r_def],
                    Vec::new(),
                );
                // Certified opaque-atom transfer lemmas (validated during
                // planning): (cl (not (= s u)) (not P) A) and the else twin.
                // The defined-equality variant carries the bound original as
                // a fourth literal, discharged by its own assume below.
                let bound_info = match plan.bound {
                    None => None,
                    Some(bound) => {
                        let Some(&bound_assume) = lift_assume.get(&bound) else {
                            return false;
                        };
                        let not_bound = self.ctx.terms.mk_not_raw(bound);
                        Some((bound, not_bound, bound_assume))
                    }
                };
                let (b_then, b_else) = match bound_info {
                    None => (
                        Self::add_triple_lemma(
                            &mut new_proof,
                            not_eq_then,
                            not_orig,
                            plan.lifted_then,
                        ),
                        Self::add_triple_lemma(
                            &mut new_proof,
                            not_eq_else,
                            not_orig,
                            plan.lifted_else,
                        ),
                    ),
                    Some((_, not_bound, _)) => (
                        Self::add_quad_lemma(
                            &mut new_proof,
                            not_eq_then,
                            not_orig,
                            not_bound,
                            plan.lifted_then,
                        ),
                        Self::add_quad_lemma(
                            &mut new_proof,
                            not_eq_else,
                            not_orig,
                            not_bound,
                            plan.lifted_else,
                        ),
                    ),
                };
                // ite_neg2 ⊢ (cl G (not c) (not A)); ite_neg1 ⊢ (cl G c (not B))
                let n2 = new_proof.add_rule_step(
                    AletheRule::IteNeg2,
                    vec![plan.goal, not_cond, not_lifted_then],
                    Vec::new(),
                    Vec::new(),
                );
                let n1 = new_proof.add_rule_step(
                    AletheRule::IteNeg1,
                    vec![plan.goal, plan.cond, not_lifted_else],
                    Vec::new(),
                    Vec::new(),
                );
                let bound_tail = |lits: &[TermId]| -> Vec<TermId> {
                    let mut lits = lits.to_vec();
                    if let Some((_, not_bound, _)) = bound_info {
                        lits.push(not_bound);
                    }
                    lits
                };
                let g1 = new_proof.add_resolution(
                    bound_tail(&[plan.goal, not_cond, not_eq_then, not_orig]),
                    plan.lifted_then,
                    n2,
                    b_then,
                );
                let g2 = new_proof.add_resolution(
                    bound_tail(&[plan.goal, not_cond, not_orig]),
                    plan.eq_then,
                    g1,
                    it2,
                );
                let mut g3 = new_proof.add_resolution(
                    bound_tail(&[plan.goal, not_cond]),
                    plan.orig,
                    g2,
                    assume_id,
                );
                if let Some((bound, _, bound_assume)) = bound_info {
                    g3 = new_proof.add_resolution(
                        vec![plan.goal, not_cond],
                        bound,
                        g3,
                        bound_assume,
                    );
                }
                let h1 = new_proof.add_resolution(
                    bound_tail(&[plan.goal, plan.cond, not_eq_else, not_orig]),
                    plan.lifted_else,
                    n1,
                    b_else,
                );
                let h2 = new_proof.add_resolution(
                    bound_tail(&[plan.goal, plan.cond, not_orig]),
                    plan.eq_else,
                    h1,
                    it1,
                );
                let mut h3 = new_proof.add_resolution(
                    bound_tail(&[plan.goal, plan.cond]),
                    plan.orig,
                    h2,
                    assume_id,
                );
                if let Some((bound, _, bound_assume)) = bound_info {
                    h3 = new_proof.add_resolution(
                        vec![plan.goal, plan.cond],
                        bound,
                        h3,
                        bound_assume,
                    );
                }
                let g = new_proof.add_resolution(vec![plan.goal], plan.cond, g3, h3);
                map[idx] = Some(g);
                continue;
            }
            if let Some(plan) = or_units.get(&idx) {
                let Some(&assume_id) = lift_assume.get(&plan.orig) else {
                    return false;
                };
                // Decompose the disjunction, then eliminate every non-unit
                // disjunct against its complementary original's assume.
                let mut cur = new_proof.add_rule_step(
                    AletheRule::Or,
                    plan.disjuncts.clone(),
                    vec![assume_id],
                    Vec::new(),
                );
                let mut remaining = plan.disjuncts.clone();
                for &(pivot, comp) in &plan.eliminations {
                    let Some(&comp_assume) = lift_assume.get(&comp) else {
                        return false;
                    };
                    remaining.retain(|&l| atom_of(&self.ctx.terms, l) != pivot);
                    cur = new_proof.add_resolution(remaining.clone(), pivot, cur, comp_assume);
                }
                map[idx] = Some(cur);
                continue;
            }
            if let Some(plan) = taut_units.get(&idx) {
                let unit = match taut_unit_of_term.get(&plan.term) {
                    Some(&u) => u,
                    None => {
                        let u = self.emit_or_tautology_derivation(&mut new_proof, plan);
                        taut_unit_of_term.insert(plan.term, u);
                        u
                    }
                };
                map[idx] = Some(unit);
                continue;
            }
            if let Some(plan) = euf_lemmas.get(&idx) {
                let plan = plan.clone();
                let unit = match plan
                    .or_term()
                    .and_then(|t| euf_unit_of_term.get(&t).copied())
                {
                    Some(u) => u,
                    None => {
                        let u = self.emit_euf_lemma(&mut new_proof, &plan);
                        if let Some(t) = plan.or_term() {
                            euf_unit_of_term.insert(t, u);
                        }
                        u
                    }
                };
                map[idx] = Some(unit);
                continue;
            }
            if let Some(plan) = quant_consequences.get(&idx) {
                // Derive the instance from the original forall's assume,
                // then close onto the trust unit with the re-verified
                // la_generic combination and one resolution per consumed
                // original premise (#quant-expansion-proof).
                let Some(&assume_id) = lift_assume.get(&plan.forall_term) else {
                    return false;
                };
                let inst_unit = self.emit_quant_instance_chain(
                    &mut new_proof,
                    plan.forall_term,
                    assume_id,
                    &plan.chain,
                );
                #[allow(clippy::cast_possible_truncation)]
                let coeffs = vec![1i64; plan.lemma.len()];
                let lemma_id = new_proof.add_step(ProofStep::TheoryLemma {
                    theory: "LRA".to_string(),
                    clause: plan.lemma.clone(),
                    farkas: Some(FarkasAnnotation::from_ints(&coeffs)),
                    kind: TheoryLemmaKind::LraFarkas,
                    lia: None,
                });
                let inst_pivot = atom_of(&self.ctx.terms, plan.chain.target);
                let mut cur = new_proof.add_resolution(
                    plan.lemma[1..].to_vec(),
                    inst_pivot,
                    lemma_id,
                    inst_unit,
                );
                for (i, &support) in plan.supports.iter().enumerate() {
                    let Some(&support_id) = lift_assume.get(&support) else {
                        return false;
                    };
                    let pivot = atom_of(&self.ctx.terms, support);
                    cur = new_proof.add_resolution(
                        plan.lemma[i + 2..].to_vec(),
                        pivot,
                        cur,
                        support_id,
                    );
                }
                map[idx] = Some(cur);
                continue;
            }
            if let Some(&(a_idx, pos)) = unit_patterns.get(&idx) {
                let Some(&assume_id) = assume_new_id.get(&a_idx) else {
                    return false;
                };
                let unit = match &assume_plans[&a_idx] {
                    AssumePlan::Distinct {
                        and_term, conjs, ..
                    } => {
                        let Some(&and_unit) = distinct_unit.get(&a_idx) else {
                            return false;
                        };
                        let (and_term, conj) = (*and_term, conjs[pos]);
                        let not_and = self.ctx.terms.mk_not_raw(and_term);
                        #[allow(clippy::cast_possible_truncation)]
                        let p = new_proof.add_rule_step(
                            AletheRule::AndPos(pos as u32),
                            vec![not_and, conj],
                            Vec::new(),
                            Vec::new(),
                        );
                        new_proof.add_resolution(vec![conj], and_term, p, and_unit)
                    }
                    AssumePlan::AndBounds {
                        raw_and,
                        raws,
                        conjs,
                    } => {
                        let (raw_and, conj) = (*raw_and, conjs[pos]);
                        let (raw, bridge_atom) = raws[pos];
                        let not_raw_and = self.ctx.terms.mk_not_raw(raw_and);
                        #[allow(clippy::cast_possible_truncation)]
                        let p = new_proof.add_rule_step(
                            AletheRule::AndPos(pos as u32),
                            vec![not_raw_and, raw],
                            Vec::new(),
                            Vec::new(),
                        );
                        let u0 = new_proof.add_resolution(vec![raw], raw_and, p, assume_id);
                        match bridge_atom {
                            None => u0,
                            Some(atom) => {
                                let raw_complement = complement_of(&mut self.ctx.terms, raw);
                                let lemma =
                                    Self::add_pair_lemma(&mut new_proof, conj, raw_complement);
                                new_proof.add_resolution(vec![conj], atom, lemma, u0)
                            }
                        }
                    }
                    AssumePlan::AndDistinct { .. } => {
                        // The plan's per-conjunct units were derived when the
                        // assume itself was walked (assume idx < consumer idx).
                        let Some(units) = anddistinct_units.get(&a_idx) else {
                            return false;
                        };
                        let Some(&unit) = units.get(pos) else {
                            return false;
                        };
                        unit
                    }
                    AssumePlan::QuantExpansion { forall_term, .. } => {
                        // Derive (once per conjunct) the unit from the
                        // ORIGINAL forall's assume via the plan-time-built
                        // forall_inst chain (#quant-expansion-proof).
                        let forall_term = *forall_term;
                        if let Some(&unit) = quant_units_emitted.get(&(a_idx, pos)) {
                            unit
                        } else {
                            let Some(chain) = quant_chains.get(&(a_idx, pos)) else {
                                return false;
                            };
                            let unit = self.emit_quant_instance_chain(
                                &mut new_proof,
                                forall_term,
                                assume_id,
                                chain,
                            );
                            quant_units_emitted.insert((a_idx, pos), unit);
                            unit
                        }
                    }
                    // Unit patterns are never planned against a `Literal`
                    // assume (step 3 skips it).
                    AssumePlan::Literal { .. } => return false,
                };
                map[idx] = Some(unit);
                continue;
            }
            match &proof.steps[idx] {
                ProofStep::Assume(_) => {
                    let Some(plan) = assume_plans.get(&idx) else {
                        continue; // faithful assume, already mapped
                    };
                    match plan {
                        AssumePlan::Distinct {
                            raw,
                            and_term,
                            conjs: _,
                        } => {
                            let (raw, and_term) = (*raw, *and_term);
                            let Some(&assume_id) = assume_new_id.get(&idx) else {
                                return false;
                            };
                            let equiv = self.ctx.terms.mk_app(
                                Symbol::named("="),
                                [raw, and_term],
                                Sort::Bool,
                            );
                            let not_equiv = self.ctx.terms.mk_not_raw(equiv);
                            let not_raw = self.ctx.terms.mk_not_raw(raw);
                            let de = new_proof.add_rule_step(
                                AletheRule::DistinctElim,
                                vec![equiv],
                                Vec::new(),
                                Vec::new(),
                            );
                            let ep = new_proof.add_rule_step(
                                AletheRule::EquivPos2,
                                vec![not_equiv, not_raw, and_term],
                                Vec::new(),
                                Vec::new(),
                            );
                            let r1 =
                                new_proof.add_resolution(vec![not_raw, and_term], equiv, ep, de);
                            let unit = new_proof.add_resolution(vec![and_term], raw, r1, assume_id);
                            distinct_unit.insert(idx, unit);
                            map[idx] = Some(unit);
                        }
                        AssumePlan::AndBounds { .. } => {
                            // Consumers were all verified to be unit
                            // patterns; the raw assume itself was already
                            // emitted in the hoist. Nothing to map.
                        }
                        AssumePlan::QuantExpansion { .. } => {
                            // Same discipline as AndBounds: every consumer is
                            // a unit pattern re-derived from the hoisted
                            // ORIGINAL forall assume. Nothing to map.
                        }
                        AssumePlan::AndDistinct {
                            raw_and,
                            and_term,
                            units,
                            conjs,
                        } => {
                            // Re-derive the canonical conjunction as a unit:
                            // extract every contributing raw conjunct, bridge
                            // the sugared ones, close with `and_neg`; every
                            // consumer is remapped onto the derived unit.
                            let (raw_and, and_term) = (*raw_and, *and_term);
                            let (units, conjs) = (units.clone(), conjs.clone());
                            let Some(&assume_id) = assume_new_id.get(&idx) else {
                                return false;
                            };
                            let not_raw_and = self.ctx.terms.mk_not_raw(raw_and);
                            let mut unit_ids: Vec<ProofId> = Vec::with_capacity(conjs.len());
                            let mut k = 0usize;
                            for u in &units {
                                let p = new_proof.add_rule_step(
                                    AletheRule::AndPos(u.pos),
                                    vec![not_raw_and, u.raw],
                                    Vec::new(),
                                    Vec::new(),
                                );
                                let u0 =
                                    new_proof.add_resolution(vec![u.raw], raw_and, p, assume_id);
                                match &u.kind {
                                    AndDistinctKind::Plain => {
                                        unit_ids.push(u0);
                                        k += 1;
                                    }
                                    AndDistinctKind::Arith { atom } => {
                                        let atom = *atom;
                                        let conj = conjs[k];
                                        let raw_complement =
                                            complement_of(&mut self.ctx.terms, u.raw);
                                        let lemma = Self::add_pair_lemma(
                                            &mut new_proof,
                                            conj,
                                            raw_complement,
                                        );
                                        unit_ids.push(new_proof.add_resolution(
                                            vec![conj],
                                            atom,
                                            lemma,
                                            u0,
                                        ));
                                        k += 1;
                                    }
                                    AndDistinctKind::DistinctBinary => {
                                        let conj = conjs[k];
                                        let equiv = self.ctx.terms.mk_app(
                                            Symbol::named("="),
                                            [u.raw, conj],
                                            Sort::Bool,
                                        );
                                        let not_equiv = self.ctx.terms.mk_not_raw(equiv);
                                        let not_raw = self.ctx.terms.mk_not_raw(u.raw);
                                        let de = new_proof.add_rule_step(
                                            AletheRule::DistinctElim,
                                            vec![equiv],
                                            Vec::new(),
                                            Vec::new(),
                                        );
                                        let ep = new_proof.add_rule_step(
                                            AletheRule::EquivPos2,
                                            vec![not_equiv, not_raw, conj],
                                            Vec::new(),
                                            Vec::new(),
                                        );
                                        let r1 = new_proof.add_resolution(
                                            vec![not_raw, conj],
                                            equiv,
                                            ep,
                                            de,
                                        );
                                        unit_ids.push(new_proof.add_resolution(
                                            vec![conj],
                                            u.raw,
                                            r1,
                                            u0,
                                        ));
                                        k += 1;
                                    }
                                    AndDistinctKind::DistinctNary {
                                        and_term: block,
                                        count,
                                    } => {
                                        let (block, count) = (*block, *count);
                                        let equiv = self.ctx.terms.mk_app(
                                            Symbol::named("="),
                                            [u.raw, block],
                                            Sort::Bool,
                                        );
                                        let not_equiv = self.ctx.terms.mk_not_raw(equiv);
                                        let not_raw = self.ctx.terms.mk_not_raw(u.raw);
                                        let not_block = self.ctx.terms.mk_not_raw(block);
                                        let de = new_proof.add_rule_step(
                                            AletheRule::DistinctElim,
                                            vec![equiv],
                                            Vec::new(),
                                            Vec::new(),
                                        );
                                        let ep = new_proof.add_rule_step(
                                            AletheRule::EquivPos2,
                                            vec![not_equiv, not_raw, block],
                                            Vec::new(),
                                            Vec::new(),
                                        );
                                        let r1 = new_proof.add_resolution(
                                            vec![not_raw, block],
                                            equiv,
                                            ep,
                                            de,
                                        );
                                        let block_unit =
                                            new_proof.add_resolution(vec![block], u.raw, r1, u0);
                                        for j in 0..count {
                                            let conj = conjs[k];
                                            let ap = new_proof.add_rule_step(
                                                AletheRule::AndPos(j),
                                                vec![not_block, conj],
                                                Vec::new(),
                                                Vec::new(),
                                            );
                                            unit_ids.push(new_proof.add_resolution(
                                                vec![conj],
                                                block,
                                                ap,
                                                block_unit,
                                            ));
                                            k += 1;
                                        }
                                    }
                                    AndDistinctKind::OrPerm { lits } => {
                                        // (cl r_1 .. r_n) from the raw unit
                                        // (full duplicate-preserving disjunct
                                        // list), contracted to the unique
                                        // literals the alignment covers.
                                        let conj = conjs[k];
                                        let TermData::App(_, full) = self.ctx.terms.get(u.raw)
                                        else {
                                            return false;
                                        };
                                        let full = full.clone();
                                        let mut clause: Vec<TermId> =
                                            lits.iter().map(|&(r, _)| r).collect();
                                        let mut cur = new_proof.add_rule_step(
                                            AletheRule::Or,
                                            full.clone(),
                                            vec![u0],
                                            Vec::new(),
                                        );
                                        if full.len() != clause.len() {
                                            cur = new_proof.add_rule_step(
                                                AletheRule::Contraction,
                                                clause.clone(),
                                                vec![cur],
                                                Vec::new(),
                                            );
                                        }
                                        // Flip each misoriented literal via a
                                        // certified eq_symmetric bridge.
                                        for (i, &(r, c)) in lits.iter().enumerate() {
                                            if r == c {
                                                continue;
                                            }
                                            let (pivot, bridge) =
                                                self.add_eq_flip_bridge(&mut new_proof, r, c);
                                            clause[i] = c;
                                            cur = new_proof.add_resolution(
                                                clause.clone(),
                                                pivot,
                                                cur,
                                                bridge,
                                            );
                                        }
                                        // or_neg permutation closure onto the
                                        // canonical or-term.
                                        for &(_, c) in lits.iter() {
                                            let not_c = self.ctx.terms.mk_not_raw(c);
                                            let on = new_proof.add_rule_step(
                                                AletheRule::OrNeg,
                                                vec![conj, not_c],
                                                Vec::new(),
                                                Vec::new(),
                                            );
                                            if let Some(p) = clause.iter().position(|&l| l == c) {
                                                // Resolution surgery: the removed
                                                // literal is the pivot `c`, already
                                                // in hand — its id is not needed.
                                                let _ = clause.remove(p);
                                            }
                                            clause.push(conj);
                                            cur = new_proof.add_resolution(
                                                clause.clone(),
                                                c,
                                                cur,
                                                on,
                                            );
                                        }
                                        unit_ids.push(new_proof.add_rule_step(
                                            AletheRule::Contraction,
                                            vec![conj],
                                            vec![cur],
                                            Vec::new(),
                                        ));
                                        k += 1;
                                    }
                                }
                            }
                            if k != conjs.len() || unit_ids.len() != conjs.len() {
                                return false;
                            }
                            anddistinct_units.insert(idx, unit_ids.clone());
                            let mut clause: Vec<TermId> = Vec::with_capacity(conjs.len() + 1);
                            clause.push(and_term);
                            for &c in &conjs {
                                clause.push(self.ctx.terms.mk_not_raw(c));
                            }
                            let mut cur = new_proof.add_rule_step(
                                AletheRule::AndNeg,
                                clause.clone(),
                                Vec::new(),
                                Vec::new(),
                            );
                            for (&conj, &unit) in conjs.iter().zip(unit_ids.iter()) {
                                let not_conj = self.ctx.terms.mk_not_raw(conj);
                                if let Some(pos) = clause.iter().position(|&l| l == not_conj) {
                                    let _ = clause.remove(pos);
                                }
                                cur = new_proof.add_resolution(clause.clone(), conj, cur, unit);
                            }
                            map[idx] = Some(cur);
                        }
                        AssumePlan::Literal {
                            raw,
                            atom,
                            canonical,
                        } => {
                            // Certified orientation bridge (validated during
                            // planning): (cl canonical (not raw)) resolved
                            // against the raw assume yields the canonical
                            // unit every downstream consumer expects.
                            let (raw, atom, canonical) = (*raw, *atom, *canonical);
                            let Some(&assume_id) = assume_new_id.get(&idx) else {
                                return false;
                            };
                            let raw_complement = complement_of(&mut self.ctx.terms, raw);
                            let lemma =
                                Self::add_pair_lemma(&mut new_proof, canonical, raw_complement);
                            let unit =
                                new_proof.add_resolution(vec![canonical], atom, lemma, assume_id);
                            map[idx] = Some(unit);
                        }
                    }
                }
                ProofStep::Step {
                    rule,
                    clause,
                    premises,
                    args,
                } => {
                    let mut new_premises = Vec::with_capacity(premises.len());
                    for p in premises {
                        let Some(mapped) = map[p.0 as usize] else {
                            return false;
                        };
                        new_premises.push(mapped);
                    }
                    // An `or` decomposition of a re-derived tautology unit
                    // may list the disjuncts in a scrambled (solver-trail)
                    // order that the Alethe `or` rule rejects: reorder the
                    // clause to the or-term's own disjunct order when it is
                    // a permutation of it (set-equivalent, so every
                    // downstream resolution still checks), fail-closed
                    // otherwise.
                    let mut clause = clause.clone();
                    if matches!(rule, AletheRule::Or) && premises.len() == 1 {
                        let src = premises[0].0 as usize;
                        let taut_term = taut_units
                            .get(&src)
                            .map(|plan| plan.term)
                            .or_else(|| euf_lemmas.get(&src).and_then(EufLemmaPlan::or_term));
                        if let Some(taut_term) = taut_term {
                            let TermData::App(Symbol::Named(op), disjuncts) =
                                self.ctx.terms.get(taut_term)
                            else {
                                return false;
                            };
                            if op != "or" {
                                return false;
                            }
                            let disjuncts = disjuncts.clone();
                            let mut want = disjuncts.clone();
                            let mut have = clause.clone();
                            want.sort_unstable();
                            have.sort_unstable();
                            if want != have {
                                return false;
                            }
                            clause = disjuncts;
                        }
                    }
                    let id =
                        new_proof.add_rule_step(rule.clone(), clause, new_premises, args.clone());
                    map[idx] = Some(id);
                }
                ProofStep::Resolution {
                    clause,
                    pivot,
                    clause1,
                    clause2,
                } => {
                    let (Some(c1), Some(c2)) = (map[clause1.0 as usize], map[clause2.0 as usize])
                    else {
                        return false;
                    };
                    let id = new_proof.add_resolution(clause.clone(), *pivot, c1, c2);
                    map[idx] = Some(id);
                }
                ProofStep::TheoryLemma { .. } => {
                    let id = new_proof.add_step(proof.steps[idx].clone());
                    map[idx] = Some(id);
                }
                _ => return false,
            }
        }

        // (5) The rebuilt proof must be trust-free (that was the point).
        let report = ay_proof::terminal_trust_report(&new_proof);
        if report.trust_rule_on_path > 0 || report.trust_theory_lemma_on_path > 0 {
            return false;
        }

        // (5b) EUF-lemma surgeries re-validate the WHOLE rebuilt proof with
        // the strict checker before swapping it in: any construction miss
        // keeps the original proof (fail-closed; USER LAW: never a wrong
        // proof step).
        let has_or_perm = assume_plans.values().any(|p| {
            matches!(p, AssumePlan::AndDistinct { units, .. }
                if units.iter().any(|u| matches!(u.kind, AndDistinctKind::OrPerm { .. })))
        });
        if (!euf_lemmas.is_empty() || has_or_perm)
            && ay_proof::check_proof_strict(&new_proof, &self.ctx.terms).is_err()
        {
            return false;
        }

        // Success. Override-purge discipline: every term the trichotomy /
        // assume-bridge surgery prints is raw-interned or canonical; a stale
        // surface override collected during the ordinary export could corrupt
        // the rigid `la_disequality` / `distinct_elim` / `and_pos` literal
        // shapes. The ite-lift surgery is the opposite: its re-added original
        // assume MUST print with the problem file's surface syntax (Carcara
        // matches assumes syntactically), so the overrides are kept — every
        // step of the lift derivation is built from the same canonical
        // subterms, so the override map keeps the printout globally
        // consistent.
        *proof = new_proof;
        fn collect(
            ctx: &mut ay_frontend::Context,
            originals: &[(TermId, FrontendTerm)],
            canonical: TermId,
            overrides: &mut HashMap<TermId, String>,
        ) {
            if let Some((canonical, parsed)) = originals.iter().find(|(c, _)| *c == canonical) {
                let (canonical, parsed) = (*canonical, parsed.clone());
                super::proof_surface_syntax::collect_surface_term_overrides(
                    ctx, canonical, &parsed, overrides,
                );
                super::proof_surface_syntax::collect_deep_arith_surface_overrides(
                    ctx, &parsed, overrides,
                );
            }
        }
        if ite_lifts.is_empty() && or_units.is_empty() {
            // Tautology-ONLY surgeries keep the collected overrides: their
            // derivations are built purely from subterms of the (already
            // consistently printed) tautological term, while the SURVIVING
            // original assumes still need their surface spellings to match
            // the problem file. The purge below protects the rigid
            // raw-interned shapes of the trichotomy / assume-bridge classes
            // only.
            if !trichotomies.is_empty() || !assume_plans.is_empty() {
                self.last_proof_term_overrides = None;
            }
        } else {
            // The preprocessor consumed the re-added originals before the
            // ordinary export collected overrides for them: collect the
            // surface spellings now so the re-added assumes (and every
            // derivation occurrence of their subterms) print like the
            // problem file.
            let mut overrides = self.last_proof_term_overrides.take().unwrap_or_default();
            for plan in ite_lifts.values() {
                collect(&mut self.ctx, originals, plan.orig, &mut overrides);
                if let Some(bound) = plan.bound {
                    collect(&mut self.ctx, originals, bound, &mut overrides);
                }
                // Re-interned surface premise: collect via its canonical
                // source, then copy the source's whole-assertion spelling
                // onto the premise term itself.
                if let Some(source) = plan.defining_source {
                    collect(&mut self.ctx, originals, source, &mut overrides);
                    if let Some(s) = overrides.get(&source).cloned() {
                        overrides.insert(plan.orig, s);
                    }
                }
            }
            for plan in or_units.values() {
                collect(&mut self.ctx, originals, plan.orig, &mut overrides);
                for &(_, comp) in &plan.eliminations {
                    collect(&mut self.ctx, originals, comp, &mut overrides);
                }
            }
            self.last_proof_term_overrides = Some(overrides);
        }
        // Quant-expansion surgeries re-introduce ORIGINAL premises (the
        // forall and any consequence supports) that the purge above may have
        // stripped: re-collect exactly their surface spellings so the
        // re-added assumes — and every derivation occurrence of the forall
        // term — print like the problem file (#quant-expansion-proof). The
        // rigid raw-interned instance chains reference no overridden term.
        if has_quant_plans {
            let mut quant_override_targets: Vec<TermId> = Vec::new();
            for plan in assume_plans.values() {
                if let AssumePlan::QuantExpansion { forall_term, .. } = plan {
                    quant_override_targets.push(*forall_term);
                }
            }
            for plan in quant_consequences.values() {
                quant_override_targets.push(plan.forall_term);
                quant_override_targets.extend(plan.supports.iter().copied());
            }
            let mut overrides = self.last_proof_term_overrides.take().unwrap_or_default();
            for t in quant_override_targets {
                collect(&mut self.ctx, originals, t, &mut overrides);
            }
            self.last_proof_term_overrides = Some(overrides);
        }
        true
    }

    /// Recognize a trust step's clause as an Int trichotomy lemma
    /// `(cl (or (= x y) S1 S2))` with a single `or`-split consumer, and
    /// pre-verify both `[1, 1]` strengthening bridges (fail-closed).
    fn plan_trichotomy(
        &mut self,
        proof: &Proof,
        clause: &[TermId],
        consumers: &[usize],
        trust_idx: usize,
    ) -> Option<TrichotomyPlan> {
        if clause.len() != 1 {
            return None;
        }
        let TermData::App(Symbol::Named(name), disjuncts) = self.ctx.terms.get(clause[0]) else {
            return None;
        };
        if name != "or" || disjuncts.len() != 3 {
            return None;
        }
        let disjuncts = disjuncts.clone();
        // Exactly one equality disjunct over Int operands.
        let mut eq_pos: Option<usize> = None;
        for (i, &d) in disjuncts.iter().enumerate() {
            if let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(d) {
                if op == "=" && args.len() == 2 {
                    if eq_pos.is_some() {
                        return None;
                    }
                    eq_pos = Some(i);
                }
            }
        }
        let eq_pos = eq_pos?;
        let eq = disjuncts[eq_pos];
        let TermData::App(_, eq_args) = self.ctx.terms.get(eq) else {
            return None;
        };
        let (x, y) = (eq_args[0], eq_args[1]);
        if *self.ctx.terms.sort(x) != Sort::Int || *self.ctx.terms.sort(y) != Sort::Int {
            return None;
        }
        let mut strengthened = disjuncts
            .iter()
            .enumerate()
            .filter(|&(i, _)| i != eq_pos)
            .map(|(_, &d)| d);
        let (s1, s2) = (strengthened.next()?, strengthened.next()?);

        // The `la_disequality` split literals (raw operand order is the
        // rule's rigid shape; fail-closed on constant-fold surprises).
        let le_xy = self
            .ctx
            .terms
            .mk_app(Symbol::named("<="), [x, y], Sort::Bool);
        let le_yx = self
            .ctx
            .terms
            .mk_app(Symbol::named("<="), [y, x], Sort::Bool);
        for le in [le_xy, le_yx] {
            let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(le) else {
                return None;
            };
            if op != "<=" || args.len() != 2 {
                return None;
            }
        }
        let not_le_xy = self.ctx.terms.mk_not_raw(le_xy);
        let not_le_yx = self.ctx.terms.mk_not_raw(le_yx);
        let or_term =
            self.ctx
                .terms
                .mk_app(Symbol::named("or"), [eq, not_le_xy, not_le_yx], Sort::Bool);

        // Pair each strengthened disjunct with the split literal that
        // implies it, VERIFYING the `[1, 1]` certificate both ways
        // (never pattern-match what a checker can decide).
        let (strong_from_yx, strong_from_xy) =
            if self.pair_lemma_valid(s1, le_yx) && self.pair_lemma_valid(s2, le_xy) {
                (s1, s2)
            } else if self.pair_lemma_valid(s2, le_yx) && self.pair_lemma_valid(s1, le_xy) {
                (s2, s1)
            } else {
                return None;
            };

        // Exactly one consumer: the `or` split of this trust step, whose
        // clause is the same 3-literal set the derivation reproduces.
        let mut uniq: Vec<usize> = consumers.to_vec();
        uniq.sort_unstable();
        uniq.dedup();
        if uniq.len() != 1 {
            return None;
        }
        let or_split_idx = uniq[0];
        let ProofStep::Step {
            rule: AletheRule::Or,
            clause: split_clause,
            premises,
            ..
        } = &proof.steps[or_split_idx]
        else {
            return None;
        };
        if premises.len() != 1 || premises[0].0 as usize != trust_idx {
            return None;
        }
        let mut want = vec![eq, strong_from_yx, strong_from_xy];
        let mut have = split_clause.clone();
        want.sort_unstable();
        have.sort_unstable();
        if want != have {
            return None;
        }

        Some(TrichotomyPlan {
            or_split_idx,
            eq,
            le_xy,
            le_yx,
            not_le_xy,
            not_le_yx,
            or_term,
            strong_from_yx,
            strong_from_xy,
        })
    }

    /// Recognize a trust step's clause as a lifted term-ite input
    /// `(cl (ite c A B))` where some ORIGINAL assertion `P` contains a
    /// term-level ite `s = (ite c u v)` with `A = P[s/u]` and `B = P[s/v]`
    /// (re-canonicalized substitution — exact `TermId` equality, so the match
    /// cannot be approximate). Both opaque-atom transfer lemmas
    /// `(cl (not (= s u)) (not P) A)` / `(cl (not (= s v)) (not P) B)` are
    /// pre-verified `[1, 1, 1]` Farkas certificates (fail-closed), and every
    /// constructed connective is shape-checked against constant-fold
    /// surprises.
    fn plan_ite_lift(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
    ) -> Option<IteLiftPlan> {
        if clause.len() != 1 {
            return None;
        }
        let goal = clause[0];
        let TermData::Ite(cond, lifted_then, lifted_else) = *self.ctx.terms.get(goal) else {
            return None;
        };
        for &(orig, _) in originals {
            // Collect the term-level ite subterms of `orig` that share the
            // lifted condition.
            let mut candidates: Vec<(TermId, TermId, TermId)> = Vec::new();
            let mut stack = vec![orig];
            let mut seen: Vec<TermId> = Vec::new();
            while let Some(t) = stack.pop() {
                if seen.contains(&t) {
                    continue;
                }
                seen.push(t);
                match self.ctx.terms.get(t) {
                    TermData::Not(inner) => stack.push(*inner),
                    TermData::Ite(c, a, b) => {
                        if *c == cond && *self.ctx.terms.sort(t) != Sort::Bool {
                            candidates.push((t, *a, *b));
                        }
                        stack.extend([*c, *a, *b]);
                    }
                    TermData::App(_, args) => stack.extend(args.iter().copied()),
                    _ => {}
                }
            }
            for (ite_term, u, v) in candidates {
                let then_subst = self.ctx.terms.substitute(orig, &[ite_term], &[u]);
                let else_subst = self.ctx.terms.substitute(orig, &[ite_term], &[v]);
                if then_subst != lifted_then || else_subst != lifted_else {
                    continue;
                }
                let Some((eq_then, eq_else, ite_def, and_term, intro_eq)) =
                    self.build_ite_lift_connectives(orig, cond, ite_term, u, v)
                else {
                    continue;
                };
                // Verify both transfer lemmas (fail-closed; never
                // pattern-match what a checker can decide).
                if !self.triple_lemma_valid(eq_then, orig, lifted_then)
                    || !self.triple_lemma_valid(eq_else, orig, lifted_else)
                {
                    continue;
                }
                return Some(IteLiftPlan {
                    orig,
                    defining_source: None,
                    bound: None,
                    cond,
                    lifted_then,
                    lifted_else,
                    goal,
                    eq_then,
                    eq_else,
                    ite_def,
                    and_term,
                    intro_eq,
                });
            }
        }
        // Defined-equality substitution variant: an original `(= d (ite c u
        // v))` defines `d`, a SECOND original `P(d)` bounds it, and the
        // lifted clause is `(ite c P[d/u] P[d/v])`. Elaboration itself lifts
        // the defining equality to the formula-level `(ite c (= d u) (= d
        // v))`, so the surface equality is recovered from the PARSED
        // original: its operands re-elaborate and the equality re-interns
        // (surface operand order) as the derivation's premise `P` — an
        // opaque-atom linear equality the transfer lemmas can carry. The
        // `ite_intro` derivation runs on that premise; the transfer lemmas
        // gain the bound original as a fourth certified literal.
        for (canonical, parsed) in originals {
            let (canonical, stripped) = (*canonical, strip_frontend_annotations(parsed).clone());
            let FrontendTerm::App(op, sides) = &stripped else {
                continue;
            };
            if op != "=" || sides.len() != 2 {
                continue;
            }
            for ite_side in [0usize, 1] {
                let ite_surface = strip_frontend_annotations(&sides[ite_side]).clone();
                let def_surface = strip_frontend_annotations(&sides[1 - ite_side]).clone();
                let FrontendTerm::App(iop, iargs) = &ite_surface else {
                    continue;
                };
                if iop != "ite" || iargs.len() != 3 {
                    continue;
                }
                let iargs = iargs.clone();
                let (Some(c), Some(u), Some(v), Some(defined)) = (
                    self.ctx.elaborate_surface_subterm(&iargs[0]),
                    self.ctx.elaborate_surface_subterm(&iargs[1]),
                    self.ctx.elaborate_surface_subterm(&iargs[2]),
                    self.ctx.elaborate_surface_subterm(&def_surface),
                ) else {
                    continue;
                };
                if c != cond {
                    continue;
                }
                let ite_term = self.ctx.terms.mk_ite(cond, u, v);
                if *self.ctx.terms.sort(ite_term) == Sort::Bool
                    || !matches!(
                        self.ctx.terms.get(ite_term),
                        TermData::Ite(ic, iu, iv) if *ic == cond && *iu == u && *iv == v
                    )
                {
                    continue;
                }
                // The defining equality, re-interned in SURFACE operand order
                // (fail-closed if interning folds it away from that shape).
                let ordered = if ite_side == 0 {
                    [ite_term, defined]
                } else {
                    [defined, ite_term]
                };
                let p_raw = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("="), ordered, Sort::Bool);
                if !matches!(
                    self.ctx.terms.get(p_raw),
                    TermData::App(Symbol::Named(eop), eargs)
                        if eop == "=" && eargs.as_slice() == ordered
                ) {
                    continue;
                }
                for &(bound, _) in originals {
                    if bound == canonical {
                        continue;
                    }
                    let then_subst = self.ctx.terms.substitute(bound, &[defined], &[u]);
                    let else_subst = self.ctx.terms.substitute(bound, &[defined], &[v]);
                    if then_subst != lifted_then || else_subst != lifted_else {
                        continue;
                    }
                    let Some((eq_then, eq_else, ite_def, and_term, intro_eq)) =
                        self.build_ite_lift_connectives(p_raw, cond, ite_term, u, v)
                    else {
                        continue;
                    };
                    if !self.quad_lemma_valid(eq_then, p_raw, bound, lifted_then)
                        || !self.quad_lemma_valid(eq_else, p_raw, bound, lifted_else)
                    {
                        continue;
                    }
                    return Some(IteLiftPlan {
                        orig: p_raw,
                        defining_source: Some(canonical),
                        bound: Some(bound),
                        cond,
                        lifted_then,
                        lifted_else,
                        goal,
                        eq_then,
                        eq_else,
                        ite_def,
                        and_term,
                        intro_eq,
                    });
                }
            }
        }
        None
    }

    /// Build and shape-check the `ite_intro` derivation's connective terms
    /// for `orig` containing the term-level `ite_term = (ite cond u v)`.
    /// Fail-closed: `None` when any raw application does not intern with the
    /// exact expected shape.
    fn build_ite_lift_connectives(
        &mut self,
        orig: TermId,
        cond: TermId,
        ite_term: TermId,
        u: TermId,
        v: TermId,
    ) -> Option<(TermId, TermId, TermId, TermId, TermId)> {
        let eq_then = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [ite_term, u], Sort::Bool);
        let eq_else = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [ite_term, v], Sort::Bool);
        let eq_shape = |terms: &ay_core::TermStore, t: TermId, l: TermId, r: TermId| {
            matches!(
                terms.get(t),
                TermData::App(Symbol::Named(op), args)
                    if op == "=" && args.len() == 2 && args[0] == l && args[1] == r
            )
        };
        if !eq_shape(&self.ctx.terms, eq_then, ite_term, u)
            || !eq_shape(&self.ctx.terms, eq_else, ite_term, v)
        {
            return None;
        }
        let ite_def = self.ctx.terms.mk_ite(cond, eq_then, eq_else);
        if !matches!(
            self.ctx.terms.get(ite_def),
            TermData::Ite(c, a, b) if *c == cond && *a == eq_then && *b == eq_else
        ) {
            return None;
        }
        let and_term = self
            .ctx
            .terms
            .mk_app(Symbol::named("and"), [orig, ite_def], Sort::Bool);
        if !matches!(
            self.ctx.terms.get(and_term),
            TermData::App(Symbol::Named(op), args)
                if op == "and" && args.len() == 2 && args[0] == orig && args[1] == ite_def
        ) {
            return None;
        }
        let intro_eq = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [orig, and_term], Sort::Bool);
        if !eq_shape(&self.ctx.terms, intro_eq, orig, and_term) {
            return None;
        }
        Some((eq_then, eq_else, ite_def, and_term, intro_eq))
    }

    /// Recognize a preprocessor-derived unit trust step `(cl L)`: an
    /// original disjunctive assertion contains `L`, and every OTHER disjunct
    /// is the syntactic complement of another original assertion (so plain
    /// resolutions against their assumes derive the unit). Fail-closed: the
    /// disjunct atoms must be pairwise distinct (unambiguous pivots) with
    /// `L` among them exactly once.
    fn plan_or_unit(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
    ) -> Option<OrUnitPlan> {
        if clause.len() != 1 {
            return None;
        }
        let lit = clause[0];
        'orig: for &(orig, _) in originals {
            let TermData::App(Symbol::Named(op), ds) = self.ctx.terms.get(orig) else {
                continue;
            };
            if op != "or" || ds.len() < 2 || !ds.contains(&lit) {
                continue;
            }
            let disjuncts = ds.clone();
            let mut atoms: Vec<TermId> = disjuncts
                .iter()
                .map(|&d| atom_of(&self.ctx.terms, d))
                .collect();
            atoms.sort_unstable();
            atoms.dedup();
            if atoms.len() != disjuncts.len() {
                continue;
            }
            let mut eliminations: Vec<(TermId, TermId)> = Vec::new();
            for &d in &disjuncts {
                if d == lit {
                    continue;
                }
                let comp = complement_of(&mut self.ctx.terms, d);
                if !originals.iter().any(|&(c, _)| c == comp) {
                    continue 'orig;
                }
                eliminations.push((atom_of(&self.ctx.terms, d), comp));
            }
            return Some(OrUnitPlan {
                orig,
                disjuncts,
                eliminations,
            });
        }
        None
    }

    /// Recognize a preprocessor-derived unit `(cl T)` as an EUF-transitivity
    /// TAUTOLOGY (see [`OrTautologyPlan`]): `T` is an `or`-term with exactly
    /// one positive binary-equality disjunct `E`, implied by the remaining
    /// disjuncts via equality transitivity. Two recognized shapes, both
    /// verified with the same all-edges-used chain check the strict
    /// `eq_transitive` checker enforces (never emit what a checker rejects):
    ///
    /// - **Plain**: every other disjunct is `(not (= s t))` and the
    ///   equalities chain from `E`'s lhs to `E`'s rhs.
    /// - **De Morgan (eq_diamond family)**: some other disjunct is
    ///   `(and D1 .. Dm)` with each `Dj = (or (not (= ..)) ..)` chaining to
    ///   `E` on its own (the unused sibling disjuncts of `T` are simply
    ///   never eliminated — the derivation reaches the `T` literal without
    ///   them).
    fn plan_or_transitivity_tautology(&mut self, clause: &[TermId]) -> Option<OrTautologyPlan> {
        if clause.len() != 1 {
            return None;
        }
        let term = clause[0];
        let terms = &self.ctx.terms;
        let TermData::App(Symbol::Named(op), disjuncts) = terms.get(term) else {
            return None;
        };
        if op != "or" || disjuncts.len() < 2 {
            return None;
        }
        let disjuncts = disjuncts.clone();
        let decode_eq = |terms: &ay_core::TermStore, t: TermId| -> Option<(TermId, TermId)> {
            match terms.get(t) {
                TermData::App(Symbol::Named(n), args) if n == "=" && args.len() == 2 => {
                    Some((args[0], args[1]))
                }
                _ => None,
            }
        };
        // Exactly one POSITIVE disjunct, and it must be a binary equality
        // (any additional positive disjunct could never be eliminated by the
        // derivation, and an ambiguous `E` is rejected outright).
        let mut eq_pos: Option<usize> = None;
        for (i, &d) in disjuncts.iter().enumerate() {
            if !matches!(terms.get(d), TermData::Not(_)) {
                if decode_eq(terms, d).is_none()
                    && !matches!(terms.get(d), TermData::App(s, _) if s.name() == "and")
                {
                    return None;
                }
                if decode_eq(terms, d).is_some() {
                    if eq_pos.is_some() {
                        return None;
                    }
                    eq_pos = Some(i);
                }
            }
        }
        let eq_pos = eq_pos?;
        let eq = disjuncts[eq_pos];
        let (lhs, rhs) = decode_eq(terms, eq)?;
        // Collect a disjunct list as negated-equality edges; `None` when any
        // entry is not `(not (= s t))`.
        let neg_edges =
            |terms: &ay_core::TermStore, lits: &[TermId]| -> Option<Vec<(TermId, TermId)>> {
                let mut edges = Vec::with_capacity(lits.len());
                for &l in lits {
                    let TermData::Not(inner) = terms.get(l) else {
                        return None;
                    };
                    edges.push(decode_eq(terms, *inner)?);
                }
                Some(edges)
            };
        // Route 1: every other disjunct is a negated equality and the whole
        // set chains lhs -> rhs.
        let others: Vec<TermId> = disjuncts
            .iter()
            .enumerate()
            .filter(|&(i, _)| i != eq_pos)
            .map(|(_, &d)| d)
            .collect();
        if let Some(edges) = neg_edges(terms, &others) {
            if Self::transitivity_chain_covers(&edges, lhs, rhs) {
                return Some(OrTautologyPlan {
                    term,
                    eq,
                    route: TautRoute::Plain { negs: others },
                });
            }
            return None;
        }
        // Route 2: an `and`-disjunct whose every conjunct is an or-term of
        // negated equalities chaining lhs -> rhs.
        'cand: for &d in &others {
            let TermData::App(Symbol::Named(n), conjs) = terms.get(d) else {
                continue;
            };
            if n != "and" || conjs.is_empty() {
                continue;
            }
            let conjs = conjs.clone();
            let mut per_conj_negs: Vec<Vec<TermId>> = Vec::with_capacity(conjs.len());
            for &c in &conjs {
                let TermData::App(Symbol::Named(cn), lits) = terms.get(c) else {
                    continue 'cand;
                };
                if cn != "or" || lits.is_empty() {
                    continue 'cand;
                }
                let lits = lits.clone();
                let Some(edges) = neg_edges(terms, &lits) else {
                    continue 'cand;
                };
                if !Self::transitivity_chain_covers(&edges, lhs, rhs) {
                    continue 'cand;
                }
                per_conj_negs.push(lits);
            }
            return Some(OrTautologyPlan {
                term,
                eq,
                route: TautRoute::And {
                    and_term: d,
                    conjs,
                    per_conj_negs,
                },
            });
        }
        None
    }

    /// Whether `edges` (undirected equalities) form a path from `lhs` to
    /// `rhs` that uses EVERY edge — exactly the strict `eq_transitive`
    /// checker's acceptance condition (BFS shortest path covering all
    /// premises; a redundant premise is rejected there and so must be
    /// rejected here).
    fn transitivity_chain_covers(edges: &[(TermId, TermId)], lhs: TermId, rhs: TermId) -> bool {
        if edges.is_empty() || lhs == rhs {
            return false;
        }
        let mut adj: HashMap<TermId, Vec<TermId>> = HashMap::default();
        for &(a, b) in edges {
            adj.entry(a).or_default().push(b);
            adj.entry(b).or_default().push(a);
        }
        let mut parent: HashMap<TermId, TermId> = HashMap::default();
        parent.insert(lhs, lhs);
        let mut queue = std::collections::VecDeque::new();
        queue.push_back(lhs);
        while let Some(cur) = queue.pop_front() {
            if cur == rhs {
                break;
            }
            if let Some(next) = adj.get(&cur) {
                for &n in next {
                    if !parent.contains_key(&n) {
                        parent.insert(n, cur);
                        queue.push_back(n);
                    }
                }
            }
        }
        if !parent.contains_key(&rhs) {
            return false;
        }
        let mut path_len = 0usize;
        let mut cur = rhs;
        while cur != lhs {
            cur = parent[&cur];
            path_len += 1;
        }
        path_len == edges.len()
    }

    /// Emit the certified derivation of `(cl T)` for a recognized
    /// transitivity tautology (see [`OrTautologyPlan`]; the plan was
    /// chain-verified, so every emitted step passes the strict checker).
    /// Returns the id of the final unit step.
    fn emit_or_tautology_derivation(
        &mut self,
        new_proof: &mut Proof,
        plan: &OrTautologyPlan,
    ) -> ProofId {
        let (t, e) = (plan.term, plan.eq);
        // Derive `(cl E <target>)` from `negs` (the ¬e literals whose
        // equalities chain to E) against the or-term `target` that lists
        // them as disjuncts: eq_transitive + one or_neg elimination per ¬e,
        // then contraction of the accumulated duplicate `target` literals.
        let derive_eq_or = |exec: &mut Self,
                            new_proof: &mut Proof,
                            negs: &[TermId],
                            target: TermId|
         -> ProofId {
            let mut clause: Vec<TermId> = negs.to_vec();
            clause.push(e);
            let mut cur = new_proof.add_rule_step(
                AletheRule::EqTransitive,
                clause.clone(),
                Vec::new(),
                Vec::new(),
            );
            for &d in negs {
                let not_d = exec.ctx.terms.mk_not_raw(d);
                let on = new_proof.add_rule_step(
                    AletheRule::OrNeg,
                    vec![target, not_d],
                    Vec::new(),
                    Vec::new(),
                );
                if let Some(pos) = clause.iter().position(|&l| l == d) {
                    // Resolution surgery: the removed literal is the pivot `d`,
                    // already in hand — its id is not needed.
                    let _ = clause.remove(pos);
                }
                clause.push(target);
                cur = new_proof.add_resolution(clause.clone(), d, cur, on);
            }
            if negs.len() > 1 {
                clause = vec![e, target];
                cur =
                    new_proof.add_rule_step(AletheRule::Contraction, clause, vec![cur], Vec::new());
            }
            cur
        };
        // `(cl E X)` where X is the disjunct of T the outer wiring
        // eliminates (T itself on the Plain route, the and-term on the De
        // Morgan route).
        let (eq_x_unit, x) = match &plan.route {
            TautRoute::Plain { negs } => (derive_eq_or(self, new_proof, negs, t), t),
            TautRoute::And {
                and_term,
                conjs,
                per_conj_negs,
            } => {
                let (and_term, conjs) = (*and_term, conjs.clone());
                let units: Vec<ProofId> = conjs
                    .iter()
                    .zip(per_conj_negs.iter())
                    .map(|(&dj, negs)| derive_eq_or(self, new_proof, negs, dj))
                    .collect();
                let mut clause: Vec<TermId> = vec![and_term];
                for &c in &conjs {
                    clause.push(self.ctx.terms.mk_not_raw(c));
                }
                let mut cur = new_proof.add_rule_step(
                    AletheRule::AndNeg,
                    clause.clone(),
                    Vec::new(),
                    Vec::new(),
                );
                for (&dj, &unit) in conjs.iter().zip(units.iter()) {
                    let not_dj = self.ctx.terms.mk_not_raw(dj);
                    if let Some(pos) = clause.iter().position(|&l| l == not_dj) {
                        // Resolution surgery: the removed literal is `not_dj`,
                        // already in hand — its id is not needed.
                        let _ = clause.remove(pos);
                    }
                    clause.push(e);
                    cur = new_proof.add_resolution(clause.clone(), dj, cur, unit);
                }
                if conjs.len() > 1 {
                    clause = vec![and_term, e];
                    cur = new_proof.add_rule_step(
                        AletheRule::Contraction,
                        clause,
                        vec![cur],
                        Vec::new(),
                    );
                }
                (cur, and_term)
            }
        };
        // Outer wiring: `(cl T (not X))` and `(cl T (not E))` or_neg
        // tautologies eliminate X and E, contraction closes `(cl T)`.
        let mut cur = eq_x_unit;
        if x != t {
            let not_x = self.ctx.terms.mk_not_raw(x);
            let on_x =
                new_proof.add_rule_step(AletheRule::OrNeg, vec![t, not_x], Vec::new(), Vec::new());
            cur = new_proof.add_resolution(vec![e, t], x, cur, on_x);
        }
        let not_e = self.ctx.terms.mk_not_raw(e);
        let on_e =
            new_proof.add_rule_step(AletheRule::OrNeg, vec![t, not_e], Vec::new(), Vec::new());
        cur = new_proof.add_resolution(vec![t, t], e, cur, on_e);
        new_proof.add_rule_step(AletheRule::Contraction, vec![t], vec![cur], Vec::new())
    }

    /// Whether `(cl (not eq) (not p) concl)` is a valid `[1, 1, 1]`
    /// `la_generic` lemma per the independent Farkas checker (the equality
    /// `eq` and atom `p` asserted true, `concl` asserted false).
    fn triple_lemma_valid(&self, eq: TermId, p: TermId, concl: TermId) -> bool {
        let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
        let lits: Vec<TheoryLit> = [eq, p]
            .iter()
            .map(|&l| match self.ctx.terms.get(l) {
                TermData::Not(inner) => TheoryLit::new(*inner, false),
                _ => TheoryLit::new(l, true),
            })
            .chain(std::iter::once(match self.ctx.terms.get(concl) {
                TermData::Not(inner) => TheoryLit::new(*inner, true),
                _ => TheoryLit::new(concl, false),
            }))
            .collect();
        // `_linear`, NOT `_full`: the lemma exports as `la_generic`, and
        // external checkers perform no congruence reasoning inside
        // `la_generic` — the opaque ite term must cancel purely linearly.
        ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            &self.ctx.terms,
            &lits,
            &farkas,
        )
        .is_ok()
    }

    /// Emit a `[1, 1, 1]` `la_generic` theory lemma `(cl a b c)`. Only called
    /// for triples already validated by [`Self::triple_lemma_valid`].
    fn add_triple_lemma(new_proof: &mut Proof, a: TermId, b: TermId, c: TermId) -> ProofId {
        new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: vec![a, b, c],
            farkas: Some(FarkasAnnotation::from_ints(&[1, 1, 1])),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        })
    }

    /// Whether `(cl (not eq) (not p) (not q) concl)` is a valid
    /// `[1, 1, 1, 1]` `la_generic` lemma per the independent Farkas checker
    /// (the equality `eq` and atoms `p`, `q` asserted true, `concl` asserted
    /// false).
    fn quad_lemma_valid(&self, eq: TermId, p: TermId, q: TermId, concl: TermId) -> bool {
        let farkas = FarkasAnnotation::from_ints(&[1, 1, 1, 1]);
        let lits: Vec<TheoryLit> = [eq, p, q]
            .iter()
            .map(|&l| match self.ctx.terms.get(l) {
                TermData::Not(inner) => TheoryLit::new(*inner, false),
                _ => TheoryLit::new(l, true),
            })
            .chain(std::iter::once(match self.ctx.terms.get(concl) {
                TermData::Not(inner) => TheoryLit::new(*inner, true),
                _ => TheoryLit::new(concl, false),
            }))
            .collect();
        // `_linear`, NOT `_full` (see `triple_lemma_valid`).
        ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            &self.ctx.terms,
            &lits,
            &farkas,
        )
        .is_ok()
    }

    /// Emit a `[1, 1, 1, 1]` `la_generic` theory lemma `(cl a b c d)`. Only
    /// called for quads already validated by [`Self::quad_lemma_valid`].
    fn add_quad_lemma(
        new_proof: &mut Proof,
        a: TermId,
        b: TermId,
        c: TermId,
        d: TermId,
    ) -> ProofId {
        new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: vec![a, b, c, d],
            farkas: Some(FarkasAnnotation::from_ints(&[1, 1, 1, 1])),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        })
    }

    /// Whether `(cl a b)` is a valid `[1, 1]` `la_generic` lemma per the
    /// independent Farkas checker (Int strengthening included).
    /// NORMALIZED-ASSUME MISMATCH fallback (the CAV09 QF_LIA class):
    /// [`Self::surface_bound_raw_term`] handles only pure orientation flips;
    /// here the canonical export REWROTE the linear atom itself — unary-minus
    /// spelling for `(* (- 1) x)`, elided `(* 1 x)` monomials, dropped
    /// `(* 0 x)` monomials, duplicate monomials folded into `(* x k)`,
    /// reordered sums, singleton-sum collapse. The surface comparison is
    /// re-interned PRINT-FAITHFULLY (so the `assume` spells exactly like the
    /// problem file) and bridged to the canonical literal with a certified
    /// `[1, 1]` `la_generic` orientation lemma: a raw linear atom and its
    /// canonicalization are mutually implying linear facts.
    ///
    /// Fail-closed (`None`) unless (a) the surface elaborates to EXACTLY the
    /// canonical literal (alignment gate) and (b) the independent Farkas
    /// checker certifies the bridge lemma up front.
    fn surface_linear_raw_term(
        &mut self,
        surf: &FrontendTerm,
        canonical: TermId,
    ) -> Option<(TermId, Option<TermId>)> {
        let stripped = strip_frontend_annotations(surf);
        let (inner, negated) = match stripped {
            FrontendTerm::App(op, operands) if op == "not" && operands.len() == 1 => {
                (strip_frontend_annotations(&operands[0]), true)
            }
            _ => (stripped, false),
        };
        let FrontendTerm::App(head, operands) = inner else {
            return None;
        };
        if operands.len() != 2 || !matches!(head.as_str(), "<=" | "<" | ">=" | ">") {
            return None;
        }
        // Alignment gate: same atom, different spelling — nothing else.
        if self.ctx.elaborate_surface_subterm(stripped)? != canonical {
            return None;
        }
        let a = self.raw_intern_surface(&operands[0])?;
        let b = self.raw_intern_surface(&operands[1])?;
        let raw_atom = self
            .ctx
            .terms
            .mk_app(Symbol::named(head.as_str()), [a, b], Sort::Bool);
        let raw = if negated {
            self.ctx.terms.mk_not_raw(raw_atom)
        } else {
            raw_atom
        };
        if raw == canonical {
            return Some((raw, None));
        }
        let raw_complement = complement_of(&mut self.ctx.terms, raw);
        if !self.pair_lemma_valid(canonical, raw_complement) {
            return None;
        }
        Some((raw, Some(raw_atom)))
    }

    /// [`Self::surface_bound_raw_term`] with the normalized-linear-atom
    /// fallback ([`Self::surface_linear_raw_term`]).
    fn surface_bound_or_linear_raw_term(
        &mut self,
        surf: &FrontendTerm,
        canonical: TermId,
    ) -> Option<(TermId, Option<TermId>)> {
        match self.surface_bound_raw_term(surf, canonical) {
            Some((raw, None)) if raw == canonical => {
                // The ELABORATED operands reproduced the canonical term, but
                // that alone does not prove the assume would print like the
                // problem file: elaboration may have canonicalized the linear
                // operands (the CAV09 class). Only a print-faithful re-intern
                // decides; when it differs, take the certified bridge.
                if let Some(hit) = self.surface_linear_raw_term(surf, canonical) {
                    return Some(hit);
                }
                Some((raw, None))
            }
            Some(hit) => Some(hit),
            None => self.surface_linear_raw_term(surf, canonical),
        }
    }

    fn pair_lemma_valid(&self, a: TermId, b: TermId) -> bool {
        let farkas = FarkasAnnotation::from_ints(&[1, 1]);
        let lits: Vec<TheoryLit> = [a, b]
            .iter()
            .map(|&l| match self.ctx.terms.get(l) {
                TermData::Not(inner) => TheoryLit::new(*inner, true),
                _ => TheoryLit::new(l, false),
            })
            .collect();
        ay_core::proof_validation::verify_farkas_conflict_lits_full(&self.ctx.terms, &lits, &farkas)
            .is_ok()
    }

    /// Emit a `[1, 1]` `la_generic` theory lemma `(cl a b)`. Only called for
    /// pairs already validated by [`Self::pair_lemma_valid`].
    fn add_pair_lemma(new_proof: &mut Proof, a: TermId, b: TermId) -> ProofId {
        new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: vec![a, b],
            farkas: Some(FarkasAnnotation::from_ints(&[1, 1])),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        })
    }

    /// Certified orientation bridge for a top-level binary-equality flip
    /// `r` → `c` (#C2b): emits `(cl (= x y)) :rule eq_symmetric` composed
    /// with `equiv_pos1`/`equiv_pos2` and one resolution into the clause
    /// `(cl (not r) c)` (positive literals) / `(cl e' c)` with `r = (not e)`,
    /// `c = (not e')` (negated literals — the clause the caller resolves on
    /// pivot `e`). Returns `(outer resolution pivot, bridge step)`. Callers
    /// guarantee the flip shape (see [`eq_top_flip`]).
    fn add_eq_flip_bridge(
        &mut self,
        new_proof: &mut Proof,
        r: TermId,
        c: TermId,
    ) -> (TermId, ProofId) {
        // (x, y): derive (cl (not x) y); pivot: the literal the OUTER
        // resolution eliminates from the caller's working clause.
        let (x, y, pivot) = match (self.ctx.terms.get(r), self.ctx.terms.get(c)) {
            (TermData::Not(e), TermData::Not(e_flip)) => {
                let (e, e_flip) = (*e, *e_flip);
                (e_flip, e, e)
            }
            _ => (r, c, r),
        };
        let equiv = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [x, y], Sort::Bool);
        let sym =
            new_proof.add_rule_step(AletheRule::EqSymmetric, vec![equiv], Vec::new(), Vec::new());
        let not_equiv = self.ctx.terms.mk_not_raw(equiv);
        let not_x = self.ctx.terms.mk_not_raw(x);
        // The `=` intern may have reoriented the equivalence itself: pick the
        // equiv_pos side whose conclusion is (cl (not x) y) either way.
        let interned_straight = matches!(
            self.ctx.terms.get(equiv),
            TermData::App(Symbol::Named(op), args) if op == "=" && args.len() == 2 && args[0] == x
        );
        let ep = if interned_straight {
            new_proof.add_rule_step(
                AletheRule::EquivPos2,
                vec![not_equiv, not_x, y],
                Vec::new(),
                Vec::new(),
            )
        } else {
            new_proof.add_rule_step(
                AletheRule::EquivPos1,
                vec![not_equiv, y, not_x],
                Vec::new(),
                Vec::new(),
            )
        };
        let bridge = new_proof.add_resolution(vec![not_x, y], equiv, ep, sym);
        (pivot, bridge)
    }

    /// Whether any assume REACHABLE from an empty-clause step is an original
    /// assertion whose exported (canonical) form would not print like the
    /// problem file — i.e. it classifies into one of the repairable assume
    /// bridge plans (expanded n-ary `distinct`, arithmetic-normalized `and`).
    /// Such proofs are checker-invalid even with ZERO trust steps: the
    /// caller uses this as a rebuild trigger alongside the trust report.
    pub(super) fn reachable_normalized_assume(
        &mut self,
        proof: &Proof,
        originals: &[(TermId, FrontendTerm)],
    ) -> bool {
        let live = live_steps(proof);
        for (idx, step) in proof.steps.iter().enumerate() {
            if !live[idx] {
                continue;
            }
            let ProofStep::Assume(term) = step else {
                continue;
            };
            let Some((_, parsed)) = originals.iter().find(|(c, _)| c == term) else {
                continue; // non-original assumes are the sibling trigger's job
            };
            // A surface override makes the assume print with the problem
            // file's own spelling: not a defect. Only override-less assumes
            // print canonically (and only those can mismatch the premise).
            if self
                .last_proof_term_overrides
                .as_ref()
                .is_some_and(|m| m.contains_key(term))
            {
                continue;
            }
            let parsed = parsed.clone();
            if matches!(self.classify_assume(*term, &parsed, true), Ok(Some(_))) {
                return true;
            }
        }
        false
    }

    /// Classify a (verified-original) assume for repair. `Ok(None)` = keep
    /// as-is; `Err(())` = a repair is needed but cannot be built
    /// (fail-closed: abort the whole surgery).
    fn classify_assume(
        &mut self,
        term: TermId,
        parsed: &FrontendTerm,
        overrides_kept: bool,
    ) -> Result<Option<AssumePlan>, ()> {
        // A `let`-wrapped surface (common in SMT-COMP inputs) hides the
        // repairable shape: expand the bindings first (pure substitution;
        // fail-closed on any capture risk). External checkers compare
        // against the same expansion (carcara: `--expand-let-bindings`).
        let expanded;
        let parsed = if matches!(strip_frontend_annotations(parsed), FrontendTerm::Let(..)) {
            match expand_surface_lets(parsed, &std::collections::HashMap::new()) {
                Some(e) => {
                    expanded = e;
                    &expanded
                }
                None => return Ok(None),
            }
        } else {
            parsed
        };
        let stripped = strip_frontend_annotations(parsed);
        let FrontendTerm::App(head, operands) = stripped else {
            return Ok(None);
        };
        match head.as_str() {
            "distinct" if operands.len() >= 3 => {
                let mut xs = Vec::with_capacity(operands.len());
                for op in operands {
                    xs.push(self.ctx.elaborate_surface_subterm(op).ok_or(())?);
                }
                // The exported assume must be the pairwise `i < j` expansion
                // (exactly the `distinct_elim` conjunct order).
                let TermData::App(Symbol::Named(name), conjs) = self.ctx.terms.get(term) else {
                    return Err(());
                };
                if name != "and" {
                    return Err(());
                }
                let conjs = conjs.clone();
                if conjs.len() != xs.len() * (xs.len() - 1) / 2 {
                    return Err(());
                }
                let mut k = 0;
                for i in 0..xs.len() {
                    for j in (i + 1)..xs.len() {
                        let TermData::Not(inner) = self.ctx.terms.get(conjs[k]) else {
                            return Err(());
                        };
                        let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(*inner)
                        else {
                            return Err(());
                        };
                        if op != "=" || args.len() != 2 || args[0] != xs[i] || args[1] != xs[j] {
                            return Err(());
                        }
                        k += 1;
                    }
                }
                let raw = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("distinct"), xs.clone(), Sort::Bool);
                if !matches!(
                    self.ctx.terms.get(raw),
                    TermData::App(Symbol::Named(op), args) if op == "distinct" && args.len() == xs.len()
                ) {
                    return Err(());
                }
                Ok(Some(AssumePlan::Distinct {
                    raw,
                    and_term: term,
                    conjs,
                }))
            }
            "and" => {
                let TermData::App(Symbol::Named(name), conjs) = self.ctx.terms.get(term) else {
                    return Err(());
                };
                if name != "and" {
                    return Err(());
                }
                let conjs = conjs.clone();
                // A `distinct`-sugar operand (exported canonically as
                // `(not (= s t))` / its pairwise expansion, whose print no
                // longer matches the file) switches the scan into the
                // full-alignment `AndDistinct` mode. Without distinct sugar
                // the historical bounds-only behavior below is preserved
                // byte-for-byte.
                if operands.iter().any(|surf| {
                    matches!(strip_frontend_annotations(surf),
                        FrontendTerm::App(h, args) if h == "distinct" && args.len() >= 2)
                }) {
                    return self.classify_and_distinct(term, &conjs, operands);
                }
                if conjs.len() != operands.len() {
                    // Canonicalization FOLDED or DEDUPLICATED whole conjuncts
                    // away (e.g. a duplicated linear atom kept once): the
                    // positional bounds pairing below is impossible, but the
                    // alignment-capable `AndDistinct` classifier handles the
                    // skew (fail-open to keeping the assume as-is).
                    return self.classify_and_distinct(term, &conjs, operands);
                }
                let mut raws: Vec<(TermId, Option<TermId>)> = Vec::with_capacity(conjs.len());
                let mut any_bridge = false;
                let mut any_unshaped = false;
                for (surf, &conj) in operands.iter().zip(conjs.iter()) {
                    let Some((raw, bridge)) = self.surface_bound_or_linear_raw_term(surf, conj)
                    else {
                        // Not a bound-literal conjunct (e.g. an `or`-term in
                        // a CNF-shaped conjunction). Whether this vetoes the
                        // surgery is decided after the scan: a conjunction
                        // with NO orientation-bridged conjunct at all is not
                        // the arithmetic-normalized-bounds class and is kept
                        // as-is; a MIX of bridged and unshaped conjuncts is
                        // unrepairable (fail-closed, as before).
                        any_unshaped = true;
                        continue;
                    };
                    // Verify the orientation bridge certificate up front
                    // (fail-closed before any emission).
                    if bridge.is_some() {
                        let raw_complement = complement_of(&mut self.ctx.terms, raw);
                        if !self.pair_lemma_valid(conj, raw_complement) {
                            return Err(());
                        }
                        any_bridge = true;
                    } else if raw != conj {
                        return Err(());
                    }
                    raws.push((raw, bridge));
                }
                if any_unshaped {
                    if any_bridge {
                        return Err(());
                    }
                    // No conjunct needs repair: the assume prints as it
                    // always did — keep it rather than vetoing the whole
                    // surgery (other defect classes in the same proof may
                    // still be repairable).
                    return Ok(None);
                }
                if !any_bridge {
                    // Every conjunct already IS its canonical form: the
                    // exported assume prints like the file. Keep it.
                    return Ok(None);
                }
                let raw_and = self.ctx.terms.mk_app(
                    Symbol::named("and"),
                    raws.iter().map(|&(r, _)| r).collect::<Vec<_>>(),
                    Sort::Bool,
                );
                if !matches!(
                    self.ctx.terms.get(raw_and),
                    TermData::App(Symbol::Named(op), args) if op == "and" && args.len() == raws.len()
                ) {
                    return Err(());
                }
                Ok(Some(AssumePlan::AndBounds {
                    raw_and,
                    raws,
                    conjs,
                }))
            }
            "<" | "<=" | ">" | ">=" | "not" => {
                // A plain bound literal whose canonical orientation differs
                // from the surface spelling (e.g. `(> a 5)` vs `(< 5 a)`).
                // When surface overrides survive the surgery (ite-lift
                // class), an override-covered literal already prints
                // correctly and must not be planned (a plan would trip the
                // ite-lift exclusivity abort and leave the WHOLE proof
                // unrepaired). When overrides are purged, the same literal
                // MUST be bridged: its canonical print no longer matches.
                // No bridge needed when the raw term IS the canonical one;
                // unsupported shapes are kept as-is (they printed without
                // the surgery's help before, and the surgery fails closed on
                // its trust-free check if that ever stops holding).
                if overrides_kept
                    && self
                        .last_proof_term_overrides
                        .as_ref()
                        .is_some_and(|m| m.contains_key(&term))
                {
                    return Ok(None);
                }
                match self.surface_bound_or_linear_raw_term(parsed, term) {
                    Some((raw, Some(atom))) => {
                        let raw_complement = complement_of(&mut self.ctx.terms, raw);
                        if !self.pair_lemma_valid(term, raw_complement) {
                            return Err(());
                        }
                        Ok(Some(AssumePlan::Literal {
                            raw,
                            atom,
                            canonical: term,
                        }))
                    }
                    Some((_, None)) | None => Ok(None),
                }
            }
            _ => Ok(None),
        }
    }

    /// Raw-intern a surface term (QF-shaped: symbols, constants, `not`, and
    /// plain applications) so it PRINTS exactly like the problem file even
    /// where elaboration folds it (e.g. `(= c c)` -> `true`). The sort is
    /// taken from the term's own elaboration. `None` fail-closed on binders
    /// or anything that does not elaborate.
    fn raw_intern_surface(&mut self, surf: &FrontendTerm) -> Option<TermId> {
        let stripped = strip_frontend_annotations(surf);
        match stripped {
            FrontendTerm::Symbol(_) | FrontendTerm::Const(_) => {
                self.ctx.elaborate_surface_subterm(stripped)
            }
            FrontendTerm::App(head, args) => {
                let elab = self.ctx.elaborate_surface_subterm(stripped)?;
                let raw_args = args
                    .iter()
                    .map(|a| self.raw_intern_surface(a))
                    .collect::<Option<Vec<TermId>>>()?;
                if head == "not" && raw_args.len() == 1 {
                    return Some(self.ctx.terms.mk_not_raw(raw_args[0]));
                }
                let sort = self.ctx.terms.sort(elab).clone();
                Some(self.ctx.terms.mk_app(Symbol::named(head), raw_args, sort))
            }
            FrontendTerm::IndexedApp(name, indices, args) => {
                let elab = self.ctx.elaborate_surface_subterm(stripped)?;
                if args.is_empty() {
                    let [FrontendIndex::Numeral(width)] = indices.as_slice() else {
                        return None;
                    };
                    let value = name.strip_prefix("bv")?;
                    if value.is_empty()
                        || !value.bytes().all(|byte| byte.is_ascii_digit())
                        || width.parse::<u32>().ok().is_none_or(|bits| bits == 0)
                    {
                        return None;
                    }
                    // Preserve the decimal-BV class accepted by the former
                    // flattened Symbol path. Other nullary indexed constants
                    // canonicalize to unrelated core shapes and fail closed.
                    return Some(elab);
                }
                let numeric_indices = indices
                    .iter()
                    .map(|index| match index {
                        FrontendIndex::Numeral(value) => value.parse::<u32>().ok(),
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>()?;
                let raw_args = args
                    .iter()
                    .map(|arg| self.raw_intern_surface(arg))
                    .collect::<Option<Vec<_>>>()?;
                let sort = self.ctx.terms.sort(elab).clone();
                Some(
                    self.ctx
                        .terms
                        .mk_app(Symbol::indexed(name, numeric_indices), raw_args, sort),
                )
            }
            _ => None,
        }
    }

    /// Classify a surface conjunction containing `distinct` sugar against
    /// its canonical export (see [`AssumePlan::AndDistinct`]). The canonical
    /// conjunction may have FOLDED trivial operands away (`(= c c)` ->
    /// `true`), DEDUPLICATED repeated conjuncts, and EXPANDED n-ary
    /// `distinct` operands into pairwise blocks — the scan aligns the
    /// surface operands with the canonical conjuncts in order, fail-open to
    /// `Ok(None)` (keep the assume as-is; the surgery's trust-free check
    /// still decides overall success) on anything unalignable.
    fn classify_and_distinct(
        &mut self,
        term: TermId,
        conjs: &[TermId],
        operands: &[FrontendTerm],
    ) -> Result<Option<AssumePlan>, ()> {
        let mut units: Vec<AndDistinctUnit> = Vec::new();
        let mut raws: Vec<TermId> = Vec::with_capacity(operands.len());
        let mut k = 0usize;
        for (pos, surf) in operands.iter().enumerate() {
            #[allow(clippy::cast_possible_truncation)]
            let pos = pos as u32;
            let stripped = strip_frontend_annotations(surf);
            if let FrontendTerm::App(head, ops) = stripped {
                if head == "distinct" && ops.len() >= 2 {
                    let Some(xs) = ops
                        .iter()
                        .map(|op| self.ctx.elaborate_surface_subterm(op))
                        .collect::<Option<Vec<TermId>>>()
                    else {
                        return Ok(None);
                    };
                    let raw =
                        self.ctx
                            .terms
                            .mk_app(Symbol::named("distinct"), xs.clone(), Sort::Bool);
                    if !matches!(
                        self.ctx.terms.get(raw),
                        TermData::App(Symbol::Named(op), args)
                            if op == "distinct" && args.len() == xs.len()
                    ) {
                        return Ok(None);
                    }
                    // The canonical export is the pairwise `i < j` block.
                    let m = xs.len() * (xs.len() - 1) / 2;
                    if k + m > conjs.len() {
                        return Ok(None);
                    }
                    let mut kk = k;
                    for i in 0..xs.len() {
                        for j in (i + 1)..xs.len() {
                            let TermData::Not(inner) = self.ctx.terms.get(conjs[kk]) else {
                                return Ok(None);
                            };
                            let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(*inner)
                            else {
                                return Ok(None);
                            };
                            if op != "=" || args.len() != 2 || args[0] != xs[i] || args[1] != xs[j]
                            {
                                return Ok(None);
                            }
                            kk += 1;
                        }
                    }
                    let kind = if xs.len() == 2 {
                        AndDistinctKind::DistinctBinary
                    } else {
                        // The expansion conjunction itself (for the
                        // `distinct_elim` equivalence + `and_pos` splits).
                        let Some(block) = self.ctx.elaborate_surface_subterm(surf) else {
                            return Ok(None);
                        };
                        let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(block)
                        else {
                            return Ok(None);
                        };
                        if op != "and" || args.as_slice() != &conjs[k..k + m] {
                            return Ok(None);
                        }
                        #[allow(clippy::cast_possible_truncation)]
                        AndDistinctKind::DistinctNary {
                            and_term: block,
                            count: m as u32,
                        }
                    };
                    units.push(AndDistinctUnit { pos, raw, kind });
                    raws.push(raw);
                    k += m;
                    continue;
                }
            }
            let Some(elab) = self.ctx.elaborate_surface_subterm(surf) else {
                return Ok(None);
            };
            if self.ctx.terms.is_true(elab) || conjs[..k].contains(&elab) {
                // Folded-away (`(= c c)`) or deduplicated conjunct: present
                // in the raw print only, supplies no unit.
                let Some(raw) = self.raw_intern_surface(surf) else {
                    return Ok(None);
                };
                raws.push(raw);
                continue;
            }
            if k < conjs.len() && elab == conjs[k] {
                let conj = conjs[k];
                if let Some((raw, bridge)) = self.surface_bound_or_linear_raw_term(surf, conj) {
                    let kind = match bridge {
                        Some(atom) => {
                            let raw_complement = complement_of(&mut self.ctx.terms, raw);
                            if !self.pair_lemma_valid(conj, raw_complement) {
                                return Ok(None);
                            }
                            AndDistinctKind::Arith { atom }
                        }
                        None => {
                            if raw != conj {
                                return Ok(None);
                            }
                            AndDistinctKind::Plain
                        }
                    };
                    units.push(AndDistinctUnit { pos, raw, kind });
                    raws.push(raw);
                } else {
                    // A plain conjunct: keep the CANONICAL term as the raw
                    // conjunct (the strict checker then sees a fully
                    // id-consistent proof), accepted only when its print
                    // differs from the file by AT MOST binary-equality
                    // orientation — the one difference carcara's default
                    // mode tolerates everywhere. Anything else (`distinct`
                    // sugar, canonicalization that reordered an `or`, ...)
                    // would print unlike the file: keep the assume as-is.
                    let Some(raw) = self.raw_intern_surface(surf) else {
                        return Ok(None);
                    };
                    if !eq_flip_equivalent(&self.ctx.terms, raw, conj) {
                        // Last chance (#C2b): an `or`-conjunct whose
                        // canonical export reordered the disjuncts and/or
                        // flipped binary-equality orientations. The RAW
                        // disjunction (file order + orientations) is kept
                        // for the assume and bridged per-literal.
                        let Some(lits) = or_perm_lits(&self.ctx.terms, raw, conj) else {
                            return Ok(None);
                        };
                        units.push(AndDistinctUnit {
                            pos,
                            raw,
                            kind: AndDistinctKind::OrPerm { lits },
                        });
                        raws.push(raw);
                        k += 1;
                        continue;
                    }
                    units.push(AndDistinctUnit {
                        pos,
                        raw: conj,
                        kind: AndDistinctKind::Plain,
                    });
                    raws.push(conj);
                }
                k += 1;
                continue;
            }
            return Ok(None);
        }
        if k != conjs.len() {
            return Ok(None);
        }
        if units
            .iter()
            .all(|u| matches!(u.kind, AndDistinctKind::Plain))
            && raws.len() == conjs.len()
        {
            // Nothing to repair: the canonical print already matches.
            return Ok(None);
        }
        let raw_and = self
            .ctx
            .terms
            .mk_app(Symbol::named("and"), raws.clone(), Sort::Bool);
        if !matches!(
            self.ctx.terms.get(raw_and),
            TermData::App(Symbol::Named(op), args) if op == "and" && args.len() == raws.len()
        ) {
            return Ok(None);
        }
        Ok(Some(AssumePlan::AndDistinct {
            raw_and,
            and_term: term,
            units,
            conjs: conjs.to_vec(),
        }))
    }

    /// Preprocessor fold-to-`false` collapse repair (#trust-count→0,
    /// carcara-invalid→valid). When the PREPROCESSOR itself derives the
    /// contradiction (e.g. `(assert (distinct x x))`, `(assert (= 1 2))`,
    /// `(assert (and p (not p)))`), the exported proof degenerates to the
    /// 3-step shape
    ///
    /// ```text
    /// (assume t0 X)
    /// (step t1 (cl (not X)) :rule false :args (X))   ; NOT the Alethe `false`
    /// (step t2 (cl) :rule resolution :premises (t0 t1))
    /// ```
    ///
    /// whose `:rule false` step misuses the Alethe `false` rule (`⊢ (cl (not
    /// false))`) and is rejected by external checkers. This pass recognizes
    /// the whole-proof shape and re-proves `(cl (not X))` from the ORIGINAL
    /// assertion `X`'s own structure with certified steps:
    ///
    /// - **`(distinct .. t .. t ..)` with a syntactically duplicated operand**
    ///   — `distinct_elim` + `equiv_pos2` (+ `and_pos` for the n-ary
    ///   conjunction form) down to `(not (= t t))`, refuted by
    ///   `eq_reflexive`.
    /// - **ground arithmetic `(= a b)` falsity** — a single-literal
    ///   `la_generic` lemma `(cl (not (= a b)))`, re-verified by the
    ///   independent Farkas checker (fail-closed) and printed with
    ///   sign-resolved coefficients.
    /// - **`(and .. p .. (not p) ..)` with a syntactically complementary
    ///   conjunct pair** — two `and_pos` extractions resolved to `⊥`.
    ///
    /// Fail-closed: any other assertion shape (or a failed certificate)
    /// leaves the proof byte-identical, keeping the honest defective step
    /// visible rather than fabricating an unchecked derivation.
    ///
    /// The collapse's assume holds the FOLDED canonical term (`false`), so
    /// the derivation is rebuilt from the parsed ORIGINAL assertion whose
    /// canonical form is the assumed term, with every operand re-elaborated
    /// and the folded application re-interned RAW (so the new assume prints
    /// like the problem file, exactly the `classify_assume` discipline).
    pub(super) fn try_rebuild_false_collapse(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
    ) -> bool {
        // (1) Recognize the whole-proof collapse shape on the LIVE steps.
        let live = live_steps(proof);
        let mut assume: Option<TermId> = None;
        let mut assume_count = 0usize;
        let mut false_step: Option<(TermId, TermId)> = None; // (clause lit, arg)
        let mut trust_false = false;
        let mut lia_lemma = false;
        let mut closing = false;
        for (idx, step) in proof.steps.iter().enumerate() {
            if !live[idx] {
                continue;
            }
            match step {
                ProofStep::Assume(t) => {
                    assume_count += 1;
                    if assume.is_none() {
                        assume = Some(*t);
                    }
                }
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::LiaGeneric,
                    ..
                } if !lia_lemma => {
                    lia_lemma = true;
                }
                ProofStep::Step {
                    rule: AletheRule::False,
                    clause,
                    premises,
                    args,
                } if false_step.is_none() && clause.len() == 1 && premises.is_empty() => {
                    // Shape A carries the assumed term as the single arg;
                    // shape C's wiring step is `(cl (not false)) :rule false`.
                    if args.len() == 1 {
                        false_step = Some((clause[0], args[0]));
                    } else if !matches!(
                        self.ctx.terms.get(atom_of(&self.ctx.terms, clause[0])),
                        TermData::Const(ay_core::term::Constant::Bool(false))
                    ) {
                        return false;
                    }
                }
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    premises,
                    ..
                } if !trust_false
                    && clause.len() == 1
                    && premises.is_empty()
                    && matches!(
                        self.ctx.terms.get(clause[0]),
                        TermData::Const(ay_core::term::Constant::Bool(false))
                    ) =>
                {
                    trust_false = true;
                }
                ProofStep::Resolution { clause, .. }
                | ProofStep::Step {
                    rule: AletheRule::Resolution | AletheRule::ThResolution,
                    clause,
                    ..
                } => {
                    if clause.is_empty() {
                        if closing {
                            return false;
                        }
                        closing = true;
                    }
                }
                _ => return false,
            }
        }
        if !closing {
            return false;
        }
        // Substitution-chain shape: equality assumes closed by ONE
        // `lia_generic` lemma (an external checker HOLE). Re-prove from the
        // original equalities with a synthesized, re-verified `la_generic`
        // certificate (fail-closed: any non-equality original keeps the
        // proof unchanged).
        if lia_lemma {
            if trust_false || false_step.is_some() || assume_count == 0 {
                return false;
            }
            return self.rebuild_consumed_equalities_collapse(proof, originals);
        }
        // Shape C: the preprocessor consumed the assertions entirely — the
        // proof is the bare `(cl false) :rule trust` (no assume, no
        // derivation). Re-prove from the ORIGINAL arithmetic-equality
        // assertions with a synthesized, re-verified Farkas certificate.
        if trust_false {
            // Any accompanying `false` step must be the proper-form wiring
            // `(cl (not false))` for `(cl false)`'s refutation.
            let wiring_ok = match false_step {
                None => true,
                Some((lit, arg)) => {
                    matches!(
                        self.ctx.terms.get(arg),
                        TermData::Const(ay_core::term::Constant::Bool(false))
                    ) && atom_of(&self.ctx.terms, lit) == arg
                        && lit != arg
                }
            };
            if assume_count == 0 && wiring_ok {
                return self.rebuild_consumed_equalities_collapse(proof, originals);
            }
            return false;
        }
        if assume_count != 1 {
            return false;
        }
        let (Some(x), Some((neg_lit, arg))) = (assume, false_step) else {
            return false;
        };
        if arg != x || atom_of(&self.ctx.terms, neg_lit) != x || neg_lit == x {
            return false;
        }

        // (2) The assume holds the folded canonical term: recover the parsed
        // original assertion(s) it came from and pick the certified
        // derivation by the ORIGINAL surface shape. First recognized shape
        // wins; no match keeps the proof byte-identical.
        for (canonical, parsed) in originals {
            if *canonical != x {
                continue;
            }
            let stripped = strip_frontend_annotations(parsed);
            // CAV09-family assertions wrap the conjunction in `let` sugar:
            // expand it (capture-safe, fail-closed) so the shape dispatch
            // sees the underlying application. The rebuilt assume prints the
            // EXPANDED form, which external checkers accept (carcara runs
            // with `--expand-let-bindings`, comparing modulo let expansion).
            let expanded;
            let stripped = if matches!(stripped, FrontendTerm::Let(..)) {
                match expand_surface_lets(stripped, &std::collections::HashMap::new()) {
                    Some(t) => {
                        expanded = t;
                        strip_frontend_annotations(&expanded)
                    }
                    None => continue,
                }
            } else {
                stripped
            };
            let FrontendTerm::App(head, operands) = stripped else {
                continue;
            };
            let ok = match head.as_str() {
                "distinct" if operands.len() >= 2 => {
                    self.rebuild_duplicate_distinct_collapse(proof, operands)
                }
                "=" if operands.len() == 2 => {
                    self.rebuild_ground_equality_collapse(proof, operands)
                }
                "and" if operands.len() >= 2 => {
                    self.rebuild_complementary_and_collapse(proof, operands)
                        || self.rebuild_linear_and_collapse(proof, operands)
                }
                _ => false,
            };
            if ok {
                return true;
            }
        }
        false
    }

    /// `(distinct ..)` with a syntactically duplicated operand: derive
    /// `(not (= t t))` via `distinct_elim` + `equiv_pos2` (+ `and_pos` for
    /// n-ary) and refute it with `eq_reflexive`.
    fn rebuild_duplicate_distinct_collapse(
        &mut self,
        proof: &mut Proof,
        operands: &[FrontendTerm],
    ) -> bool {
        let mut args = Vec::with_capacity(operands.len());
        for op in operands {
            let Some(t) = self.ctx.elaborate_surface_subterm(op) else {
                return false;
            };
            args.push(t);
        }
        let args = &args[..];
        // Re-intern the folded `distinct` application RAW: the new assume
        // must print like the problem file. Fail-closed if the interner
        // folds it (the derivation would not match the premise).
        let x = self
            .ctx
            .terms
            .mk_app(Symbol::named("distinct"), args, Sort::Bool);
        if !matches!(
            self.ctx.terms.get(x),
            TermData::App(Symbol::Named(op), a) if op == "distinct" && a.len() == args.len()
        ) {
            return false;
        }
        let n = args.len();
        let Some((di, dj)) = (0..n)
            .flat_map(|i| ((i + 1)..n).map(move |j| (i, j)))
            .find(|&(i, j)| args[i] == args[j])
        else {
            return false;
        };
        // Carcara's `distinct_elim` special-cases >2 Bool operands (they
        // collapse to `false`, a different bridge): out of scope.
        if n > 2 && matches!(self.ctx.terms.sort(args[0]), Sort::Bool) {
            return false;
        }
        let terms = &mut self.ctx.terms;
        let dup = args[di];
        let eq_dup = terms.mk_app(Symbol::named("="), [dup, dup], Sort::Bool);
        if !matches!(
            terms.get(eq_dup),
            TermData::App(Symbol::Named(op), a) if op == "=" && a.len() == 2 && a[0] == dup && a[1] == dup
        ) {
            return false;
        }
        let not_eq_dup = terms.mk_not_raw(eq_dup);
        let not_x = terms.mk_not_raw(x);

        let mut new_proof = Proof::new();
        let assume_id = new_proof.add_assume(x, None);
        if n == 2 {
            // (= (distinct t t) (not (= t t)))
            let equiv = terms.mk_app(Symbol::named("="), [x, not_eq_dup], Sort::Bool);
            let not_equiv = terms.mk_not_raw(equiv);
            let de = new_proof.add_rule_step(
                AletheRule::DistinctElim,
                vec![equiv],
                Vec::new(),
                Vec::new(),
            );
            let ep = new_proof.add_rule_step(
                AletheRule::EquivPos2,
                vec![not_equiv, not_x, not_eq_dup],
                Vec::new(),
                Vec::new(),
            );
            let r1 = new_proof.add_resolution(vec![not_x, not_eq_dup], equiv, ep, de);
            let r2 = new_proof.add_resolution(vec![not_eq_dup], x, r1, assume_id);
            let er = new_proof.add_rule_step(
                AletheRule::EqReflexive,
                vec![eq_dup],
                Vec::new(),
                Vec::new(),
            );
            new_proof.add_resolution(Vec::new(), eq_dup, r2, er);
        } else {
            // (= (distinct x1..xn) (and (not (= xi xj)) ..)) in `i < j` order.
            let mut conjs: Vec<TermId> = Vec::with_capacity(n * (n - 1) / 2);
            let mut dup_pos = 0usize;
            let mut k = 0usize;
            for i in 0..n {
                for j in (i + 1)..n {
                    let eq = terms.mk_app(Symbol::named("="), [args[i], args[j]], Sort::Bool);
                    conjs.push(terms.mk_not_raw(eq));
                    if (i, j) == (di, dj) {
                        dup_pos = k;
                    }
                    k += 1;
                }
            }
            let and_term = terms.mk_app(Symbol::named("and"), conjs.clone(), Sort::Bool);
            if !matches!(
                terms.get(and_term),
                TermData::App(Symbol::Named(op), a) if op == "and" && a.len() == conjs.len()
            ) {
                return false;
            }
            let not_and = terms.mk_not_raw(and_term);
            let equiv = terms.mk_app(Symbol::named("="), [x, and_term], Sort::Bool);
            let not_equiv = terms.mk_not_raw(equiv);
            let de = new_proof.add_rule_step(
                AletheRule::DistinctElim,
                vec![equiv],
                Vec::new(),
                Vec::new(),
            );
            let ep = new_proof.add_rule_step(
                AletheRule::EquivPos2,
                vec![not_equiv, not_x, and_term],
                Vec::new(),
                Vec::new(),
            );
            let r1 = new_proof.add_resolution(vec![not_x, and_term], equiv, ep, de);
            let r2 = new_proof.add_resolution(vec![and_term], x, r1, assume_id);
            #[allow(clippy::cast_possible_truncation)]
            let ap = new_proof.add_rule_step(
                AletheRule::AndPos(dup_pos as u32),
                vec![not_and, conjs[dup_pos]],
                Vec::new(),
                Vec::new(),
            );
            let r3 = new_proof.add_resolution(vec![conjs[dup_pos]], and_term, ap, r2);
            let er = new_proof.add_rule_step(
                AletheRule::EqReflexive,
                vec![eq_dup],
                Vec::new(),
                Vec::new(),
            );
            new_proof.add_resolution(Vec::new(), eq_dup, r3, er);
        }
        *proof = new_proof;
        true
    }

    /// Ground arithmetic `(= a b)` falsity: a single-literal `la_generic`
    /// lemma `(cl (not (= a b)))`, re-verified by the independent Farkas
    /// checker before emission (fail-closed).
    fn rebuild_ground_equality_collapse(
        &mut self,
        proof: &mut Proof,
        operands: &[FrontendTerm],
    ) -> bool {
        let (Some(lhs), Some(rhs)) = (
            self.ctx.elaborate_surface_subterm(&operands[0]),
            self.ctx.elaborate_surface_subterm(&operands[1]),
        ) else {
            return false;
        };
        if !matches!(self.ctx.terms.sort(lhs), Sort::Int | Sort::Real)
            || self.ctx.terms.sort(lhs) != self.ctx.terms.sort(rhs)
        {
            return false;
        }
        // Re-intern the folded equality RAW (see the distinct emitter).
        let x = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool);
        if !matches!(
            self.ctx.terms.get(x),
            TermData::App(Symbol::Named(op), a) if op == "=" && a.len() == 2 && a[0] == lhs && a[1] == rhs
        ) {
            return false;
        }
        if !equality_is_pure_linear_arith(&self.ctx.terms, x) {
            return false;
        }
        let farkas = FarkasAnnotation::from_ints(&[1]);
        let lits = [TheoryLit::new(x, true)];
        if ay_core::proof_validation::verify_farkas_conflict_lits_full(
            &self.ctx.terms,
            &lits,
            &farkas,
        )
        .is_err()
        {
            return false;
        }
        // The printer orients equality coefficients from the certificate;
        // require the orientation to exist so the printed signs are sound.
        if ay_core::proof_validation::resolve_equality_coefficient_signs(
            &self.ctx.terms,
            &lits,
            &farkas,
        )
        .is_none()
        {
            return false;
        }
        let not_x = self.ctx.terms.mk_not_raw(x);
        let mut new_proof = Proof::new();
        let assume_id = new_proof.add_assume(x, None);
        let lemma = new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: vec![not_x],
            farkas: Some(farkas),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        });
        new_proof.add_resolution(Vec::new(), x, lemma, assume_id);
        *proof = new_proof;
        true
    }

    /// `(and .. p .. (not p) ..)` with a syntactically complementary conjunct
    /// pair: two `and_pos` extractions resolved to the empty clause.
    fn rebuild_complementary_and_collapse(
        &mut self,
        proof: &mut Proof,
        operands: &[FrontendTerm],
    ) -> bool {
        let mut conjs = Vec::with_capacity(operands.len());
        for op in operands {
            let Some(t) = self.ctx.elaborate_surface_subterm(op) else {
                return false;
            };
            conjs.push(t);
        }
        let conjs = &conjs[..];
        // Re-intern the folded conjunction RAW (see the distinct emitter).
        let x = self
            .ctx
            .terms
            .mk_app(Symbol::named("and"), conjs, Sort::Bool);
        if !matches!(
            self.ctx.terms.get(x),
            TermData::App(Symbol::Named(op), a) if op == "and" && a.len() == conjs.len()
        ) {
            return false;
        }
        // Collect every Bool node reachable through the `and`-tree of `x`,
        // recording the path (child indices) from the root. The complementary
        // pair need NOT be two top-level conjuncts: a conjunct may itself be a
        // nested `(and ..)`, so a literal `p` can sit one or more levels deep
        // while its complement `(not p)` is a sibling conjunct (the class
        // `(and .. (and .. p) .. (not p) ..)`). Each node's unit is derived by
        // the strictly-validated `and_pos` + resolution chain down its path.
        let mut nodes: Vec<(TermId, Vec<u32>)> = Vec::new();
        {
            let mut stack: Vec<(TermId, Vec<u32>)> = vec![(x, Vec::new())];
            while let Some((t, path)) = stack.pop() {
                if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) {
                    if name == "and" && !args.is_empty() {
                        let args = args.clone();
                        // Reverse push keeps the pop order left-to-right.
                        for (i, &child) in args.iter().enumerate().rev() {
                            let Ok(pos) = u32::try_from(i) else { continue };
                            let mut cp = path.clone();
                            cp.push(pos);
                            stack.push((child, cp));
                        }
                        continue;
                    }
                }
                if matches!(self.ctx.terms.sort(t), Sort::Bool) {
                    nodes.push((t, path));
                }
            }
        }
        // First-occurrence path per node (shortest is fine; any valid
        // extraction closes the proof). A node reachable only as the root `x`
        // itself is never recorded (the root is an `and`, descended above).
        let mut node_path: HashMap<TermId, Vec<u32>> = HashMap::default();
        for (t, p) in &nodes {
            node_path.entry(*t).or_insert_with(|| p.clone());
        }
        // Find a complementary pair `p` / `(not p)` where both are reachable.
        let Some((pos_term, neg_term)) = nodes.iter().find_map(|(t, _)| {
            let TermData::Not(inner) = self.ctx.terms.get(*t) else {
                return None;
            };
            let inner = *inner;
            node_path.contains_key(&inner).then_some((inner, *t))
        }) else {
            return false;
        };
        let pos_path = node_path[&pos_term].clone();
        let neg_path = node_path[&neg_term].clone();

        let mut new_proof = Proof::new();
        let assume_id = new_proof.add_assume(x, None);
        let (Some(pos_unit), Some(neg_unit)) = (
            Self::emit_and_pos_chain(
                &mut self.ctx.terms,
                &mut new_proof,
                assume_id,
                x,
                &pos_path,
                pos_term,
            ),
            Self::emit_and_pos_chain(
                &mut self.ctx.terms,
                &mut new_proof,
                assume_id,
                x,
                &neg_path,
                neg_term,
            ),
        ) else {
            return false;
        };
        new_proof.add_resolution(Vec::new(), pos_term, neg_unit, pos_unit);
        *proof = new_proof;
        true
    }

    /// `(and c1 .. cn)` of pure linear-arithmetic atoms whose conjunction is
    /// arithmetically infeasible (the CAV09 fold-to-false family): synthesize
    /// a Farkas certificate over the POSITIVE pure-linear conjuncts with the
    /// LRA solver, keep only the conjuncts carrying a NONZERO coefficient
    /// (the certificate identifies exactly the participating atoms, so large
    /// conjunctions do not degenerate into one `and_pos` per conjunct),
    /// independently re-verify the pruned certificate at external
    /// `la_generic` strength plus a printable equality-sign orientation, and
    /// derive `and_pos` extraction + one `la_generic` lemma + resolutions to
    /// the empty clause. Fail-closed: negated/impure/duplicated conjuncts
    /// never enter the candidate set, and any failed synthesis or
    /// re-verification keeps the proof byte-identical.
    fn rebuild_linear_and_collapse(
        &mut self,
        proof: &mut Proof,
        operands: &[FrontendTerm],
    ) -> bool {
        let mut conjs = Vec::with_capacity(operands.len());
        for op in operands {
            let Some(t) = self.raw_intern_surface(op) else {
                return false;
            };
            conjs.push(t);
        }
        // Re-intern the folded conjunction RAW (see the distinct emitter).
        let x = self
            .ctx
            .terms
            .mk_app(Symbol::named("and"), conjs.clone(), Sort::Bool);
        if !matches!(
            self.ctx.terms.get(x),
            TermData::App(Symbol::Named(op), a) if op == "and" && a.len() == conjs.len()
        ) {
            return false;
        }
        // Candidate conjuncts: POSITIVE pure linear-arithmetic atoms, first
        // occurrence only (a duplicated conjunct would double-count its
        // coefficient position; the first extraction suffices).
        let mut cand: Vec<usize> = Vec::new();
        for (i, &c) in conjs.iter().enumerate() {
            let pure = match self.ctx.terms.get(c) {
                TermData::App(Symbol::Named(op), args) if args.len() == 2 => match op.as_str() {
                    "<=" | "<" | ">=" | ">" => args
                        .iter()
                        .all(|&a| term_is_pure_linear_arith(&self.ctx.terms, a)),
                    "=" => equality_is_pure_linear_arith(&self.ctx.terms, c),
                    _ => false,
                },
                _ => false,
            };
            if pure && !conjs[..i].contains(&c) {
                cand.push(i);
            }
        }
        if cand.is_empty() {
            return false;
        }
        // Synthesize the certificate: assert ALL candidates into a fresh LRA
        // solver; the returned conflict names exactly the participating
        // atoms with their coefficients (so large conjunctions do not
        // degenerate into one `and_pos` per conjunct).
        let mut lra = ay_lra::LraSolver::new(&self.ctx.terms);
        lra.set_combined_theory_mode(true);
        for &i in &cand {
            ay_core::TheorySolver::register_atom(&mut lra, conjs[i]);
        }
        for &i in &cand {
            ay_core::TheorySolver::assert_literal(&mut lra, conjs[i], true);
        }
        let (lits, all) = match ay_core::TheorySolver::check(&mut lra) {
            ay_core::TheoryResult::UnsatWithFarkas(conflict) => {
                let lits = conflict.literals;
                match conflict.farkas {
                    Some(f) if f.coefficients.len() == lits.len() => (lits, f),
                    // No (or misaligned) certificate metadata: fall back to
                    // the all-ones candidate, judged solely by the
                    // independent re-verification below.
                    _ => {
                        let ones = FarkasAnnotation::from_ints(&vec![1i64; lits.len()]);
                        (lits, ones)
                    }
                }
            }
            // A conflict without Farkas metadata (e.g. a single conjunct
            // whose linear form cancels to `0 <= -1`): all-ones candidate,
            // fail-closed on the re-verification below.
            ay_core::TheoryResult::Unsat(lits) => {
                let ones = FarkasAnnotation::from_ints(&vec![1i64; lits.len()]);
                (lits, ones)
            }
            _ => return false,
        };
        if lits.is_empty() {
            return false;
        }
        // Map the conflict literals back to conjunct positions, dropping
        // zero-coefficient entries. Fail-closed on any literal that is not a
        // positively-asserted candidate conjunct (or appears twice).
        let mut sel: Vec<usize> = Vec::new();
        let mut coeffs = Vec::new();
        for (lit, coef) in lits.iter().zip(all.coefficients.iter()) {
            if num_traits::Zero::is_zero(coef) {
                continue;
            }
            if !lit.value {
                return false;
            }
            let Some(&i) = cand.iter().find(|&&i| conjs[i] == lit.term) else {
                return false;
            };
            if sel.contains(&i) {
                return false;
            }
            sel.push(i);
            coeffs.push(*coef);
        }
        // Deterministic conjunct order for stable printing.
        let mut order: Vec<usize> = (0..sel.len()).collect();
        order.sort_by_key(|&k| sel[k]);
        let sel: Vec<usize> = order.iter().map(|&k| sel[k]).collect();
        let coeffs: Vec<_> = order.iter().map(|&k| coeffs[k]).collect();
        if sel.is_empty() {
            return false;
        }
        let farkas = FarkasAnnotation::new(coeffs);
        let sel_conjs: Vec<TermId> = sel.iter().map(|&i| conjs[i]).collect();
        // Independent re-verification at external `la_generic` strength
        // (no congruence), plus the printable sign orientation (fail-closed).
        let conflict: Vec<TheoryLit> = sel_conjs.iter().map(|&c| TheoryLit::new(c, true)).collect();
        if ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            &self.ctx.terms,
            &conflict,
            &farkas,
        )
        .is_err()
        {
            return false;
        }
        if ay_core::proof_validation::resolve_equality_coefficient_signs(
            &self.ctx.terms,
            &conflict,
            &farkas,
        )
        .is_none()
        {
            return false;
        }
        let terms = &mut self.ctx.terms;
        let not_x = terms.mk_not_raw(x);
        let clause: Vec<TermId> = sel_conjs.iter().map(|&c| terms.mk_not_raw(c)).collect();
        let mut new_proof = Proof::new();
        let assume_id = new_proof.add_assume(x, None);
        let mut units: Vec<ProofId> = Vec::with_capacity(sel.len());
        for (&i, &c) in sel.iter().zip(sel_conjs.iter()) {
            #[allow(clippy::cast_possible_truncation)]
            let ap = new_proof.add_rule_step(
                AletheRule::AndPos(i as u32),
                vec![not_x, c],
                Vec::new(),
                Vec::new(),
            );
            units.push(new_proof.add_resolution(vec![c], x, ap, assume_id));
        }
        let lemma = new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: clause.clone(),
            farkas: Some(farkas),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        });
        let mut current = lemma;
        for (k, (&c, &uid)) in sel_conjs.iter().zip(units.iter()).enumerate() {
            current = new_proof.add_resolution(clause[k + 1..].to_vec(), c, current, uid);
        }
        *proof = new_proof;
        true
    }

    /// Consumed-assertions collapse (`x = 1 ∧ y = 2 ∧ x + y = 4`): the
    /// preprocessor substituted the assertions into each other, folded the
    /// contradiction, and the exported proof is the bare `(cl false) :rule
    /// trust` — no assume, no derivation. Re-prove from the ORIGINAL
    /// arithmetic-equality assertions: a single `la_generic` lemma over
    /// their negations, coefficients SYNTHESIZED by the LRA solver and
    /// independently re-verified (rational check + printable sign
    /// orientation, both fail-closed), closed by one resolution per assumed
    /// equality. Any non-equality original or failed certificate keeps the
    /// honest trust step.
    fn rebuild_consumed_equalities_collapse(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
    ) -> bool {
        // Every original must be a re-internable arithmetic equality (the
        // lemma's premises must cover the WHOLE assertion set: a dropped
        // non-equality premise could be the one that mattered — though any
        // certified subset would still be sound, requiring totality keeps
        // the rebuilt proof honest about what refuted the instance).
        let mut eqs: Vec<TermId> = Vec::with_capacity(originals.len());
        for (_, parsed) in originals {
            let stripped = strip_frontend_annotations(parsed);
            let FrontendTerm::App(head, operands) = stripped else {
                return false;
            };
            if head != "=" || operands.len() != 2 {
                return false;
            }
            let (Some(lhs), Some(rhs)) = (
                self.ctx.elaborate_surface_subterm(&operands[0]),
                self.ctx.elaborate_surface_subterm(&operands[1]),
            ) else {
                return false;
            };
            if !matches!(self.ctx.terms.sort(lhs), Sort::Int | Sort::Real)
                || self.ctx.terms.sort(lhs) != self.ctx.terms.sort(rhs)
            {
                return false;
            }
            let eq = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool);
            if !matches!(
                self.ctx.terms.get(eq),
                TermData::App(Symbol::Named(op), a) if op == "=" && a.len() == 2 && a[0] == lhs && a[1] == rhs
            ) {
                return false;
            }
            // External `la_generic` evaluates the combination syntactically:
            // impure atoms (UF/array applications) are out of scope.
            if !equality_is_pure_linear_arith(&self.ctx.terms, eq) {
                return false;
            }
            if !eqs.contains(&eq) {
                eqs.push(eq);
            }
        }
        if eqs.len() < 2 {
            return false;
        }
        let clause: Vec<TermId> = eqs.iter().map(|&e| self.ctx.terms.mk_not_raw(e)).collect();
        // Synthesize the certificate, then independently re-verify it and
        // require a printable equality-sign orientation (fail-closed).
        let mut farkas: Option<FarkasAnnotation> = None;
        let mut kind = TheoryLemmaKind::Generic;
        if !super::proof_farkas::try_lra_farkas_reconstruction(
            &self.ctx.terms,
            &clause,
            &mut farkas,
            &mut kind,
        ) {
            return false;
        }
        let Some(farkas) = farkas else {
            return false;
        };
        let conflict: Vec<TheoryLit> = eqs.iter().map(|&e| TheoryLit::new(e, true)).collect();
        if ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            &self.ctx.terms,
            &conflict,
            &farkas,
        )
        .is_err()
        {
            return false;
        }
        if ay_core::proof_validation::resolve_equality_coefficient_signs(
            &self.ctx.terms,
            &conflict,
            &farkas,
        )
        .is_none()
        {
            return false;
        }
        let mut new_proof = Proof::new();
        let assume_ids: Vec<ProofId> = eqs.iter().map(|&e| new_proof.add_assume(e, None)).collect();
        // Rationally certified: `la_generic`, fully checked externally.
        let lemma = new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: clause.clone(),
            farkas: Some(farkas),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        });
        let mut current = lemma;
        for (i, (&eq, &aid)) in eqs.iter().zip(assume_ids.iter()).enumerate() {
            let remaining: Vec<TermId> = clause[i + 1..].to_vec();
            current = new_proof.add_resolution(remaining, eq, current, aid);
        }
        *proof = new_proof;
        true
    }

    /// Recognize an exported assume as a recorded finite-domain quantifier
    /// expansion (#quant-expansion-proof): the assume term must equal a
    /// record's current replacement conjunction, the record's original must
    /// be a `forall` that is a genuine problem premise (present in
    /// `originals` with a `forall` surface). Fail-open `None` keeps the
    /// caller's existing behavior.
    fn classify_quant_expansion(
        &self,
        term: TermId,
        originals: &[(TermId, FrontendTerm)],
    ) -> Option<AssumePlan> {
        let TermData::App(sym, conjs) = self.ctx.terms.get(term) else {
            return None;
        };
        if sym.name() != "and" || conjs.is_empty() {
            return None;
        }
        let conjs = conjs.clone();
        for rec in &self.quant_expansion_records {
            if !matches!(self.ctx.terms.get(rec.original), TermData::Forall(..)) {
                continue;
            }
            // Pair with the ORIGINAL premise positionally: `originals` is
            // index-aligned with the parsed assertion stack, and
            // re-elaborating a `forall` surface mints fresh binder terms
            // (the canonical ids differ), so an id lookup cannot work. The
            // surface-shape gates below (a `forall` surface whose binder
            // count matches the recorded values) plus the per-conjunct
            // certificate validation and the external checker keep a
            // misalignment fail-closed.
            let Some((forall_canonical, parsed)) = originals.get(rec.assertion_index) else {
                continue;
            };
            let forall_canonical = *forall_canonical;
            if !matches!(self.ctx.terms.get(forall_canonical), TermData::Forall(..))
                || !matches!(strip_frontend_annotations(parsed), FrontendTerm::Forall(..))
            {
                continue;
            }
            let mut instances: HashMap<TermId, Vec<TermId>> = HashMap::default();
            for (vals, inst) in &rec.instances {
                instances.entry(*inst).or_insert_with(|| vals.clone());
            }
            // The assume must be COVERED by this record: ground
            // preprocessing may reorder/merge the expansion conjunction, so
            // the match is per-conjunct set inclusion, not whole-term
            // equality.
            if conjs.iter().all(|c| instances.contains_key(c)) {
                return Some(AssumePlan::QuantExpansion {
                    forall_term: forall_canonical,
                    parsed: parsed.clone(),
                    conjs,
                    instances,
                });
            }
        }
        None
    }

    /// Whether `(cl (not a1) .. (not an) concl)` is a valid all-ones
    /// `la_generic` lemma per the independent LINEAR Farkas checker (the
    /// antecedent literals asserted true, the conclusion asserted false).
    /// `_linear`, not `_full`: the lemma exports as `la_generic` and
    /// external checkers perform no congruence reasoning inside it.
    fn quant_lemma_valid(&self, antecedents: &[TermId], conclusion: TermId) -> bool {
        let mut lits: Vec<TheoryLit> = antecedents
            .iter()
            .map(|&l| match self.ctx.terms.get(l) {
                TermData::Not(inner) => TheoryLit::new(*inner, false),
                _ => TheoryLit::new(l, true),
            })
            .collect();
        lits.push(match self.ctx.terms.get(conclusion) {
            TermData::Not(inner) => TheoryLit::new(*inner, true),
            _ => TheoryLit::new(conclusion, false),
        });
        #[allow(clippy::cast_possible_truncation)]
        let coeffs = vec![1i64; lits.len()];
        ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            &self.ctx.terms,
            &lits,
            &FarkasAnnotation::from_ints(&coeffs),
        )
        .is_ok()
    }

    /// Whether the unit clause `(cl atom)` is a ground arithmetic tautology
    /// per the independent Farkas checker (its negation is infeasible on its
    /// own — e.g. the instantiated guard bound `(<= 0 24)`).
    fn ground_arith_unit_valid(&self, atom: TermId) -> bool {
        let lit = match self.ctx.terms.get(atom) {
            TermData::Not(inner) => TheoryLit::new(*inner, true),
            _ => TheoryLit::new(atom, false),
        };
        ay_core::proof_validation::verify_farkas_conflict_lits_full(
            &self.ctx.terms,
            &[lit],
            &FarkasAnnotation::from_ints(&[1]),
        )
        .is_ok()
    }

    /// Emit a `[1]` `la_generic` unit lemma `(cl atom)`. Only called for
    /// atoms already validated by [`Self::ground_arith_unit_valid`].
    fn add_unit_lemma(new_proof: &mut Proof, atom: TermId) -> ProofId {
        new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: vec![atom],
            farkas: Some(FarkasAnnotation::from_ints(&[1])),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        })
    }

    /// Build the certified derivation chain from the parsed `forall` premise
    /// to the unit `(cl target)` at binder values `values`
    /// (#quant-expansion-proof). Every ingredient is validated here, at plan
    /// time; emission ([`Self::emit_quant_instance_chain`]) is mechanical.
    /// Fail-closed `None` on: binder/value arity or sort mismatch, a body
    /// with any nested binding construct, a guard that is not a conjunction
    /// of distinct positive ground arithmetic truths, or a consequent that
    /// neither equals `target` nor bridges to it by a re-verified `[1, 1]`
    /// `la_generic` lemma.
    fn build_quant_instance_chain(
        &mut self,
        parsed_forall: &FrontendTerm,
        values: &[TermId],
        target: TermId,
    ) -> Option<QuantInstanceChain> {
        let stripped = strip_frontend_annotations(parsed_forall);
        let FrontendTerm::Forall(binders, body) = stripped else {
            return None;
        };
        if binders.len() != values.len() {
            return None;
        }
        let mut subst: HashMap<String, FrontendTerm> = HashMap::default();
        for ((name, _), &value) in binders.iter().zip(values.iter()) {
            subst.insert(name.clone(), value_to_surface(&self.ctx.terms, value)?);
        }
        let substituted = surface_subst_ground(body.as_ref(), &subst)?;
        let phi = self.raw_intern_surface(&substituted)?;
        let (guard, body_lit) = match &substituted {
            FrontendTerm::App(op, operands) if op == "=>" && operands.len() == 2 => {
                let guard_term = self.raw_intern_surface(&operands[0])?;
                let body_lit = self.raw_intern_surface(&operands[1])?;
                let atoms: Vec<TermId> = match strip_frontend_annotations(&operands[0]) {
                    FrontendTerm::App(gop, gargs) if gop == "and" && !gargs.is_empty() => gargs
                        .iter()
                        .map(|g| self.raw_intern_surface(g))
                        .collect::<Option<Vec<_>>>()?,
                    _ => vec![guard_term],
                };
                // Distinct positive atoms keep the and_neg resolution chain
                // unambiguous (a duplicated pivot would remove the wrong
                // number of literals; a negated conjunct would double-negate
                // in the and_neg clause).
                let mut seen = atoms.clone();
                seen.sort_unstable();
                seen.dedup();
                if seen.len() != atoms.len()
                    || atoms
                        .iter()
                        .any(|&a| matches!(self.ctx.terms.get(a), TermData::Not(_)))
                {
                    return None;
                }
                for &atom in &atoms {
                    if !self.ground_arith_unit_valid(atom) {
                        return None;
                    }
                }
                (Some((guard_term, atoms)), body_lit)
            }
            _ => (None, phi),
        };
        if body_lit != target {
            let body_complement = complement_of(&mut self.ctx.terms, body_lit);
            if !self.pair_lemma_valid(target, body_complement) {
                return None;
            }
        }
        Some(QuantInstanceChain {
            values: values.to_vec(),
            phi,
            guard,
            body_lit,
            target,
        })
    }

    /// Recognize a trust unit `(cl L)` as a folded consequence of ONE
    /// quantifier-expansion instance plus at most one original premise, and
    /// pre-build its certified derivation (#quant-expansion-proof).
    /// Fail-open `None` lets the caller's remaining plans (or the
    /// fail-closed abort) decide.
    fn plan_quant_consequence(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
    ) -> Option<QuantConsequencePlan> {
        if clause.len() != 1 || self.quant_expansion_records.is_empty() {
            return None;
        }
        let conclusion = clause[0];
        // Candidate support premises: non-quantifier original assertions.
        // The independent Farkas validation below is the real filter.
        let supports: Vec<TermId> = originals
            .iter()
            .map(|(c, _)| *c)
            .filter(|&c| {
                !matches!(
                    self.ctx.terms.get(c),
                    TermData::Forall(..) | TermData::Exists(..)
                )
            })
            .take(12)
            .collect();
        // Snapshot the record data to end the `self` borrow (bounded: the
        // expansion caps instances at 4096 per quantifier).
        let records: Vec<(usize, Vec<(Vec<TermId>, TermId)>)> = self
            .quant_expansion_records
            .iter()
            .map(|r| (r.assertion_index, r.instances.clone()))
            .collect();
        let mut budget = 20_000usize;
        for (assertion_index, instances) in records {
            // Positional pairing with the parsed premise (see
            // `classify_quant_expansion` for the alignment rationale).
            let Some((forall_term, parsed)) = originals.get(assertion_index) else {
                continue;
            };
            let forall_term = *forall_term;
            if !matches!(self.ctx.terms.get(forall_term), TermData::Forall(..))
                || !matches!(strip_frontend_annotations(parsed), FrontendTerm::Forall(..))
            {
                continue;
            }
            let parsed = parsed.clone();
            for (values, inst) in instances {
                if budget == 0 {
                    return None;
                }
                budget -= 1;
                // Instances folded to a constant carry no derivable content.
                if matches!(self.ctx.terms.get(inst), TermData::Const(_)) {
                    continue;
                }
                let used: Vec<TermId> = if self.quant_lemma_valid(&[inst], conclusion) {
                    Vec::new()
                } else {
                    let Some(&support) = supports.iter().find(|&&s| {
                        budget = budget.saturating_sub(1);
                        self.quant_lemma_valid(&[inst, s], conclusion)
                    }) else {
                        continue;
                    };
                    vec![support]
                };
                // Build (and thereby validate) the instance derivation; a
                // miss keeps searching other instances.
                let Some(chain) = self.build_quant_instance_chain(&parsed, &values, inst) else {
                    continue;
                };
                let mut lemma: Vec<TermId> = Vec::with_capacity(2 + used.len());
                lemma.push(complement_of(&mut self.ctx.terms, inst));
                for &s in &used {
                    lemma.push(complement_of(&mut self.ctx.terms, s));
                }
                lemma.push(conclusion);
                return Some(QuantConsequencePlan {
                    forall_term,
                    chain,
                    supports: used,
                    lemma,
                });
            }
        }
        None
    }

    /// Emit the plan-time-validated instance derivation
    /// (#quant-expansion-proof): `forall_inst` (positional binder-value
    /// args) + `or` + resolution against the forall's assume yields the raw
    /// substituted body; `implies_pos` + per-atom `[1]` `la_generic` guard
    /// units + `and_neg` discharge the instantiated guard; the optional
    /// re-verified `[1, 1]` bridge lands on the canonical target unit.
    fn emit_quant_instance_chain(
        &mut self,
        new_proof: &mut Proof,
        forall_term: TermId,
        assume_id: ProofId,
        chain: &QuantInstanceChain,
    ) -> ProofId {
        let not_forall = self.ctx.terms.mk_not_raw(forall_term);
        let inst_or =
            self.ctx
                .terms
                .mk_app(Symbol::named("or"), [not_forall, chain.phi], Sort::Bool);
        let fi = new_proof.add_rule_step(
            AletheRule::ForallInst,
            vec![inst_or],
            Vec::new(),
            chain.values.clone(),
        );
        let or_step = new_proof.add_rule_step(
            AletheRule::Or,
            vec![not_forall, chain.phi],
            vec![fi],
            Vec::new(),
        );
        let phi_unit = new_proof.add_resolution(vec![chain.phi], forall_term, or_step, assume_id);
        let body_unit = match &chain.guard {
            None => phi_unit,
            Some((guard_term, atoms)) => {
                let (guard_term, atoms) = (*guard_term, atoms.clone());
                let not_phi = self.ctx.terms.mk_not_raw(chain.phi);
                let not_guard = self.ctx.terms.mk_not_raw(guard_term);
                let ip = new_proof.add_rule_step(
                    AletheRule::ImpliesPos,
                    vec![not_phi, not_guard, chain.body_lit],
                    Vec::new(),
                    Vec::new(),
                );
                let guard_unit = if atoms.len() == 1 && atoms[0] == guard_term {
                    Self::add_unit_lemma(new_proof, guard_term)
                } else {
                    let not_atoms: Vec<TermId> = atoms
                        .iter()
                        .map(|&a| self.ctx.terms.mk_not_raw(a))
                        .collect();
                    let mut working = vec![guard_term];
                    working.extend(not_atoms.iter().copied());
                    let mut cur = new_proof.add_rule_step(
                        AletheRule::AndNeg,
                        working.clone(),
                        Vec::new(),
                        Vec::new(),
                    );
                    for (&atom, &not_atom) in atoms.iter().zip(not_atoms.iter()) {
                        let unit = Self::add_unit_lemma(new_proof, atom);
                        if let Some(p) = working.iter().position(|&l| l == not_atom) {
                            let _ = working.remove(p);
                        }
                        cur = new_proof.add_resolution(working.clone(), atom, cur, unit);
                    }
                    cur
                };
                let r1 = new_proof.add_resolution(
                    vec![not_guard, chain.body_lit],
                    chain.phi,
                    ip,
                    phi_unit,
                );
                new_proof.add_resolution(vec![chain.body_lit], guard_term, r1, guard_unit)
            }
        };
        if chain.target == chain.body_lit {
            body_unit
        } else {
            let body_pivot = atom_of(&self.ctx.terms, chain.body_lit);
            let body_complement = complement_of(&mut self.ctx.terms, chain.body_lit);
            let lemma = Self::add_pair_lemma(new_proof, chain.target, body_complement);
            new_proof.add_resolution(vec![chain.target], body_pivot, lemma, body_unit)
        }
    }
}
