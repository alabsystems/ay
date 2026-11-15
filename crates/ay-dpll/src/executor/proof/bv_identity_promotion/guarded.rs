// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Preserve the complete authored assertion when rebuilding a folded BV refutation.

use super::super::authored_bv_bitblast_refutation::SingletonSearch;
use super::super::{FrontendConstant, FrontendTerm};
use super::{Executor, GuardedCollapseStage};
use ay_core::{AletheRule, Proof, ProofStep, Sort, Symbol, TermId, TheoryLemmaKind};

mod before_promotion;
mod early;
mod mul_overflow;
mod rederive;
mod shadowed;
mod source;
mod urem_bound;

#[cfg(test)]
mod singleton_tests;
#[cfg(test)]
mod wire_repair_tests;
#[cfg(test)]
mod zero_addition_tests;

impl Executor {
    /// Returns whether a candidate replaced `proof`.
    pub(in crate::executor::proof) fn promote_bv_guarded_collapse(
        &mut self,
        proof: &mut Proof,
        stage: GuardedCollapseStage,
    ) -> bool {
        if !Self::proof_needs_schema_collapse_reconstruction(proof) {
            return false;
        }
        if self.ctx.assertions_parsed().len() > MAX_GUARDED_ROOTS {
            return false;
        }
        let stop = self.make_proof_assembly_should_stop();
        let publishable = self.authored_cascade_publishable(proof);
        let mut incumbent = IncumbentFacts::new(publishable);
        let mut roots = Vec::new();
        let mut retry_joint = !publishable;
        let mut singletons = SingletonSearch::default();
        for index in 0..self.ctx.assertions_parsed().len() {
            let Some((root, negated, has_array_read)) = self.guarded_source_root(index) else {
                continue;
            };
            roots.push(root);
            // Array macro spellings can still have a wire gap after native
            // checking. Keep every admitted guard for the joint refutation.
            retry_joint |= has_array_read;
            // The array escape repairs gaps, not already anchored proofs.
            // A blanket `BvBitBlast` would discard their finer certificate
            // (`eq_reflexive`, `refl`, `and_pos`, `ArraySelectStore`, ...),
            // the downgrade also prevented in `bv_bitblast_collapse.rs`.
            // A named arithmetic lane may still certify the same root in a
            // measurably smaller document (`rederive.rs`).
            if publishable && (!has_array_read || proof_already_assumes(proof, root)) {
                if self.promote_cheaper_named_rederivation(proof, root, negated) {
                    return true;
                }
                continue;
            }
            if self.promote_shadowed_store_source(proof, root) {
                return true;
            }
            let arithmetic =
                ay_proof::recognize_arith_clause_tautology(&self.ctx.terms, &[negated]);
            // Advice never removes an assumption: roots already retains it
            // for the joint replay. Cheap named admissions stay ahead of it.
            if !arithmetic
                && singletons.may_skip(root, &roots, &self.ctx, &self.proof_source_work, &stop)
            {
                #[cfg(test)]
                singleton_tests::skipped(root);
                continue;
            }
            let kind = if arithmetic {
                TheoryLemmaKind::ArithClauseTautology
            } else {
                TheoryLemmaKind::BvBitBlast
            };
            let candidate = rederive::anchored_refutation(root, negated, kind);
            if has_array_read
                && !arithmetic
                && !self.guarded_repair_worth_checking(proof, &candidate, stage, &mut incumbent)
            {
                // Before the promotion, a decision that turns on the promoted
                // incumbent is left to the cascade (`before_promotion.rs`).
                if stage == GuardedCollapseStage::BeforePromotion
                    && self.guarded_decision_awaits_promotion(&candidate)
                {
                    return false;
                }
                continue;
            }
            if !arithmetic {
                #[cfg(test)]
                singleton_tests::replayed(root);
                if self.check_proof_strict_until_stopped(&candidate).is_err() {
                    continue;
                }
            }
            self.record_raw_authored_problem_assertion(root);
            self.purge_surface_overrides_for_certified_proof(&candidate);
            *proof = candidate;
            return true;
        }
        if !retry_joint {
            return false;
        }
        match self.promote_urem_bound_joint(proof, &roots, stage, &mut incumbent, &stop) {
            Some(true) => true,
            Some(false) => {
                self.promote_joint_bv_guarded_collapse(proof, &roots, stage, &mut incumbent)
            }
            None => false,
        }
    }

    /// Rebuild one authored root and authenticate its canonical wire spelling
    /// before either the singleton advice or the complete joint proof sees it.
    fn guarded_source_root(&mut self, index: usize) -> Option<(TermId, TermId, bool)> {
        let assertion = &self.ctx.assertions_parsed()[index];
        let assertion = source::expand(&self.ctx, assertion)?;
        let has_array_read = bounded_source(&assertion)?;
        let root = self.raw_intern_ground_bv_surface(&assertion)?;
        if self.ctx.terms.sort(root) != &Sort::Bool {
            return None;
        }
        let negated = self.ctx.terms.mk_not_raw(root);
        self.guarded_terms_print_canonically(&[root, negated])
            .then_some((root, negated, has_array_read))
    }

    /// The array-read singles and the joint conjunction exist to REPAIR a
    /// wire gap (the escape documented in the loop above), and each costs a
    /// full strict bit-blast replay. Ask that purpose before paying for it.
    ///
    /// While the rendered Alethe is observable (a caller can retrieve the
    /// document, or the mint's presentation policy makes it verdict-relevant)
    /// every candidate keeps its replay: a replacement that still prints a
    /// `hole` can render where the incumbent's render is refused, so it can
    /// change the published certificate. Otherwise only the checked internal
    /// proof is consumed, and a candidate that would itself keep a known wire
    /// gap merely trades the incumbent's derivation for the coarsest lemma in
    /// the family. Mid-pipeline that is never worth a replay: later cascade
    /// members and derivation passes still own the incumbent's repair. At the
    /// final boundary it is worth one only while the incumbent is not
    /// strict-complete, so the candidate can still rescue the verdict.
    /// Declining never admits anything: every installed candidate still passes
    /// the unchanged strict check, and the mint stays the authority.
    ///
    /// The observable case has nothing to repair when the incumbent is
    /// strict-complete and every presentation gate already passes it with no
    /// unproved step (`proof_presents_without_unproved_step`): whatever the
    /// candidate prints, it would only trade that checked document for the
    /// coarsest lemma in the family (see the loop above). The incumbent's
    /// render is asked directly, because the known-wire-gap screen reports
    /// every multi-literal bit-blast lemma as a gap on purpose
    /// (`ay_proof::alethe_printer::complete_blast::clause`); only under
    /// `:check-proofs-strict`, whose library gate withholds any screened gap,
    /// does the screen count too. Measured once the
    /// strict checker could bit-blast 8-bit array reads: while every observed
    /// candidate was checked (as through 1c4ed9d77), `(= x #x00000000)` with
    /// `(bvugt (select (store a #x00 (bvmul x y)) #x00) #x00000000)` over
    /// `(Array (_ BitVec 8) (_ BitVec 32))` traded the trust-free exact
    /// authored BV refutation for the joint lemma, which prints as `hole`
    /// (`--strict-proofs`: `unknown (incomplete proof-trusted)`); and while a
    /// candidate that prints without a known gap was still checked, the ROW2
    /// fixture of `qfabv_row2_derived_index_disequality_is_strict_verified`
    /// traded its `ArraySelectStore` refutation for a 491-line joint blast.
    fn guarded_repair_worth_checking(
        &mut self,
        incumbent: &Proof,
        candidate: &Proof,
        stage: GuardedCollapseStage,
        facts: &mut IncumbentFacts,
    ) -> bool {
        // Ahead of the promotion or of an exact divider the incumbent's facts
        // are not yet settled, and asking whether it is complete would run the
        // producer the stage runs ahead of: the candidate must print clean.
        if stage.precedes_the_producer() {
            return self.guarded_candidate_prints_clean(candidate);
        }
        if self.proof_document_observable() {
            return !facts.complete(self, incumbent) || !facts.presents_clean(self, incumbent);
        }
        if self.guarded_candidate_prints_without_gap(candidate) {
            return true;
        }
        stage == GuardedCollapseStage::Final && !facts.complete(self, incumbent)
    }

    // Installation purges the overrides of every term the candidate prints
    // (`purge_surface_overrides_for_certified_proof`), so ask the wire screen
    // in that prospective view. Restore the map exactly afterwards: this only
    // asks, and a declined candidate must leave presentation state untouched.
    fn guarded_candidate_prints_without_gap(&mut self, candidate: &Proof) -> bool {
        let current = self.last_proof_term_overrides.clone();
        self.purge_surface_overrides_for_certified_proof(candidate);
        let wire_clean = !self.proof_has_known_wire_gap(candidate);
        self.last_proof_term_overrides = current;
        wire_clean
    }

    // Re-elaboration selects declaration identity even for a user symbol with
    // a builtin spelling. The raw builder preserves binary distinct and array
    // macro expansions; exact TermId equality rejects a misleading override.
    fn guarded_terms_print_faithfully(&mut self, terms: &[TermId]) -> bool {
        let overrides = self.proof_export_term_overrides().unwrap_or_default();
        terms.iter().all(|&term| {
            let rendered =
                ay_proof::format_term_alethe_with_overrides(&self.ctx.terms, term, &overrides);
            self.guarded_rendering_matches_term(&rendered, term)
        })
    }

    // Certified replacement purges overrides on every term it prints. Check
    // that prospective view: applying an old folded subterm's source override
    // to an already raw-rebuilt operation would introduce the operation twice.
    // The source builder and this exact roundtrip still authenticate every
    // declaration; neither an override nor a normalized expression is authority.
    fn guarded_terms_print_canonically(&mut self, terms: &[TermId]) -> bool {
        terms.iter().all(|&term| {
            let rendered = ay_proof::format_term_alethe(&self.ctx.terms, term);
            self.guarded_rendering_matches_term(&rendered, term)
        })
    }

    fn guarded_rendering_matches_term(&mut self, rendered: &str, term: TermId) -> bool {
        super::super::parse_rendered_assertion(rendered)
            .is_some_and(|parsed| self.guarded_parsed_rendering_matches_term(&parsed, term))
    }

    fn guarded_parsed_rendering_matches_term(
        &mut self,
        parsed: &FrontendTerm,
        term: TermId,
    ) -> bool {
        // Existing presentation overrides may name authenticated nullary
        // definitions; expansion and raw interning retain their bounds.
        source::expand(&self.ctx, parsed).and_then(|mut parsed| {
            compact_roundtrip_literals(&mut parsed)?;
            self.raw_intern_ground_bv_surface(&parsed)
        }) == Some(term)
    }

    /// A raw conjunction is derived from the author's separate premises using
    /// and_neg and resolution. It is never introduced as an extra assumption.
    fn promote_joint_bv_guarded_collapse(
        &mut self,
        proof: &mut Proof,
        roots: &[TermId],
        stage: GuardedCollapseStage,
        incumbent: &mut IncumbentFacts,
    ) -> bool {
        if roots.len() < 2 {
            return false;
        }
        #[cfg(test)]
        singleton_tests::joint(roots);
        let root = self
            .ctx
            .terms
            .mk_app(Symbol::named("and"), roots.to_vec(), Sort::Bool);
        let negative = self.ctx.terms.mk_not_raw(root);
        let mut candidate = Proof::new();
        let mut assumptions = Vec::new();
        let mut clause = vec![root];
        for &premise in roots {
            assumptions.push(candidate.add_assume(premise, None));
            clause.push(self.ctx.terms.mk_not_raw(premise));
        }
        let mut unit =
            candidate.add_rule_step(AletheRule::AndNeg, clause.clone(), Vec::new(), Vec::new());
        for (&premise, assumption) in roots.iter().zip(assumptions) {
            let _ = clause.remove(1);
            unit = candidate.add_resolution(clause.clone(), premise, unit, assumption);
        }
        let lemma =
            candidate.add_theory_lemma_with_kind("bv", vec![negative], TheoryLemmaKind::BvBitBlast);
        candidate.add_resolution(Vec::new(), root, lemma, unit);
        if !self.guarded_repair_worth_checking(proof, &candidate, stage, incumbent)
            || self.check_proof_strict_until_stopped(&candidate).is_err()
        {
            return false;
        }
        for &root in roots {
            self.record_raw_authored_problem_assertion(root);
        }
        self.purge_surface_overrides_for_certified_proof(&candidate);
        *proof = candidate;
        true
    }
}

/// What the guarded repairs ask about the incumbent, each asked at most once
/// per promotion.
struct IncumbentFacts {
    complete: Option<bool>,
    presents_clean: Option<bool>,
}

impl IncumbentFacts {
    fn new(publishable: bool) -> Self {
        // Lazily: is the incumbent strict-complete? Publishable implies it.
        Self {
            complete: publishable.then_some(true),
            presents_clean: None,
        }
    }

    fn complete(&mut self, executor: &Executor, incumbent: &Proof) -> bool {
        *self.complete.get_or_insert_with(|| {
            executor
                .check_proof_strict_with_datatypes(incumbent)
                .is_ok_and(|quality| quality.is_complete())
        })
    }

    fn presents_clean(&mut self, executor: &Executor, incumbent: &Proof) -> bool {
        *self
            .presents_clean
            .get_or_insert_with(|| executor.proof_presents_without_unproved_step(incumbent))
    }
}

// The printer spells BV constants as full-width binary strings. Normalize only
// the temporary round-trip AST to exact decimal numerals before re-elaboration:
// otherwise the original frame's 4 MiB source-work estimate grows past 8 MiB
// solely from literal spelling. Keep width (including leading zeroes), original
// source, emitted proof, declaration authentication and all work limits intact.
fn compact_roundtrip_literals(root: &mut FrontendTerm) -> Option<()> {
    bounded_source(root)?;
    compact_roundtrip_literal_leaves(root)
}

// Callers must first bound their own linear input traversal. This only
// rewrites literal spelling in a temporary AST, without interning or expansion.
fn compact_roundtrip_literal_leaves(root: &mut FrontendTerm) -> Option<()> {
    use ay_frontend::command::Index;
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        match term {
            FrontendTerm::Const(constant) => {
                let (digits, radix, bits) = match constant {
                    FrontendConstant::Binary(text) => {
                        (text.strip_prefix("#b").unwrap_or(text.as_str()), 2, 1)
                    }
                    FrontendConstant::Hexadecimal(text) => {
                        (text.strip_prefix("#x").unwrap_or(text.as_str()), 16, 4)
                    }
                    _ => continue,
                };
                let width = digits.len().checked_mul(bits)?;
                if !(1..=128).contains(&width) {
                    return None;
                }
                let value = num_bigint::BigUint::parse_bytes(digits.as_bytes(), radix)?;
                *term = FrontendTerm::IndexedApp(
                    format!("bv{value}"),
                    vec![Index::Numeral(width.to_string())],
                    Vec::new(),
                );
            }
            FrontendTerm::App(_, args)
            | FrontendTerm::IndexedApp(_, _, args)
            | FrontendTerm::QualifiedApp(_, _, args) => stack.extend(args.iter_mut()),
            _ => (),
        }
    }
    Some(())
}

/// Most authored assertions the guarded collapse walks.
const MAX_GUARDED_ROOTS: usize = 64;

// Bound the source walk before cloning or invoking the recursive faithful
// builder. Every accepted indexed operator and array annotation is bounded too.
fn bounded_source(root: &FrontendTerm) -> Option<bool> {
    let mut stack = vec![(root, 0usize)];
    let mut nodes = 0usize;
    let mut has_array_read = false;
    while let Some((term, depth)) = stack.pop() {
        nodes += 1;
        if nodes > 16_384 || depth > 96 {
            return None;
        }
        match term {
            FrontendTerm::App(op, args)
                if op.len() <= 64
                    && (args.len() <= 2
                        || matches!(op.as_str(), "ite" | "store") && args.len() == 3
                        || matches!(op.as_str(), "and" | "or") && args.len() <= 128) =>
            {
                has_array_read |= op == "select";
                stack.extend(args.iter().map(|arg| (arg, depth + 1)));
            }
            FrontendTerm::Symbol(name) if name.len() <= 4096 => {}
            FrontendTerm::Const(FrontendConstant::True | FrontendConstant::False) => {}
            FrontendTerm::Const(
                FrontendConstant::Binary(text) | FrontendConstant::Hexadecimal(text),
            ) if text.len() <= 130 => {}
            FrontendTerm::IndexedApp(name, indices, args)
                if args.is_empty()
                    && name.len() <= 64
                    && indices.len() == 1
                    && indices[0].as_numeral().is_some_and(|n| n.len() <= 3) => {}
            FrontendTerm::IndexedApp(name, indices, args)
                if matches!(name.as_str(), "extract" | "zero_extend" | "sign_extend")
                    && args.len() == 1
                    && (1..=2).contains(&indices.len())
                    && indices
                        .iter()
                        .all(|i| i.as_numeral().is_some_and(|n| n.len() <= 3)) =>
            {
                stack.push((&args[0], depth + 1));
            }
            FrontendTerm::QualifiedApp(identifier, sort, args)
                if identifier.as_symbol() == Some("const")
                    && args.len() == 1
                    && bounded_array_sort(sort) =>
            {
                stack.push((&args[0], depth + 1));
            }
            _ => return None,
        }
    }
    Some(has_array_read)
}

fn bounded_array_sort(sort: &ay_frontend::command::ParsedSort) -> bool {
    use ay_frontend::command::ParsedSort;
    let ParsedSort::Parameterized(name, args) = sort else {
        return false;
    };
    name == "Array"
        && args.len() == 2
        && args.iter().all(|sort| {
            let ParsedSort::Indexed(name, indices) = sort else {
                return false;
            };
            name == "BitVec"
                && indices.len() == 1
                && indices[0].as_numeral().is_some_and(|n| {
                    n.len() <= 3
                        && n.parse::<u32>()
                            .is_ok_and(|width| (1..=128).contains(&width))
                })
        })
}

// Whether the refutation in hand already rests on this exact raw authored
// assertion. The rebuild above would install the identical `assume`, so it has
// nothing left to preserve and declining keeps the finer anchor already there.
fn proof_already_assumes(proof: &Proof, root: TermId) -> bool {
    proof
        .steps
        .iter()
        .any(|step| matches!(step, ProofStep::Assume(term) if *term == root))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_literals_preserve_value_and_full_width() {
        let mut context = ay_frontend::Context::new();
        for width in [1, 4, 9, 64, 128] {
            for digits in [
                "0".repeat(width),
                format!("{}1", "0".repeat(width - 1)),
                "1".repeat(width),
            ] {
                let original = FrontendTerm::Const(FrontendConstant::Binary(format!("#b{digits}")));
                let expected = context.elaborate_surface_subterm(&original).unwrap();
                let mut compact = original;
                compact_roundtrip_literals(&mut compact).unwrap();
                assert_eq!(context.elaborate_surface_subterm(&compact), Some(expected));
                assert_eq!(context.terms.sort(expected), &Sort::bitvec(width as u32));
            }
        }
        for digits in [
            "0001",
            "0000000000000000",
            "ffffffffffffffffffffffffffffffff",
        ] {
            let original =
                FrontendTerm::Const(FrontendConstant::Hexadecimal(format!("#x{digits}")));
            let expected = context.elaborate_surface_subterm(&original).unwrap();
            let mut compact = original;
            compact_roundtrip_literals(&mut compact).unwrap();
            assert_eq!(context.elaborate_surface_subterm(&compact), Some(expected));
        }
    }

    #[test]
    fn roundtrip_literals_reject_malformed_or_over_budget_inputs() {
        for digits in [String::new(), "2".into(), "1".repeat(129)] {
            let mut term = FrontendTerm::Const(FrontendConstant::Binary(digits));
            assert!(compact_roundtrip_literals(&mut term).is_none());
        }
        let mut term = FrontendTerm::Symbol("x".into());
        for _ in 0..96 {
            term = FrontendTerm::App("not".into(), vec![term]);
        }
        assert!(compact_roundtrip_literals(&mut term).is_some());
        term = FrontendTerm::App("not".into(), vec![term]);
        assert!(compact_roundtrip_literals(&mut term).is_none());
    }
}
