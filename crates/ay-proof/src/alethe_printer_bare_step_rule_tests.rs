// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A theory lemma prints as a BARE step — `(step id (cl …) :rule R)` with no
//! `:premises` and no `:args`. These pin that `R` is never a rule the pinned
//! Alethe checker refuses on the premise/argument count.
//!
//! `is_checkable_alethe_rule` answers only "does the checker know this NAME".
//! For a bare step that is the wrong question: `string_decompose` (1 premise,
//! 1 arg), `re_inter` (2 premises), `concat_unify` (2 premises, 1 arg) and the
//! rest of `PREMISE_OR_ARG_REQUIRED_ALETHE_RULES` are rejected on the count
//! before the checker ever inspects the clause, and one such step takes the
//! whole document from `holey` to `invalid` — not a weaker proof, *no* proof.
//!
//! Measured on carcara 1.1.0 `[git master 9a352ee]`, given a problem declaring
//! `x : String` and the bare step
//!
//! ```text
//! (step t0 (cl (and (= x (str.++ x "")) (= (str.len x) 0))) :rule string_decompose)
//! ```
//!
//! the checker answers
//!
//! ```text
//! [ERROR] checking failed on step 't0' with rule 'string_decompose': expected 1 premises, got 0
//! invalid
//! ```
//!
//! and the identical step under `:rule hole` answers `holey`.

use super::*;
use ay_core::{Sort, Symbol, TermStore, TheoryLemmaKind};

/// `(str.contains x (str.++ y "a"))` — a clause AY's string solver can hand to
/// `TheoryLemmaKind::StringContentAxiom`, which requires a content-rewriting
/// operator to be present.
fn string_content_clause(terms: &mut TermStore) -> TermId {
    let x = terms.mk_var("bare_x", Sort::String);
    let y = terms.mk_var("bare_y", Sort::String);
    let a = terms.mk_string("a".to_string());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![y, a], Sort::String);
    terms.mk_app(Symbol::named("str.contains"), vec![x, concat], Sort::Bool)
}

fn theory_lemma(clause: Vec<TermId>, kind: TheoryLemmaKind) -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "string".to_string(),
        clause,
        farkas: None,
        kind,
        lia: None,
    }
}

/// The live regression: `StringContentAxiom.alethe_rule()` is
/// `"string_decompose"`, a REAL carcara rule name, so `wire_rule_name` passed
/// it straight through and AY published a step no checker run could accept.
#[test]
fn string_content_axiom_prints_hole_not_string_decompose() {
    let mut terms = TermStore::new();
    let clause = string_content_clause(&mut terms);
    let step = theory_lemma(vec![clause], TheoryLemmaKind::StringContentAxiom);
    let printer = AlethePrinter::new(&terms);

    let text = printer
        .format_step(&step, ProofId(1))
        .expect("a string content axiom renders as an honest unproved step");

    assert!(
        !text.contains("string_decompose"),
        "a bare step must not claim a rule the checker refuses on the premise \
         count; carcara answers `expected 1 premises, got 0` and voids the \
         whole document: {text}"
    );
    assert_eq!(
        text,
        "(step t1 (cl (str.contains bare_x (str.++ bare_y \"a\"))) :rule hole)"
    );
}

/// The internal identity is untouched — only the WIRE name is demoted. AY's
/// own strict checker still re-validates the kind through
/// `checker::string_axiom`, and the terminal-trust detector still reads the
/// proof IR, so nothing is hidden from AY's gates by this rendering.
#[test]
fn string_content_axiom_keeps_its_internal_rule_identity() {
    assert_eq!(
        TheoryLemmaKind::StringContentAxiom.alethe_rule(),
        "string_decompose",
        "the demotion is emission-only; classifiers and dedup keys still \
         match on the internal name"
    );
}

/// The general invariant, over EVERY kind rather than the one that regressed:
/// whatever a theory lemma publishes, it is never a rule the bare step cannot
/// back. A kind that refuses to print at all (missing Farkas annotation, an
/// array shape the surface validators reject) is fine — this is about what
/// reaches the wire, not about which kinds print.
#[test]
fn no_theory_lemma_kind_publishes_a_rule_its_bare_step_cannot_back() {
    let mut terms = TermStore::new();
    let clause = string_content_clause(&mut terms);
    let printer = AlethePrinter::new(&terms);

    let mut checked = 0usize;
    for kind in every_theory_lemma_kind() {
        let step = theory_lemma(vec![clause], kind);
        let Ok(text) = printer.format_step(&step, ProofId(1)) else {
            continue;
        };
        checked += 1;
        let rule = text
            .rsplit_once(":rule ")
            .and_then(|(_, tail)| tail.strip_suffix(')'))
            .unwrap_or_else(|| panic!("printed step must name a rule: {text}"));
        assert!(
            !ay_core::alethe_rule_requires_premises_or_args(rule),
            "{kind:?} published `{rule}` on a step with no :premises and no \
             :args; the checker refuses that on the count and marks the whole \
             document invalid. Print `hole` instead: {text}"
        );
        assert!(
            !text.contains(":premises") && !text.contains(":args"),
            "this invariant assumes the bare rendering; {kind:?} grew one: {text}"
        );
    }
    assert!(
        checked >= 8,
        "the sweep went vacuous — only {checked} kinds published a step"
    );
}

/// Every `TheoryLemmaKind` a bare theory-lemma step can carry.
///
/// Spelled out rather than derived so that a newly added kind fails to compile
/// here and its author has to state what the wire name is.
fn every_theory_lemma_kind() -> Vec<TheoryLemmaKind> {
    use ay_core::{BvGateType, FpOp};
    let all = vec![
        TheoryLemmaKind::EufTransitive,
        TheoryLemmaKind::EufReflexive,
        TheoryLemmaKind::EufCongruent,
        TheoryLemmaKind::EufCongruentPred,
        TheoryLemmaKind::LraFarkas,
        TheoryLemmaKind::LiaGeneric,
        TheoryLemmaKind::LiaModRange,
        TheoryLemmaKind::BvLiaTautology,
        TheoryLemmaKind::BvBitBlast,
        TheoryLemmaKind::BvBitBlastGate {
            gate_type: BvGateType::And,
            width: 8,
        },
        TheoryLemmaKind::ArraySelectStore { index_eq: true },
        TheoryLemmaKind::ArraySelectStore { index_eq: false },
        TheoryLemmaKind::ArrayStorePermutation,
        TheoryLemmaKind::ArrayRowChain,
        TheoryLemmaKind::ArrayDefaultConst,
        TheoryLemmaKind::SetCardNonNegative,
        TheoryLemmaKind::SetCardMemberLowerBound,
        TheoryLemmaKind::SetCardEmpty,
        TheoryLemmaKind::SetCardMemberCount,
        TheoryLemmaKind::SetCardEmptyByAssertion,
        TheoryLemmaKind::SetCardChainRecurrence,
        TheoryLemmaKind::SubsetReflexive,
        TheoryLemmaKind::SubsetElementInstance,
        TheoryLemmaKind::SubsetTransitive,
        TheoryLemmaKind::SubsetGroundEval,
        TheoryLemmaKind::ArrayExtensionality,
        TheoryLemmaKind::FpToBv {
            operation: FpOp::Add,
        },
        TheoryLemmaKind::StringLengthAxiom,
        TheoryLemmaKind::StringLengthLemma,
        TheoryLemmaKind::StringContentAxiom,
        TheoryLemmaKind::StringNormalForm,
        TheoryLemmaKind::StringGroundEval,
        TheoryLemmaKind::RegexIntersectEmpty,
        TheoryLemmaKind::StringContainmentIdentity,
        TheoryLemmaKind::StringConcatCancellation,
        TheoryLemmaKind::StringGroundFactorConflict,
        TheoryLemmaKind::RegexLengthLowerBound,
        TheoryLemmaKind::DatatypeDistinct,
        TheoryLemmaKind::DatatypeEnumPigeonhole,
        TheoryLemmaKind::DatatypeSelectorProject,
        TheoryLemmaKind::DatatypeTesterEval,
        TheoryLemmaKind::OrderIteTautology,
        TheoryLemmaKind::BoolTautology,
        TheoryLemmaKind::IteSame,
        TheoryLemmaKind::FpClassification {
            operation: FpOp::Abs,
        },
        TheoryLemmaKind::FpRoundingModeDomain,
        TheoryLemmaKind::FpForwardError,
        TheoryLemmaKind::NraIntervalUnsat,
        TheoryLemmaKind::NraUnivariateUnsat,
        TheoryLemmaKind::Generic,
        TheoryLemmaKind::RoundingModeDomain,
        TheoryLemmaKind::FpGroundEval,
    ];
    // Non-vacuity: the enumeration must actually reach the kind that regressed
    // and the near-miss string/regex family the wire-mapping audit covered.
    for required in [
        TheoryLemmaKind::StringContentAxiom,
        TheoryLemmaKind::StringLengthLemma,
        TheoryLemmaKind::RegexIntersectEmpty,
        TheoryLemmaKind::LiaModRange,
        TheoryLemmaKind::NraIntervalUnsat,
    ] {
        assert!(
            all.contains(&required),
            "{required:?} missing from the sweep"
        );
    }
    all
}
