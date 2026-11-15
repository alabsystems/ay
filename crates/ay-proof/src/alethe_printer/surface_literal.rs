// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Narrow syntactic equivalence for alternate SMT-LIB bit-vector literal
//! spellings below otherwise byte-identical applications.

use super::surface_tokens::split_smt_term_slices_bounded;
use super::*;

const MAX_LITERAL_EQUIVALENCE_BYTES: usize = 64 * 1024;
const MAX_LITERAL_EQUIVALENCE_DEPTH: usize = 64;
const MAX_LITERAL_EQUIVALENCE_NODES: usize = 256;

pub(super) fn equal_modulo_bitvec_literal_spelling(left: &str, right: &str) -> bool {
    if left.len() > MAX_LITERAL_EQUIVALENCE_BYTES || right.len() > MAX_LITERAL_EQUIVALENCE_BYTES {
        return false;
    }
    let mut nodes = 0;
    equal_inner(left, right, 0, &mut nodes, &mut HashSet::default())
}

/// Cache only completed identities, at the depth where they were checked.
/// Repeated printed DAG subtrees then consume one comparison state rather
/// than exhausting the node budget as an expanded tree. Including depth
/// prevents a shallow success from concealing an over-deep occurrence.
fn equal_inner<'s>(
    left: &'s str,
    right: &'s str,
    depth: usize,
    nodes: &mut usize,
    proven: &mut HashSet<(&'s str, &'s str, usize)>,
) -> bool {
    if left == right {
        return true;
    }
    if depth > MAX_LITERAL_EQUIVALENCE_DEPTH {
        return false;
    }
    let key = (left, right, depth);
    if proven.contains(&key) {
        return true;
    }
    if *nodes >= MAX_LITERAL_EQUIVALENCE_NODES {
        return false;
    }
    *nodes += 1;
    let equal = if let (Some(left_bv), Some(right_bv)) = (
        parse_printed_bitvec_literal(left),
        parse_printed_bitvec_literal(right),
    ) {
        left_bv == right_bv
    } else {
        let (Some(left), Some(right)) = (
            left.strip_prefix('(')
                .and_then(|term| term.strip_suffix(')')),
            right
                .strip_prefix('(')
                .and_then(|term| term.strip_suffix(')')),
        ) else {
            return false;
        };
        let split = |text| {
            split_smt_term_slices_bounded(
                text,
                MAX_LITERAL_EQUIVALENCE_BYTES,
                MAX_LITERAL_EQUIVALENCE_BYTES,
            )
        };
        let (Ok(left_parts), Ok(right_parts)) = (split(left), split(right)) else {
            return false;
        };
        left_parts.len() == right_parts.len()
            && left_parts
                .iter()
                .zip(right_parts.iter())
                .all(|(left, right)| equal_inner(left, right, depth + 1, nodes, proven))
    };
    if equal {
        proven.insert(key);
    }
    equal
}

/// [`clause_surface_agreement_admitting`] reading only byte-identical
/// overrides as the identity: the classifier every wire promotion but the
/// `evaluate` lowering uses.
pub(crate) fn clause_surface_agreement(
    terms: &TermStore,
    clause: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
) -> ClauseSurfaceAgreement {
    clause_surface_agreement_admitting(terms, clause, term_overrides, false)
}

/// Whether an override `surface` reproduces its term's `canonical` rendering:
/// byte for byte, or — only with `literal_respellings` — up to alternate
/// spellings of the same bit-vector literals ([`equal_modulo_bitvec_literal_spelling`]).
///
/// The second reading is what the `evaluate` lowering needs: AY interns
/// `(_ bv65 64)` and `#b0..01000001` as one constant, the authored-surface
/// channel prints the problem's spelling back, and pinned carcara's parser
/// builds one `Constant::BitVec(value, width)` from either, so it evaluates the
/// very term AY's validator did. Other promotions keep byte identity: the
/// LIA `evaluate` arm of `promoted_wire_rule` hands its clause to
/// `format_lia_ground_evaluate`, which self-guards on byte-identical clause
/// text, so widening them would split the gate from the printer.
pub(super) fn spelled_alike(surface: &str, canonical: &str, literal_respellings: bool) -> bool {
    surface == canonical
        || literal_respellings && equal_modulo_bitvec_literal_spelling(surface, canonical)
}

/// carcara's term identity on two printed operands: identical text parses to
/// one term, whatever its length, and the two spellings the surface can give
/// one term (whitespace inside an application, alternate bit-vector literal
/// spellings) are one term to its parser as well.
///
/// The byte comparison comes FIRST, and it is load-bearing: the modulo-
/// spelling walk refuses any operand over its 64 KiB cap, identical or not,
/// and the array lanes' units quote nested store chains of 80 KiB per
/// operand (QF_AUFLIA `swap_t1_pp_sf_ai_00009_002` at `-T:120`: three units
/// whose shared array position is 82 KiB of text). Through the walk alone
/// those three were declined to holes; identical text is the checker's own
/// identity and needs no walk.
///
/// This is a SPELLING predicate, never a semantic one: it equates two texts
/// only when carcara's parser builds one term from both, so two bit-vector
/// constants of different value OR different width, and any pair whose
/// application shapes differ, stay distinct. A caller may therefore use it
/// wherever it would otherwise compare the printed surface against the
/// certified rendering byte-for-byte, and no wider.
pub(super) fn same_printed_term(left: &str, right: &str) -> bool {
    left == right || equal_modulo_bitvec_literal_spelling(left, right)
}

/// The steps that derive `(= left right)` when [`same_printed_term`] holds —
/// i.e. when the external checker's PARSER builds one term from both printed
/// texts — bound to `id`, or `None` when it does not.
///
/// Byte-identical texts need no step at all: a caller that already names the
/// pair in its own conclusion can cite nothing. Texts that differ only in
/// bit-vector literal spelling need exactly one, because the identity is real
/// but invisible in the bytes: `#xAA` and `#b10101010` are one
/// `Constant::BitVec(170, 8)` to carcara's parser, so reflexivity over them
/// is an ordinary instance of its own `refl` rule. MEASURED on pinned carcara
/// 1.1.0 (git 9a352ee): `(step t1 (cl (= (store mem idx #xAA) (store mem idx
/// #b10101010))) :rule refl)` checks `valid`, while the same step over
/// `#b10101011` fails as "reflexivity failed with terms '(store mem idx (_
/// bv170 8))' and '(store mem idx (_ bv171 8))'". So this states an identity
/// the checker re-derives; it never asserts one the checker cannot see.
///
/// `None` is the conservative answer and leaves every caller's existing
/// repair, and its refusal, exactly where they were.
pub(super) fn same_printed_term_steps(id: &str, left: &str, right: &str) -> Option<Vec<String>> {
    if left == right {
        return Some(Vec::new());
    }
    if !equal_modulo_bitvec_literal_spelling(left, right) {
        return None;
    }
    Some(vec![format!(
        "(step {id} (cl (= {left} {right})) :rule refl)"
    )])
}

/// The other orientation of a printed arithmetic order, directly or under one
/// `not`: `(>= x 3)` -> `(<= 3 x)`, `(not (>= x 3))` -> `(not (<= 3 x))`.
/// `order_orientation_bridge_clause` bridges both forms with one
/// `la_generic` step.
///
/// The negated form is what a descendant override leaves on a `not` whose
/// atom is a comparison: `(assert (>= x 3))`, `(assert (or (not (>= x 3))
/// r))`, `(assert (not r))` prints the `cong` premise `(= (not (>= x 3))
/// false)` over the override while its `equiv_neg2` clause literal reads
/// `(not (<= 3 x))` (the atom's own spelling is confined to its `assume`).
/// MEASURED without this form: the judge, reading the shipped literal, found
/// no template ("no equiv_neg2 instance over the printed surface reproduces
/// this clause") and the whole document was refused; with it the step ships
/// the spec instance, one `la_generic` orientation bridge and a resolution,
/// and pinned carcara 1.1.0 checks the document `valid`.
pub(super) fn surface_order_orientation_twin(s: &str) -> Option<String> {
    if let Some(reversed) = surface_order_reversal(s) {
        return Some(reversed);
    }
    let [atom] = <[String; 1]>::try_from(split_application(s, "not")?).ok()?;
    Some(format!("(not {})", surface_order_reversal(&atom)?))
}

mod negative_shorthand;
pub(super) use negative_shorthand::negative_literal_shorthand_steps;
mod refl_spelling;
pub(super) use refl_spelling::{canonical_literal_respelling, carcara_refl_steps};
mod ground_value;
pub(super) use ground_value::ground_value_steps;

#[cfg(test)]
mod evaluate_agreement_tests;

#[cfg(test)]
mod derived_literal_tests;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alternate_bitvector_literal_spellings_match_positionally() {
        assert!(equal_modulo_bitvec_literal_spelling(
            "(store mem idx #xAA)",
            "(store mem idx #b10101010)"
        ));
        assert!(equal_modulo_bitvec_literal_spelling("#xAA", "(_ bv170 8)"));
    }

    #[test]
    fn respelled_bitvec_literal_pair_states_its_identity_with_refl() {
        assert_eq!(
            same_printed_term_steps("t3.ac0.l", "(store mem idx #xAA)", "(store mem idx #b10101010)"),
            Some(vec![
                "(step t3.ac0.l (cl (= (store mem idx #xAA) (store mem idx #b10101010))) :rule refl)"
                    .to_string()
            ])
        );
    }

    #[test]
    fn byte_identical_printed_pair_needs_no_step() {
        assert_eq!(
            same_printed_term_steps("t3.ac0.l", "(store mem idx #xAA)", "(store mem idx #xAA)"),
            Some(Vec::new())
        );
    }

    #[test]
    fn two_terms_decline_rather_than_claim_reflexivity() {
        assert_eq!(
            same_printed_term_steps("t3.ac0.l", "#xAA", "#xAB"),
            None,
            "a different bit-vector VALUE is two terms to the checker"
        );
        assert_eq!(
            same_printed_term_steps("t3.ac0.l", "#xAA", "#x00AA"),
            None,
            "a different bit-vector WIDTH is two terms to the checker"
        );
        assert_eq!(
            same_printed_term_steps("t3.ac0.l", "(+ x 0)", "x"),
            None,
            "an arithmetic identity is not a parser-level identity"
        );
    }

    #[test]
    fn changed_bitvector_values_or_application_shapes_decline() {
        assert!(!equal_modulo_bitvec_literal_spelling("#xAA", "#xAB"));
        assert!(!equal_modulo_bitvec_literal_spelling("#xAA", "#x00AA"));
        assert!(!equal_modulo_bitvec_literal_spelling(
            "(store mem idx #xAA)",
            "(select mem idx #b10101010)"
        ));
    }

    #[test]
    fn repeated_literal_spellings_share_the_identity_work_budget() {
        let mut left = "#xAA".to_string();
        let mut right = "(_ bv170 8)".to_string();
        for _ in 0..8 {
            left = format!("(concat {left} {left})");
            right = format!("(concat {right} {right})");
        }
        assert!(same_printed_term(&left, &right));
        let changed = right.replacen("bv170", "bv171", 1);
        assert!(!same_printed_term(&left, &changed));
    }

    #[test]
    fn distinct_literal_pairs_still_exhaust_the_identity_node_budget() {
        let left = (0..300)
            .map(|n| format!("#x{n:04x}"))
            .collect::<Vec<_>>()
            .join(" ");
        let right = (0..300)
            .map(|n| format!("(_ bv{n} 16)"))
            .collect::<Vec<_>>()
            .join(" ");
        assert!(!same_printed_term(
            &format!("(f {left})"),
            &format!("(f {right})")
        ));
    }

    #[test]
    fn shallow_cached_identity_cannot_hide_an_overdeep_occurrence() {
        let left = "(g #xAA)";
        let right = "(g (_ bv170 8))";
        let mut deep_left = left.to_string();
        let mut deep_right = right.to_string();
        for _ in 0..MAX_LITERAL_EQUIVALENCE_DEPTH {
            deep_left = format!("(f {deep_left})");
            deep_right = format!("(f {deep_right})");
        }
        assert!(!same_printed_term(
            &format!("(h {left} {deep_left})"),
            &format!("(h {right} {deep_right})"),
        ));
        let padding = "a ".repeat(MAX_LITERAL_EQUIVALENCE_BYTES / 2);
        assert!(!same_printed_term(
            &format!("(f {padding} #xAA)"),
            &format!("(f {padding} (_ bv170 8))"),
        ));
    }
}
