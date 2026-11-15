// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked Alethe lowering for "this conjunction pins ONE term to two
//! different bit-vector CONSTANTS", and the printed-surface judgements that
//! decide whether it may fire.

use super::{
    eq_transitive, parse_printed_bitvec_literal, split_sexpr_tokens, surface_literal, AlethePrinter,
};
use ay_core::{Constant, ProofId, Symbol, TermData, TermId};

#[cfg(test)]
#[path = "bv_shared_endpoint/tests.rs"]
mod tests;

impl AlethePrinter<'_> {
    /// Largest conjunction this printer scans for a shared-endpoint constant
    /// conflict. The producer that reaches this shape refuses to build a joint
    /// guarded collapse past 64 parsed assertions
    /// (`executor/proof/bv_identity_promotion/guarded.rs`), so the bound never
    /// truncates that lane; it exists so the quadratic pair scan below cannot
    /// be handed an unbounded `and`.
    const MAX_SHARED_ENDPOINT_CONJUNCTS: usize = 64;

    /// Lower "this conjunction pins ONE term to two different bit-vector
    /// CONSTANTS" to Carcara's `evaluate`.
    ///
    /// WHY THE SHAPE EXISTS. [`Self::format_bv_constant_disequality`] above
    /// covers the UNIT clause `(cl (not (= c d)))` that the endpoint refuter
    /// in `executor/proof/authored_linear.rs` emits. The joint guarded
    /// collapse (`executor/proof/bv_identity_promotion/guarded.rs`,
    /// `promote_joint_bv_guarded_collapse`) reaches the SAME contradiction
    /// through a different clause: it derives the conjunction of the authored
    /// assertions with `and_neg` and refutes it with one coarse
    /// [`ay_core::TheoryLemmaKind::BvBitBlast`] over
    /// `(cl (not (and (= t c) (= t d))))`. Without this lane that clause falls
    /// through to `format_bv_complete_blast_refutation`, which is correct but
    /// blasts the whole conjunction bit by bit — around ninety steps and a
    /// per-bit `define-fun` table where the only fact in play is that two
    /// constants differ.
    ///
    /// EVERY BYTE THIS LANE EMITS IS READ OFF THE PRINTED SURFACE, and that
    /// is the whole of its safety argument. The defect class this file's
    /// sibling `alethe_printer_printed_rule_gate_tests.rs` exists for is a
    /// rule name read off the TERM DAG under text read off a SURFACE
    /// OVERRIDE, with nothing downstream comparing the two — and in this
    /// lane's production shape the root is SYNTHESIZED by
    /// `promote_joint_bv_guarded_collapse` (`terms.mk_app("and", roots)`)
    /// while the conjuncts are the AUTHORED assertions, i.e. precisely the
    /// terms `term_overrides` is keyed on. So:
    ///
    /// * the conjunct texts are SPLIT OUT OF the printed root rather than
    ///   reassembled from the printed conjuncts. A reassembly is equal to the
    ///   root's own rendering BY CONSTRUCTION — [`Self::format_term_data`]
    ///   builds an application as `({name} {args})` — for every root whose own
    ///   `TermId` carries no override, so it cannot see an override on a
    ///   conjunct or on anything below one. (#printed-rule-gate)
    /// * each selected conjunct's printed text must STATE the equality this
    ///   lane decoded it as: exactly `(= A B)` whose operands are, in some
    ///   order, the printed shared term and the printed constant whose value
    ///   the conclusion names. That comparison is between the conjunct's own
    ///   rendering and its sub-terms' renderings, so an override at the
    ///   conjunct — or a rendering that stopped agreeing with itself because
    ///   the #A2b emission budget ran out between two `format_term` calls —
    ///   declines instead of shipping a premise the conclusion cannot be
    ///   derived from.
    /// * the two selected conjuncts must print the shared side with the SAME
    ///   bytes. They are the same `TermId`, but that does not imply the same
    ///   text once the emission budget can turn one rendering into the
    ///   `@a2b_emission_budget_exhausted` placeholder mid-document.
    ///
    /// SUBSET ARGUMENT, rule by rule. Nothing here is asserted; Carcara
    /// re-derives every step from the printed text.
    ///
    /// * `and_pos :args (k)` concludes `(cl (not (and ...)) <k-th conjunct>)`
    ///   structurally over the conjunction it PARSES out of the printed root,
    ///   and `k` indexes the list that parse produced.
    /// * `eq_transitive` concludes `(cl (not A) (not B) (= c d))` for two
    ///   equalities that share a side. `A` and `B` are the printed conjuncts
    ///   verbatim, each checked to be a three-token `=` over the common
    ///   printed shared text and its own printed constant, in either
    ///   orientation; and the three literals the step actually ships are then
    ///   put to [`eq_transitive::printed_eq_transitive_chain_holds`], the
    ///   replay of the pinned checker's own `find_chain` that every other
    ///   `eq_transitive` emitter in this printer is judged by. It orients each
    ///   hypothesis itself, so a flipped equality needs no `eq_symmetric`
    ///   (probed on carcara 1.1.0, git 9a352ee: `(= t c)`/`(= t d)` and
    ///   `(= c t)`/`(= t d)` are both `valid`).
    /// * `evaluate` accepts `(cl (= term value))` exactly when its own ground
    ///   evaluator reduces `term` to `value`. Here `term` is `(= c d)` over two
    ///   bit-vector LITERALS — the same bytes the premises carry — so the
    ///   evaluator does nothing but compare two constants: no bit-vector
    ///   OPERATOR semantics are involved, and there is no room for AY's and
    ///   Carcara's evaluators to disagree.
    /// * `equiv_pos2`, `false` and `resolution` are premise-checked.
    ///
    /// The term DAG still has to exhibit the same conflict at the same two
    /// indices — the surface decides the BYTES, `decode_endpoint_equality`
    /// decides that AY's own claim is the one being printed — so the lane
    /// fires only where both agree.
    ///
    /// NEGATIVE DIRECTION. A conjunction with no two equalities sharing a
    /// side, one whose shared-term equalities carry EQUAL constants
    /// (satisfiable, so no refutation exists), one over non-constant or
    /// differently sized endpoints, a clause that is not a single negated
    /// `and`, a printed root that is not an `and` of exactly as many operands
    /// as the term has conjuncts, and any surface override that moves a
    /// selected conjunct's text out from under the equality it was decoded as
    /// all return `None` and leave the remaining lowerings — ultimately the
    /// complete bit-blast, and failing that the honest `hole` — exactly as
    /// they were.
    pub(super) fn format_bv_shared_endpoint_constant_conflict(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        let [literal] = clause else {
            return None;
        };
        let TermData::Not(root) = self.terms.get(*literal) else {
            return None;
        };
        let root = *root;
        let TermData::App(Symbol::Named(connective), conjuncts) = self.terms.get(root) else {
            return None;
        };
        if connective != "and"
            || conjuncts.len() < 2
            || conjuncts.len() > Self::MAX_SHARED_ENDPOINT_CONJUNCTS
        {
            return None;
        }
        let conjuncts = conjuncts.clone();

        // The conjuncts AS THE CHECKER SEES THEM: split out of the printed
        // root, which is the only authority on what `and_pos :args (k)`
        // indexes. Requiring the same count as the term's own conjunct list
        // is what ties the checker's view back to the shape decoded below.
        let printed_root = self.format_term(root);
        let printed_conjuncts = split_printed_and_operands(&printed_root)?;
        if printed_conjuncts.len() != conjuncts.len() {
            return None;
        }
        let printed_literal = self.format_term(*literal);
        if printed_literal != format!("(not {printed_root})") {
            return None;
        }

        let (first, second, first_constant, second_constant) =
            self.shared_endpoint_constant_conflict(&conjuncts, &printed_conjuncts)?;

        let left_text = &printed_conjuncts[first];
        let right_text = &printed_conjuncts[second];
        let equality_text = format!("(= {first_constant} {second_constant})");

        // THE SAME JUDGE EVERY OTHER `eq_transitive` EMITTER USES, over the
        // exact three literals this step ships. `printed_eq_transitive_chain_
        // holds` replays the pinned checker's own `find_chain` on the printed
        // operands, so the step is admitted only if the text carcara parses
        // really is a transitivity chain — never because the term DAG says so.
        let shipped_chain = [
            format!("(not {left_text})"),
            format!("(not {right_text})"),
            equality_text.clone(),
        ];
        let shipped_chain: Vec<&str> = shipped_chain.iter().map(String::as_str).collect();
        if !eq_transitive::printed_eq_transitive_chain_holds(&shipped_chain) {
            return None;
        }

        Some(format!(
            "(step {id}.sec.a (cl {printed_literal} {left_text}) :rule and_pos :args ({first}))\n\
             (step {id}.sec.b (cl {printed_literal} {right_text}) :rule and_pos :args ({second}))\n\
             (step {id}.sec.t (cl (not {left_text}) (not {right_text}) {equality_text}) :rule eq_transitive)\n\
             (step {id}.sec.ev (cl (= {equality_text} false)) :rule evaluate)\n\
             (step {id}.sec.eq (cl (not (= {equality_text} false)) (not {equality_text}) false) :rule equiv_pos2)\n\
             (step {id}.sec.f (cl (not false)) :rule false)\n\
             (step {id}.sec.r (cl (not {equality_text}) false) :rule resolution :premises ({id}.sec.ev {id}.sec.eq))\n\
             (step {id}.sec.n (cl (not {equality_text})) :rule resolution :premises ({id}.sec.r {id}.sec.f))\n\
             (step {id} (cl {printed_literal}) :rule resolution :premises ({id}.sec.a {id}.sec.b {id}.sec.t {id}.sec.n))"
        ))
    }

    /// Decode every conjunct on BOTH sides of the printer — off the term DAG
    /// (what AY's strict checker validated) and off the text the external
    /// checker will parse — and name the first pair that pins one shared term
    /// to two different constants.
    ///
    /// A conjunct is a candidate only where the two readings agree, so no step
    /// can name a premise from one and a conclusion from the other. The answer
    /// carries the two PRINTED constants, because the conclusion the caller
    /// emits is built from exactly those bytes and never from the term DAG.
    fn shared_endpoint_constant_conflict(
        &self,
        conjuncts: &[TermId],
        printed_conjuncts: &[String],
    ) -> Option<(usize, usize, String, String)> {
        let decoded: Vec<Option<EndpointEquality>> = conjuncts
            .iter()
            .zip(printed_conjuncts.iter())
            .map(|(&conjunct, printed)| {
                let decoded = self.decode_endpoint_equality(conjunct)?;
                printed_equality_states(printed, &decoded.printed_shared, &decoded.printed_constant)
                    .then_some(decoded)
            })
            .collect();

        for (first, left) in decoded.iter().enumerate() {
            let Some(left) = left else { continue };
            for (second, right) in decoded.iter().enumerate().skip(first + 1) {
                let Some(right) = right else { continue };
                if left.shared == right.shared
                    // Same node, but the emission budget can turn one of two
                    // renderings of it into the placeholder, and the printed
                    // chain only meets when both premises spell it alike.
                    && left.printed_shared == right.printed_shared
                    && left.width == right.width
                    && left.value != right.value
                {
                    return Some((
                        first,
                        second,
                        left.printed_constant.clone(),
                        right.printed_constant.clone(),
                    ));
                }
            }
        }
        None
    }

    /// Decode `(= shared constant)` / `(= constant shared)` over a canonical
    /// bit-vector literal, reporting both sides AS PRINTED plus the value and
    /// width the CHECKER reads off the printed constant.
    ///
    /// The caller re-checks the printed conjunct against these two strings, so
    /// what this returns is a CANDIDATE reading of the term, never the last
    /// word on what the checker will see.
    pub(super) fn decode_endpoint_equality(&self, equality: TermId) -> Option<EndpointEquality> {
        let TermData::App(Symbol::Named(eq), args) = self.terms.get(equality) else {
            return None;
        };
        if eq != "=" || args.len() != 2 {
            return None;
        }
        let (left, right) = (args[0], args[1]);
        // The equality node can have its own authored override, independently
        // of either child. Shared TermIds justify `eq_transitive` only if the
        // printed equality still names those same printed endpoints. Even an
        // equivalent `(bvadd t #x00)` spelling needs a separate checked bridge;
        // this direct lowering has none, so leave it to the existing fallback.
        let expected = format!("(= {} {})", self.format_term(left), self.format_term(right));
        if !surface_literal::same_printed_term(&self.format_term(equality), &expected) {
            return None;
        }
        for (shared, constant) in [(left, right), (right, left)] {
            if !matches!(
                self.terms.get(constant),
                TermData::Const(Constant::BitVec { .. })
            ) {
                continue;
            }
            let printed_constant = self.format_term(constant);
            let (value, width) = parse_printed_bitvec_literal(&printed_constant)?;
            return Some(EndpointEquality {
                shared,
                printed_shared: self.format_term(shared),
                printed_constant,
                value,
                width,
            });
        }
        None
    }
}

/// One conjunct decoded as `(= shared constant)` for the shared-endpoint
/// constant-conflict lowering: the opaque side as a node, BOTH sides as the
/// checker will read them, and the value and width parsed out of that
/// literal's printed spelling.
///
/// The two strings are what makes the decode auditable against the surface:
/// [`AlethePrinter::format_bv_shared_endpoint_constant_conflict`] requires the
/// conjunct's OWN printed text to state exactly `(= printed_shared
/// printed_constant)` (in either order) before it will name that conjunct as
/// an `eq_transitive` premise.
pub(super) struct EndpointEquality {
    shared: TermId,
    printed_shared: String,
    printed_constant: String,
    value: num_bigint::BigUint,
    width: u32,
}

/// Split a printed conjunction into the operand texts the external checker
/// parses out of it, or `None` when the text is not an `and` application.
///
/// `and_pos :args (k)` indexes THIS list, so it is read off the printed root
/// itself rather than reassembled from the printed conjuncts: a reassembly
/// `format!("(and {})", printed_conjuncts.join(" "))` equals the root's own
/// rendering BY CONSTRUCTION, because [`AlethePrinter::format_term_data`]
/// builds `TermData::App(Symbol::Named(..), args)` as
/// `format!("({} {})", name, args.map(format_term).join(" "))` from those same
/// renderings. Such a comparison can only ever see an override registered on
/// the ROOT's own `TermId` — never one on a conjunct, which in this lane's
/// production shape is the authored assertion and therefore the term most
/// likely to carry one. (#printed-rule-gate)
fn split_printed_and_operands(printed_root: &str) -> Option<Vec<String>> {
    let inner = printed_root.strip_prefix('(')?.strip_suffix(')')?;
    let mut tokens = split_sexpr_tokens(inner)?;
    if tokens.first().map(String::as_str) != Some("and") {
        return None;
    }
    tokens.remove(0);
    Some(tokens)
}

/// Whether one printed conjunct STATES the equality it was decoded as: a
/// three-token `(= A B)` whose operands are, in some order, the printed shared
/// term and the printed constant.
///
/// Balanced tokenization is load-bearing, not decoration. A shared-term
/// override that is not a single term — `a b` — renders the conjunct as
/// `(= a b #b00000101)`, a three-argument `=` whose transitivity chain is not
/// the two-endpoint chain the emitted conclusion names; the token count
/// refuses it.
///
/// The two operands are compared with [`surface_literal::same_printed_term`],
/// carcara's own identity on a printed operand, and NOT byte-for-byte. That is
/// the comparison the rest of this lane is judged by — the shipped chain goes
/// to [`eq_transitive::printed_eq_transitive_chain_holds`], whose `find_chain`
/// replay equates operands exactly this way — so a byte comparison here would
/// refuse a conjunct whose chain the checker then accepts. It is not a wider
/// predicate: `same_printed_term` equates two texts only where carcara's
/// parser builds ONE term from both (whitespace inside an application, and the
/// alternate spellings of one bit-vector literal at one width), so `five`,
/// `#x05` at a different width, and `(bvadd t #x00)` all still refuse.
fn printed_equality_states(printed: &str, shared: &str, constant: &str) -> bool {
    let Some(inner) = printed.strip_prefix('(').and_then(|s| s.strip_suffix(')')) else {
        return false;
    };
    let Some(tokens) = split_sexpr_tokens(inner) else {
        return false;
    };
    let [head, first, second] = tokens.as_slice() else {
        return false;
    };
    let states = |left: &str, right: &str| {
        surface_literal::same_printed_term(first, left)
            && surface_literal::same_printed_term(second, right)
    };
    head == "=" && (states(shared, constant) || states(constant, shared))
}
