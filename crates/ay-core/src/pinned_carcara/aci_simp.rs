// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A Carcara verdict that rests on an `aci_simp` step deduplicating a
//! non-idempotent operator is not evidence.
//!
//! Pinned carcara 1.1.0 (git 9a352ee) checks `(step _ (cl (= t1 t2)) :rule
//! aci_simp)` (`checker/rules/simplification.rs`, `aci_simp` and
//! `apply_aci_simp`) by normalizing each side whose head is one of the ten
//! operators its `is_assoc` lists (`and`, `or`, `+`, `*`, `bvadd`, `bvor`,
//! `bvmul`, `bvand`, `bvxor`, `concat`): it flattens nested applications of
//! that operator, drops EVERY repeated argument (`utils::Dedup` keeps a seen
//! set, so a repeat need not be adjacent), drops the operator's identity and
//! collapses a lone survivor to itself. Then it compares the two sides as
//! multisets of arguments (`concat`: syntactically). Dropping a repeat is
//! idempotence, which holds for `and`, `or`, `bvand` and `bvor` only, so over
//! the six operators of [`ACI_SIMP_OPERATORS_PINNED_CARCARA_DEDUPLICATES`] it
//! accepts false equalities.
//!
//! Measured 2026-10-07 with that checker, both plain and under
//! `--expand-let-bindings`: it prints `valid` for the one-step `aci_simp`
//! refutation of `(not (= L R))`, a SATISFIABLE problem (z3 `sat`), for
//! `(= (bvmul a a) a)`, `(= (bvadd a a) a)`, `(= (bvxor a a) a)`, `(= (+ x x)
//! x)` and `(= (* x x) x)` over `Int` and over `Real`, `(= a (bvadd a a))`,
//! `(= (bvmul a b a) (bvmul a b))`, `(= (bvmul a (bvmul a b)) (bvmul a b))`
//! and `(= (concat a a b) (concat a b b))`; for repeats spelled apart that it
//! parses as one term: `#x02`, `#b00000010` and `(_ bv2 8)`; `a` and `|a|`;
//! `2.0` and `2.00`; a `let` variable (under `--expand-let-bindings`), a
//! problem `:named` label, a proof `define-fun`, an annotated `(! a :named
//! q)`; and for `(= (bvadd a #x00) (bvmul a (bvadd a #x00)))`, which repeats
//! nothing as written: the left side normalizes to `a`, and the cache the two
//! sides share hands that `a` back for the right side's `(bvadd a #x00)`, so
//! the right side reads `(bvmul a a)`, deduplicated to `a`. Bool `xor` is not
//! on its list: `(= (xor p p) p)` is rejected. The true `(= (bvand a a) a)`,
//! `(= (bvor a a) a)`, `(= (and p p) p)` and `(= (or p p) p)` and the binary
//! swaps AY prints are accepted.
//!
//! THE GUARD. An `aci_simp` step is flagged when it applies one of those six
//! operators, directly or through a name Carcara expands before any rule runs
//! (a `:named` label or a `define-fun` whose command applies one, closed over
//! the names it uses), and its conclusion is not an AC identity
//! ([`aci_simp_equality_is_ac_identity`]). Every token is read where pinned
//! Carcara's lexer ends it (a non-ASCII space separates, `bvmul#x02` is
//! `bvmul` and `#x02`), so no spelling hides an operator or a name from the
//! scan. An AC identity holds whatever its arguments denote, so Carcara
//! accepting one is sound whichever route it took; a step that applies none of
//! the six even after expansion drops repeats only under an idempotent
//! operator, which Carcara checks soundly. Anything else may rest on the
//! defect. The guard does not re-run Carcara's normalization (its
//! deduplication, its identity removal, its cache shared between the two
//! sides, its literal folding): leaving each out can only flag more, e.g. the
//! true `(= (bvadd a #x00) a)`.
//!
//! AY's printer emits `aci_simp` only for an AC identity (binary `bvand` and
//! numeric `*` operand swaps, through `alethe_printer/aci_simp_step.rs` in
//! ay-proof), so no printed document rests on this defect; this is the
//! gate-side twin that catches any producer that does.

use super::lexer::{
    alethe_commands, command_atoms, record_names_applying, step_rule_of, LexedDocument, SexpToken,
};
use std::collections::BTreeSet;

/// The operators pinned Carcara's `aci_simp` deduplicates although they are
/// not idempotent (see above).
pub const ACI_SIMP_OPERATORS_PINNED_CARCARA_DEDUPLICATES: &[&str] =
    &["+", "*", "bvadd", "bvmul", "bvxor", "concat"];

/// Every operator pinned Carcara's `aci_simp` flattens (`is_assoc`). All are
/// associative, and all but `concat` commutative.
const ACI_SIMP_OPERATORS: &[&str] = &[
    "and", "or", "+", "*", "bvadd", "bvor", "bvmul", "bvand", "bvxor", "concat",
];

/// The `aci_simp` steps (whole commands) of `proof` that apply an operator of
/// [`ACI_SIMP_OPERATORS_PINNED_CARCARA_DEDUPLICATES`], directly or through a
/// name Carcara expands (a proof-local `define-fun`, a `:named` label of the
/// problem or the proof; a problem `define-fun` is recorded too, which can
/// only flag more), and whose conclusion is not an AC identity.
pub fn aci_simp_steps_pinned_carcara_misjudges<'a>(
    problem: &'a str,
    proof: &'a str,
) -> Vec<&'a str> {
    // Cheap exit: the rule name, quoted or not, spells `aci_simp`.
    if !proof.contains("aci_simp") {
        return Vec::new();
    }
    let mut names = BTreeSet::new();
    for command in alethe_commands(problem) {
        record_names_applying(
            &command_atoms(command),
            ACI_SIMP_OPERATORS_PINNED_CARCARA_DEDUPLICATES,
            &mut names,
        );
    }
    alethe_commands(proof)
        .into_iter()
        .filter(|command| {
            let atoms = command_atoms(command);
            record_names_applying(
                &atoms,
                ACI_SIMP_OPERATORS_PINNED_CARCARA_DEDUPLICATES,
                &mut names,
            ) && step_rule_of(&atoms) == Some("aci_simp")
                && !step_concludes_ac_identity(command)
        })
        .collect()
}

/// Whether `(= left right)`, spelled exactly so, is an AC identity: the two
/// sides spell the same term, or both apply one operator of `aci_simp`'s and,
/// with nested applications of it flattened, have the same arguments (spelled
/// exactly the same, quoting included) as a multiset, or for `concat` as a
/// sequence. Flattening is associativity and the multiset commutativity, so
/// an AC identity holds whatever its arguments denote. It repeats no argument
/// away, removes no identity element and folds no literal, so it can only
/// answer `false` where Carcara's own normalization would accept.
///
/// The one condition under which AY's printer emits an `aci_simp` step.
#[must_use]
pub fn aci_simp_equality_is_ac_identity(left: &str, right: &str) -> bool {
    let equality = format!("(= {left} {right})");
    let lexed = LexedDocument::new(&equality);
    let [equals, left, right] = lexed.children(0)[..] else {
        return false;
    };
    lexed.symbol(equals) == Some("=") && is_ac_identity(&lexed, left, right)
}

/// Whether the `(step id (cl (= t1 t2)) ..)` command concludes an AC
/// identity. Any other shape answers `false` (and Carcara rejects it).
fn step_concludes_ac_identity(command: &str) -> bool {
    let lexed = LexedDocument::new(command);
    let Some(&clause) = lexed.children(0).get(2) else {
        return false;
    };
    let [cl, literal] = lexed.children(clause)[..] else {
        return false;
    };
    let [equals, left, right] = lexed.children(literal)[..] else {
        return false;
    };
    lexed.symbol(cl) == Some("cl")
        && lexed.symbol(equals) == Some("=")
        && is_ac_identity(&lexed, left, right)
}

fn is_ac_identity(lexed: &LexedDocument<'_>, left: usize, right: usize) -> bool {
    if spelling(lexed, left) == spelling(lexed, right) {
        return true;
    }
    let (Some(operator), Some(right_operator)) = (lexed.head(left), lexed.head(right)) else {
        return false;
    };
    if operator != right_operator || !ACI_SIMP_OPERATORS.contains(&operator) {
        return false;
    }
    let mut left_arguments = flattened_arguments(lexed, left, operator);
    let mut right_arguments = flattened_arguments(lexed, right, operator);
    if operator != "concat" {
        left_arguments.sort_unstable();
        right_arguments.sort_unstable();
    }
    left_arguments == right_arguments
}

/// The arguments of the `operator` application at `application`, in order,
/// with nested applications of `operator` flattened. An explicit stack, so a
/// deep chain does not recurse.
fn flattened_arguments<'a>(
    lexed: &LexedDocument<'a>,
    application: usize,
    operator: &str,
) -> Vec<Vec<SexpToken<'a>>> {
    let mut arguments = Vec::new();
    let mut pending = vec![application];
    while let Some(position) = pending.pop() {
        if lexed.head(position) == Some(operator) {
            pending.extend(lexed.children(position).into_iter().skip(1).rev());
        } else {
            arguments.push(spelling(lexed, position));
        }
    }
    arguments
}

/// The tokens of the term at `position`, exactly as spelled. A quoted symbol
/// is NOT read as its unquoted text: `|#x02|`, `|2|` and `|_|` are symbols
/// where `#x02`, `2` and `_` are a literal, a numeral and a reserved word, and
/// pinned Carcara keeps them apart, so equating them would pass the false
/// `(= (bvmul #x02 #x02 |#x02|) (bvmul |#x02| |#x02| #x02))` as an AC identity
/// (measured 2026-10-07: Carcara deduplicates each side to `{#x02, |#x02|}`
/// and prints `valid` for its refutation of a SATISFIABLE problem). Two
/// spellings lexed alike are one term to Carcara (the shared lexer never splits
/// more finely than it does); raw spellings can only refuse more, e.g. the
/// true `(= (bvmul |a| b) (bvmul b a))`.
fn spelling<'a>(lexed: &LexedDocument<'a>, position: usize) -> Vec<SexpToken<'a>> {
    lexed.tokens[position..=lexed.last[position]].to_vec()
}
