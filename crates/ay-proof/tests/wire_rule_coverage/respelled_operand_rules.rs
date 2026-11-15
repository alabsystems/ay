// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The respelled-atom lowering's complete operand-bridge rule table.
//!
//! `alethe_printer/respelled_atom.rs` landed in `d22d4f03f fix(proof): three
//! strict-certificate defects` and was the one dynamic `:rule` producer added
//! since `be0a253a1` that no part of the coverage argument reached: it prints
//! `:rule {rule}` from a local binding, so the literal scan sees nothing, and
//! nothing else enumerated the binding's values.
//!
//! WHAT THIS PROVES. Every rule name that lowering can put on the wire is read
//! out of one production body and probed against the installed carcara. It is
//! a real bound, not a note: `respelled_operand_rule` is the binding's only
//! producer, `function_body` is brace-balanced so it reads the whole table
//! however the arms are spelled, and every literal found there is offered to
//! the inventory -- which refuses any that is not a plain Alethe symbol. The
//! source handed in is the one `printer_source_paths` scanned, so a lowering
//! that left the printer scan fails at its caller rather than being read from
//! a file the census never saw. Measured 2026-09-23 against carcara 1.1.0
//! (git 9a352ee): the table spells `refl` and `poly_simp`, and the checker
//! implements both. Renaming either to a name carcara does not implement fails
//! the coverage test at the probe.
//!
//! WHAT IT DOES NOT PROVE. That the lowering is SOUND: a rule the checker
//! implements can still be applied to the wrong clause. `respelled_atom`'s own
//! tests and carcara's re-derivation of the emitted document are what answer
//! that; this module only answers "can the checker resolve the spelling".

use super::{function_body, rust_string_literals, RustStringLiteral};

/// The production file whose rule table this module reads, as
/// `printer_source_paths` spells it.
const RESPELLED_ATOM: &str = "src/alethe_printer/respelled_atom.rs";

/// The one function the lowering may take a `:rule` name from.
const RULE_TABLE: &str = "fn respelled_operand_rule(";

/// How many rules that table spells today.
const RULE_TABLE_ARMS: usize = 2;

/// Read every rule name `format_respelled_atom_implication` can print.
///
/// That lowering prints `:rule {rule}` from a local `rule` binding, so unlike
/// a fixed `:rule name` it contributes nothing to the literal scan. Its names
/// are not open-ended, though: `respelled_operand_rule` is the only producer
/// of that binding, so reading its body enumerates the set exactly -- the same
/// closed-production-table reading the idempotent BV gate decoder gets.
///
/// Reading the BODY rather than the `let` statement is deliberate:
/// `function_body` is brace-balanced, so an arm that spells its condition with
/// an inner statement (and therefore an inner `;`) is still read, where a scan
/// to the selector's first `;` would silently stop short. Every string literal
/// in that body is offered to the inventory, and the inventory asserts each is
/// a plain Alethe symbol, so a non-rule literal appearing there fails loudly
/// instead of narrowing what the external probe covers.
pub(super) fn table(source: &str) -> Vec<RustStringLiteral> {
    let mut rules = rust_string_literals(function_body(source, RULE_TABLE));
    // `function_body` hands back a slice, so its literals are numbered from
    // the table's own first line; re-base them on the file the reader names.
    let declaration = source
        .find(RULE_TABLE)
        .expect("function_body already proved the rule table is present exactly once");
    let preceding = source[..declaration]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count();
    for literal in &mut rules {
        literal.line += preceding;
    }
    assert_eq!(
        rules.len(),
        RULE_TABLE_ARMS,
        "{RESPELLED_ATOM}: `{RULE_TABLE}` must spell each operand-bridge rule as a \
         literal so the wire-rule inventory can read it"
    );
    rules
}
