// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Closed bit-vector atoms, decided by value and re-derived for the checker.
//!
//! An atom is CLOSED when each operand is a bit-vector literal, or a `select`
//! that reads a literal out of a store chain over literal indices, reached
//! through the problem's own nullary `define-fun` premise `(= a body)`.
//!
//! The truth value is computed here exactly, and then PROVED, never asserted:
//!
//! * an order comparison or a false equality is pseudo-Boolean blasted over
//!   `@pbbterm` constants (`pbblast_pbbconst`, `cong`, `pbblast_bv*`,
//!   `trans`) and the resulting closed integer inequality is `la_generic`.
//!   Pinned carcara's `evaluate` is NOT used: it reads a negative signed
//!   operand as its magnitude (`Value::as_signed_bitvec` returns `2^w - v`),
//!   so it would refute the true `(bvsge #xff..ff #xff..fe)`;
//! * a true equality of two literals is `eq_reflexive` (the checker's lexer
//!   gives `#x07` and `#b00000111` one token);
//! * a store read is `arrays_idx` on a hit and `arrays_row` on a miss, whose
//!   index disequality is itself a closed atom proved as above; a `(as const
//!   ..)` base has no checker rule, so a read that reaches it is not closed.

use super::emit::Emitter;
use super::{
    parse_printed_bitvec_literal, split_application, AlethePrinter, HashMap, MAX_READ_DEPTH,
    MAX_WIDTH,
};
use num_bigint::{BigInt, BigUint};

/// A decided atom: its value and the commands that derive its unit clause.
pub(super) struct Decided {
    pub(super) value: bool,
    pub(super) derivation: String,
    pub(super) label: String,
}

/// One operand, read down to a literal.
struct Operand {
    literal: String,
    value: BigUint,
    width: u32,
    /// Step concluding `(= operand literal)`, when the operand was not one.
    proof: Option<String>,
}

const ORDER_HEADS: [&str; 8] = [
    "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
];

/// Decide `atom` and derive `(cl atom)` or `(cl (not atom))` under `prefix`.
pub(super) fn decide(
    printer: &AlethePrinter<'_>,
    prefix: String,
    atom: &str,
    definitions: Option<&HashMap<String, String>>,
) -> Option<Decided> {
    match atom.trim() {
        "true" | "false" => return decide_constant(printer, prefix, atom.trim()),
        _ => {}
    }
    let head = ["="]
        .into_iter()
        .chain(ORDER_HEADS)
        .find(|head| split_application(atom, head).is_some())?;
    let [left, right]: [String; 2] = split_application(atom, head)?.try_into().ok()?;
    let mut emitter = Emitter::new(printer, prefix);
    let left = operand(&mut emitter, &left, definitions)?;
    let right = operand(&mut emitter, &right, definitions)?;
    if left.width != right.width {
        return None;
    }
    let value = truth(head, &left, &right)?;
    let closed = format!("({head} {} {})", left.literal, right.literal);
    let premises: Vec<&str> = [&left.proof, &right.proof]
        .into_iter()
        .filter_map(Option::as_deref)
        .collect();
    let label = if premises.is_empty() {
        closed_unit(&mut emitter, head, &left, &right, atom, value)?
    } else {
        let unit = closed_unit(&mut emitter, head, &left, &right, &closed, value)?;
        transport(&mut emitter, atom, &closed, &premises, value, &unit)?
    };
    Some(Decided {
        value,
        derivation: emitter.out,
        label,
    })
}

fn decide_constant(printer: &AlethePrinter<'_>, prefix: String, atom: &str) -> Option<Decided> {
    let mut emitter = Emitter::new(printer, prefix);
    let value = atom == "true";
    let label = if value {
        emitter.step(&["true".to_string()], "true", &[], None)?
    } else {
        emitter.step(&["(not false)".to_string()], "false", &[], None)?
    };
    Some(Decided {
        value,
        derivation: emitter.out,
        label,
    })
}

fn operand(
    emitter: &mut Emitter<'_, '_>,
    text: &str,
    definitions: Option<&HashMap<String, String>>,
) -> Option<Operand> {
    let text = text.trim();
    if let Some((value, width)) = parse_printed_bitvec_literal(text) {
        return Some(Operand {
            literal: text.to_string(),
            value,
            width,
            proof: None,
        })
        .filter(|operand| (1..=MAX_WIDTH).contains(&operand.width));
    }
    let [array, index]: [String; 2] = split_application(text, "select")?.try_into().ok()?;
    let (literal, proof) = read(emitter, text, &array, &index, definitions, 0)?;
    let (value, width) = parse_printed_bitvec_literal(&literal)?;
    (1..=MAX_WIDTH).contains(&width).then_some(Operand {
        literal,
        value,
        width,
        proof: Some(proof),
    })
}

/// Read `(select array index)` (spelled `read`) down to a literal, returning
/// it and the step concluding `(= read literal)`.
fn read(
    emitter: &mut Emitter<'_, '_>,
    read_text: &str,
    array: &str,
    index: &str,
    definitions: Option<&HashMap<String, String>>,
    depth: usize,
) -> Option<(String, String)> {
    if depth > MAX_READ_DEPTH {
        return None;
    }
    let (key, key_width) = parse_printed_bitvec_literal(index)?;
    let array = array.trim();
    if let Some(body) = definitions.and_then(|definitions| definitions.get(array)) {
        // The problem's own `define-fun` premise, as pinned carcara reads it
        // without `--apply-function-defs`: `(= a body)`.
        let premise = emitter.assume(&format!("(= {array} {body})"))?;
        let unfolded = format!("(select {body} {index})");
        let unfold = emitter.step(
            &[format!("(= {read_text} {unfolded})")],
            "cong",
            &[&premise],
            None,
        )?;
        let (literal, rest) = read(emitter, &unfolded, body, index, definitions, depth + 1)?;
        let chained = format!("(= {read_text} {literal})");
        let label = emitter.step(&[chained], "trans", &[&unfold, &rest], None)?;
        return Some((literal, label));
    }
    let [base, stored_at, element]: [String; 3] =
        split_application(array, "store")?.try_into().ok()?;
    let (position, position_width) = parse_printed_bitvec_literal(&stored_at)?;
    if position_width != key_width {
        return None;
    }
    if position == key {
        let element = element.trim().to_string();
        parse_printed_bitvec_literal(&element)?;
        let hit = format!("(= {read_text} {element})");
        let label = emitter.step(&[hit], "arrays_idx", &[], None)?;
        return Some((element, label));
    }
    let stored = Operand {
        literal: stored_at.trim().to_string(),
        value: position,
        width: position_width,
        proof: None,
    };
    let read_at = Operand {
        literal: index.trim().to_string(),
        value: key,
        width: key_width,
        proof: None,
    };
    let apart_atom = format!("(= {} {})", stored.literal, read_at.literal);
    let apart = closed_unit(emitter, "=", &stored, &read_at, &apart_atom, false)?;
    let inner = format!("(select {base} {index})");
    let miss = format!("(= {read_text} {inner})");
    let skipped = emitter.step(&[miss], "arrays_row", &[&apart], None)?;
    let (literal, rest) = read(emitter, &inner, &base, index, definitions, depth + 1)?;
    let chained = format!("(= {read_text} {literal})");
    let label = emitter.step(&[chained], "trans", &[&skipped, &rest], None)?;
    Some((literal, label))
}

fn signed(value: &BigUint, width: u32) -> BigInt {
    let value = BigInt::from(value.clone());
    if width > 0 && value.bit(u64::from(width - 1)) {
        value - (BigInt::from(1u8) << width)
    } else {
        value
    }
}

fn truth(head: &str, x: &Operand, y: &Operand) -> Option<bool> {
    let (sx, sy) = (signed(&x.value, x.width), signed(&y.value, y.width));
    Some(match head {
        "=" => x.value == y.value,
        "bvult" => x.value < y.value,
        "bvule" => x.value <= y.value,
        "bvugt" => x.value > y.value,
        "bvuge" => x.value >= y.value,
        _ if x.width < 2 => return None,
        "bvslt" => sx < sy,
        "bvsle" => sx <= sy,
        "bvsgt" => sx > sy,
        "bvsge" => sx >= sy,
        _ => return None,
    })
}

fn bit(value: &BigUint, index: u32) -> &'static str {
    if value.bit(u64::from(index)) {
        "1"
    } else {
        "0"
    }
}

/// `(@pbbterm b_0 .. b_{w-1})`, least significant first.
fn pbb_term(operand: &Operand) -> String {
    let bits: Vec<&str> = (0..operand.width)
        .map(|index| bit(&operand.value, index))
        .collect();
    format!("(@pbbterm {})", bits.join(" "))
}

/// The short-circuited `@pbbterm` sum of the low `count` bits.
fn pb_sum(operand: &Operand, count: u32) -> String {
    let terms: Vec<String> = (0..count)
        .map(|index| {
            let bit = bit(&operand.value, index);
            if index == 0 {
                bit.to_string()
            } else {
                format!("(* {} {bit})", 1u128 << index)
            }
        })
        .collect();
    match terms.as_slice() {
        [only] => only.clone(),
        _ => format!("(+ {})", terms.join(" ")),
    }
}

/// The pinned `pbblast_*` rule for `head` and the relation it states over the
/// two `@pbbterm` operands (carcara `checker/rules/pb_blasting.rs`).
fn pb_relation(head: &str, x: &Operand, y: &Operand) -> Option<(&'static str, String)> {
    let width = x.width;
    let (sum_x, sum_y) = (pb_sum(x, width), pb_sum(y, width));
    let unsigned = |rule, left: &str, right: &str, floor: u8| {
        Some((rule, format!("(>= (- {left} {right}) {floor})")))
    };
    match head {
        "=" => Some(("pbblast_bveq", format!("(= (- {sum_x} {sum_y}) 0)"))),
        "bvult" => unsigned("pbblast_bvult", &sum_y, &sum_x, 1),
        "bvule" => unsigned("pbblast_bvule", &sum_y, &sum_x, 0),
        "bvugt" => unsigned("pbblast_bvugt", &sum_x, &sum_y, 1),
        "bvuge" => unsigned("pbblast_bvuge", &sum_x, &sum_y, 0),
        _ => signed_relation(head, x, y),
    }
}

fn signed_relation(head: &str, x: &Operand, y: &Operand) -> Option<(&'static str, String)> {
    if x.width < 2 {
        return None;
    }
    let msb = x.width - 1;
    let weight = 1u128 << msb;
    let (low_x, low_y) = (pb_sum(x, msb), pb_sum(y, msb));
    let sign_x = format!("(* {weight} {})", bit(&x.value, msb));
    let sign_y = format!("(* {weight} {})", bit(&y.value, msb));
    let less = format!("(+ (- {low_y} {sign_y}) (- {sign_x} {low_x}))");
    let greater = format!("(+ (- {low_x} {sign_x}) (- {sign_y} {low_y}))");
    let (rule, relation) = match head {
        "bvslt" => ("pbblast_bvslt", format!("(>= {less} 1)")),
        "bvsle" => ("pbblast_bvsle", format!("(>= {less} 0)")),
        "bvsgt" => ("pbblast_bvsgt", format!("(>= {greater} 1)")),
        "bvsge" => ("pbblast_bvsge", format!("(>= {greater} 0)")),
        _ => return None,
    };
    Some((rule, relation))
}

/// Derive the unit clause of a closed atom whose operands are both literals.
fn closed_unit(
    emitter: &mut Emitter<'_, '_>,
    head: &str,
    x: &Operand,
    y: &Operand,
    atom: &str,
    value: bool,
) -> Option<String> {
    if head == "=" && value {
        return emitter.step(&[atom.to_string()], "eq_reflexive", &[], None);
    }
    let (rule, relation) = pb_relation(head, x, y)?;
    let (px, py) = (pbb_term(x), pbb_term(y));
    let left = emitter.step(
        &[format!("(= {} {px})", x.literal)],
        "pbblast_pbbconst",
        &[],
        None,
    )?;
    let right = emitter.step(
        &[format!("(= {} {py})", y.literal)],
        "pbblast_pbbconst",
        &[],
        None,
    )?;
    let blasted = format!("({head} {px} {py})");
    let respelled = format!("(= {atom} {blasted})");
    let respelled = emitter.step(&[respelled], "cong", &[&left, &right], None)?;
    let stated = emitter.step(&[format!("(= {blasted} {relation})")], rule, &[], None)?;
    let equivalence = format!("(= {atom} {relation})");
    let equivalence = emitter.step(&[equivalence], "trans", &[&respelled, &stated], None)?;
    // The closed integer relation is the only arithmetic claim, and
    // `la_generic` re-derives it from its constants: a wrong value is refused.
    let relation_unit = if value {
        relation.clone()
    } else {
        format!("(not {relation})")
    };
    let relation_unit = emitter.step(&[relation_unit], "la_generic", &[], Some("1"))?;
    carry_unit(
        emitter,
        atom,
        &relation,
        &equivalence,
        value,
        &relation_unit,
    )
}

/// Carry the closed atom's unit back to the atom as printed.
fn transport(
    emitter: &mut Emitter<'_, '_>,
    atom: &str,
    closed: &str,
    premises: &[&str],
    value: bool,
    closed_unit: &str,
) -> Option<String> {
    let equivalence = emitter.step(&[format!("(= {atom} {closed})")], "cong", premises, None)?;
    carry_unit(emitter, atom, closed, &equivalence, value, closed_unit)
}

/// From `equivalence` concluding `(= atom other)` and `other_unit`
/// concluding `(cl other)` (`value`) or `(cl (not other))`, conclude the
/// same unit for `atom`.
fn carry_unit(
    emitter: &mut Emitter<'_, '_>,
    atom: &str,
    other: &str,
    equivalence: &str,
    value: bool,
    other_unit: &str,
) -> Option<String> {
    if value {
        let direction = [atom.to_string(), format!("(not {other})")];
        let direction = emitter.step(&direction, "equiv2", &[equivalence], None)?;
        emitter.step(
            &[atom.to_string()],
            "resolution",
            &[&direction, other_unit],
            None,
        )
    } else {
        let direction = [format!("(not {atom})"), other.to_string()];
        let direction = emitter.step(&direction, "equiv1", &[equivalence], None)?;
        let unit = format!("(not {atom})");
        emitter.step(&[unit], "resolution", &[&direction, other_unit], None)
    }
}
