// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Discharge the outside assumption before simplifying either preservation or
//! its De Morgan counterexample. Every connective position comes from source.

use super::*;

pub(super) fn finish(
    proof: &mut PackedProof<'_, '_>,
    info: &Outside,
    equality: Equality,
    end: &str,
    assumption: &str,
) -> Option<Equality> {
    let outside = proof.printer.format_term(info.shape.outside);
    let equal = proof.printer.format_term(info.shape.equality);
    let property = proof.printer.format_term(info.shape.property);
    if equal != format!("(= {} {})", equality.left, equality.right) {
        return None;
    }
    proof.named_step(
        end,
        &format!("(not {outside}) {equal}"),
        "subproof",
        &[],
        &format!(" :discharge ({assumption})"),
    )?;
    let (unit, literal, value) = if info.shape.property_value {
        (preserved(proof, info, end)?, property.clone(), "true")
    } else {
        (
            violated(proof, info, end)?,
            format!("(not {property})"),
            "false",
        )
    };
    let fact = format!("(= {property} {value})");
    let simple = proof.equality(&fact, &literal, "equiv_simplify", &[])?;
    let reverse = proof.equality(&literal, &fact, "symm", &[&simple.step])?;
    let step = proof.transport_unit(&reverse, &unit)?;
    Some(Equality {
        left: property,
        right: value.into(),
        step,
    })
}

fn preserved(proof: &mut PackedProof<'_, '_>, info: &Outside, end: &str) -> Option<String> {
    let outside = proof.printer.format_term(info.shape.outside);
    let equal = proof.printer.format_term(info.shape.equality);
    let property = proof.printer.format_term(info.shape.property);
    let negative_index = if property == format!("(or (not {outside}) {equal})") {
        0
    } else if property == format!("(or {equal} (not {outside}))") {
        1
    } else {
        return None;
    };
    let first = proof.fresh();
    let second = proof.fresh();
    proof.named_step(
        &first,
        &format!("{property} (not (not {outside}))"),
        "or_neg",
        &[],
        &format!(" :args ({negative_index})"),
    )?;
    proof.named_step(
        &second,
        &format!("{property} (not {equal})"),
        "or_neg",
        &[],
        &format!(" :args ({})", 1 - negative_index),
    )?;
    proof.step(&property, "resolution", &[end, &first, &second])
}

fn violated(proof: &mut PackedProof<'_, '_>, info: &Outside, end: &str) -> Option<String> {
    let terms = proof.printer.terms;
    let TermData::App(Symbol::Named(op), args) = terms.get(info.shape.property) else {
        return None;
    };
    if op != "and" || args.len() > 128 {
        return None;
    }
    let outside_index = args.iter().position(|&term| term == info.shape.outside)?;
    let negative_index = args.iter().position(
        |&term| matches!(terms.get(term), TermData::Not(inner) if *inner == info.shape.equality),
    )?;
    let property = proof.printer.format_term(info.shape.property);
    let children: Vec<_> = args.iter().map(|&t| proof.printer.format_term(t)).collect();
    if property != format!("(and {})", children.join(" ")) {
        return None;
    }
    let mut units = Vec::new();
    for index in [outside_index, negative_index] {
        let unit = proof.fresh();
        proof.named_step(
            &unit,
            &format!("(not {property}) {}", children[index]),
            "and_pos",
            &[],
            &format!(" :args ({index})"),
        )?;
        units.push(unit);
    }
    proof.step(
        &format!("(not {property})"),
        "resolution",
        &[end, &units[0], &units[1]],
    )
}
