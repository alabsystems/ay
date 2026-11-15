// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn prove(
    proof: &mut PackedProof<'_, '_>,
    shape: OutsideFrameShape,
) -> Option<(Outside, Instant)> {
    let offset = format!("{}outside_offset", proof.definition_prefix);
    let (terms, query) = source::query(proof.printer, &shape, &offset)?;
    let budget = MAX_TEXT as u64;
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(budget));
    let mut inner = PackedProof::new(&printer, ProofId(0))?;
    inner.prefix = format!("{}.outside", proof.prefix);
    inner.definition_prefix = format!("{}outside!", proof.definition_prefix);
    let text = printer.format_term(query);
    let body = format!("(not {text})");
    let sort = format!("(_ BitVec {})", shape.width);
    let bindings = format!("(({offset} {sort}))");
    let universal = format!("(forall {bindings} {body})");
    let quantified_true = format!("(forall {bindings} true)");
    let bound = inner.fresh();
    let end = inner.fresh();
    let assumption = inner.fresh();
    inner.append(&format!(
        "(anchor :step {end})\n(assume {assumption} {text})\n"
    ))?;
    let mut circuit = Circuit::new(&mut inner);
    let (bit, equality) = circuit.boolean(query, 0)?;
    let unit = circuit.proof.transport_unit(&equality, &assumption)?;
    circuit.input(vec![bit], unit)?;
    circuit.refutation_parts = 2;
    circuit.refute()?;
    let deadline = circuit.deadline?;
    inner.named_step(
        &end,
        &format!("{body} false"),
        "subproof",
        &[],
        &format!(" :discharge ({assumption})"),
    )?;
    let nf = inner.step("(not false)", "false", &[])?;
    let body_unit = inner.step(&body, "resolution", &[&end, &nf])?;
    let fact = format!("(= {body} true)");
    let simple = inner.equality(&fact, &body, "equiv_simplify", &[])?;
    let reversed = inner.equality(&body, &fact, "symm", &[&simple.step])?;
    inner.transport_unit(&reversed, &body_unit)?;
    inner.named_step(
        &bound,
        &format!("(= {universal} {quantified_true})"),
        "bind",
        &[],
        "",
    )?;
    let simple = inner.equality(&quantified_true, "true", "qnt_rm_unused", &[])?;
    let eq = inner.equality(&universal, "true", "trans", &[&bound, &simple.step])?;
    let reversed = inner.equality("true", &universal, "symm", &[&eq.step])?;
    let yes = inner.step("true", "true", &[])?;
    let unit = inner.transport_unit(&reversed, &yes)?;
    // Definitions mentioning offsets are parsed within their binder scope.
    // They never escape as premises; the checked forall equality closes it.
    proof.append(&format!("(anchor :step {bound} :args {bindings})\n"))?;
    proof.append(&inner.definitions)?;
    proof.append(&inner.out)?;
    proof.printer.charge(printer.work_used());
    if printer.work_budget_exhausted() || proof.printer.work_budget_exhausted() {
        return None;
    }
    Some((
        Outside {
            shape,
            universal,
            unit,
            guard_unit: String::new(),
        },
        deadline,
    ))
}
