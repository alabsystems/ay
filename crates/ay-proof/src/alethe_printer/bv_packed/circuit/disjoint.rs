// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Generalize the checked symbolic-offset refutation, then instantiate it at
//! each actual read/write offset. Only standard Alethe binder/array rules cross
//! this boundary; recognition itself contributes no premise.

use super::*;
use crate::checker::bv_bitblast::disjoint::Shape;

mod instantiate;
mod source;

#[derive(Clone)]
pub(super) struct Disjoint {
    pub(super) shape: Shape,
    universal: String,
    unit: String,
    pub(super) guard_unit: String,
}

impl Disjoint {
    fn guard_text(&self, proof: &PackedProof<'_, '_>) -> String {
        let [a, b, c] = self
            .shape
            .guards
            .map(|term| proof.printer.format_term(term));
        format!("(and {a} (and {b} {c}))")
    }

    pub(super) fn collect_guard(
        &self,
        proof: &mut PackedProof<'_, '_>,
        root: TermId,
        assumption: &str,
    ) -> Option<String> {
        fn collect(
            proof: &mut PackedProof<'_, '_>,
            root: TermId,
            unit: &str,
            facts: &mut DetHashMap<TermId, String>,
            nodes: &mut usize,
        ) -> Option<()> {
            *nodes = nodes.checked_add(1)?;
            if *nodes > 64 {
                return None;
            }
            facts.insert(root, unit.into());
            if let TermData::App(Symbol::Named(op), args) = proof.printer.terms.get(root) {
                if op == "and" && !args.is_empty() && args.len() <= 128 {
                    let text = proof.printer.format_term(root);
                    for (i, &child) in args.iter().enumerate() {
                        let child_text = proof.printer.format_term(child);
                        let child_unit = proof.project_conjunct(&text, unit, &child_text, i)?;
                        collect(proof, child, &child_unit, facts, nodes)?;
                    }
                }
            }
            Some(())
        }
        let mut facts = DetHashMap::default();
        collect(proof, root, assumption, &mut facts, &mut 0)?;
        let [a, b, c] = self.shape.guards;
        let tail = format!(
            "(and {} {})",
            proof.printer.format_term(b),
            proof.printer.format_term(c)
        );
        let tail = proof.step(&tail, "and_intro", &[facts.get(&b)?, facts.get(&c)?])?;
        proof.step(
            &self.guard_text(proof),
            "and_intro",
            &[facts.get(&a)?, &tail],
        )
    }
}

pub(super) fn prove(proof: &mut PackedProof<'_, '_>, shape: Shape) -> Option<Disjoint> {
    let i = format!("{}offset_i", proof.definition_prefix);
    let j = format!("{}offset_j", proof.definition_prefix);
    let (terms, query) = source::query(proof.printer.terms, &shape, &i, &j)?;
    let budget = MAX_TEXT as u64;
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(budget));
    let mut inner = PackedProof::new(&printer, ProofId(0))?;
    inner.prefix = format!("{}.offset", proof.prefix);
    inner.definition_prefix = format!("{}offset!", proof.definition_prefix);
    let text = printer.format_term(query);
    let body = format!("(not {text})");
    let sort = format!("(_ BitVec {})", shape.width);
    let bindings = format!("(({i} {sort}) ({j} {sort}))");
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
    circuit.refute()?;
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
    Some(Disjoint {
        shape,
        universal,
        unit,
        guard_unit: String::new(),
    })
}
