// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The steps of one flattened-clause equivalence (see the parent module).

use super::super::{Derivation, MAX_PRINTED_EQUIVALENCE_OUTPUT_BYTES};
use super::{Connective, PairedLeaf, UnfoldedClause};

/// The printed pieces one flattened-clause equivalence relates.
#[derive(Clone, Copy)]
pub(super) struct FlattenedClause<'a> {
    pub(super) surface: &'a str,
    pub(super) disjunction: &'a str,
    pub(super) clause: &'a UnfoldedClause,
    pub(super) disjuncts: &'a [&'a str],
    pub(super) paired: &'a [PairedLeaf],
}

/// The derivation's steps and the bytes this schema pushed; `push` reports
/// `false` once they pass the output cap.
struct Emission<'d> {
    steps: &'d mut Vec<String>,
    bytes: usize,
}

impl Emission<'_> {
    fn push(&mut self, step: String) -> bool {
        self.bytes = self.bytes.saturating_add(step.len());
        self.steps.push(step);
        self.bytes <= MAX_PRINTED_EQUIVALENCE_OUTPUT_BYTES
    }
}

pub(super) fn emit_flattened_clause_equivalence(
    id: &str,
    shape: FlattenedClause<'_>,
    derivation: &mut Derivation,
) -> bool {
    let mut emission = Emission {
        steps: &mut derivation.steps,
        bytes: 0,
    };
    emit_both_directions(id, shape, &mut emission).is_some()
}

fn emit_both_directions(
    id: &str,
    shape: FlattenedClause<'_>,
    out: &mut Emission<'_>,
) -> Option<()> {
    let forward = emit_forward(id, shape, out)?;
    let backward = emit_backward(id, shape, out)?;
    let FlattenedClause {
        surface,
        disjunction,
        ..
    } = shape;
    let equality = format!("(= {surface} {disjunction})");
    let (forward, backward) = (forward.join(" "), backward.join(" "));
    [
        format!("(step {id}.u1 (cl (not {surface}) {disjunction}) :rule resolution :premises ({forward}))"),
        format!("(step {id}.u2 (cl {surface} (not {disjunction})) :rule resolution :premises ({backward}))"),
        format!("(step {id}.ux1 (cl {equality} (not {surface}) (not {disjunction})) :rule equiv_neg1)"),
        format!("(step {id}.ux2 (cl {equality} {surface} {disjunction}) :rule equiv_neg2)"),
        format!("(step {id}.uy1 (cl {equality} (not {disjunction})) :rule resolution :premises ({id}.ux1 {id}.u2))"),
        format!("(step {id}.uy2 (cl {equality} {disjunction}) :rule resolution :premises ({id}.ux2 {id}.u1))"),
        format!("(step {id} (cl {equality}) :rule resolution :premises ({id}.uy1 {id}.uy2))"),
    ]
    .into_iter()
    .all(|step| out.push(step))
    .then_some(())
}

/// The premises of `(cl (not S) O)`: each connective's positive unfolding,
/// `or_neg` per disjunct and `equiv_pos2` per re-spelled leaf.
fn emit_forward(
    id: &str,
    shape: FlattenedClause<'_>,
    out: &mut Emission<'_>,
) -> Option<Vec<String>> {
    let FlattenedClause {
        disjunction,
        clause,
        disjuncts,
        paired,
        ..
    } = shape;
    let mut premises = Vec::new();
    for (index, connective) in clause.connectives.iter().enumerate() {
        let step_id = format!("{id}.uf{index}");
        let step = match connective {
            Connective::Or { text, operands } => format!(
                "(step {step_id} (cl (not {text}) {}) :rule or_pos)",
                operands.join(" ")
            ),
            Connective::Implies {
                text,
                antecedent,
                consequent,
            } => format!(
                "(step {step_id} (cl (not {text}) (not {antecedent}) {consequent}) :rule implies_pos)"
            ),
            Connective::NegatedAnd {
                conjunction,
                conjuncts,
                ..
            } => {
                let negated: Vec<String> = conjuncts.iter().map(|c| format!("(not {c})")).collect();
                format!(
                    "(step {step_id} (cl {conjunction} {}) :rule and_neg)",
                    negated.join(" ")
                )
            }
            Connective::DoubleNegation => continue,
        };
        out.push(step).then_some(())?;
        premises.push(step_id);
    }
    for (index, disjunct) in disjuncts.iter().enumerate() {
        let step_id = format!("{id}.uo{index}");
        out.push(format!(
            "(step {step_id} (cl {disjunction} (not {disjunct})) :rule or_neg :args ({index}))"
        ))
        .then_some(())?;
        premises.push(step_id);
    }
    for pair in paired {
        let Some(equality) = &pair.equality else {
            continue;
        };
        let (leaf, disjunct) = (&clause.leaves[pair.leaf], disjuncts[pair.disjunct]);
        let step_id = format!("{id}.up{}", pair.leaf);
        out.push(format!(
            "(step {step_id} (cl (not (= {leaf} {disjunct})) (not {leaf}) {disjunct}) :rule equiv_pos2)"
        ))
        .then_some(())?;
        premises.push(step_id);
        premises.push(equality.clone());
    }
    Some(premises)
}

/// The premises of `(cl S (not O))`: each connective's negative unfolding per
/// child, `or_pos` over the disjuncts and `equiv_pos1` per re-spelled leaf.
fn emit_backward(
    id: &str,
    shape: FlattenedClause<'_>,
    out: &mut Emission<'_>,
) -> Option<Vec<String>> {
    let FlattenedClause {
        disjunction,
        clause,
        disjuncts,
        paired,
        ..
    } = shape;
    let mut steps: Vec<String> = vec![format!(
        "(cl (not {disjunction}) {}) :rule or_pos)",
        disjuncts.join(" ")
    )];
    for connective in &clause.connectives {
        match connective {
            Connective::Or { text, operands } => {
                steps.extend(operands.iter().enumerate().map(|(index, child)| {
                    format!("(cl {text} (not {child})) :rule or_neg :args ({index}))")
                }));
            }
            Connective::Implies {
                text,
                antecedent,
                consequent,
            } => {
                steps.push(format!("(cl {text} {antecedent}) :rule implies_neg1)"));
                steps.push(format!(
                    "(cl {text} (not {consequent})) :rule implies_neg2)"
                ));
            }
            Connective::NegatedAnd {
                text, conjuncts, ..
            } => {
                steps.extend(conjuncts.iter().enumerate().map(|(index, conjunct)| {
                    format!("(cl {text} {conjunct}) :rule and_pos :args ({index}))")
                }));
            }
            Connective::DoubleNegation => {}
        }
    }
    let mut premises = Vec::with_capacity(steps.len());
    for (index, step) in steps.into_iter().enumerate() {
        let step_id = format!("{id}.ub{index}");
        out.push(format!("(step {step_id} {step}")).then_some(())?;
        premises.push(step_id);
    }
    for pair in paired {
        let Some(equality) = &pair.equality else {
            continue;
        };
        let (leaf, disjunct) = (&clause.leaves[pair.leaf], disjuncts[pair.disjunct]);
        let step_id = format!("{id}.uv{}", pair.leaf);
        out.push(format!(
            "(step {step_id} (cl (not (= {leaf} {disjunct})) {leaf} (not {disjunct})) :rule equiv_pos1)"
        ))
        .then_some(())?;
        premises.push(step_id);
        premises.push(equality.clone());
    }
    Some(premises)
}
