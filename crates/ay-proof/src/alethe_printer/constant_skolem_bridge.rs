// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A checked bridge from an authored Skolemized body to the Bool constant
//! the term store folded it to.
//!
//! The store folds a vacuous body such as `(not (= q q))` to `false` (or
//! `(= q q)` to `true`) when it is built, so the Skolem instance of
//! `(forall ((q Int)) (not (= q q)))` is the store's SHARED `false` term. The
//! Skolem preparation used to install the authored instance text
//! `(not (= c c))` as an override keyed on that term, and so every `false` in
//! the document printed as `(not (= c c))`: the `false` axiom no longer
//! printed as `(cl (not false))` and was demoted to a hole, and a
//! `(= (not true) false)` bridge further down printed over the respelled
//! constant and was a hole as well (`forall-int-unsat`; Trust's `__trust_u_q`
//! spelling of it is the same document).
//!
//! The instance can stay the constant. Carcara's `sko_forall` / `sko_ex`
//! (`generic_skolemization_rule`) only needs the step immediately before it to
//! be an equality `(= BODY psi)` whose left side is the printed quantifier's
//! body and whose right side is the step's own right side; it never asks
//! that `psi` be `BODY[x := choice]`. A constant mentions no binder, so
//! Clean's export guard (`check_not_exported`) holds as well. This module
//! derives that equality from the printed body with rules Carcara re-checks,
//! inside the anchor:
//!
//! | printed body  | sub-steps                                        | constant |
//! |---------------|--------------------------------------------------|----------|
//! | `(= t t)`     | `eq_simplify`                                    | `true`   |
//! | `(< t t)`     | `comp_simplify`                                  | `false`  |
//! | `(<= t t)`    | `comp_simplify`                                  | `true`   |
//! | `(>= t t)`    | `comp_simplify`                                  | `true`   |
//! | `(> t t)`     | `comp_simplify` twice, `cong`, `not_simplify`, `trans` | `false` |
//! | `(not X)`     | `X`'s chain, then `cong`, `not_simplify`, `trans` | `¬X`    |
//!
//! Everything else declines, and the caller keeps today's bytes (the honest
//! hole). MEASURED 2026-10-01 with Trust's checker (`clean cert
//! verify-external`, Clean's vendored Carcara): every row is accepted, and so
//! are the `(not (= t t))` instance of the last row and the end-to-end shapes
//! built from them; the pinned upstream carcara 1.1.0 (git `9a352ee`) answers
//! `valid` on those end-to-end shapes as well. `(= (> t t) false)` as ONE `comp_simplify` is REFUSED —
//! that rule rewrites `(> a b)` to `(not (<= a b))` and stops there — which
//! is why `>` takes the two-rewrite chain; `(= (= q q) false)` and a `trans`
//! concluding the wrong constant are refused as well.
//!
//! Every row is guarded on the PRINTED text: the two sides of a comparison
//! must be the same bytes, so two spellings the store happens to identify
//! (`q` and `(+ q 0)`) decline rather than ship a rewrite the checker might
//! not see. The matcher declines `(= q |q|)` too, but end to end it never
//! sees that text: the printer already spells the authored `|q|` as `q`, so
//! `(forall ((q Int)) (not (= q |q|)))` reaches it as `(not (= q q))` and is
//! bridged (the same symbol, so the rewrite is the one the checker sees). A
//! wrong line here is a Carcara `invalid`, never a false accept; the decline
//! is the hole the base already printed.
//!
//! Every command this module writes goes through [`bridge_command`], which
//! converts the raw name to the private [`CheckableRule`] type before a
//! separate writer can format it; the caller prints the honest hole when the
//! conversion fails. The external wire-rule probe checks every name the type
//! can represent.
//!
//! Matching is pure and uncharged, so a body that declines leaves the
//! emission budget exactly where the base left it; only a bridge the
//! preparation RECORDS is charged
//! ([`AlethePrinter::record_constant_skolem_bridge`]).

use super::*;

/// Nesting cap on the `(not ..)` shells one bridge descends.
const MAX_NEGATION_DEPTH: usize = 8;

/// Byte cap on one printed body the matcher reads.
const MAX_BODY_BYTES: usize = 8192;

/// One rewrite the bridge ships, printed as the anchored sub-step `{id}.tK`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ConstantBridgeStep {
    /// The equality the sub-step concludes, `(= LEFT RIGHT)`.
    pub(super) conclusion: String,
    /// The Carcara rule that re-derives it.
    pub(super) rule: &'static str,
    /// Zero-based positions of the earlier sub-steps it cites.
    pub(super) premises: Vec<usize>,
}

/// The derivation of `(= BODY b)` for one printed body that folds to the
/// Bool constant `b`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ConstantSkolemBridge {
    /// The sub-steps, in emission order. The last one concludes
    /// `(= BODY b)`.
    pub(super) steps: Vec<ConstantBridgeStep>,
    /// `b`.
    pub(super) value: bool,
}

impl ConstantSkolemBridge {
    /// The sub-step commands under `id`: `{id}.t1` .. `{id}.tk`, or `None`
    /// when any of them names a rule [`bridge_command`] refuses.
    pub(super) fn lines(&self, id: ProofId) -> Option<Vec<String>> {
        self.steps
            .iter()
            .enumerate()
            .map(|(index, step)| {
                let premises: Vec<String> = step
                    .premises
                    .iter()
                    .map(|premise| format!("{id}.t{}", premise + 1))
                    .collect();
                bridge_command(
                    &format!("{id}.t{}", index + 1),
                    &step.conclusion,
                    step.rule,
                    &premises,
                )
            })
            .collect()
    }

    /// The equality the last sub-step concludes, which the closing
    /// `sko_forall` / `sko_ex` reads as its previous command.
    pub(super) fn last_conclusion(&self) -> Option<&str> {
        self.steps.last().map(|step| step.conclusion.as_str())
    }

    fn bytes(&self) -> usize {
        self.steps
            .iter()
            .map(|step| step.conclusion.len() + step.rule.len())
            .sum()
    }
}

/// One `(step LABEL (cl CLAUSE) :rule RULE[ :premises (..)])` command, or
/// `None` when `rule` is not in [`ay_core::CHECKABLE_ALETHE_RULES`].
///
/// This is the ONLY raw rule-name entry point in the module. The separate
/// typed writer cannot format a rule name this conversion refused.
fn bridge_command(label: &str, clause: &str, rule: &str, premises: &[String]) -> Option<String> {
    let rule = CheckableRule::new(rule)?;
    bridge_command_with_rule(label, clause, rule, premises)
}

fn bridge_command_with_rule(
    label: &str,
    clause: &str,
    rule: CheckableRule,
    premises: &[String],
) -> Option<String> {
    let mut command = format!("(step {label} (cl {clause}) :rule {rule}");
    if !premises.is_empty() {
        command.push_str(&format!(" :premises ({})", premises.join(" ")));
    }
    command.push(')');
    Some(command)
}

/// The printed spelling of a Bool constant.
pub(super) fn bool_text(value: bool) -> &'static str {
    if value {
        "true"
    } else {
        "false"
    }
}

/// The two operands of a printed binary application of `head`, as borrowed
/// slices; `None` for anything else.
fn binary_operands<'a>(printed: &'a str, head: &str) -> Option<(&'a str, &'a str)> {
    let operands = split_alethe_application_bounded(printed, head, 2, MAX_BODY_BYTES).ok()?;
    let [left, right] = operands.as_slice() else {
        return None;
    };
    Some((left, right))
}

/// The one operand of a printed `(not X)`.
fn negated_operand(printed: &str) -> Option<&str> {
    let operands = split_alethe_application_bounded(printed, "not", 1, MAX_BODY_BYTES).ok()?;
    let [operand] = operands.as_slice() else {
        return None;
    };
    Some(operand)
}

/// A comparison whose two sides are the same bytes, and the one-step
/// rewrite of it to a constant: `(rule, constant)`.
fn reflexive_atom(printed: &str) -> Option<(&'static str, bool)> {
    const ONE_STEP: [(&str, &str, bool); 4] = [
        ("=", "eq_simplify", true),
        ("<", "comp_simplify", false),
        ("<=", "comp_simplify", true),
        (">=", "comp_simplify", true),
    ];
    ONE_STEP.into_iter().find_map(|(head, rule, value)| {
        let (left, right) = binary_operands(printed, head)?;
        (left == right).then_some((rule, value))
    })
}

fn push(
    steps: &mut Vec<ConstantBridgeStep>,
    conclusion: String,
    rule: &'static str,
    premises: Vec<usize>,
) -> usize {
    steps.push(ConstantBridgeStep {
        conclusion,
        rule,
        premises,
    });
    steps.len() - 1
}

/// Derive `(= body b)` into `steps`; the index of the sub-step that
/// concludes it, and `b`.
fn derive(body: &str, depth: usize, steps: &mut Vec<ConstantBridgeStep>) -> Option<(usize, bool)> {
    if depth > MAX_NEGATION_DEPTH {
        return None;
    }
    if let Some(operand) = negated_operand(body) {
        let (inner, value) = derive(operand, depth + 1, steps)?;
        let (from, to) = (bool_text(value), bool_text(!value));
        let congruence = push(
            steps,
            format!("(= {body} (not {from}))"),
            "cong",
            vec![inner],
        );
        let negation = push(
            steps,
            format!("(= (not {from}) {to})"),
            "not_simplify",
            Vec::new(),
        );
        let last = push(
            steps,
            format!("(= {body} {to})"),
            "trans",
            vec![congruence, negation],
        );
        return Some((last, !value));
    }
    if let Some((rule, value)) = reflexive_atom(body) {
        let last = push(
            steps,
            format!("(= {body} {})", bool_text(value)),
            rule,
            Vec::new(),
        );
        return Some((last, value));
    }
    // `comp_simplify` rewrites `(> a b)` to `(not (<= a b))` and stops, so
    // `(> t t)` reaches `false` through `(<= t t)`.
    let (left, right) = binary_operands(body, ">")?;
    if left != right {
        return None;
    }
    let at_most = format!("(<= {left} {right})");
    let unfolded = push(
        steps,
        format!("(= {body} (not {at_most}))"),
        "comp_simplify",
        Vec::new(),
    );
    let reflexive = push(
        steps,
        format!("(= {at_most} true)"),
        "comp_simplify",
        Vec::new(),
    );
    let congruence = push(
        steps,
        format!("(= (not {at_most}) (not true))"),
        "cong",
        vec![reflexive],
    );
    let negation = push(
        steps,
        "(= (not true) false)".to_string(),
        "not_simplify",
        Vec::new(),
    );
    let last = push(
        steps,
        format!("(= {body} false)"),
        "trans",
        vec![unfolded, congruence, negation],
    );
    Some((last, false))
}

/// The checked derivation of `(= BODY b)` for a printed Skolemized body the
/// store folded to a Bool constant, or `None` when the body is not one of
/// the shapes in the module table (the caller then prints exactly what it
/// printed before). Pure: the work is bounded by [`MAX_BODY_BYTES`] and
/// [`MAX_NEGATION_DEPTH`], and nothing is charged until a bridge is
/// recorded.
pub(super) fn constant_skolem_bridge(body: &str) -> Option<ConstantSkolemBridge> {
    if body.len() > MAX_BODY_BYTES {
        return None;
    }
    let mut steps = Vec::new();
    let (_, value) = derive(body, 0, &mut steps)?;
    Some(ConstantSkolemBridge { steps, value })
}

impl AlethePrinter<'_> {
    /// The bridge for one Skolem step, when its instance is the store's
    /// `true` / `false`, the printed body is not already that constant's
    /// text, and the body derives to that same constant. Uncharged, like
    /// [`constant_skolem_bridge`].
    pub(super) fn constant_skolem_bridge_for_instance(
        &self,
        instance: TermId,
        body: &str,
    ) -> Option<ConstantSkolemBridge> {
        let TermData::Const(Constant::Bool(value)) = self.terms.get(instance) else {
            return None;
        };
        if body == bool_text(*value) {
            return None;
        }
        constant_skolem_bridge(body).filter(|bridge| bridge.value == *value)
    }

    /// Record the bridge Skolem step `id` prints, charging the body it read
    /// and the text it will write to the emission budget (exhaustion then
    /// surfaces at the next per-step budget check, as for any other work).
    pub(super) fn record_constant_skolem_bridge(
        &self,
        id: ProofId,
        body: &str,
        bridge: ConstantSkolemBridge,
    ) {
        self.charge((body.len() + bridge.bytes()) as u64);
        self.constant_skolem_bridges.borrow_mut().insert(id, bridge);
    }
}

/// How one certified Skolem step prints.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum SkolemStepForm {
    /// The anchor, the bridge's sub-steps and the closing rule
    /// ([`format_bridged_skolem_step`]).
    Bridged(String),
    /// The anchor, `(= BODY INSTANCE)` by `refl` and the closing rule.
    Refl,
    /// The honest hole over the same clause.
    Hole,
}

/// Choose the form of a certified Skolem step from its printed pieces.
///
/// Each path has exactly ONE judgement. A step with a recorded bridge is
/// judged by [`quantifier_surface::printed_constant_skolem_step_holds`]
/// only: when that refuses (another Skolem step respelled the shared
/// constant, say) the step is the hole, NEVER the `refl` form, even where
/// the `refl` judgement would accept the printed text, because the
/// preparation withheld the authored instance override for that step and
/// its instance text is not this step's to vouch for. A step without one is
/// judged by [`quantifier_surface::printed_skolem_step_holds`], exactly as
/// before the bridge existed.
pub(super) fn skolem_step_form(
    id: ProofId,
    step: &quantifier_surface::PrintedSkolemStep<'_>,
    bridge: Option<&ConstantSkolemBridge>,
) -> SkolemStepForm {
    match bridge {
        Some(bridge) => format_bridged_skolem_step(id, step, bridge)
            .map_or(SkolemStepForm::Hole, SkolemStepForm::Bridged),
        None if quantifier_surface::printed_skolem_step_holds(step) => SkolemStepForm::Refl,
        None => SkolemStepForm::Hole,
    }
}

/// The anchor, the bridge's sub-steps and the closing `sko_forall` /
/// `sko_ex` over `(= QUANTIFIER b)`, when the printed pieces instantiate the
/// rule ([`quantifier_surface::printed_constant_skolem_step_holds`]) and
/// every rule is one [`bridge_command`] admits. `None` otherwise: the caller
/// prints the honest hole over the same clause, exactly as an unbridged
/// step that fails its judgement does.
pub(super) fn format_bridged_skolem_step(
    id: ProofId,
    step: &quantifier_surface::PrintedSkolemStep<'_>,
    bridge: &ConstantSkolemBridge,
) -> Option<String> {
    let last = bridge.last_conclusion()?;
    if !quantifier_surface::printed_constant_skolem_step_holds(step, last) {
        return None;
    }
    let mut output = format!(
        "(anchor :step {id} :args ((:= ({} {}) {})))\n",
        step.binder, step.sort, step.choice
    );
    for line in bridge.lines(id)? {
        output.push_str(&line);
        output.push('\n');
    }
    output.push_str(&bridge_command(
        &id.to_string(),
        &format!("(= {} {})", step.quantified, step.instance),
        step.rule,
        &[],
    )?);
    Some(output)
}

#[cfg(test)]
#[path = "constant_skolem_bridge_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "constant_skolem_bridge_printer_tests.rs"]
mod printer_tests;
