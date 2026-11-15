// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One closed finite-case theorem per exact zero-extension bit pattern.
//!
//! The Boolean parameters are universally bound. An instance supplies only
//! actual bit formulas through checked forall_inst; no query assumption or
//! inner definition is retained in the cache.

use super::*;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Bit {
    False,
    True,
    Variable(usize),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct TemplateKey {
    input_width: usize,
    output_width: usize,
    extra: usize,
    support: usize,
    pattern: Vec<Bit>,
}

impl TemplateKey {
    pub(super) fn from_input(input: &[String], extra: usize) -> Option<(Self, Vec<String>)> {
        let input_width = input.len();
        let output_width = input_width.checked_add(extra)?;
        if input_width == 0 || input_width > MAX_WIDTH || output_width > MAX_WIDTH {
            return None;
        }
        // This is the original wire-case admission, including its unchanged
        // eight DISTINCT symbolic-bit bound, not a bound on the word width.
        let arguments = super::super::wire::case_atoms(input.iter())?;
        let pattern = input
            .iter()
            .map(|bit| match bit.as_str() {
                "false" => Some(Bit::False),
                "true" => Some(Bit::True),
                _ => arguments
                    .iter()
                    .position(|arg| arg == bit)
                    .map(Bit::Variable),
            })
            .collect::<Option<Vec<_>>>()?;
        Some((
            Self {
                input_width,
                output_width,
                extra,
                support: arguments.len(),
                pattern,
            },
            arguments,
        ))
    }

    pub(super) fn bits(&self, arguments: &[String]) -> Option<Vec<String>> {
        if arguments.len() != self.support {
            return None;
        }
        self.pattern
            .iter()
            .map(|bit| match bit {
                Bit::False => Some("false".into()),
                Bit::True => Some("true".into()),
                Bit::Variable(index) => arguments.get(*index).cloned(),
            })
            .collect()
    }
}

#[derive(Clone)]
pub(super) struct Universal {
    key: TemplateKey,
    scope: Rc<()>,
    formula: String,
    pub(super) unit: String,
}

fn prove(proof: &mut PackedProof<'_, '_>, key: &TemplateKey, scope: Rc<()>) -> Option<Universal> {
    if key.support == 0 {
        return None;
    }
    // Same printer means the SAME work/cancellation state. The child's text
    // base also reserves the parent's current document, not another grant.
    let mut inner = proof.fresh_universal_child()?;
    let parameters = (0..key.support)
        .map(|index| format!("{}argument_{index}", inner.definition_prefix))
        .collect::<Vec<_>>();
    let bindings = format!(
        "({})",
        parameters
            .iter()
            .map(|name| format!("({name} Bool)"))
            .collect::<Vec<_>>()
            .join(" ")
    );
    let bound = inner.fresh();
    let anchor = format!("(anchor :step {bound} :args {bindings})\n");
    inner.text_base_bytes = inner.text_base_bytes.checked_add(anchor.len())?;
    let input = key.bits(&parameters)?;
    let mut output = input.clone();
    output.resize(key.output_width, "false".into());
    let input_word = bbterm(&input);
    let identity = inner.equality(&input_word, &input_word, "refl", &[])?;
    let source = Value {
        bits: input,
        equality: identity,
    };
    let operation = format!("(_ zero_extend {})", key.extra);
    let mapped = inner.wire_operation(&operation, source, None, output)?;
    let body = format!("(= {} {})", mapped.equality.left, mapped.equality.right);
    let fact = format!("(= {body} true)");
    let simple = inner.equality(&fact, &body, "equiv_simplify", &[])?;
    let reversed = inner.equality(&body, &fact, "symm", &[&simple.step])?;
    inner.transport_unit(&reversed, &mapped.equality.step)?;
    let formula = format!("(forall {bindings} {body})");
    let quantified_true = format!("(forall {bindings} true)");
    // bind closes all parameters and all definitions that mention them.
    inner.named_step(
        &bound,
        &format!("(= {formula} {quantified_true})"),
        "bind",
        &[],
        "",
    )?;
    let simple = inner.equality(&quantified_true, "true", "qnt_rm_unused", &[])?;
    let equality = inner.equality(&formula, "true", "trans", &[&bound, &simple.step])?;
    let reversed = inner.equality("true", &formula, "symm", &[&equality.step])?;
    let yes = inner.step("true", "true", &[])?;
    let unit = inner.transport_unit(&reversed, &yes)?;
    // The generic child inlines terms rather than creating nullary aliases
    // with free parameters. Only this closed theorem escapes the bind scope.
    proof.append(&anchor)?;
    proof.append(&inner.definitions)?;
    proof.append(&inner.out)?;
    // Appending pays again for retained copies; no spent work is refunded.
    Some(Universal {
        key: key.clone(),
        scope,
        formula,
        unit,
    })
}

impl Circuit<'_, '_, '_> {
    pub(super) fn checked_zero_extend(&mut self, source: Value, extra: usize) -> Option<Value> {
        let (key, arguments) = TemplateKey::from_input(&source.bits, extra)?;
        let operation = format!("(_ zero_extend {extra})");
        let mut output = source.bits.clone();
        output.resize(key.output_width, "false".into());
        if extra == 0 && crate::alethe_printer::dialect::current() == crate::AletheDialect::Clean {
            // The cached theorem's outer Cong would also lose this head in
            // Clean. Transport the actual operand with the same identity
            // lowering used by the closed wire cases, before any cache use.
            return self.proof.wire_operation(&operation, source, None, output);
        }
        if arguments.is_empty() {
            // A closed value needs one evaluate, not an empty forall binder.
            return self.proof.wire_operation(&operation, source, None, output);
        }
        if !self.zero_extend_lemmas.contains_key(&key) {
            let universal = prove(self.proof, &key, self.zero_extend_scope.clone())?;
            // Only a fully closed and committed theorem enters the map.
            self.zero_extend_lemmas.insert(key.clone(), universal);
        }
        // Borrow the closed formula; do not clone a whole lemma per read.
        let universal = self.zero_extend_lemmas.get(&key)?;
        if universal.key != key || !Rc::ptr_eq(&universal.scope, &self.zero_extend_scope) {
            return None;
        }
        let source_word = bbterm(&source.bits);
        let target_word = bbterm(&output);
        if source.equality.right != source_word {
            return None;
        }
        let left = format!("({operation} {source_word})");
        let right = target_word;
        let changed = self.proof.equality(
            &format!("({operation} {})", source.equality.left),
            &left,
            "cong",
            &[&source.equality.step],
        )?;
        let sort = format!("(_ BitVec {})", key.output_width);
        let left_name = self.proof.define_term(&left, &sort)?;
        let right_name = self.proof.define_word(&output)?;
        let instance = format!("(= {left_name} {right_name})");
        let inst = self.proof.fresh();
        self.proof.named_step(
            &inst,
            &format!("(or (not {}) {instance})", universal.formula),
            "forall_inst",
            &[],
            &format!(" :args ({})", arguments.join(" ")),
        )?;
        let expanded = self.proof.step(
            &format!("(not {}) {instance}", universal.formula),
            "or",
            &[&inst],
        )?;
        let unit = self
            .proof
            .step(&instance, "resolution", &[&universal.unit, &expanded])?;
        let mapped = Equality {
            left,
            right,
            step: unit,
        };
        Some(Value {
            equality: self.proof.chain(changed, mapped)?,
            bits: output,
        })
    }
}
