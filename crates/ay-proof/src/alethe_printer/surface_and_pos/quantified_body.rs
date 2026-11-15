// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An authored quantified conjunct whose BODY elaboration rewrote
//! (#screened-surface-gaps).
//!
//! `(assert (and G (forall ((i S)) (=> (p i) (= (g i) #x01))) ..))`: the root
//! keeps its authored text, while `and_pos` projects the canonical conjunct
//! `(forall ((i_1 S)) (or (= (g i_1) #b00000001) (not (p i_1))))`. The two are
//! not alpha-equivalent, so the projection refused the whole export. MEASURED
//! at 938ec0327: `and_pos indexed conjunct is absent from its effective
//! source`, and the run failed with no certificate at all.
//!
//! The equality is derived with stock pinned-carcara rules only:
//!
//! ```text
//! (step t.qa (cl (not AND) Q) :rule and_pos :args (k))   ; authored conjunct
//! (step t.qr (cl (= Q Q')) :rule refl)                    ; binders respelled
//! (anchor :step t.qb :args ((i_1 S)))
//! ..         (cl (= B' C))                               ; surface schemas
//! (step t.qb (cl (= Q' T)) :rule bind)
//! (step t.qt (cl (= Q T)) :rule trans :premises (t.qr t.qb))
//! equiv_pos2, then two resolutions onto (cl (not AND) T)
//! ```
//!
//! `Q'` is the authored quantifier with its binders spelled as the canonical
//! ones, so `bind` needs no context substitution: carcara's `bind`
//! (`checker/rules/subproof.rs`) asserts the subproof's last step concludes
//! `(= phi phi')` with `phi` and `phi'` IDENTICAL to the two bodies, and that
//! the binders agree outside the anchor's variables. The respelling is textual
//! and is kept only when the bounded comparator that mirrors carcara's
//! `alpha_equiv` confirms `Q` and `Q'`, so a wrong respelling (a capture, a
//! sort named like a binder) declines instead of shipping a failing `refl`.
//! The body derivation is the one confined `assume` / `forall_inst` surfaces
//! already use, over the canonical body the document prints; when no schema
//! relates the two bodies the bridge declines and the caller keeps its
//! refusal.

use super::super::quantifier_surface::{bare_symbol, printed_terms_alpha_equivalent};
use super::super::surface_tokens::split_smt_term_slices_bounded;
use super::{split_alethe_application_bounded, AlethePrintError, AlethePrinter};
use ay_core::{ProofId, TermData, TermId};

/// Byte cap on either printed quantifier this bridge reads.
const MAX_QUANTIFIER_BYTES: usize = 64 * 1024;

impl AlethePrinter<'_> {
    /// `(cl gate target)` for an authored quantifier `source` at `index` of
    /// the gate's conjunction whose canonical projection `target` rewrote the
    /// body, or `None` when the bodies are not related by a checked schema.
    pub(super) fn quantified_body_and_pos_bridge(
        &self,
        id: ProofId,
        selected: TermId,
        index: usize,
        gate: &str,
        source: &str,
        target: &str,
    ) -> Result<Option<String>, AlethePrintError> {
        let bridge = self.quantified_body_bridge(id, selected, source, target);
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(id.0));
        }
        let Some(bridge) = bridge else {
            return Ok(None);
        };
        let output_bound = (bridge.len() as u64)
            .saturating_add((gate.len() as u64).saturating_mul(2))
            .saturating_add((source.len() as u64).saturating_mul(4))
            .saturating_add(1024);
        self.charge(output_bound);
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(id.0));
        }
        Ok(Some(format!(
            "(step {id}.qa (cl {gate} {source}) :rule and_pos :args ({index}))\n\
             {bridge}\n\
             (step {id}.qe (cl (not (= {source} {target})) (not {source}) {target}) :rule equiv_pos2)\n\
             (step {id}.qc (cl (not {source}) {target}) :rule resolution :premises ({id}.qt {id}.qe))\n\
             (step {id} (cl {gate} {target}) :rule resolution :premises ({id}.qa {id}.qc))"
        )))
    }

    /// The commands concluding `(step {id}.qt (cl (= source target)))`.
    fn quantified_body_bridge(
        &self,
        id: ProofId,
        selected: TermId,
        source: &str,
        target: &str,
    ) -> Option<String> {
        let (keyword, body_term) = match self.terms.get(selected) {
            TermData::Forall(_, body, _) => ("forall", *body),
            TermData::Exists(_, body, _) => ("exists", *body),
            _ => return None,
        };
        self.charge((source.len() as u64).saturating_add(target.len() as u64));
        let [source_bindings, source_body] = quantifier_parts(source, keyword)?;
        let [target_bindings, target_body] = quantifier_parts(target, keyword)?;
        // The derivation talks about the canonical body the document prints.
        if self.format_term(body_term) != target_body {
            return None;
        }
        let renames = binder_renames(source_bindings, target_bindings)?;
        let renamed_body = rename_symbols(source_body, &renames)?;
        let renamed = format!("({keyword} {target_bindings} {renamed_body})");
        let respelled = renamed != source;
        if respelled && !printed_terms_alpha_equivalent(source, &renamed) {
            return None;
        }
        let (body_steps, _) = self.printed_surface_equivalence_steps(
            &format!("{id}.qd"),
            &renamed_body,
            body_term,
            target_body,
        )?;
        // `bind` reads the subproof's LAST step, which must state both bodies.
        let closing = format!("(step {id}.qd (cl (= {renamed_body} {target_body})) ");
        if !body_steps
            .last()
            .is_some_and(|step| step.starts_with(&closing))
        {
            return None;
        }
        // Without a respelling the `bind` step itself is `{id}.qt`.
        let bound = if respelled { "qb" } else { "qt" };
        let mut out = String::new();
        if respelled {
            out.push_str(&format!(
                "(step {id}.qr (cl (= {source} {renamed})) :rule refl)\n"
            ));
        }
        out.push_str(&format!(
            "(anchor :step {id}.{bound} :args {target_bindings})\n"
        ));
        for step in &body_steps {
            out.push_str(step);
            out.push('\n');
        }
        out.push_str(&format!(
            "(step {id}.{bound} (cl (= {renamed} {target})) :rule bind)"
        ));
        if respelled {
            out.push_str(&format!(
                "\n(step {id}.qt (cl (= {source} {target})) :rule trans :premises ({id}.qr {id}.qb))"
            ));
        }
        Some(out)
    }
}

/// `[binding list, body]` of a printed `(keyword ((x S) ..) body)`.
fn quantifier_parts<'a>(text: &'a str, keyword: &str) -> Option<[&'a str; 2]> {
    let parts = split_alethe_application_bounded(text, keyword, 2, MAX_QUANTIFIER_BYTES).ok()?;
    let [bindings, body] = parts.as_slice() else {
        return None;
    };
    Some([*bindings, *body])
}

/// `(name, sort)` of each entry of a printed binding list.
fn binding_entries(list: &str) -> Option<Vec<(&str, &str)>> {
    let inner = list.strip_prefix('(')?.strip_suffix(')')?;
    let entries = split_smt_term_slices_bounded(inner, usize::MAX, MAX_QUANTIFIER_BYTES).ok()?;
    entries
        .into_iter()
        .map(|entry| {
            let fields = entry.strip_prefix('(')?.strip_suffix(')')?;
            let fields = split_smt_term_slices_bounded(fields, 2, MAX_QUANTIFIER_BYTES).ok()?;
            let [name, sort] = fields.as_slice() else {
                return None;
            };
            Some((bare_symbol(name), *sort))
        })
        .collect()
}

/// The positional `(authored, canonical)` binder renaming, when both lists
/// bind pairwise-distinct names at byte-identical sorts.
fn binder_renames(source: &str, target: &str) -> Option<Vec<(String, String)>> {
    let source = binding_entries(source)?;
    let target = binding_entries(target)?;
    if source.is_empty() || source.len() != target.len() {
        return None;
    }
    let mut renames: Vec<(String, String)> = Vec::with_capacity(source.len());
    for ((from, from_sort), (to, to_sort)) in source.iter().zip(&target) {
        let repeated = renames
            .iter()
            .any(|(seen_from, seen_to)| seen_from == from || seen_to == to);
        if from_sort != to_sort || repeated {
            return None;
        }
        renames.push(((*from).to_string(), (*to).to_string()));
    }
    Some(renames)
}

/// `text` with every symbol token an entry of `renames` names replaced by its
/// new name, simultaneously. String literals are copied verbatim. `None` on an
/// unterminated string or quoted symbol. The result is only a candidate: the
/// caller keeps it only when the alpha-equivalence comparator confirms it.
fn rename_symbols(text: &str, renames: &[(String, String)]) -> Option<String> {
    let bytes = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut index = 0usize;
    while index < bytes.len() {
        let start = index;
        match bytes[index] {
            b'(' | b')' => index += 1,
            byte if byte.is_ascii_whitespace() => index += 1,
            b'"' => {
                index += 1;
                loop {
                    match bytes.get(index)? {
                        b'"' if bytes.get(index + 1) == Some(&b'"') => index += 2,
                        b'"' => break,
                        _ => index += 1,
                    }
                }
                index += 1;
            }
            _ => {
                if bytes[index] == b'|' {
                    // AY/Z3 quoted-symbol escapes are `\|` and `\\`.
                    index += 1;
                    loop {
                        match bytes.get(index)? {
                            b'\\' => index += 2,
                            b'|' => break,
                            _ => index += 1,
                        }
                    }
                }
                index += 1;
                while index < bytes.len()
                    && !bytes[index].is_ascii_whitespace()
                    && !matches!(bytes[index], b'(' | b')' | b'"' | b'|')
                {
                    index += 1;
                }
                let token = &text[start..index];
                let symbol = bare_symbol(token);
                if let Some((_, to)) = renames.iter().find(|(from, _)| from == symbol) {
                    out.push_str(to);
                    continue;
                }
            }
        }
        out.push_str(&text[start..index]);
    }
    Some(out)
}

/// The flat projection's parsed-literal comparison (`surface_and_pos.rs`),
/// declared here so that file stays within its size ratchet.
#[cfg(test)]
#[path = "respelled_tests.rs"]
mod respelled_tests;
#[cfg(test)]
mod tests;
