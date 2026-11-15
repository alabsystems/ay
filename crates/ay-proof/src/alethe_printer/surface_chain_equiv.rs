// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `equiv_*` tautologies whose source prints as a CHAINABLE `=`.
//!
//! SMT-LIB `=` is `:chainable`: `(= a1 a2 .. an)` means
//! `(and (= a1 a2) .. (= a(n-1) an))`, and elaboration stores exactly that
//! conjunction. The store then folds it. In `(= p q q)` the reflexive link
//! `(= q q)` is `true`, so the stored term is the BINARY `(= p q)`, while the
//! authored-surface override keeps printing that `TermId` as `(= p q q)`,
//! because the `assume` (or the authored assertion the chain sits inside) must
//! quote the problem file. AY's strict checker validates `equiv_pos2` over the
//! binary term it holds; the pinned checker reads the printed one. MEASURED on
//! 938ec0327: `(assert (= p q q)) (assert p) (assert (not q))` published
//! `(step t3 (cl (not (= p q q)) (not p) q) :rule equiv_pos2)` under
//! `unproved_steps=0 trust_free=yes ay_self_checkable=yes`, and carcara 1.1.0
//! answered "term '(not (= p q q))' is of the wrong form, expected
//! '(not (= phi_1 phi_2))'". The same step shipped for `(= q p p)`
//! (`equiv_pos1`), `(= p q q q)`, `(= p q p q)`, `(= p (not q) (not q))`, and
//! for a chain NESTED in an authored `(or (= p q q) r)` / `(and (= p q q) r)`.
//!
//! The nested case is why this is repaired at the USE site and not by
//! confining the authored spelling to the `assume` (the `folded_assume`
//! device): there the chain is printed inside another assertion's authored
//! text, so the override has to stay document-wide and every step that reads
//! the chain's SHAPE has to be judged on the printed text.
//!
//! Two repairs, both judged on the PRINTED text:
//!
//! * [`fixed_shape_operands`]: the surface judge's fixed-shape templates only
//!   instantiate at the operand count the pinned rule's pattern binds. Since
//!   5d0f29dc1 the `equiv_pos2` template read operands 0 and 1 of the
//!   three-operand split, ignored operand 2, reproduced the printed clause,
//!   and answered "the default rendering is exact". The judge is the gate
//!   that exists to catch a printed/stored disagreement; binding a chain as a
//!   pair is how it waved this one through.
//! * [`AlethePrinter::format_chainable_equiv_surface`]: derive the printed
//!   clause instead. `nary_elim` states `(= S (and L0 .. Lm))` for the printed
//!   chain `S` and its links `Lk`; `equiv_pos1`/`equiv_pos2` and resolution
//!   turn that definition into the implication the step needs; and the binary
//!   `equiv_*` rule runs over a LINK, which is a genuine two-operand `=`. Each
//!   emitted step is a rule instance the pinned checker verifies on its own;
//!   a link instance stating `(not (not x))` where the traced clause holds the
//!   stripped `x` (the `(= (not p) q q)` shape) carries a `not_not` bridge.
//!   A clause the chain does not justify finds no link and returns `None`, so
//!   the caller's `NoMatch` declines the export.

use super::{split_application, AlethePrinter};
use ay_core::{AletheRule, ProofId, TermId};
use std::fmt::Write as _;

/// The exact operand count of the pinned checker's pattern for a fixed-shape
/// surface template keyed by `op`, or `None` when `op` has no such template.
///
/// carcara 1.1.0's `match_term!` binds `(= phi_1 phi_2)`, `(xor phi_1 phi_2)`,
/// `(=> phi_1 phi_2)` and `(ite phi_1 phi_2 phi_3)` with SLICE patterns. The
/// chainable `(= p q q)`, the right-associative `(=> p q r)` and the
/// left-associative `(xor p q r)` are therefore not instances of the rules
/// keyed on those operators, even where a template reads only its first two
/// operands.
fn fixed_template_arity(op: &str) -> Option<usize> {
    match op {
        "=" | "=>" | "xor" => Some(2),
        "ite" => Some(3),
        _ => None,
    }
}

/// The printed operands of `source` when it applies `op` at EXACTLY the
/// arity of the pinned rule's pattern; `None` otherwise, which leaves the
/// surface judge's fixed-shape templates for `op` without a candidate. An
/// operator with no fixed-shape template yields nothing (fail closed).
pub(super) fn fixed_shape_operands(source: &str, op: &str) -> Option<Vec<String>> {
    let arity = fixed_template_arity(op)?;
    split_application(source, op).filter(|operands| operands.len() == arity)
}

/// One binary `equiv_*` spec instance over a chain link.
struct LinkInstance {
    /// `(cl ..) :rule ..` exactly as the pinned rule states it.
    step: String,
    /// The link literal the instance states: `L` or `(not L)`.
    link_lit: String,
    /// The two operand literals it states beside the link.
    spec: [String; 2],
}

/// The binary `equiv_*` spec instances over the link `(= u v)`. The rule
/// names are fixed text, so the wire-rule inventory reads them.
fn link_instances(positive_source: bool, u: &str, v: &str) -> [LinkInstance; 2] {
    let link = format!("(= {u} {v})");
    let (nu, nv) = (format!("(not {u})"), format!("(not {v})"));
    let instance = |step: String, link_lit: &str, spec: [&str; 2]| LinkInstance {
        step,
        link_lit: link_lit.to_string(),
        spec: spec.map(str::to_string),
    };
    if positive_source {
        [
            instance(
                format!("(cl {link} {nu} {nv}) :rule equiv_neg1"),
                &link,
                [&nu, &nv],
            ),
            instance(
                format!("(cl {link} {u} {v}) :rule equiv_neg2"),
                &link,
                [u, v],
            ),
        ]
    } else {
        let not_link = format!("(not {link})");
        [
            instance(
                format!("(cl {not_link} {u} {nv}) :rule equiv_pos1"),
                &not_link,
                [u, &nv],
            ),
            instance(
                format!("(cl {not_link} {nu} {v}) :rule equiv_pos2"),
                &not_link,
                [&nu, v],
            ),
        ]
    }
}

/// `x` when `lit` is `(not (not x))`, read off balanced printed operands.
fn double_negation_inner(lit: &str) -> Option<&str> {
    let [once] = <[String; 1]>::try_from(split_application(lit, "not")?).ok()?;
    let [twice] = <[String; 1]>::try_from(split_application(&once, "not")?).ok()?;
    let inner = lit.strip_prefix("(not (not ")?.strip_suffix("))")?;
    (inner == twice).then_some(inner)
}

/// Match an instance's two operand literals against the printed clause's two
/// operand literals as a multiset. A spec literal `(not (not x))` matches a
/// printed `x` (the traced clause is double-negation stripped) and is returned
/// for a `not_not` bridge. Exact matches are preferred.
fn match_operands<'s>(spec: &'s [String; 2], printed: [&str; 2]) -> Option<Vec<&'s str>> {
    let mut best: Option<Vec<&'s str>> = None;
    for (first, second) in [(0, 1), (1, 0)] {
        let mut stripped = Vec::new();
        let ok = [(first, printed[0]), (second, printed[1])]
            .into_iter()
            .all(|(i, lit)| {
                if spec[i] == lit {
                    return true;
                }
                if double_negation_inner(&spec[i]) == Some(lit) {
                    stripped.push(spec[i].as_str());
                    return true;
                }
                false
            });
        if ok && best.as_ref().is_none_or(|b| stripped.len() < b.len()) {
            best = Some(stripped);
        }
    }
    best
}

/// One chain link's binary step, rendered under `name`: the spec instance and,
/// for each stripped literal, a `not_not` bridge and a resolution that
/// restores the printed literals.
fn link_step(name: &str, instance: &LinkInstance, printed: [&str; 2], stripped: &[&str]) -> String {
    if stripped.is_empty() {
        return format!("(step {name} {})\n", instance.step);
    }
    let mut out = format!("(step {name}.s {})\n", instance.step);
    let mut premises = format!("{name}.s");
    for (j, lit) in stripped.iter().enumerate() {
        let inner = double_negation_inner(lit).unwrap_or(lit);
        let _ = writeln!(
            out,
            "(step {name}.n{j} (cl (not {lit}) {inner}) :rule not_not)"
        );
        let _ = write!(premises, " {name}.n{j}");
    }
    let _ = writeln!(
        out,
        "(step {name} (cl {} {} {}) :rule resolution :premises ({premises}))",
        instance.link_lit, printed[0], printed[1]
    );
    out
}

impl AlethePrinter<'_> {
    /// Checked derivation of a premise-free `equiv_*` step whose source term
    /// prints as the chainable `(= a1 .. an)`, `n >= 3`. `None` when the rule
    /// is outside the family, the source is not such a chain, or no chain link
    /// reproduces the printed operand literals.
    ///
    /// `equiv_pos1`/`equiv_pos2` (source negated) need `S => (lit1 or lit2)`:
    /// ONE non-reflexive link whose binary instance states exactly those two
    /// literals, projected off the definition by `and_pos`.
    ///
    /// `equiv_neg1`/`equiv_neg2` (source positive) need
    /// `(not lit1) and (not lit2) => S`: EVERY link must follow, a reflexive
    /// one by `eq_reflexive` and every other by a binary instance stating the
    /// same two literals, and `and_neg` recombines them into the definition.
    pub(super) fn format_chainable_equiv_surface(
        &self,
        id: ProofId,
        rule: &AletheRule,
        clause: &[TermId],
        source_str: &str,
    ) -> Option<String> {
        let positive_source = match rule {
            AletheRule::EquivPos1 | AletheRule::EquivPos2 => false,
            AletheRule::EquivNeg1 | AletheRule::EquivNeg2 => true,
            _ => return None,
        };
        let chain = split_application(source_str, "=")?;
        if chain.len() < 3 || clause.len() != 3 {
            return None;
        }
        // The literals exactly as `format_clause` prints them: the link steps
        // restate these strings and the final resolution concludes
        // `format_clause(clause)`, so both must read the same text.
        let printed = self.format_derived_clause_literals(clause);
        let source_lit = if positive_source {
            source_str.to_string()
        } else {
            format!("(not {source_str})")
        };
        let at = printed.iter().position(|lit| *lit == source_lit)?;
        let others: Vec<&str> = (0..3)
            .filter(|&i| i != at)
            .map(|i| printed[i].as_str())
            .collect();
        let operands = [others[0], others[1]];

        let links: Vec<String> = chain
            .windows(2)
            .map(|pair| format!("(= {} {})", pair[0], pair[1]))
            .collect();
        // The rendering quotes the link list a bounded number of times.
        let link_bytes: usize = links.iter().map(String::len).sum();
        let work = link_bytes
            .saturating_add(source_str.len())
            .saturating_mul(8);
        self.charge(work as u64);
        if self.work_budget_exhausted() {
            return None;
        }
        // The binary step over link `k` that states exactly `operands`.
        let link_derivation = |k: usize, name: &str| -> Option<String> {
            link_instances(positive_source, &chain[k], &chain[k + 1])
                .iter()
                .find_map(|instance| {
                    let stripped = match_operands(&instance.spec, operands)?;
                    Some(link_step(name, instance, operands, &stripped))
                })
        };

        let conjunction = format!("(and {})", links.join(" "));
        let definition = format!("(= {source_str} {conjunction})");
        let mut out = format!("(step {id}.nary (cl {definition}) :rule nary_elim)\n");
        let mut premises = format!("{id}.chain");
        if positive_source {
            let negated_links: Vec<String> = links.iter().map(|l| format!("(not {l})")).collect();
            let _ = writeln!(
                out,
                "(step {id}.fold (cl (not {definition}) {source_str} (not {conjunction})) :rule equiv_pos1)\n\
                 (step {id}.chain (cl {source_str} (not {conjunction})) :rule resolution :premises ({id}.nary {id}.fold))\n\
                 (step {id}.links (cl {conjunction} {}) :rule and_neg)",
                negated_links.join(" ")
            );
            let _ = write!(premises, " {id}.links");
            for (k, link) in links.iter().enumerate() {
                let name = format!("{id}.link{k}");
                if chain[k] == chain[k + 1] {
                    let _ = writeln!(out, "(step {name} (cl {link}) :rule eq_reflexive)");
                } else {
                    out.push_str(&link_derivation(k, &name)?);
                }
                let _ = write!(premises, " {name}");
            }
        } else {
            let (k, bin) = (0..links.len())
                .filter(|&k| chain[k] != chain[k + 1])
                .find_map(|k| link_derivation(k, &format!("{id}.bin")).map(|bin| (k, bin)))?;
            let _ = write!(
                out,
                "(step {id}.unfold (cl (not {definition}) (not {source_str}) {conjunction}) :rule equiv_pos2)\n\
                 (step {id}.chain (cl (not {source_str}) {conjunction}) :rule resolution :premises ({id}.nary {id}.unfold))\n\
                 (step {id}.link (cl (not {conjunction}) {}) :rule and_pos :args ({k}))\n{bin}",
                links[k]
            );
            let _ = write!(premises, " {id}.link {id}.bin");
        }
        let _ = write!(
            out,
            "(step {id} {} :rule resolution :premises ({premises}))",
            self.format_clause(clause)
        );
        Some(out)
    }
}

#[cfg(test)]
mod tests;
