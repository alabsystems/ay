// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Surface-safe reconstruction of right-associated implication decomposition.

use super::{split_application, split_binary_implies, AlethePrinter, PRINTED_NESTING_NODE_BUDGET};
use ay_core::{ProofId, Symbol, TermData, TermId};

struct ImplicationSource {
    printed: String,
    disjuncts: Vec<TermId>,
}

struct ImplicationChain {
    links: Vec<(String, String, String)>,
    flattened: Vec<String>,
}

fn canonical_not_eq(literal: &str) -> Option<(String, String)> {
    let operands = split_application(literal, "distinct")?;
    let [a, b] = operands.as_slice() else {
        return None;
    };
    Some((a.clone(), b.clone()))
}

fn canonicalize_not_eq(literal: &str) -> String {
    match canonical_not_eq(literal) {
        Some((a, b)) => format!("(not (= {a} {b}))"),
        None => literal.to_string(),
    }
}

impl AlethePrinter<'_> {
    /// Resugar an `or` decomposition whose single assume premise is an
    /// internal canonical or-term but prints as a right-associated binary
    /// implication chain.
    ///
    /// For `(=> A (=> B C))`, the internal `or` rule concludes
    /// `{(not A), (not B), C}`. The printed premise is not an or-term, so this
    /// rebuilds the clause with `implies_pos` links and n-ary resolution.
    ///
    /// Admission is deliberately syntactic: internal operands, the traced
    /// clause, printed operands, and flattened implication literals must agree
    /// exactly as multisets with equal arity. The final step retains the
    /// original id for downstream references.
    pub(super) fn resugar_implies_decomposition(
        &self,
        id: ProofId,
        clause: &[TermId],
        premise: ProofId,
    ) -> Result<Option<String>, String> {
        let Some(source) = self.implication_source(premise, clause)? else {
            return Ok(None);
        };
        let Some(chain) = Self::decode_implication_chain(&source.printed, source.disjuncts.len())?
        else {
            return Ok(None);
        };
        let printed_clause =
            self.validate_printed_implication(&source.disjuncts, clause, &chain.flattened)?;
        Ok(Some(Self::render_implication_decomposition(
            id,
            premise,
            &chain.links,
            &printed_clause,
        )))
    }

    fn implication_source(
        &self,
        premise: ProofId,
        clause: &[TermId],
    ) -> Result<Option<ImplicationSource>, String> {
        let Some(&source) = self.assume_terms.borrow().get(&premise) else {
            return Ok(None);
        };
        let printed = self.format_term(source);
        if split_binary_implies(&printed).is_none() {
            if split_application(&printed, "=>").is_some() {
                return Err("printed implication premise is not binary".to_string());
            }
            return Ok(None);
        }
        let TermData::App(Symbol::Named(name), disjuncts) = self.terms.get(source) else {
            return Err("printed implication premise is not an internal or-term".to_string());
        };
        if name != "or" || disjuncts.len() < 2 || disjuncts.len() != clause.len() {
            return Err("printed implication/internal or arity mismatch".to_string());
        }
        let mut sorted_source = disjuncts.clone();
        let mut sorted_clause = clause.to_vec();
        sorted_source.sort_unstable();
        sorted_clause.sort_unstable();
        if sorted_source != sorted_clause {
            return Err(
                "or decomposition clause is not the assumed internal disjunct multiset".to_string(),
            );
        }
        Ok(Some(ImplicationSource {
            printed,
            disjuncts: disjuncts.clone(),
        }))
    }

    fn decode_implication_chain(
        source: &str,
        expected_arity: usize,
    ) -> Result<Option<ImplicationChain>, String> {
        let mut implication = source.to_string();
        let mut links = Vec::new();
        let mut flattened = Vec::new();
        while let Some((antecedent, consequent)) = split_binary_implies(&implication) {
            if links.len() >= PRINTED_NESTING_NODE_BUDGET {
                return Err("printed implication nesting exceeds the printer limit".to_string());
            }
            flattened.push(format!("(not {antecedent})"));
            links.push((implication, antecedent, consequent.clone()));
            implication = consequent;
        }
        if links.is_empty() {
            return Ok(None);
        }
        // A non-binary `=>` is malformed, not an atomic final consequent.
        if split_application(&implication, "=>").is_some() {
            return Err("right-nested printed implication contains a non-binary link".to_string());
        }
        flattened.push(implication);
        if flattened.len() != expected_arity {
            return Err("printed implication/internal or arity mismatch".to_string());
        }
        Ok(Some(ImplicationChain { links, flattened }))
    }

    fn validate_printed_implication(
        &self,
        source_disjuncts: &[TermId],
        clause: &[TermId],
        flattened: &[String],
    ) -> Result<Vec<String>, String> {
        // `distinct a b` is AY's authored spelling of `not (= a b)` for the
        // guarded mod-witness antecedent. Compare canonically, then render an
        // explicit `distinct_elim` / `equiv2` bridge below.
        let mut printed_source = source_disjuncts
            .iter()
            .map(|&literal| canonicalize_not_eq(&self.format_term(literal)))
            .collect::<Vec<_>>();
        let printed_clause = clause
            .iter()
            .map(|&literal| self.format_term(literal))
            .collect::<Vec<_>>();
        let mut sorted_clause = printed_clause
            .iter()
            .map(|literal| canonicalize_not_eq(literal))
            .collect::<Vec<_>>();
        let mut sorted_flattened = flattened.to_vec();
        printed_source.sort_unstable();
        sorted_clause.sort_unstable();
        sorted_flattened.sort_unstable();
        if printed_source != sorted_flattened || sorted_clause != sorted_flattened {
            return Err(
                "printed implication literals do not match the internal source and conclusion"
                    .to_string(),
            );
        }
        Ok(printed_clause)
    }

    fn render_implication_decomposition(
        id: ProofId,
        premise: ProofId,
        links: &[(String, String, String)],
        printed_clause: &[String],
    ) -> String {
        let mut out = String::new();
        let mut resolution_premises = vec![premise.to_string()];
        for (index, (current, antecedent, consequent)) in links.iter().enumerate() {
            let implication_id = format!("{id}.imp{index}");
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!(
                    "(step {implication_id} (cl (not {current}) (not {antecedent}) {consequent}) :rule implies_pos)\n"
                ),
            );
            resolution_premises.push(implication_id);
        }

        // Bridge each distinct printed literal once and reuse its premise id.
        let mut bridged: Vec<String> = Vec::new();
        for literal in printed_clause {
            let Some((a, b)) = canonical_not_eq(literal) else {
                continue;
            };
            let index = match bridged.iter().position(|seen| seen == literal) {
                Some(index) => index,
                None => {
                    let index = bridged.len();
                    let _ = std::fmt::Write::write_fmt(
                        &mut out,
                        format_args!(
                            "(step {id}.d{index} (cl (= (distinct {a} {b}) (not (= {a} {b})))) \
                             :rule distinct_elim)\n\
                             (step {id}.q{index} (cl (distinct {a} {b}) (not (not (= {a} {b})))) \
                             :rule equiv2 :premises ({id}.d{index}))\n"
                        ),
                    );
                    bridged.push(literal.clone());
                    index
                }
            };
            resolution_premises.push(format!("{id}.q{index}"));
        }
        let _ = std::fmt::Write::write_fmt(
            &mut out,
            format_args!(
                "(step {id} (cl {}) :rule resolution :premises ({}))",
                printed_clause.join(" "),
                resolution_premises.join(" ")
            ),
        );
        out
    }
}
