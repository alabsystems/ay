// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed bridges for congruence steps whose authored surface spelling
//! commutes numeric multiplication below an otherwise unchanged application.

use super::authored_assume::EquivalenceDirection;
use super::*;

const MAX_SURFACE_CONG_BRIDGE_STEPS: usize = 64 * 1024;
const MAX_SURFACE_CONG_BRIDGE_OUTPUT_BYTES: usize = 32 * 1024 * 1024;
const MAX_DIAGNOSTIC_CHARS: usize = 256;

struct SurfaceCongruenceApplication {
    left_args: Vec<String>,
    right_args: Vec<String>,
    left_internal_args: Vec<TermId>,
    right_internal_args: Vec<TermId>,
}

struct SurfaceCongruencePremise {
    id: ProofId,
    left: TermId,
    right: TermId,
    printed_left: String,
    printed_right: String,
}

struct SurfacePositionRepair {
    steps: Vec<String>,
    premise: String,
    consumed_premise: Option<usize>,
}

struct SurfacePremiseBridge<'a> {
    id: &'a str,
    target_left: &'a str,
    target_right: &'a str,
    internal_left: TermId,
    internal_right: TermId,
    premise_left: &'a str,
    premise_right: &'a str,
    premise: ProofId,
}

impl AlethePrinter<'_> {
    /// Repair exact Int/Real multiplication commutations below
    /// position-preserving congruence. Every native premise is matched by its
    /// internal endpoints first; surface-only matches never acquire authority.
    pub(super) fn surface_ac_cong_bridge(
        &self,
        id: ProofId,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Result<Option<String>, String> {
        let Some(application) = self.decode_surface_congruence(clause, args)? else {
            return Ok(None);
        };
        let premise_rows = self.surface_congruence_premises(premises)?;
        let mut used = vec![false; premise_rows.len()];
        let mut ordered_premises = Vec::new();
        let mut generated = Vec::new();
        let mut generated_bytes = 0usize;
        let mut bridge_count = 0usize;

        for position in 0..application.left_args.len() {
            if application.left_args[position] == application.right_args[position] {
                continue;
            }
            let bridge_id = format!("{id}.ac{bridge_count}");
            let repair = self.repair_surface_congruence_position(
                position,
                &bridge_id,
                &application,
                &premise_rows,
                &used,
            )?;
            if let Some(index) = repair.consumed_premise {
                used[index] = true;
            }
            append_generated_steps(&mut generated, &mut generated_bytes, repair.steps)?;
            ordered_premises.push(repair.premise);
            bridge_count += 1;
        }
        if used.iter().any(|used| !used) {
            return Err(
                "surface congruence carries a premise unused by its printed arguments".to_string(),
            );
        }
        if generated.is_empty() {
            return Ok(None);
        }
        let mut output = generated.join("\n");
        output.push('\n');
        let _ = std::fmt::Write::write_fmt(
            &mut output,
            format_args!(
                "(step {id} {} :rule cong :premises ({}))",
                self.format_clause(clause),
                ordered_premises.join(" ")
            ),
        );
        Ok(Some(output))
    }

    fn decode_surface_congruence(
        &self,
        clause: &[TermId],
        args: &[TermId],
    ) -> Result<Option<SurfaceCongruenceApplication>, String> {
        if self.term_overrides.is_none() || !args.is_empty() {
            return Ok(None);
        }
        let [conclusion] = clause else {
            return Ok(None);
        };
        let TermData::App(Symbol::Named(equality), equality_args) = self.terms.get(*conclusion)
        else {
            return Ok(None);
        };
        let [left, right] = equality_args.as_slice() else {
            return Ok(None);
        };
        let (
            TermData::App(left_symbol, left_internal_args),
            TermData::App(right_symbol, right_internal_args),
        ) = (self.terms.get(*left), self.terms.get(*right))
        else {
            return Ok(None);
        };
        if equality != "="
            || left_symbol != right_symbol
            || left_internal_args.len() != right_internal_args.len()
        {
            return Ok(None);
        }
        let operator = Self::format_symbol(left_symbol);
        let Some(left_args) = split_application(&self.format_term(*left), &operator) else {
            return Ok(None);
        };
        let Some(right_args) = split_application(&self.format_term(*right), &operator) else {
            return Ok(None);
        };
        if left_args.len() != right_args.len() || left_args.len() != left_internal_args.len() {
            return Err("surface congruence changed the certified application arity".to_string());
        }
        Ok(Some(SurfaceCongruenceApplication {
            left_args,
            right_args,
            left_internal_args: left_internal_args.clone(),
            right_internal_args: right_internal_args.clone(),
        }))
    }

    fn surface_congruence_premises(
        &self,
        premises: &[ProofId],
    ) -> Result<Vec<SurfaceCongruencePremise>, String> {
        let clauses = self.proof_clauses.borrow();
        let mut rows = Vec::with_capacity(premises.len());
        for &id in premises {
            let Some([literal]) = clauses.get(&id).map(Vec::as_slice) else {
                return Err("surface congruence premise is not a unit equality".to_string());
            };
            let TermData::App(Symbol::Named(equality), internal_args) = self.terms.get(*literal)
            else {
                return Err("surface congruence premise is not an internal equality".to_string());
            };
            let [left, right] = internal_args.as_slice() else {
                return Err("surface congruence premise has non-binary equality arity".to_string());
            };
            if equality != "=" {
                return Err("surface congruence premise is not an internal equality".to_string());
            }
            let printed = self.format_term(*literal);
            let Some([printed_left, printed_right]) = split_application(&printed, "=")
                .and_then(|parts| <[String; 2]>::try_from(parts).ok())
            else {
                return Err("surface congruence premise is not a printed equality".to_string());
            };
            rows.push(SurfaceCongruencePremise {
                id,
                left: *left,
                right: *right,
                printed_left,
                printed_right,
            });
        }
        Ok(rows)
    }

    fn repair_surface_congruence_position(
        &self,
        position: usize,
        bridge_id: &str,
        application: &SurfaceCongruenceApplication,
        premises: &[SurfaceCongruencePremise],
        used: &[bool],
    ) -> Result<SurfacePositionRepair, String> {
        let left = application.left_internal_args[position];
        let right = application.right_internal_args[position];
        let left_surface = &application.left_args[position];
        let right_surface = &application.right_args[position];
        if left == right {
            // Different SMT-LIB spellings of the same bit-vector literal are
            // parsed as the same term. The bounded positional comparator also
            // admits this equivalence below otherwise identical applications;
            // make that identity explicit with `refl` before using it as a
            // congruence premise. Changed values, widths, heads, or argument
            // positions still fall through to the existing narrow repair.
            if surface_literal::equal_modulo_bitvec_literal_spelling(left_surface, right_surface) {
                return Ok(SurfacePositionRepair {
                    steps: vec![format!(
                        "(step {bridge_id} (cl (= {left_surface} {right_surface})) :rule refl)"
                    )],
                    premise: bridge_id.to_string(),
                    consumed_premise: None,
                });
            }
            let steps = self.multiplication_surface_pair_steps(
                bridge_id,
                left_surface,
                right_surface,
                left,
            )?;
            return Ok(SurfacePositionRepair {
                steps,
                premise: bridge_id.to_string(),
                consumed_premise: None,
            });
        }

        let Some((index, premise, premise_left, premise_right)) =
            premises.iter().enumerate().find_map(|(index, premise)| {
                if used[index] {
                    return None;
                }
                if premise.left == left && premise.right == right {
                    Some((
                        index,
                        premise,
                        &premise.printed_left,
                        &premise.printed_right,
                    ))
                } else if premise.left == right && premise.right == left {
                    Some((
                        index,
                        premise,
                        &premise.printed_right,
                        &premise.printed_left,
                    ))
                } else {
                    None
                }
            })
        else {
            return Err(format!(
                "printed argument {position} differs internally without a matching certified premise"
            ));
        };
        if left_surface == premise_left && right_surface == premise_right {
            return Ok(SurfacePositionRepair {
                steps: Vec::new(),
                premise: premise.id.to_string(),
                consumed_premise: Some(index),
            });
        }
        let steps = self.bridge_surface_premise_spelling(&SurfacePremiseBridge {
            id: bridge_id,
            target_left: left_surface,
            target_right: right_surface,
            internal_left: left,
            internal_right: right,
            premise_left,
            premise_right,
            premise: premise.id,
        })?;
        Ok(SurfacePositionRepair {
            steps,
            premise: bridge_id.to_string(),
            consumed_premise: Some(index),
        })
    }

    fn bridge_surface_premise_spelling(
        &self,
        bridge: &SurfacePremiseBridge<'_>,
    ) -> Result<Vec<String>, String> {
        let mut output = Vec::new();
        let mut chain = Vec::new();
        if bridge.target_left != bridge.premise_left {
            let left_id = format!("{}.l", bridge.id);
            output.extend(self.multiplication_surface_pair_steps(
                &left_id,
                bridge.target_left,
                bridge.premise_left,
                bridge.internal_left,
            )?);
            chain.push(left_id);
        }
        chain.push(bridge.premise.to_string());
        if bridge.premise_right != bridge.target_right {
            let right_id = format!("{}.r", bridge.id);
            output.extend(self.multiplication_surface_pair_steps(
                &right_id,
                bridge.premise_right,
                bridge.target_right,
                bridge.internal_right,
            )?);
            chain.push(right_id);
        }
        output.push(format!(
            "(step {} (cl (= {} {})) :rule trans :premises ({}))",
            bridge.id,
            bridge.target_left,
            bridge.target_right,
            chain.join(" ")
        ));
        Ok(output)
    }

    fn multiplication_surface_pair_steps(
        &self,
        id: &str,
        left: &str,
        right: &str,
        canonical_term: TermId,
    ) -> Result<Vec<String>, String> {
        if left == right {
            return Ok(Vec::new());
        }
        let canonical = crate::render_term_canonical(self.terms, canonical_term);
        let steps = if right == canonical {
            self.format_nested_multiplication_surface_equivalence(
                id,
                left,
                canonical_term,
                EquivalenceDirection::SurfaceToCanonical,
            )
        } else if left == canonical {
            self.format_nested_multiplication_surface_equivalence(
                id,
                right,
                canonical_term,
                EquivalenceDirection::CanonicalToSurface,
            )
        } else {
            self.bridge_two_noncanonical_multiplication_surfaces(id, left, right, canonical_term)
        };
        steps.ok_or_else(|| unsupported_surface_pair_reason(left, right, &canonical))
    }

    fn bridge_two_noncanonical_multiplication_surfaces(
        &self,
        id: &str,
        left: &str,
        right: &str,
        canonical_term: TermId,
    ) -> Option<Vec<String>> {
        let left_id = format!("{id}.l");
        let right_id = format!("{id}.r");
        let mut output = self.format_nested_multiplication_surface_equivalence(
            &left_id,
            left,
            canonical_term,
            EquivalenceDirection::SurfaceToCanonical,
        )?;
        output.extend(self.format_nested_multiplication_surface_equivalence(
            &right_id,
            right,
            canonical_term,
            EquivalenceDirection::CanonicalToSurface,
        )?);
        output.push(format!(
            "(step {id} (cl (= {left} {right})) :rule trans :premises ({left_id} {right_id}))"
        ));
        Some(output)
    }

    pub(super) fn surface_cong_has_different_order_operators(&self, clause: &[TermId]) -> bool {
        let [conclusion] = clause else {
            return false;
        };
        let Some([left, right]) = split_application(&self.format_term(*conclusion), "=")
            .and_then(|args| <[String; 2]>::try_from(args).ok())
        else {
            return false;
        };
        matches!(
            (
                surface_order_operator(left.as_str()),
                surface_order_operator(right.as_str())
            ),
            (Some(left_op), Some(right_op)) if left_op != right_op
        )
    }

    pub(super) fn surface_cong_has_uncheckable_operands(
        &self,
        clause: &[TermId],
    ) -> Option<String> {
        let [conclusion] = clause else {
            return None;
        };
        let [left, right] = split_application(&self.format_term(*conclusion), "=")
            .and_then(|args| <[String; 2]>::try_from(args).ok())?;
        match (printed_head_symbol(&left), printed_head_symbol(&right)) {
            (Some(left_head), Some(right_head)) if left_head != right_head => Some(format!(
                "surface rewriting gives the two congruence applications different operators ('{left_head}' and '{right_head}')"
            )),
            (Some(_), Some(_)) => None,
            _ => Some(format!(
                "a congruence operand is not a printed application ('{left}' and '{right}'), which no congruence rule can check"
            )),
        }
    }
}

fn append_generated_steps(
    output: &mut Vec<String>,
    output_bytes: &mut usize,
    steps: Vec<String>,
) -> Result<(), String> {
    let Some(next_steps) = output.len().checked_add(steps.len()) else {
        return Err("surface congruence bridge step count overflowed".to_string());
    };
    let step_bytes = steps.iter().try_fold(0usize, |bytes, step| {
        bytes.checked_add(step.len().saturating_add(1))
    });
    let Some(next_bytes) = step_bytes.and_then(|bytes| output_bytes.checked_add(bytes)) else {
        return Err("surface congruence bridge output size overflowed".to_string());
    };
    if next_steps > MAX_SURFACE_CONG_BRIDGE_STEPS
        || next_bytes > MAX_SURFACE_CONG_BRIDGE_OUTPUT_BYTES
    {
        return Err("surface congruence bridge exceeds its aggregate output bound".to_string());
    }
    *output_bytes = next_bytes;
    output.extend(steps);
    Ok(())
}

fn unsupported_surface_pair_reason(left: &str, right: &str, canonical: &str) -> String {
    let left = bounded_surface_diagnostic(left);
    let right = bounded_surface_diagnostic(right);
    let canonical = bounded_surface_diagnostic(canonical);
    format!(
        "printed congruence operands are not position-preserving congruence over exact multiplication commutations; left={left:?}; right={right:?}; canonical={canonical:?}"
    )
}

pub(super) fn bounded_surface_diagnostic(surface: &str) -> String {
    let mut diagnostic: String = surface.chars().take(MAX_DIAGNOSTIC_CHARS).collect();
    if surface.chars().count() > MAX_DIAGNOSTIC_CHARS {
        diagnostic.push_str("...");
    }
    diagnostic
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cong_bridge_aggregate_step_cap_fails_closed() {
        let mut output = Vec::new();
        let mut bytes = 0;
        let steps = vec![String::new(); MAX_SURFACE_CONG_BRIDGE_STEPS + 1];
        assert!(append_generated_steps(&mut output, &mut bytes, steps).is_err());
        assert!(output.is_empty());
    }

    #[test]
    fn test_cong_bridge_aggregate_byte_cap_fails_closed_atomically() {
        let mut output = Vec::new();
        let mut bytes = MAX_SURFACE_CONG_BRIDGE_OUTPUT_BYTES;
        assert!(append_generated_steps(&mut output, &mut bytes, vec![String::new()]).is_err());
        assert!(output.is_empty());
        assert_eq!(bytes, MAX_SURFACE_CONG_BRIDGE_OUTPUT_BYTES);
    }
}
