// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Polynomial Calculus / GF(2) certificate export for XOR-heavy SAT inputs.

use std::collections::BTreeMap;
use std::io::{self, Write};

use ay_sat::Literal;
use serde_json::{json, Value};

use crate::finder::XorDetection;
use crate::{VarId, XorConstraint, XorFinder};

/// Summary of an emitted Polynomial Calculus / GF(2) certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PcGf2CertificateStats {
    /// Complete CNF parity encodings exported as GF(2) input equations.
    pub detected_xors: usize,
    /// Algebraic derivation steps emitted, including input equations.
    pub algebraic_steps: usize,
    /// Whether the GF(2) row derivation reaches `1 = 0`.
    pub has_contradiction: bool,
    /// Whether ay replayed the emitted row-combination derivation internally.
    pub internally_verified: bool,
}

/// Errors that can occur while emitting a Polynomial Calculus / GF(2) certificate.
#[derive(Debug)]
pub enum PcGf2CertificateError {
    /// I/O failed while writing the certificate artifact.
    Io(io::Error),
    /// JSON serialization failed while materializing the certificate artifact.
    Json(serde_json::Error),
    /// ay's internal row-combination replay rejected the generated derivation.
    Internal(String),
}

impl std::fmt::Display for PcGf2CertificateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(error) => write!(f, "I/O error while writing PC/GF(2) certificate: {error}"),
            Self::Json(error) => {
                write!(f, "JSON error while writing PC/GF(2) certificate: {error}")
            }
            Self::Internal(message) => {
                write!(f, "internal PC/GF(2) certificate replay failed: {message}")
            }
        }
    }
}

impl std::error::Error for PcGf2CertificateError {}

impl From<io::Error> for PcGf2CertificateError {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

impl From<serde_json::Error> for PcGf2CertificateError {
    fn from(error: serde_json::Error) -> Self {
        Self::Json(error)
    }
}

/// Build a Polynomial Calculus / GF(2) certificate as pretty-printed JSON.
///
/// The artifact records:
/// - CNF clause to polynomial translation over GF(2)
/// - complete CNF parity encodings recovered as linear XOR equations
/// - Gauss-Jordan row additions over GF(2)
/// - a final contradiction (`1 = 0`) when the recovered XOR subsystem refutes
///   the input, or a partial/consequence status otherwise
pub fn pc_gf2_certificate_json(
    num_vars: usize,
    clauses: &[Vec<Literal>],
) -> Result<(String, PcGf2CertificateStats), PcGf2CertificateError> {
    let (certificate, stats) = build_certificate(num_vars, clauses)?;
    let mut bytes = Vec::new();
    serde_json::to_writer_pretty(&mut bytes, &certificate)?;
    bytes.push(b'\n');
    let text = String::from_utf8(bytes).map_err(|error| {
        PcGf2CertificateError::Internal(format!("certificate JSON was not UTF-8: {error}"))
    })?;
    Ok((text, stats))
}

/// Write a Polynomial Calculus / GF(2) certificate as pretty-printed JSON.
///
/// This is the production export API for DIMACS proof/artifact integrations.
pub fn write_pc_gf2_certificate<W: Write>(
    writer: &mut W,
    num_vars: usize,
    clauses: &[Vec<Literal>],
) -> Result<PcGf2CertificateStats, PcGf2CertificateError> {
    let (certificate, stats) = build_certificate(num_vars, clauses)?;
    serde_json::to_writer_pretty(&mut *writer, &certificate)?;
    writer.write_all(b"\n")?;
    Ok(stats)
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LinearEquation {
    vars: Vec<VarId>,
    rhs: bool,
}

impl LinearEquation {
    fn from_xor(xor: &XorConstraint) -> Self {
        Self {
            vars: xor.vars.clone(),
            rhs: xor.rhs,
        }
    }

    fn contains(&self, var: VarId) -> bool {
        self.vars.binary_search(&var).is_ok()
    }

    fn xor_with(&self, other: &Self) -> Self {
        let mut vars = Vec::with_capacity(self.vars.len() + other.vars.len());
        let mut lhs = 0usize;
        let mut rhs = 0usize;

        while lhs < self.vars.len() || rhs < other.vars.len() {
            if rhs == other.vars.len()
                || (lhs < self.vars.len() && self.vars[lhs] < other.vars[rhs])
            {
                vars.push(self.vars[lhs]);
                lhs += 1;
            } else if lhs == self.vars.len() || other.vars[rhs] < self.vars[lhs] {
                vars.push(other.vars[rhs]);
                rhs += 1;
            } else {
                lhs += 1;
                rhs += 1;
            }
        }

        Self {
            vars,
            rhs: self.rhs ^ other.rhs,
        }
    }

    fn is_contradiction(&self) -> bool {
        self.vars.is_empty() && self.rhs
    }

    fn polynomial(&self) -> String {
        let mut terms: Vec<String> = self.vars.iter().map(|var| format_var(*var)).collect();
        if self.rhs {
            terms.push("1".to_string());
        }
        let lhs = if terms.is_empty() {
            "0".to_string()
        } else {
            terms.join(" + ")
        };
        format!("{lhs} = 0")
    }

    fn to_json(&self) -> Value {
        let vars: Vec<u32> = self.vars.iter().map(|var| var + 1).collect();
        json!({
            "vars": vars,
            "rhs": self.rhs,
            "field": "GF(2)",
            "polynomial": self.polynomial(),
        })
    }
}

#[derive(Clone, Debug)]
enum DerivationKind {
    InputXor,
    RowAddition,
}

impl DerivationKind {
    fn as_str(&self) -> &'static str {
        match self {
            Self::InputXor => "input_xor",
            Self::RowAddition => "gf2_row_addition",
        }
    }
}

#[derive(Clone, Debug)]
struct DerivationStep {
    id: String,
    kind: DerivationKind,
    premises: Vec<String>,
    equation: LinearEquation,
}

impl DerivationStep {
    fn to_json(&self) -> Value {
        let rule = match self.kind {
            DerivationKind::InputXor => "cnf_parity_encoding_to_linear_polynomial",
            DerivationKind::RowAddition => "polynomial_calculus_linear_combination_gf2",
        };
        json!({
            "id": &self.id,
            "kind": self.kind.as_str(),
            "step_class": "algebraic",
            "rule": rule,
            "premises": &self.premises,
            "equation": self.equation.to_json(),
        })
    }
}

fn build_certificate(
    num_vars: usize,
    clauses: &[Vec<Literal>],
) -> Result<(Value, PcGf2CertificateStats), PcGf2CertificateError> {
    let mut finder = XorFinder::new();
    let detections = finder.find_complete_xors_with_clause_indices(clauses);
    let (steps, contradiction_step, final_equation) = build_derivation(&detections);

    let mut detected_equations = BTreeMap::new();
    for (idx, detection) in detections.iter().enumerate() {
        detected_equations.insert(xor_id(idx), LinearEquation::from_xor(&detection.constraint));
    }
    verify_derivation(&detected_equations, &steps, contradiction_step.as_deref())
        .map_err(PcGf2CertificateError::Internal)?;

    let final_json = build_final_json(
        contradiction_step.as_deref(),
        final_equation.as_ref(),
        steps.last(),
    );
    let has_contradiction = contradiction_step.is_some();
    let readiness_blockers = readiness_blockers(has_contradiction, detections.len());

    let certificate = json!({
        "schema": "ay.pcgf2.certificate.v1",
        "producer": {
            "name": "ay",
            "component": "ay-xor",
            "certificate": "Polynomial Calculus / GF(2)",
        },
        "input": {
            "format": "DIMACS CNF",
            "num_vars": num_vars,
            "num_clauses": clauses.len(),
        },
        "translation": {
            "field": "GF(2)",
            "boolean_axioms": boolean_axioms_json(num_vars),
            "clauses": clauses_json(clauses),
            "clause_encoding": "A clause l1 ... lk maps to product(false(l_i)) = 0 over GF(2).",
        },
        "detected_xors": detections_json(&detections),
        "derivation": steps.iter().map(DerivationStep::to_json).collect::<Vec<_>>(),
        "final": final_json,
        "search": {
            "heuristic_decisions": [],
            "note": "This artifact records only algebraic GF(2) derivation steps; CDCL branching, restarts, and learned-clause heuristics are intentionally outside this certificate.",
        },
        "ay_internal_check": {
            "status": "passed",
            "checked": "input-xor references and GF(2) row-addition replay",
            "proved_contradiction": has_contradiction,
        },
        "readiness": {
            "sat_comp_scope": "UNSAT certificate sidecar for XOR-heavy DIMACS instances",
            "proof_replay_status": "not_yet_integrated",
            "blockers": readiness_blockers,
        }
    });

    let stats = PcGf2CertificateStats {
        detected_xors: detections.len(),
        algebraic_steps: steps.len(),
        has_contradiction,
        internally_verified: true,
    };
    Ok((certificate, stats))
}

fn build_derivation(
    detections: &[XorDetection],
) -> (Vec<DerivationStep>, Option<String>, Option<LinearEquation>) {
    let mut steps = Vec::new();
    let mut rows = Vec::new();

    for (idx, detection) in detections.iter().enumerate() {
        let id = format!("r{}", steps.len() + 1);
        let source = xor_id(idx);
        let equation = LinearEquation::from_xor(&detection.constraint);
        steps.push(DerivationStep {
            id: id.clone(),
            kind: DerivationKind::InputXor,
            premises: vec![source],
            equation: equation.clone(),
        });
        rows.push((equation, id));
    }

    let mut all_vars: Vec<VarId> = rows
        .iter()
        .flat_map(|(equation, _)| equation.vars.iter().copied())
        .collect();
    all_vars.sort_unstable();
    all_vars.dedup();

    let mut pivot_pos = 0usize;
    let mut contradiction_step = None;
    let mut contradiction_equation = None;

    'eliminate: for col in all_vars {
        let Some(pivot_idx) =
            (pivot_pos..rows.len()).find(|row_idx| rows[*row_idx].0.contains(col))
        else {
            continue;
        };
        rows.swap(pivot_idx, pivot_pos);
        let pivot_equation = rows[pivot_pos].0.clone();
        let pivot_step = rows[pivot_pos].1.clone();

        for (row_idx, row) in rows.iter_mut().enumerate() {
            if row_idx == pivot_pos || !row.0.contains(col) {
                continue;
            }

            let lhs_equation = row.0.clone();
            let lhs_step = row.1.clone();
            let derived = lhs_equation.xor_with(&pivot_equation);
            let id = format!("r{}", steps.len() + 1);
            steps.push(DerivationStep {
                id: id.clone(),
                kind: DerivationKind::RowAddition,
                premises: vec![lhs_step, pivot_step.clone()],
                equation: derived.clone(),
            });
            *row = (derived.clone(), id.clone());

            if derived.is_contradiction() {
                contradiction_step = Some(id);
                contradiction_equation = Some(derived);
                break 'eliminate;
            }
        }

        pivot_pos += 1;
    }

    (steps, contradiction_step, contradiction_equation)
}

fn verify_derivation(
    detected_equations: &BTreeMap<String, LinearEquation>,
    steps: &[DerivationStep],
    contradiction_step: Option<&str>,
) -> Result<(), String> {
    let mut step_equations: BTreeMap<String, LinearEquation> = BTreeMap::new();

    for step in steps {
        match step.kind {
            DerivationKind::InputXor => {
                let Some(source) = step.premises.first() else {
                    return Err(format!("{} input step has no source XOR", step.id));
                };
                let Some(source_equation) = detected_equations.get(source) else {
                    return Err(format!(
                        "{} references unknown source XOR {source}",
                        step.id
                    ));
                };
                if source_equation != &step.equation {
                    return Err(format!("{} equation does not match {source}", step.id));
                }
            }
            DerivationKind::RowAddition => {
                if step.premises.len() != 2 {
                    return Err(format!(
                        "{} row-addition step must have 2 premises",
                        step.id
                    ));
                }
                let lhs = step_equations
                    .get(&step.premises[0])
                    .ok_or_else(|| format!("{} has unknown lhs premise", step.id))?;
                let rhs = step_equations
                    .get(&step.premises[1])
                    .ok_or_else(|| format!("{} has unknown rhs premise", step.id))?;
                let expected = lhs.xor_with(rhs);
                if expected != step.equation {
                    return Err(format!("{} equation is not lhs + rhs over GF(2)", step.id));
                }
            }
        }

        step_equations.insert(step.id.clone(), step.equation.clone());
    }

    if let Some(final_step) = contradiction_step {
        let Some(equation) = step_equations.get(final_step) else {
            return Err(format!(
                "final contradiction references unknown step {final_step}"
            ));
        };
        if !equation.is_contradiction() {
            return Err(format!("final step {final_step} is not 1 = 0"));
        }
    }

    Ok(())
}

fn build_final_json(
    contradiction_step: Option<&str>,
    contradiction_equation: Option<&LinearEquation>,
    last_step: Option<&DerivationStep>,
) -> Value {
    if let (Some(step), Some(equation)) = (contradiction_step, contradiction_equation) {
        return json!({
            "kind": "contradiction",
            "step": step,
            "equation": equation.to_json(),
        });
    }

    if let Some(step) = last_step {
        return json!({
            "kind": "consequence",
            "step": &step.id,
            "equation": step.equation.to_json(),
            "note": "The exported GF(2) subsystem did not derive contradiction; this is a partial algebraic consequence certificate.",
        });
    }

    json!({
        "kind": "partial",
        "reason": "No complete CNF parity encodings were detected, so no GF(2) derivation was emitted.",
    })
}

fn boolean_axioms_json(num_vars: usize) -> Vec<Value> {
    (0..num_vars)
        .map(|idx| {
            let var = format_var(idx as VarId);
            json!({
                "var": idx + 1,
                "polynomial": format!("{var}^2 + {var} = 0"),
            })
        })
        .collect()
}

fn clauses_json(clauses: &[Vec<Literal>]) -> Vec<Value> {
    clauses
        .iter()
        .enumerate()
        .map(|(idx, clause)| {
            let literals: Vec<i32> = clause.iter().map(|lit| lit.to_dimacs()).collect();
            let factors: Vec<String> = clause.iter().map(|lit| false_factor(*lit)).collect();
            let polynomial = if factors.is_empty() {
                "1 = 0".to_string()
            } else {
                format!("{} = 0", factors.join(" * "))
            };
            json!({
                "id": idx + 1,
                "literals": literals,
                "false_factors": factors,
                "polynomial": polynomial,
            })
        })
        .collect()
}

fn detections_json(detections: &[XorDetection]) -> Vec<Value> {
    detections
        .iter()
        .enumerate()
        .map(|(idx, detection)| {
            let premise_clause_ids: Vec<usize> = detection
                .clause_indices
                .iter()
                .map(|clause_idx| clause_idx + 1)
                .collect();
            json!({
                "id": xor_id(idx),
                "source": "complete_cnf_parity_encoding",
                "step_class": "algebraic",
                "premise_clause_ids": premise_clause_ids,
                "equation": LinearEquation::from_xor(&detection.constraint).to_json(),
            })
        })
        .collect()
}

fn readiness_blockers(has_contradiction: bool, detected_xors: usize) -> Vec<String> {
    let mut blockers = vec![
        "Lean 4 checker for ay.pcgf2.certificate.v1 JSON is not wired into this repository yet."
            .to_string(),
        "The CNF parity-encoding to linear-polynomial lemma is recorded by clause IDs; the Lean theorem for replaying that translation remains to be implemented."
            .to_string(),
        "Mixed UNSAT proofs that require non-XOR CDCL/LRAT reasoning still need a composition layer between this GF(2) sidecar and DRAT/LRAT certificates."
            .to_string(),
    ];

    if detected_xors == 0 {
        blockers.push(
            "No complete CNF parity encodings were detected in this formula; the artifact is a readiness report only."
                .to_string(),
        );
    } else if !has_contradiction {
        blockers.push(
            "The detected GF(2) subsystem did not derive 1 = 0; the artifact is a partial algebraic consequence certificate."
                .to_string(),
        );
    }

    blockers
}

fn false_factor(lit: Literal) -> String {
    let var = format_var(lit.variable().id());
    if lit.is_positive() {
        format!("(1 + {var})")
    } else {
        var
    }
}

fn format_var(var: VarId) -> String {
    format!("x{}", var + 1)
}

fn xor_id(idx: usize) -> String {
    format!("xor{}", idx + 1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_sat::Variable;

    fn lit(var: u32, positive: bool) -> Literal {
        if positive {
            Literal::positive(Variable::new(var))
        } else {
            Literal::negative(Variable::new(var))
        }
    }

    fn xor2(a: u32, b: u32, rhs: bool) -> Vec<Vec<Literal>> {
        if rhs {
            vec![
                vec![lit(a, true), lit(b, true)],
                vec![lit(a, false), lit(b, false)],
            ]
        } else {
            vec![
                vec![lit(a, true), lit(b, false)],
                vec![lit(a, false), lit(b, true)],
            ]
        }
    }

    #[test]
    fn pc_gf2_certificate_records_nontrivial_contradiction() {
        let mut clauses = Vec::new();
        clauses.extend(xor2(0, 1, true));
        clauses.extend(xor2(1, 2, true));
        clauses.extend(xor2(0, 2, true));

        let (text, stats) = pc_gf2_certificate_json(3, &clauses).expect("emit certificate");
        let json: Value = serde_json::from_str(&text).expect("certificate JSON");

        assert_eq!(stats.detected_xors, 3);
        assert!(stats.has_contradiction);
        assert!(stats.internally_verified);
        assert_eq!(json["schema"], "ay.pcgf2.certificate.v1");
        assert_eq!(json["translation"]["clauses"].as_array().unwrap().len(), 6);
        assert_eq!(
            json["translation"]["clauses"][0]["polynomial"],
            "(1 + x1) * (1 + x2) = 0"
        );
        assert_eq!(json["detected_xors"].as_array().unwrap().len(), 3);
        assert_eq!(json["final"]["kind"], "contradiction");
        assert_eq!(json["ay_internal_check"]["status"], "passed");
        assert!(json["search"]["heuristic_decisions"]
            .as_array()
            .unwrap()
            .is_empty());
        assert!(json["derivation"].as_array().unwrap().iter().any(|step| {
            step["kind"] == "gf2_row_addition" && step["step_class"] == "algebraic"
        }));
    }
}
