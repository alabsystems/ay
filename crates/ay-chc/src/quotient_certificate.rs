// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fail-closed recursive-LIA quotient certificate checks.
//!
//! This is the initial quotient-certificate checker surface: it intentionally validates only an
//! identity finite quotient for linear recursive Int CHCs. Wider quotient maps
//! can be added only after their lift and replay obligations become executable.

use std::collections::{BTreeMap, BTreeSet};

use ay_core::kani_compat::DetHashSet as HashSet;
use serde_json::Value;

use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ClauseHead, PredicateId};

/// Payload schema tag for quotient-compression certificates.
pub const CHC_QUOTIENT_CERTIFICATE_SCHEMA: &str = "quotient-certificate-v1";

/// Namespaced checker schema for reports and future replay bindings.
pub const CHC_QUOTIENT_CHECKER_SCHEMA: &str = "ay.chc.quotient-certificate/v1";

const REQUIRED_SAFE_OBLIGATIONS: &[&str] = &[
    "quotient-map-total",
    "lift-total",
    "boundary-witness",
    "trace-equivalence",
    "energy-descent",
    "safety-preservation",
];

const REQUIRED_UNSAFE_OBLIGATIONS: &[&str] = &[
    "quotient-map-total",
    "lift-total",
    "boundary-witness",
    "trace-equivalence",
    "energy-descent",
    "counterexample-lift",
];

/// Verdict returned by the quotient checker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuotientCheckVerdict {
    StructurallyValid,
    Rejected,
}

impl QuotientCheckVerdict {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::StructurallyValid => "structurally-valid",
            Self::Rejected => "rejected",
        }
    }
}

/// Machine-readable summary of a quotient certificate replay attempt.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct QuotientCheckReport {
    pub schema: &'static str,
    pub schema_version: u64,
    pub verdict: QuotientCheckVerdict,
    pub problem_sha256: String,
    pub certificate_schema: Option<String>,
    pub certificate_result: Option<String>,
    pub quotient_nodes: usize,
    pub quotient_edges: usize,
    pub obligations_checked: usize,
    pub reject_reasons: Vec<String>,
}

impl QuotientCheckReport {
    fn rejected(problem: &ChcProblem, reasons: Vec<String>) -> Self {
        Self {
            schema: "ay.chc.quotient-certificate-check/v1",
            schema_version: 1,
            verdict: QuotientCheckVerdict::Rejected,
            problem_sha256: problem.normalized_input_sha256(),
            certificate_schema: None,
            certificate_result: None,
            quotient_nodes: 0,
            quotient_edges: 0,
            obligations_checked: 0,
            reject_reasons: reasons,
        }
    }

    pub fn structurally_valid(&self) -> bool {
        self.verdict == QuotientCheckVerdict::StructurallyValid
    }

    /// Proof acceptance is deliberately unavailable in this v1 scaffold.
    ///
    /// A structurally valid quotient certificate is not a trusted proof until a
    /// replay checker recomputes the lift, boundary, trace, and energy
    /// obligations against the original CHC problem.
    pub fn accepted(&self) -> bool {
        false
    }

    pub fn to_json_value(&self) -> Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": self.schema_version,
            "verdict": self.verdict.as_str(),
            "structurally_valid": self.structurally_valid(),
            "accepted": self.accepted(),
            "promotion_allowed": false,
            "trusted_replay": "not_implemented",
            "problem_sha256": self.problem_sha256,
            "certificate_schema": self.certificate_schema,
            "certificate_result": self.certificate_result,
            "quotient_nodes": self.quotient_nodes,
            "quotient_edges": self.quotient_edges,
            "obligations_checked": self.obligations_checked,
            "reject_reasons": self.reject_reasons,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct QuotientNode {
    id: String,
    predicate: PredicateId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct QuotientEdge {
    clause_index: usize,
    source: String,
    target: String,
    energy_before: u64,
    energy_after: u64,
}

/// Check a `ay.chc.quotient-certificate/v1` JSON certificate against a CHC problem.
///
/// The checker is fail-closed: malformed JSON, unsupported quotient kinds,
/// unchecked obligations, non-recursive structure, and non-LIA syntax all return
/// a rejected report rather than a partial success. A structurally valid report
/// is still not a proof acceptance until a trusted replay checker is available.
pub fn check_recursive_lia_quotient_certificate(
    problem: &ChcProblem,
    certificate_json: &str,
) -> QuotientCheckReport {
    let value: Value = match serde_json::from_str(certificate_json) {
        Ok(value) => value,
        Err(err) => {
            return QuotientCheckReport::rejected(
                problem,
                vec![format!("certificate JSON parse failed: {err}")],
            );
        }
    };
    check_recursive_lia_quotient_value(problem, &value)
}

/// Check a parsed quotient certificate JSON value against a CHC problem.
pub fn check_recursive_lia_quotient_value(
    problem: &ChcProblem,
    value: &Value,
) -> QuotientCheckReport {
    let mut reasons = Vec::new();
    let object = match value.as_object() {
        Some(object) => object,
        None => {
            return QuotientCheckReport::rejected(
                problem,
                vec!["certificate root must be an object".to_string()],
            );
        }
    };

    if is_artifact_certificate_shape(object) {
        return check_recursive_lia_quotient_artifact_object(problem, object);
    }

    expect_string_field(
        object.get("schema"),
        CHC_QUOTIENT_CERTIFICATE_SCHEMA,
        "schema",
        &mut reasons,
    );
    expect_u64_field(
        object.get("schema_version"),
        1,
        "schema_version",
        &mut reasons,
    );
    expect_string_field(
        object.get("target_logic"),
        "recursive-lia",
        "target_logic",
        &mut reasons,
    );

    let result = string_field(object.get("result"), "result", &mut reasons);
    match result.as_deref() {
        Some("safe") | Some("unsafe") => {}
        Some(other) => reasons.push(format!("result={other:?} is unsupported")),
        None => {}
    }

    match string_field(object.get("problem_sha256"), "problem_sha256", &mut reasons) {
        Some(hash) if hash == problem.normalized_input_sha256() => {}
        Some(hash) => reasons.push(format!(
            "problem_sha256={hash} does not match normalized input {}",
            problem.normalized_input_sha256()
        )),
        None => {}
    }

    check_problem_is_recursive_lia(problem, &mut reasons);

    let nodes = parse_nodes(problem, object.get("quotient"), &mut reasons);
    let edges = parse_edges(object.get("quotient"), &mut reasons);
    check_identity_nodes_cover_predicates(problem, &nodes, &mut reasons);
    check_edges_cover_clauses(problem, &nodes, &edges, &mut reasons);
    check_auxiliary_certificate_sections(problem, object, result.as_deref(), &mut reasons);

    let obligations_checked =
        check_obligations(object.get("obligations"), result.as_deref(), &mut reasons);
    let verdict = if reasons.is_empty() {
        QuotientCheckVerdict::StructurallyValid
    } else {
        QuotientCheckVerdict::Rejected
    };

    QuotientCheckReport {
        schema: "ay.chc.quotient-certificate-check/v1",
        schema_version: 1,
        verdict,
        problem_sha256: problem.normalized_input_sha256(),
        certificate_schema: object
            .get("schema")
            .and_then(Value::as_str)
            .map(ToOwned::to_owned),
        certificate_result: result,
        quotient_nodes: nodes.len(),
        quotient_edges: edges.len(),
        obligations_checked,
        reject_reasons: reasons,
    }
}

/// Check the checked-in quotient-certificate artifact shape without enabling proof promotion.
pub fn check_recursive_lia_quotient_artifact_value(
    problem: &ChcProblem,
    value: &Value,
) -> QuotientCheckReport {
    let object = match value.as_object() {
        Some(object) => object,
        None => {
            return QuotientCheckReport::rejected(
                problem,
                vec!["certificate root must be an object".to_string()],
            );
        }
    };
    check_recursive_lia_quotient_artifact_object(problem, object)
}

fn is_artifact_certificate_shape(object: &serde_json::Map<String, Value>) -> bool {
    object.contains_key("artifact")
        || object.contains_key("derivation_dag")
        || object.contains_key("boundary_witness")
        || object.contains_key("trace_certificate")
        || object.contains_key("replay")
}

fn check_recursive_lia_quotient_artifact_object(
    problem: &ChcProblem,
    object: &serde_json::Map<String, Value>,
) -> QuotientCheckReport {
    let mut reasons = Vec::new();
    expect_string_field(
        object.get("schema"),
        CHC_QUOTIENT_CERTIFICATE_SCHEMA,
        "schema",
        &mut reasons,
    );

    check_problem_is_recursive_lia(problem, &mut reasons);
    check_artifact_envelope(object.get("artifact"), &mut reasons);
    let result = check_artifact_problem_binding(problem, object.get("problem"), &mut reasons);
    let class_ids = check_artifact_quotient(problem, object.get("quotient"), &mut reasons);
    check_artifact_lift_and_concretization(object, &class_ids, &mut reasons);
    let dag = check_artifact_derivation_dag(
        object.get("derivation_dag"),
        &class_ids,
        object.get("problem"),
        &mut reasons,
    );
    check_artifact_boundary_witness(object.get("boundary_witness"), &mut reasons);
    check_artifact_trace_certificate(object.get("trace_certificate"), &dag.node_ids, &mut reasons);
    check_artifact_proof_energy(object.get("proof_energy"), &mut reasons);
    let obligations_checked = check_artifact_replay(object.get("replay"), &mut reasons);

    let verdict = if reasons.is_empty() {
        QuotientCheckVerdict::StructurallyValid
    } else {
        QuotientCheckVerdict::Rejected
    };

    QuotientCheckReport {
        schema: "ay.chc.quotient-certificate-check/v1",
        schema_version: 1,
        verdict,
        problem_sha256: problem.normalized_input_sha256(),
        certificate_schema: object
            .get("schema")
            .and_then(Value::as_str)
            .map(ToOwned::to_owned),
        certificate_result: result,
        quotient_nodes: class_ids.len(),
        quotient_edges: dag.edge_count,
        obligations_checked,
        reject_reasons: reasons,
    }
}

#[derive(Debug, Default)]
struct ArtifactDagSummary {
    node_ids: BTreeSet<String>,
    edge_count: usize,
}

fn check_artifact_envelope(value: Option<&Value>, reasons: &mut Vec<String>) {
    let Some(object) = value.and_then(Value::as_object) else {
        reasons.push("artifact object is missing".to_string());
        return;
    };
    expect_string_field(
        object.get("envelope_schema"),
        "proof-artifact-v1",
        "artifact.envelope_schema",
        reasons,
    );
    expect_string_field(
        object.get("payload_schema"),
        CHC_QUOTIENT_CERTIFICATE_SCHEMA,
        "artifact.payload_schema",
        reasons,
    );
    string_field(object.get("artifact_id"), "artifact.artifact_id", reasons);
}

fn check_artifact_problem_binding(
    problem: &ChcProblem,
    value: Option<&Value>,
    reasons: &mut Vec<String>,
) -> Option<String> {
    let Some(object) = value.and_then(Value::as_object) else {
        reasons.push("problem object is missing".to_string());
        return None;
    };
    expect_string_field(
        object.get("logic"),
        "recursive-lia-chc",
        "problem.logic",
        reasons,
    );
    if let Some(scope) = object.get("scope").and_then(Value::as_object) {
        expect_bool_field(
            scope.get("recursive"),
            true,
            "problem.scope.recursive",
            reasons,
        );
        expect_bool_field(
            scope.get("linear_integer_arithmetic"),
            true,
            "problem.scope.linear_integer_arithmetic",
            reasons,
        );
        for key in ["arrays", "adts", "bitvectors", "nonlinear_arithmetic"] {
            expect_bool_field(
                scope.get(key),
                false,
                &format!("problem.scope.{key}"),
                reasons,
            );
        }
    } else {
        reasons.push("problem.scope object is missing".to_string());
    }

    let result = string_field(object.get("status_claim"), "problem.status_claim", reasons);
    match result.as_deref() {
        Some("candidate_unsat_safety") | Some("candidate_sat_counterexample") => {}
        Some(other) => reasons.push(format!("problem.status_claim={other:?} is unsupported")),
        None => {}
    }

    check_artifact_predicates_match_problem(problem, object.get("predicates"), reasons);
    check_artifact_clauses_match_problem(problem, object.get("clauses"), reasons);
    result
}

fn check_artifact_predicates_match_problem(
    problem: &ChcProblem,
    value: Option<&Value>,
    reasons: &mut Vec<String>,
) {
    let Some(predicates) = value.and_then(Value::as_array) else {
        reasons.push("problem.predicates must be an array".to_string());
        return;
    };
    let mut seen = BTreeSet::new();
    for (index, predicate) in predicates.iter().enumerate() {
        let Some(object) = predicate.as_object() else {
            reasons.push(format!("problem.predicates[{index}] must be an object"));
            continue;
        };
        let name = string_field(
            object.get("name"),
            &format!("problem.predicates[{index}].name"),
            reasons,
        );
        let arity = usize_field(
            object.get("arity"),
            &format!("problem.predicates[{index}].arity"),
            reasons,
        );
        if let (Some(name), Some(arity)) = (name, arity) {
            if !seen.insert(name.clone()) {
                reasons.push(format!("duplicate problem predicate {name:?}"));
            }
            match problem.get_predicate_by_name(&name) {
                Some(predicate) if predicate.arg_sorts.len() == arity => {}
                Some(predicate) => reasons.push(format!(
                    "problem predicate {name:?} arity {arity} does not match external arity {}",
                    predicate.arg_sorts.len()
                )),
                None => reasons.push(format!(
                    "artifact problem predicate {name:?} is not declared in external CHC"
                )),
            }
        }
    }
    for predicate in problem.predicates() {
        if !seen.contains(&predicate.name) {
            reasons.push(format!(
                "external predicate {} is missing from artifact problem",
                predicate.name
            ));
        }
    }
}

fn check_artifact_clauses_match_problem(
    problem: &ChcProblem,
    value: Option<&Value>,
    reasons: &mut Vec<String>,
) {
    let Some(clauses) = value.and_then(Value::as_array) else {
        reasons.push("problem.clauses must be an array".to_string());
        return;
    };
    if clauses.len() != problem.clauses().len() {
        reasons.push(format!(
            "artifact problem has {} clauses; external CHC has {}",
            clauses.len(),
            problem.clauses().len()
        ));
    }
    let mut seen = BTreeSet::new();
    for (index, clause) in clauses.iter().enumerate() {
        let Some(object) = clause.as_object() else {
            reasons.push(format!("problem.clauses[{index}] must be an object"));
            continue;
        };
        if let Some(id) = string_field(
            object.get("id"),
            &format!("problem.clauses[{index}].id"),
            reasons,
        ) {
            if !seen.insert(id.clone()) {
                reasons.push(format!("duplicate problem clause id {id:?}"));
            }
        }
        string_field(
            object.get("role"),
            &format!("problem.clauses[{index}].role"),
            reasons,
        );
        string_field(
            object.get("head"),
            &format!("problem.clauses[{index}].head"),
            reasons,
        );
        if !matches!(object.get("body"), Some(Value::Array(_))) {
            reasons.push(format!("problem.clauses[{index}].body must be an array"));
        }
    }
}

fn artifact_clause_ids(
    problem_value: Option<&Value>,
    reasons: &mut Vec<String>,
) -> BTreeSet<String> {
    let mut ids = BTreeSet::new();
    let Some(clauses) = problem_value
        .and_then(Value::as_object)
        .and_then(|object| object.get("clauses"))
        .and_then(Value::as_array)
    else {
        return ids;
    };
    for (index, clause) in clauses.iter().enumerate() {
        if let Some(id) = clause
            .as_object()
            .and_then(|object| object.get("id"))
            .and_then(Value::as_str)
        {
            ids.insert(id.to_string());
        } else {
            reasons.push(format!(
                "problem.clauses[{index}].id is missing or not a string"
            ));
        }
    }
    ids
}

fn check_artifact_quotient(
    problem: &ChcProblem,
    value: Option<&Value>,
    reasons: &mut Vec<String>,
) -> BTreeSet<String> {
    let Some(object) = value.and_then(Value::as_object) else {
        reasons.push("quotient object is missing".to_string());
        return BTreeSet::new();
    };
    expect_bool_field(object.get("finite"), true, "quotient.finite", reasons);

    let mut class_ids = BTreeSet::new();
    let Some(classes) = object.get("classes").and_then(Value::as_array) else {
        reasons.push("quotient.classes must be an array".to_string());
        return class_ids;
    };
    for (index, class) in classes.iter().enumerate() {
        let Some(class_object) = class.as_object() else {
            reasons.push(format!("quotient.classes[{index}] must be an object"));
            continue;
        };
        let id = string_field(
            class_object.get("id"),
            &format!("quotient.classes[{index}].id"),
            reasons,
        );
        let predicate_name = string_field(
            class_object.get("predicate"),
            &format!("quotient.classes[{index}].predicate"),
            reasons,
        );
        if let Some(id) = id {
            if !class_ids.insert(id.clone()) {
                reasons.push(format!("duplicate quotient class id {id:?}"));
            }
            if let Some(predicate_name) = predicate_name {
                if problem.get_predicate_by_name(&predicate_name).is_none() {
                    reasons.push(format!(
                        "quotient class {id:?} references unknown predicate {predicate_name:?}"
                    ));
                }
            }
        }
    }

    check_artifact_string_refs(
        object.get("initial_classes"),
        "quotient.initial_classes",
        &class_ids,
        "quotient class",
        reasons,
    );
    check_artifact_string_refs(
        object.get("bad_classes"),
        "quotient.bad_classes",
        &class_ids,
        "quotient class",
        reasons,
    );
    check_artifact_quotient_map(object.get("quotient_map"), &class_ids, reasons);
    check_artifact_representatives(object.get("representatives"), &class_ids, reasons);
    class_ids
}

fn check_artifact_quotient_map(
    value: Option<&Value>,
    class_ids: &BTreeSet<String>,
    reasons: &mut Vec<String>,
) {
    let Some(object) = value.and_then(Value::as_object) else {
        reasons.push("quotient.quotient_map object is missing".to_string());
        return;
    };
    expect_bool_field(
        object.get("total"),
        true,
        "quotient.quotient_map.total",
        reasons,
    );
    expect_bool_field(
        object.get("deterministic"),
        true,
        "quotient.quotient_map.deterministic",
        reasons,
    );
    let Some(guards) = object.get("guards").and_then(Value::as_array) else {
        reasons.push("quotient.quotient_map.guards must be an array".to_string());
        return;
    };
    for (index, guard) in guards.iter().enumerate() {
        let Some(guard_object) = guard.as_object() else {
            reasons.push(format!(
                "quotient.quotient_map.guards[{index}] must be an object"
            ));
            continue;
        };
        if let Some(class_id) = string_field(
            guard_object.get("class"),
            &format!("quotient.quotient_map.guards[{index}].class"),
            reasons,
        ) {
            check_artifact_ref(
                &class_id,
                class_ids,
                &format!("quotient.quotient_map.guards[{index}].class"),
                "quotient class",
                reasons,
            );
        }
        if !matches!(guard_object.get("when"), Some(Value::Array(_))) {
            reasons.push(format!(
                "quotient.quotient_map.guards[{index}].when must be an array"
            ));
        }
    }
}

fn check_artifact_representatives(
    value: Option<&Value>,
    class_ids: &BTreeSet<String>,
    reasons: &mut Vec<String>,
) {
    let Some(representatives) = value.and_then(Value::as_array) else {
        reasons.push("quotient.representatives must be an array".to_string());
        return;
    };
    for (index, representative) in representatives.iter().enumerate() {
        let Some(object) = representative.as_object() else {
            reasons.push(format!(
                "quotient.representatives[{index}] must be an object"
            ));
            continue;
        };
        if let Some(class_id) = string_field(
            object.get("class"),
            &format!("quotient.representatives[{index}].class"),
            reasons,
        ) {
            check_artifact_ref(
                &class_id,
                class_ids,
                &format!("quotient.representatives[{index}].class"),
                "quotient class",
                reasons,
            );
        }
        if !matches!(object.get("assignment"), Some(Value::Object(_))) {
            reasons.push(format!(
                "quotient.representatives[{index}].assignment must be an object"
            ));
        }
    }
}

fn check_artifact_lift_and_concretization(
    object: &serde_json::Map<String, Value>,
    class_ids: &BTreeSet<String>,
    reasons: &mut Vec<String>,
) {
    let Some(concretization) = object.get("concretization").and_then(Value::as_object) else {
        reasons.push("concretization object is missing".to_string());
        return;
    };
    let Some(class_interpretations) = concretization
        .get("class_interpretations")
        .and_then(Value::as_array)
    else {
        reasons.push("concretization.class_interpretations must be an array".to_string());
        return;
    };
    for (index, interpretation) in class_interpretations.iter().enumerate() {
        let Some(interpretation_object) = interpretation.as_object() else {
            reasons.push(format!(
                "concretization.class_interpretations[{index}] must be an object"
            ));
            continue;
        };
        if let Some(class_id) = string_field(
            interpretation_object.get("class"),
            &format!("concretization.class_interpretations[{index}].class"),
            reasons,
        ) {
            check_artifact_ref(
                &class_id,
                class_ids,
                &format!("concretization.class_interpretations[{index}].class"),
                "quotient class",
                reasons,
            );
        }
        if !matches!(
            interpretation_object.get("constraints"),
            Some(Value::Array(_))
        ) {
            reasons.push(format!(
                "concretization.class_interpretations[{index}].constraints must be an array"
            ));
        }
    }
    if let Some(coverage) = concretization.get("coverage").and_then(Value::as_object) {
        for key in [
            "covers_all_classes",
            "classes_are_disjoint",
            "covers_all_predicate_states",
        ] {
            expect_bool_field(
                coverage.get(key),
                true,
                &format!("concretization.coverage.{key}"),
                reasons,
            );
        }
    } else {
        reasons.push("concretization.coverage object is missing".to_string());
    }

    let Some(lift) = object.get("lift").and_then(Value::as_object) else {
        reasons.push("lift object is missing".to_string());
        return;
    };
    expect_bool_field(lift.get("map_total"), true, "lift.map_total", reasons);
    if let Some(unsat_safety) = lift.get("unsat_safety").and_then(Value::as_object) {
        expect_bool_field(
            unsat_safety.get("preserves_original_query"),
            true,
            "lift.unsat_safety.preserves_original_query",
            reasons,
        );
        if let Some(class_to_formula) = unsat_safety
            .get("class_to_formula")
            .and_then(Value::as_array)
        {
            for (index, entry) in class_to_formula.iter().enumerate() {
                let Some(entry_object) = entry.as_object() else {
                    reasons.push(format!(
                        "lift.unsat_safety.class_to_formula[{index}] must be an object"
                    ));
                    continue;
                };
                if let Some(class_id) = string_field(
                    entry_object.get("class"),
                    &format!("lift.unsat_safety.class_to_formula[{index}].class"),
                    reasons,
                ) {
                    check_artifact_ref(
                        &class_id,
                        class_ids,
                        &format!("lift.unsat_safety.class_to_formula[{index}].class"),
                        "quotient class",
                        reasons,
                    );
                }
                string_field(
                    entry_object.get("formula"),
                    &format!("lift.unsat_safety.class_to_formula[{index}].formula"),
                    reasons,
                );
            }
        }
    }
}

fn check_artifact_derivation_dag(
    value: Option<&Value>,
    class_ids: &BTreeSet<String>,
    problem_value: Option<&Value>,
    reasons: &mut Vec<String>,
) -> ArtifactDagSummary {
    let mut summary = ArtifactDagSummary::default();
    let clause_ids = artifact_clause_ids(problem_value, reasons);
    let Some(object) = value.and_then(Value::as_object) else {
        reasons.push("derivation_dag object is missing".to_string());
        return summary;
    };
    expect_bool_field(
        object.get("acyclic"),
        true,
        "derivation_dag.acyclic",
        reasons,
    );
    let Some(nodes) = object.get("nodes").and_then(Value::as_array) else {
        reasons.push("derivation_dag.nodes must be an array".to_string());
        return summary;
    };
    for (index, node) in nodes.iter().enumerate() {
        let Some(node_object) = node.as_object() else {
            reasons.push(format!("derivation_dag.nodes[{index}] must be an object"));
            continue;
        };
        if let Some(id) = string_field(
            node_object.get("id"),
            &format!("derivation_dag.nodes[{index}].id"),
            reasons,
        ) {
            if !summary.node_ids.insert(id.clone()) {
                reasons.push(format!("duplicate derivation DAG node id {id:?}"));
            }
        }
        if let Some(class_id) = string_field(
            node_object.get("class"),
            &format!("derivation_dag.nodes[{index}].class"),
            reasons,
        ) {
            check_artifact_ref(
                &class_id,
                class_ids,
                &format!("derivation_dag.nodes[{index}].class"),
                "quotient class",
                reasons,
            );
        }
        if let Some(source_clause) = string_field(
            node_object.get("source_clause"),
            &format!("derivation_dag.nodes[{index}].source_clause"),
            reasons,
        ) {
            check_artifact_ref(
                &source_clause,
                &clause_ids,
                &format!("derivation_dag.nodes[{index}].source_clause"),
                "problem clause",
                reasons,
            );
        }
    }

    let Some(edges) = object.get("edges").and_then(Value::as_array) else {
        reasons.push("derivation_dag.edges must be an array".to_string());
        return summary;
    };
    summary.edge_count = edges.len();
    for (index, edge) in edges.iter().enumerate() {
        let Some(edge_object) = edge.as_object() else {
            reasons.push(format!("derivation_dag.edges[{index}] must be an object"));
            continue;
        };
        for key in ["from", "to"] {
            if let Some(node_id) = string_field(
                edge_object.get(key),
                &format!("derivation_dag.edges[{index}].{key}"),
                reasons,
            ) {
                check_artifact_ref(
                    &node_id,
                    &summary.node_ids,
                    &format!("derivation_dag.edges[{index}].{key}"),
                    "derivation DAG node",
                    reasons,
                );
            }
        }
    }
    check_artifact_string_refs(
        object.get("roots"),
        "derivation_dag.roots",
        &summary.node_ids,
        "derivation DAG node",
        reasons,
    );
    check_artifact_string_refs(
        object.get("topological_order"),
        "derivation_dag.topological_order",
        &summary.node_ids,
        "derivation DAG node",
        reasons,
    );
    summary
}

fn check_artifact_boundary_witness(value: Option<&Value>, reasons: &mut Vec<String>) {
    let Some(object) = value.and_then(Value::as_object) else {
        reasons.push("boundary_witness object is missing".to_string());
        return;
    };
    expect_string_field(
        object.get("lattice"),
        "integer-interval",
        "boundary_witness.lattice",
        reasons,
    );
    let reachable_var = check_artifact_interval(
        object.get("reachable_interval"),
        "reachable_interval",
        reasons,
    );
    let bad_var = check_artifact_interval(object.get("bad_interval"), "bad_interval", reasons);
    if let (Some(reachable_var), Some(bad_var)) = (reachable_var, bad_var) {
        if reachable_var != bad_var {
            reasons.push(format!(
                "boundary_witness intervals use different variables {reachable_var:?} and {bad_var:?}"
            ));
        }
    }
    expect_bool_field(
        object.get("separates_bad"),
        true,
        "boundary_witness.separates_bad",
        reasons,
    );
    let Some(obligations) = object.get("closure_obligations").and_then(Value::as_array) else {
        reasons.push("boundary_witness.closure_obligations must be an array".to_string());
        return;
    };
    if obligations.is_empty() {
        reasons.push("boundary_witness.closure_obligations must be nonempty".to_string());
    }
    let mut seen = BTreeSet::new();
    for (index, obligation) in obligations.iter().enumerate() {
        let Some(obligation_object) = obligation.as_object() else {
            reasons.push(format!(
                "boundary_witness.closure_obligations[{index}] must be an object"
            ));
            continue;
        };
        if let Some(id) = string_field(
            obligation_object.get("id"),
            &format!("boundary_witness.closure_obligations[{index}].id"),
            reasons,
        ) {
            if !seen.insert(id.clone()) {
                reasons.push(format!("duplicate boundary closure obligation id {id:?}"));
            }
        }
        let formula = string_field(
            obligation_object.get("formula"),
            &format!("boundary_witness.closure_obligations[{index}].formula"),
            reasons,
        );
        if matches!(formula.as_deref(), Some("")) {
            reasons.push(format!(
                "boundary_witness.closure_obligations[{index}].formula must be nonempty"
            ));
        }
    }
}

fn check_artifact_interval(
    value: Option<&Value>,
    label: &str,
    reasons: &mut Vec<String>,
) -> Option<String> {
    let Some(object) = value.and_then(Value::as_object) else {
        reasons.push(format!("boundary_witness.{label} object is missing"));
        return None;
    };
    let var = string_field(
        object.get("var"),
        &format!("boundary_witness.{label}.var"),
        reasons,
    );
    check_artifact_bound(
        object.get("lower"),
        &format!("boundary_witness.{label}.lower"),
        reasons,
    );
    check_artifact_bound(
        object.get("upper"),
        &format!("boundary_witness.{label}.upper"),
        reasons,
    );
    var
}

fn check_artifact_bound(value: Option<&Value>, label: &str, reasons: &mut Vec<String>) {
    let Some(object) = value.and_then(Value::as_object) else {
        reasons.push(format!("{label} object is missing"));
        return;
    };
    let kind = string_field(object.get("kind"), &format!("{label}.kind"), reasons);
    match kind.as_deref() {
        Some("finite") => {
            string_field(object.get("value"), &format!("{label}.value"), reasons);
        }
        Some("pos_inf") | Some("neg_inf") => {}
        Some(other) => reasons.push(format!("{label}.kind={other:?} is unsupported")),
        None => {}
    }
}

fn check_artifact_trace_certificate(
    value: Option<&Value>,
    dag_node_ids: &BTreeSet<String>,
    reasons: &mut Vec<String>,
) {
    let Some(object) = value.and_then(Value::as_object) else {
        reasons.push("trace_certificate object is missing".to_string());
        return;
    };
    expect_string_field(
        object.get("mode"),
        "equivalence",
        "trace_certificate.mode",
        reasons,
    );
    let Some(traces) = object.get("canonical_traces").and_then(Value::as_array) else {
        reasons.push("trace_certificate.canonical_traces must be an array".to_string());
        return;
    };
    let mut trace_ids = BTreeSet::new();
    for (index, trace) in traces.iter().enumerate() {
        let Some(trace_object) = trace.as_object() else {
            reasons.push(format!(
                "trace_certificate.canonical_traces[{index}] must be an object"
            ));
            continue;
        };
        if let Some(trace_id) = string_field(
            trace_object.get("trace_id"),
            &format!("trace_certificate.canonical_traces[{index}].trace_id"),
            reasons,
        ) {
            if !trace_ids.insert(trace_id.clone()) {
                reasons.push(format!("duplicate canonical trace id {trace_id:?}"));
            }
        }
        check_artifact_string_refs(
            trace_object.get("dag_path"),
            &format!("trace_certificate.canonical_traces[{index}].dag_path"),
            dag_node_ids,
            "derivation DAG node",
            reasons,
        );
    }
    let Some(classes) = object.get("equivalence_classes").and_then(Value::as_array) else {
        reasons.push("trace_certificate.equivalence_classes must be an array".to_string());
        return;
    };
    for (index, class) in classes.iter().enumerate() {
        let Some(class_object) = class.as_object() else {
            reasons.push(format!(
                "trace_certificate.equivalence_classes[{index}] must be an object"
            ));
            continue;
        };
        if let Some(representative) = string_field(
            class_object.get("representative"),
            &format!("trace_certificate.equivalence_classes[{index}].representative"),
            reasons,
        ) {
            check_artifact_ref(
                &representative,
                &trace_ids,
                &format!("trace_certificate.equivalence_classes[{index}].representative"),
                "canonical trace",
                reasons,
            );
        }
        if !matches!(class_object.get("members"), Some(Value::Array(_))) {
            reasons.push(format!(
                "trace_certificate.equivalence_classes[{index}].members must be an array"
            ));
        }
    }
}

fn check_artifact_proof_energy(value: Option<&Value>, reasons: &mut Vec<String>) {
    let Some(object) = value.and_then(Value::as_object) else {
        reasons.push("proof_energy object is missing".to_string());
        return;
    };
    expect_bool_field(
        object.get("decreases"),
        true,
        "proof_energy.decreases",
        reasons,
    );
    expect_bool_field(
        object.get("checker_must_recompute"),
        true,
        "proof_energy.checker_must_recompute",
        reasons,
    );
    let before = object
        .get("before")
        .and_then(Value::as_object)
        .and_then(|before| before.get("value"))
        .and_then(Value::as_u64);
    let after = object
        .get("after")
        .and_then(Value::as_object)
        .and_then(|after| after.get("value"))
        .and_then(Value::as_u64);
    match (before, after) {
        (Some(before), Some(after)) if before > after => {}
        (Some(before), Some(after)) => reasons.push(format!(
            "proof_energy before value {before} must be greater than after value {after}"
        )),
        _ => reasons.push("proof_energy before/after values must be unsigned integers".to_string()),
    }
}

fn check_artifact_replay(value: Option<&Value>, reasons: &mut Vec<String>) -> usize {
    const REQUIRED_REPLAY_OBLIGATIONS: &[&str] = &[
        "scope_recursive_lia_only",
        "finite_total_quotient",
        "lift_and_concretization",
        "dag_boundary_trace_energy",
    ];

    let Some(object) = value.and_then(Value::as_object) else {
        reasons.push("replay object is missing".to_string());
        return 0;
    };
    match string_field(object.get("status"), "replay.status", reasons).as_deref() {
        Some("not_replayed") | Some("passed") => {}
        Some(other) => reasons.push(format!("replay.status={other:?} is unsupported")),
        None => {}
    }
    expect_bool_field(
        object.get("fail_closed"),
        true,
        "replay.fail_closed",
        reasons,
    );
    expect_bool_field(
        object.get("promotion_allowed"),
        false,
        "replay.promotion_allowed",
        reasons,
    );
    let Some(obligations) = object.get("obligations").and_then(Value::as_array) else {
        reasons.push("replay.obligations must be an array".to_string());
        return 0;
    };
    let mut seen = BTreeSet::new();
    for (index, obligation) in obligations.iter().enumerate() {
        let Some(obligation_object) = obligation.as_object() else {
            reasons.push(format!("replay.obligations[{index}] must be an object"));
            continue;
        };
        let id = string_field(
            obligation_object.get("id"),
            &format!("replay.obligations[{index}].id"),
            reasons,
        );
        let status = string_field(
            obligation_object.get("status"),
            &format!("replay.obligations[{index}].status"),
            reasons,
        );
        if let Some(id) = &id {
            if !seen.insert(id.clone()) {
                reasons.push(format!("duplicate replay obligation id {id:?}"));
            }
            if !REQUIRED_REPLAY_OBLIGATIONS.contains(&id.as_str()) {
                reasons.push(format!("replay obligation id {id:?} is unsupported"));
            }
        }
        match status.as_deref() {
            Some("pending") | Some("passed") | Some("failed") | Some("unsupported") => {}
            Some(other) => {
                reasons.push(format!("replay obligation status {other:?} is unsupported"))
            }
            None => {}
        }
    }
    for id in REQUIRED_REPLAY_OBLIGATIONS {
        if !seen.contains(*id) {
            reasons.push(format!("required replay obligation id {id:?} is missing"));
        }
    }
    seen.len()
}

fn check_artifact_string_refs(
    value: Option<&Value>,
    label: &str,
    allowed: &BTreeSet<String>,
    allowed_label: &str,
    reasons: &mut Vec<String>,
) {
    let Some(values) = value.and_then(Value::as_array) else {
        reasons.push(format!("{label} must be an array"));
        return;
    };
    if values.is_empty() {
        reasons.push(format!("{label} must be nonempty"));
    }
    for (index, value) in values.iter().enumerate() {
        if let Some(id) = value.as_str() {
            check_artifact_ref(
                id,
                allowed,
                &format!("{label}[{index}]"),
                allowed_label,
                reasons,
            );
        } else {
            reasons.push(format!("{label}[{index}] is missing or not a string"));
        }
    }
}

fn check_artifact_ref(
    id: &str,
    allowed: &BTreeSet<String>,
    label: &str,
    allowed_label: &str,
    reasons: &mut Vec<String>,
) {
    if !allowed.contains(id) {
        reasons.push(format!("{label}={id:?} is not a known {allowed_label}"));
    }
}

fn check_problem_is_recursive_lia(problem: &ChcProblem, reasons: &mut Vec<String>) {
    if let Err(err) = problem.validate() {
        reasons.push(format!("problem validation failed: {err}"));
    }
    if problem.predicates().is_empty() {
        reasons.push("recursive-LIA quotient requires at least one predicate".to_string());
    }
    if problem.clauses().is_empty() {
        reasons.push("recursive-LIA quotient requires at least one clause".to_string());
    }

    for predicate in problem.predicates() {
        for (index, sort) in predicate.arg_sorts.iter().enumerate() {
            if sort != &ChcSort::Int {
                reasons.push(format!(
                    "predicate {} argument {index} has sort {sort}; only Int is supported",
                    predicate.name
                ));
            }
        }
    }

    for (clause_index, clause) in problem.clauses().iter().enumerate() {
        if clause.body.predicates.len() > 1 {
            reasons.push(format!(
                "clause {clause_index} has {} body predicates; first quotient checker supports linear CHCs only",
                clause.body.predicates.len()
            ));
        }

        if let Some(constraint) = &clause.body.constraint {
            if !expr_is_lia_constraint(constraint) {
                reasons.push(format!(
                    "clause {clause_index} body constraint is outside linear integer arithmetic"
                ));
            }
        }
        for (_, args) in &clause.body.predicates {
            for arg in args {
                if !expr_is_lia_int_term(arg) {
                    reasons.push(format!(
                        "clause {clause_index} body predicate argument is outside linear integer arithmetic"
                    ));
                }
            }
        }
        if let ClauseHead::Predicate(_, args) = &clause.head {
            for arg in args {
                if !expr_is_lia_int_term(arg) {
                    reasons.push(format!(
                        "clause {clause_index} head predicate argument is outside linear integer arithmetic"
                    ));
                }
            }
        }
    }

    if !has_recursive_dependency(problem) {
        reasons.push("problem has no recursive predicate dependency cycle".to_string());
    }
}

fn parse_nodes(
    problem: &ChcProblem,
    quotient_value: Option<&Value>,
    reasons: &mut Vec<String>,
) -> Vec<QuotientNode> {
    let Some(quotient) = quotient_value.and_then(Value::as_object) else {
        reasons.push("quotient object is missing".to_string());
        return Vec::new();
    };
    expect_string_field(
        quotient.get("kind"),
        "finite-predicate-identity",
        "quotient.kind",
        reasons,
    );

    let Some(nodes) = quotient.get("nodes").and_then(Value::as_array) else {
        reasons.push("quotient.nodes must be an array".to_string());
        return Vec::new();
    };

    let mut out = Vec::new();
    let mut seen = HashSet::default();
    for (index, node) in nodes.iter().enumerate() {
        let Some(object) = node.as_object() else {
            reasons.push(format!("quotient.nodes[{index}] must be an object"));
            continue;
        };
        let id = string_field(
            object.get("id"),
            &format!("quotient.nodes[{index}].id"),
            reasons,
        );
        let predicate_name = string_field(
            object.get("predicate"),
            &format!("quotient.nodes[{index}].predicate"),
            reasons,
        );
        let class = string_field(
            object.get("class"),
            &format!("quotient.nodes[{index}].class"),
            reasons,
        );
        if let (Some(id), Some(predicate_name), Some(class)) = (id, predicate_name, class) {
            if !seen.insert(id.clone()) {
                reasons.push(format!("duplicate quotient node id {id:?}"));
                continue;
            }
            if class != predicate_name {
                reasons.push(format!(
                    "quotient node {id} class {class:?} is not the identity class for predicate {predicate_name:?}"
                ));
            }
            match problem.get_predicate_by_name(&predicate_name) {
                Some(predicate) => out.push(QuotientNode {
                    id,
                    predicate: predicate.id,
                }),
                None => reasons.push(format!(
                    "quotient node {id} references unknown predicate {predicate_name:?}"
                )),
            }
        }
    }
    out
}

fn parse_edges(quotient_value: Option<&Value>, reasons: &mut Vec<String>) -> Vec<QuotientEdge> {
    let Some(quotient) = quotient_value.and_then(Value::as_object) else {
        return Vec::new();
    };
    let Some(edges) = quotient.get("edges").and_then(Value::as_array) else {
        reasons.push("quotient.edges must be an array".to_string());
        return Vec::new();
    };

    let mut out = Vec::new();
    let mut seen = HashSet::default();
    for (index, edge) in edges.iter().enumerate() {
        let Some(object) = edge.as_object() else {
            reasons.push(format!("quotient.edges[{index}] must be an object"));
            continue;
        };
        let id = string_field(
            object.get("id"),
            &format!("quotient.edges[{index}].id"),
            reasons,
        );
        let clause_index = usize_field(
            object.get("clause_index"),
            &format!("quotient.edges[{index}].clause_index"),
            reasons,
        );
        let source = string_field(
            object.get("source"),
            &format!("quotient.edges[{index}].source"),
            reasons,
        );
        let target = string_field(
            object.get("target"),
            &format!("quotient.edges[{index}].target"),
            reasons,
        );
        let energy_before = u64_field(
            object.get("energy_before"),
            &format!("quotient.edges[{index}].energy_before"),
            reasons,
        );
        let energy_after = u64_field(
            object.get("energy_after"),
            &format!("quotient.edges[{index}].energy_after"),
            reasons,
        );
        if let (
            Some(id),
            Some(clause_index),
            Some(source),
            Some(target),
            Some(energy_before),
            Some(energy_after),
        ) = (
            id,
            clause_index,
            source,
            target,
            energy_before,
            energy_after,
        ) {
            if !seen.insert(id.clone()) {
                reasons.push(format!("duplicate quotient edge id {id:?}"));
                continue;
            }
            out.push(QuotientEdge {
                clause_index,
                source,
                target,
                energy_before,
                energy_after,
            });
        }
    }
    out
}

fn check_identity_nodes_cover_predicates(
    problem: &ChcProblem,
    nodes: &[QuotientNode],
    reasons: &mut Vec<String>,
) {
    let mut by_predicate = BTreeMap::new();
    for node in nodes {
        by_predicate
            .entry(node.predicate.index())
            .or_insert_with(Vec::new)
            .push(node.id.clone());
    }
    for predicate in problem.predicates() {
        match by_predicate.get(&predicate.id.index()) {
            Some(ids) if ids.len() == 1 => {}
            Some(ids) => reasons.push(format!(
                "predicate {} has {} quotient nodes ({ids:?}); identity quotient requires exactly one",
                predicate.name,
                ids.len()
            )),
            None => reasons.push(format!(
                "predicate {} is missing from quotient nodes",
                predicate.name
            )),
        }
    }
}

fn check_edges_cover_clauses(
    problem: &ChcProblem,
    nodes: &[QuotientNode],
    edges: &[QuotientEdge],
    reasons: &mut Vec<String>,
) {
    let node_predicates: BTreeMap<String, PredicateId> = nodes
        .iter()
        .map(|node| (node.id.clone(), node.predicate))
        .collect();
    let mut seen_clauses = BTreeSet::new();
    let mut saw_recursive_descent = false;

    for edge in edges {
        if edge.clause_index >= problem.clauses().len() {
            reasons.push(format!(
                "quotient edge for clause {} is out of bounds",
                edge.clause_index
            ));
            continue;
        }
        if !seen_clauses.insert(edge.clause_index) {
            reasons.push(format!(
                "clause {} has more than one quotient edge",
                edge.clause_index
            ));
        }
        let clause = &problem.clauses()[edge.clause_index];
        let expected_source = match clause.body.predicates.as_slice() {
            [] => Endpoint::Entry,
            [(predicate, _)] => Endpoint::Predicate(*predicate),
            _ => {
                reasons.push(format!(
                    "clause {} is non-linear and cannot be represented by one quotient edge",
                    edge.clause_index
                ));
                continue;
            }
        };
        let expected_target = match &clause.head {
            ClauseHead::False => Endpoint::Exit,
            ClauseHead::Predicate(predicate, _) => Endpoint::Predicate(*predicate),
        };

        check_endpoint(
            "source",
            edge.clause_index,
            &edge.source,
            expected_source,
            &node_predicates,
            reasons,
        );
        check_endpoint(
            "target",
            edge.clause_index,
            &edge.target,
            expected_target,
            &node_predicates,
            reasons,
        );

        let recursive_edge = match (expected_source, expected_target) {
            (Endpoint::Predicate(source), Endpoint::Predicate(target)) => {
                predicates_share_cycle(problem, source, target)
            }
            _ => false,
        };
        if recursive_edge {
            if edge.energy_before <= edge.energy_after {
                reasons.push(format!(
                    "recursive quotient edge for clause {} must strictly decrease proof energy",
                    edge.clause_index
                ));
            } else {
                saw_recursive_descent = true;
            }
        } else if edge.energy_before < edge.energy_after {
            reasons.push(format!(
                "quotient edge for clause {} increases proof energy",
                edge.clause_index
            ));
        }
    }

    for clause_index in 0..problem.clauses().len() {
        if !seen_clauses.contains(&clause_index) {
            reasons.push(format!(
                "clause {clause_index} is not covered by quotient.edges"
            ));
        }
    }
    if has_recursive_dependency(problem) && !saw_recursive_descent {
        reasons.push("recursive certificate has no strict proof-energy descent edge".to_string());
    }
}

#[derive(Debug, Clone, Copy)]
enum Endpoint {
    Entry,
    Exit,
    Predicate(PredicateId),
}

fn check_endpoint(
    label: &str,
    clause_index: usize,
    actual: &str,
    expected: Endpoint,
    node_predicates: &BTreeMap<String, PredicateId>,
    reasons: &mut Vec<String>,
) {
    match expected {
        Endpoint::Entry if actual == "entry" => {}
        Endpoint::Entry => reasons.push(format!(
            "clause {clause_index} quotient edge {label}={actual:?}; expected \"entry\""
        )),
        Endpoint::Exit if actual == "exit" => {}
        Endpoint::Exit => reasons.push(format!(
            "clause {clause_index} quotient edge {label}={actual:?}; expected \"exit\""
        )),
        Endpoint::Predicate(expected_predicate) => match node_predicates.get(actual) {
            Some(actual_predicate) if *actual_predicate == expected_predicate => {}
            Some(actual_predicate) => reasons.push(format!(
                "clause {clause_index} quotient edge {label}={actual:?} maps predicate {}, expected {}",
                actual_predicate.index(),
                expected_predicate.index()
            )),
            None => reasons.push(format!(
                "clause {clause_index} quotient edge {label}={actual:?} is not a quotient node"
            )),
        },
    }
}

fn check_auxiliary_certificate_sections(
    problem: &ChcProblem,
    object: &serde_json::Map<String, Value>,
    result: Option<&str>,
    reasons: &mut Vec<String>,
) {
    expect_nested_kind(
        object.get("concretization"),
        "identity-predicate-arguments",
        "concretization",
        reasons,
    );
    expect_nested_kind(
        object.get("lift"),
        "identity-predicate-arguments",
        "lift",
        reasons,
    );
    expect_nested_kind(
        object.get("trace"),
        "identity-trace-equivalence",
        "trace",
        reasons,
    );
    expect_nested_kind(
        object.get("proof_energy"),
        "natural-descent",
        "proof_energy",
        reasons,
    );
    if let Some(proof_energy) = object.get("proof_energy").and_then(Value::as_object) {
        match proof_energy.get("strict").and_then(Value::as_bool) {
            Some(true) => {}
            Some(false) => reasons.push("proof_energy.strict must be true".to_string()),
            None => reasons.push("proof_energy.strict is missing".to_string()),
        }
    }

    let Some(boundary) = object.get("boundary").and_then(Value::as_object) else {
        reasons.push("boundary object is missing".to_string());
        return;
    };
    expect_string_field(
        boundary.get("kind"),
        "safety-interval",
        "boundary.kind",
        reasons,
    );
    if let Some(predicate_name) = string_field(
        boundary.get("witness_predicate"),
        "boundary.witness_predicate",
        reasons,
    ) {
        if problem.get_predicate_by_name(&predicate_name).is_none() {
            reasons.push(format!(
                "boundary witness predicate {predicate_name:?} is not declared"
            ));
        }
    }
    let lower = i64_field(boundary.get("lower"), "boundary.lower", reasons);
    let upper = i64_field(boundary.get("upper"), "boundary.upper", reasons);
    if let (Some(lower), Some(upper)) = (lower, upper) {
        if lower > upper {
            reasons.push(format!("boundary interval [{lower}, {upper}] is empty"));
        }
    }
    if matches!(result, Some("unsafe")) {
        expect_nested_kind(
            object.get("counterexample_lift"),
            "constructive-original-trace",
            "counterexample_lift",
            reasons,
        );
    }
}

fn check_obligations(
    obligations_value: Option<&Value>,
    result: Option<&str>,
    reasons: &mut Vec<String>,
) -> usize {
    let Some(obligations) = obligations_value.and_then(Value::as_array) else {
        reasons.push("obligations must be an array".to_string());
        return 0;
    };
    let required = match result {
        Some("unsafe") => REQUIRED_UNSAFE_OBLIGATIONS,
        _ => REQUIRED_SAFE_OBLIGATIONS,
    };
    let mut accepted = BTreeSet::new();
    let mut seen = BTreeSet::new();
    for (index, obligation) in obligations.iter().enumerate() {
        let Some(object) = obligation.as_object() else {
            reasons.push(format!("obligations[{index}] must be an object"));
            continue;
        };
        let kind = string_field(
            object.get("kind"),
            &format!("obligations[{index}].kind"),
            reasons,
        );
        let status = string_field(
            object.get("status"),
            &format!("obligations[{index}].status"),
            reasons,
        );
        if let Some(kind) = &kind {
            if !seen.insert(kind.clone()) {
                reasons.push(format!("duplicate obligation {kind:?}"));
            }
            if !required.contains(&kind.as_str()) {
                reasons.push(format!(
                    "obligation {kind:?} is not supported for result {:?}",
                    result.unwrap_or("safe")
                ));
            }
        }
        match (kind, status) {
            (Some(kind), Some(status))
                if status == "accepted" && required.contains(&kind.as_str()) =>
            {
                accepted.insert(kind);
            }
            (Some(kind), Some(status)) => reasons.push(format!(
                "obligation {kind:?} has status {status:?}; only accepted obligations are replayable"
            )),
            _ => {}
        }
    }
    for kind in required {
        if !accepted.contains(*kind) {
            reasons.push(format!(
                "required obligation {kind:?} is missing or not accepted"
            ));
        }
    }
    accepted.len()
}

fn expr_is_lia_constraint(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Bool(_) => true,
        ChcExpr::Var(var) => matches!(var.sort, ChcSort::Bool),
        ChcExpr::Op(op, args) => match op {
            ChcOp::Not => args.len() == 1 && expr_is_lia_constraint(args[0].as_ref()),
            ChcOp::And | ChcOp::Or => args.iter().all(|arg| expr_is_lia_constraint(arg)),
            ChcOp::Implies | ChcOp::Iff => {
                args.len() == 2 && args.iter().all(|arg| expr_is_lia_constraint(arg))
            }
            ChcOp::Eq | ChcOp::Ne => {
                args.len() == 2
                    && ((expr_is_lia_int_term(args[0].as_ref())
                        && expr_is_lia_int_term(args[1].as_ref()))
                        || (expr_is_lia_bool_atom(args[0].as_ref())
                            && expr_is_lia_bool_atom(args[1].as_ref())))
            }
            ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge => {
                args.len() == 2
                    && expr_is_lia_int_term(args[0].as_ref())
                    && expr_is_lia_int_term(args[1].as_ref())
            }
            _ => false,
        },
        _ => false,
    }
}

fn expr_is_lia_bool_atom(expr: &ChcExpr) -> bool {
    matches!(expr, ChcExpr::Bool(_))
        || matches!(expr, ChcExpr::Var(var) if matches!(var.sort, ChcSort::Bool))
}

fn expr_is_lia_int_term(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Int(_) => true,
        ChcExpr::Real(_, _)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Bool(_)
        | ChcExpr::PredicateApp(_, _, _)
        | ChcExpr::FuncApp(_, _, _)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_)
        | ChcExpr::ConstArray(_, _) => false,
        ChcExpr::Var(var) => matches!(var.sort, ChcSort::Int),
        ChcExpr::Op(op, args) => match op {
            ChcOp::Add | ChcOp::Sub => args.iter().all(|arg| expr_is_lia_int_term(arg)),
            ChcOp::Neg => args.len() == 1 && args.iter().all(|arg| expr_is_lia_int_term(arg)),
            ChcOp::Mul => {
                args.len() == 2
                    && args.iter().all(|arg| expr_is_lia_int_term(arg))
                    && (matches!(args[0].as_ref(), ChcExpr::Int(_))
                        || matches!(args[1].as_ref(), ChcExpr::Int(_)))
            }
            ChcOp::Not
            | ChcOp::And
            | ChcOp::Or
            | ChcOp::Implies
            | ChcOp::Iff
            | ChcOp::Eq
            | ChcOp::Ne
            | ChcOp::Lt
            | ChcOp::Le
            | ChcOp::Gt
            | ChcOp::Ge
            | ChcOp::Ite
            | ChcOp::Div
            | ChcOp::Mod
            | ChcOp::Select
            | ChcOp::Store
            | ChcOp::BvAdd
            | ChcOp::BvSub
            | ChcOp::BvMul
            | ChcOp::BvUDiv
            | ChcOp::BvURem
            | ChcOp::BvSDiv
            | ChcOp::BvSRem
            | ChcOp::BvSMod
            | ChcOp::BvAnd
            | ChcOp::BvOr
            | ChcOp::BvXor
            | ChcOp::BvNand
            | ChcOp::BvNor
            | ChcOp::BvXnor
            | ChcOp::BvNot
            | ChcOp::BvNeg
            | ChcOp::BvShl
            | ChcOp::BvLShr
            | ChcOp::BvAShr
            | ChcOp::BvULt
            | ChcOp::BvULe
            | ChcOp::BvUGt
            | ChcOp::BvUGe
            | ChcOp::BvSLt
            | ChcOp::BvSLe
            | ChcOp::BvSGt
            | ChcOp::BvSGe
            | ChcOp::BvComp
            | ChcOp::BvConcat
            | ChcOp::Bv2Nat
            | ChcOp::BvExtract(_, _)
            | ChcOp::BvZeroExtend(_)
            | ChcOp::BvSignExtend(_)
            | ChcOp::BvRotateLeft(_)
            | ChcOp::BvRotateRight(_)
            | ChcOp::BvRepeat(_)
            | ChcOp::Int2Bv(_) => false,
        },
    }
}

fn has_recursive_dependency(problem: &ChcProblem) -> bool {
    let n = problem.predicates().len();
    if n == 0 {
        return false;
    }
    let mut graph = vec![Vec::new(); n];
    for clause in problem.clauses() {
        let Some(head) = clause.head.predicate_id() else {
            continue;
        };
        if head.index() >= n {
            return false;
        }
        for (body, _) in &clause.body.predicates {
            if body.index() >= n {
                return false;
            }
            graph[body.index()].push(head.index());
        }
    }

    for start in 0..n {
        let mut stack = graph[start].clone();
        let mut seen = vec![false; n];
        while let Some(next) = stack.pop() {
            if next >= n {
                return false;
            }
            if next == start {
                return true;
            }
            if seen[next] {
                continue;
            }
            seen[next] = true;
            stack.extend(graph[next].iter().copied());
        }
    }
    false
}

fn predicates_share_cycle(problem: &ChcProblem, source: PredicateId, target: PredicateId) -> bool {
    source == target || predicate_reaches(problem, target, source)
}

fn predicate_reaches(problem: &ChcProblem, from: PredicateId, to: PredicateId) -> bool {
    let n = problem.predicates().len();
    if from.index() >= n || to.index() >= n {
        return false;
    }
    let mut graph = vec![Vec::new(); n];
    for clause in problem.clauses() {
        let Some(head) = clause.head.predicate_id() else {
            continue;
        };
        if head.index() >= n {
            return false;
        }
        for (body, _) in &clause.body.predicates {
            if body.index() >= n {
                return false;
            }
            graph[body.index()].push(head.index());
        }
    }

    let mut stack = graph[from.index()].clone();
    let mut seen = vec![false; n];
    while let Some(next) = stack.pop() {
        if next == to.index() {
            return true;
        }
        if next >= n || seen[next] {
            continue;
        }
        seen[next] = true;
        stack.extend(graph[next].iter().copied());
    }
    false
}

fn expect_nested_kind(
    value: Option<&Value>,
    expected: &str,
    label: &str,
    reasons: &mut Vec<String>,
) {
    let Some(object) = value.and_then(Value::as_object) else {
        reasons.push(format!("{label} object is missing"));
        return;
    };
    expect_string_field(
        object.get("kind"),
        expected,
        &format!("{label}.kind"),
        reasons,
    );
}

fn expect_string_field(
    value: Option<&Value>,
    expected: &str,
    label: &str,
    reasons: &mut Vec<String>,
) {
    match value.and_then(Value::as_str) {
        Some(actual) if actual == expected => {}
        Some(actual) => reasons.push(format!("{label}={actual:?} does not match {expected:?}")),
        None => reasons.push(format!("{label} is missing or not a string")),
    }
}

fn expect_u64_field(value: Option<&Value>, expected: u64, label: &str, reasons: &mut Vec<String>) {
    match value.and_then(Value::as_u64) {
        Some(actual) if actual == expected => {}
        Some(actual) => reasons.push(format!("{label}={actual} does not match {expected}")),
        None => reasons.push(format!("{label} is missing or not an unsigned integer")),
    }
}

fn expect_bool_field(
    value: Option<&Value>,
    expected: bool,
    label: &str,
    reasons: &mut Vec<String>,
) {
    match value.and_then(Value::as_bool) {
        Some(actual) if actual == expected => {}
        Some(actual) => reasons.push(format!("{label}={actual} does not match {expected}")),
        None => reasons.push(format!("{label} is missing or not a boolean")),
    }
}

fn string_field(value: Option<&Value>, label: &str, reasons: &mut Vec<String>) -> Option<String> {
    match value.and_then(Value::as_str) {
        Some(value) => Some(value.to_string()),
        None => {
            reasons.push(format!("{label} is missing or not a string"));
            None
        }
    }
}

fn u64_field(value: Option<&Value>, label: &str, reasons: &mut Vec<String>) -> Option<u64> {
    match value.and_then(Value::as_u64) {
        Some(value) => Some(value),
        None => {
            reasons.push(format!("{label} is missing or not an unsigned integer"));
            None
        }
    }
}

fn usize_field(value: Option<&Value>, label: &str, reasons: &mut Vec<String>) -> Option<usize> {
    let value = u64_field(value, label, reasons)?;
    usize::try_from(value).ok().or_else(|| {
        reasons.push(format!("{label}={value} does not fit in usize"));
        None
    })
}

fn i64_field(value: Option<&Value>, label: &str, reasons: &mut Vec<String>) -> Option<i64> {
    match value.and_then(Value::as_i64) {
        Some(value) => Some(value),
        None => {
            reasons.push(format!("{label} is missing or not an integer"));
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;
    use crate::{ChcExpr, ChcParser, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

    fn parsed_minimal_recursive_lia_problem() -> ChcProblem {
        ChcParser::parse(
            r#"
            (set-logic HORN)
            (declare-rel Inv (Int))
            (declare-var x Int)
            (rule (=> (= x 0) (Inv x)))
            (rule (=> (and (Inv x) (< x 3)) (Inv (+ x 1))))
            (query (and (Inv x) (> x 3)))
            "#,
        )
        .expect("minimal recursive-LIA CHC should parse")
    }

    fn recursive_lia_problem() -> ChcProblem {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);
        let xp = ChcVar::new("xp", ChcSort::Int);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::and_all([
                    ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(3)),
                    ChcExpr::eq(
                        ChcExpr::var(xp.clone()),
                        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                    ),
                ])),
            ),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(xp)]),
        ));
        problem.add_clause(HornClause::query(ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(3))),
        )));
        problem
    }

    fn accepted_certificate(problem: &ChcProblem) -> Value {
        json!({
            "schema": CHC_QUOTIENT_CERTIFICATE_SCHEMA,
            "schema_version": 1,
            "target_logic": "recursive-lia",
            "result": "safe",
            "problem_sha256": problem.normalized_input_sha256(),
            "quotient": {
                "kind": "finite-predicate-identity",
                "nodes": [
                    {"id": "q.Inv", "predicate": "Inv", "class": "Inv"}
                ],
                "edges": [
                    {
                        "id": "e.init",
                        "clause_index": 0,
                        "source": "entry",
                        "target": "q.Inv",
                        "energy_before": 3,
                        "energy_after": 3
                    },
                    {
                        "id": "e.step",
                        "clause_index": 1,
                        "source": "q.Inv",
                        "target": "q.Inv",
                        "energy_before": 3,
                        "energy_after": 2
                    },
                    {
                        "id": "e.query",
                        "clause_index": 2,
                        "source": "q.Inv",
                        "target": "exit",
                        "energy_before": 2,
                        "energy_after": 2
                    }
                ]
            },
            "concretization": {"kind": "identity-predicate-arguments"},
            "lift": {"kind": "identity-predicate-arguments"},
            "boundary": {
                "kind": "safety-interval",
                "witness_predicate": "Inv",
                "lower": 0,
                "upper": 3
            },
            "trace": {"kind": "identity-trace-equivalence"},
            "proof_energy": {"kind": "natural-descent", "strict": true},
            "obligations": [
                {"kind": "quotient-map-total", "status": "accepted"},
                {"kind": "lift-total", "status": "accepted"},
                {"kind": "boundary-witness", "status": "accepted"},
                {"kind": "trace-equivalence", "status": "accepted"},
                {"kind": "energy-descent", "status": "accepted"},
                {"kind": "safety-preservation", "status": "accepted"}
            ]
        })
    }

    #[test]
    fn structurally_validates_identity_recursive_lia_certificate() {
        let problem = recursive_lia_problem();
        let report = check_recursive_lia_quotient_value(&problem, &accepted_certificate(&problem));

        assert!(report.structurally_valid(), "{:?}", report.reject_reasons);
        assert!(!report.accepted());
        assert_eq!(report.quotient_nodes, 1);
        assert_eq!(report.quotient_edges, 3);
        assert_eq!(report.obligations_checked, 6);
        assert_eq!(report.to_json_value()["structurally_valid"], json!(true));
        assert_eq!(report.to_json_value()["accepted"], json!(false));
        assert_eq!(report.to_json_value()["promotion_allowed"], json!(false));
    }

    #[test]
    fn parsed_minimal_recursive_lia_identity_certificate_is_structural_only() {
        let problem = parsed_minimal_recursive_lia_problem();

        assert_eq!(problem.predicates().len(), 1);
        assert_eq!(problem.clauses().len(), 3);

        let report = check_recursive_lia_quotient_value(&problem, &accepted_certificate(&problem));

        assert_eq!(report.verdict, QuotientCheckVerdict::StructurallyValid);
        assert!(report.structurally_valid());
        assert!(!report.accepted());
        assert!(
            report.reject_reasons.is_empty(),
            "{:?}",
            report.reject_reasons
        );
        assert_eq!(report.problem_sha256, problem.normalized_input_sha256());
        assert_eq!(
            report.certificate_schema.as_deref(),
            Some(CHC_QUOTIENT_CERTIFICATE_SCHEMA)
        );
        assert_eq!(report.certificate_result.as_deref(), Some("safe"));
        assert_eq!(report.quotient_nodes, 1);
        assert_eq!(report.quotient_edges, 3);
        assert_eq!(report.obligations_checked, REQUIRED_SAFE_OBLIGATIONS.len());
        assert_eq!(report.to_json_value()["accepted"], json!(false));
    }

    #[test]
    fn parsed_minimal_rejects_malformed_certificate_json() {
        let problem = parsed_minimal_recursive_lia_problem();
        let report = check_recursive_lia_quotient_certificate(
            &problem,
            r#"{"schema":"quotient-certificate-v1""#,
        );

        assert_eq!(report.verdict, QuotientCheckVerdict::Rejected);
        assert!(!report.structurally_valid());
        assert!(!report.accepted());
        assert_eq!(report.quotient_nodes, 0);
        assert_eq!(report.quotient_edges, 0);
        assert_eq!(report.obligations_checked, 0);
        assert!(report
            .reject_reasons
            .iter()
            .any(|reason| reason.contains("certificate JSON parse failed")));
    }

    #[test]
    fn parsed_minimal_rejects_nonmatching_certificate_edge() {
        let problem = parsed_minimal_recursive_lia_problem();
        let mut cert = accepted_certificate(&problem);
        cert["quotient"]["edges"][1]["source"] = json!("entry");

        let report = check_recursive_lia_quotient_value(&problem, &cert);

        assert_eq!(report.verdict, QuotientCheckVerdict::Rejected);
        assert!(!report.structurally_valid());
        assert!(!report.accepted());
        assert!(report
            .reject_reasons
            .iter()
            .any(|reason| reason.contains("clause 1 quotient edge source=\"entry\"")));
    }

    #[test]
    fn rejects_stale_problem_hash() {
        let problem = recursive_lia_problem();
        let mut cert = accepted_certificate(&problem);
        cert["problem_sha256"] =
            json!("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");

        let report = check_recursive_lia_quotient_value(&problem, &cert);

        assert!(!report.accepted());
        assert!(report
            .reject_reasons
            .iter()
            .any(|reason| reason.contains("does not match normalized input")));
    }

    #[test]
    fn rejects_unchecked_obligation() {
        let problem = recursive_lia_problem();
        let mut cert = accepted_certificate(&problem);
        cert["obligations"][3]["status"] = json!("unchecked");

        let report = check_recursive_lia_quotient_value(&problem, &cert);

        assert!(!report.accepted());
        assert!(report
            .reject_reasons
            .iter()
            .any(|reason| reason.contains("only accepted obligations are replayable")));
    }

    #[test]
    fn rejects_unknown_accepted_obligation_kind() {
        let problem = recursive_lia_problem();
        let mut cert = accepted_certificate(&problem);
        cert["obligations"]
            .as_array_mut()
            .expect("obligations array")
            .push(json!({"kind": "magic-proof", "status": "accepted"}));

        let report = check_recursive_lia_quotient_value(&problem, &cert);

        assert_eq!(report.verdict, QuotientCheckVerdict::Rejected);
        assert!(!report.accepted());
        assert_eq!(report.obligations_checked, REQUIRED_SAFE_OBLIGATIONS.len());
        assert!(report.reject_reasons.iter().any(|reason| {
            reason.contains("obligation \"magic-proof\" is not supported for result \"safe\"")
        }));
    }

    #[test]
    fn rejects_duplicate_obligation_kind() {
        let problem = recursive_lia_problem();
        let mut cert = accepted_certificate(&problem);
        cert["obligations"]
            .as_array_mut()
            .expect("obligations array")
            .push(json!({"kind": "lift-total", "status": "accepted"}));

        let report = check_recursive_lia_quotient_value(&problem, &cert);

        assert_eq!(report.verdict, QuotientCheckVerdict::Rejected);
        assert!(!report.accepted());
        assert_eq!(report.obligations_checked, REQUIRED_SAFE_OBLIGATIONS.len());
        assert!(report
            .reject_reasons
            .iter()
            .any(|reason| reason.contains("duplicate obligation \"lift-total\"")));
    }

    #[test]
    fn rejects_non_recursive_problem() {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(x)]),
        ));
        let cert = accepted_certificate(&recursive_lia_problem());

        let report = check_recursive_lia_quotient_value(&problem, &cert);

        assert!(!report.accepted());
        assert!(report
            .reject_reasons
            .iter()
            .any(|reason| reason.contains("no recursive predicate dependency cycle")));
    }

    #[test]
    fn rejects_non_lia_predicate_sort() {
        let mut problem = recursive_lia_problem();
        problem.declare_predicate("Bv", vec![ChcSort::BitVec(8)]);
        let cert = accepted_certificate(&problem);

        let report = check_recursive_lia_quotient_value(&problem, &cert);

        assert!(!report.accepted());
        assert!(report
            .reject_reasons
            .iter()
            .any(|reason| reason.contains("only Int is supported")));
    }
}
