// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use serde::{Deserialize, Serialize};

use super::{Inventory, InventoryDocument, NamedContract, RequestContract, SemanticExpectation};

/// A complete unresolved acceptance plan, with the original contracts retained.
#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct AcceptancePlan {
    pub inventory_sha256: String,
    pub document: InventoryDocument,
    pub requests: Vec<PlannedRequest>,
    pub promotable_for_ask_closure: bool,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct PlannedRequest {
    pub contract: RequestContract,
    pub resolved_status: String,
    pub resource_policy_ids: Vec<String>,
    pub consumer_unit_ids: Vec<String>,
    pub dataset_ids: Vec<String>,
    pub performance_contract_ids: Vec<String>,
    pub routes: Vec<RouteObligation>,
    pub blockers: Vec<PlanBlocker>,
}

/// Preserves an original route without claiming that a diagnostic qualifies it.
#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct RouteObligation {
    pub contract: NamedContract,
    pub evidence_qualified: bool,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct PlanBlocker {
    pub kind: BlockerKind,
    pub subject: String,
    pub detail: String,
}

#[derive(Debug, Clone, Copy, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum BlockerKind {
    DeclaredInventoryBlocker,
    RouteEvidenceMissing,
    InputIdentityMissing,
    ArchiveAdapterMissing,
    TypedInputReconstructionMissing,
    SolverInvocationAbsent,
    OracleUnresolved,
    PreparedConsumerExportMissing,
    BudgetBindingMissing,
    DatasetExecutionBindingMissing,
    PerformanceEvidenceMissing,
}

pub(super) fn plan(inventory: &Inventory) -> AcceptancePlan {
    let document = &inventory.document;
    let requests = document
        .request_inventory
        .iter()
        .map(|request| plan_request(document, request))
        .collect();
    AcceptancePlan {
        inventory_sha256: inventory.sha256.clone(),
        document: document.clone(),
        requests,
        promotable_for_ask_closure: false,
    }
}

fn plan_request(document: &InventoryDocument, request: &RequestContract) -> PlannedRequest {
    let mut blockers = declared_blockers(document, request);
    let routes = document
        .routes
        .iter()
        .filter(|route| request.required_routes.contains(&route.id))
        .map(|route| {
            add_blocker(
                &mut blockers,
                BlockerKind::RouteEvidenceMissing,
                &route.id,
                "Original route has no current qualified execution evidence; whole-HORN diagnostics cannot discharge it.",
            );
            RouteObligation { contract: route.clone(), evidence_qualified: false }
        })
        .collect();
    input_blockers(document, request, &mut blockers);
    let consumer_unit_ids: Vec<_> = document
        .consumer_units
        .iter()
        .filter(|unit| unit.request_ids.contains(&request.id))
        .map(|unit| unit.id.clone())
        .collect();
    if request
        .required_routes
        .iter()
        .any(|route| route.contains("consumer"))
    {
        add_blocker(
            &mut blockers,
            BlockerKind::PreparedConsumerExportMissing,
            &request.id,
            "Current qualified source/property-bound post-transform input, VC mapping, row grant and proof evidence are required; historical exports and whole-HORN bytes are insufficient.",
        );
    }
    if request.harness_or_solve_budget_ms.is_none() {
        add_blocker(&mut blockers, BlockerKind::BudgetBindingMissing, &request.id,
            "This request needs a route-specific bounded invocation; no solver timeout is inferred.");
    }
    let dataset_ids: Vec<String> = request
        .dataset_ids()
        .into_iter()
        .map(str::to_owned)
        .collect();
    for id in &dataset_ids {
        add_blocker(&mut blockers, BlockerKind::DatasetExecutionBindingMissing, id,
            "Frozen dataset reference is preserved; exact runnable membership and current evidence remain required.");
    }
    let performance_contract_ids = document.performance_contracts.targets.iter()
        .filter(|target| target.request_ids.contains(&request.id))
        .map(|target| {
            add_blocker(&mut blockers, BlockerKind::PerformanceEvidenceMissing, &target.id,
                "Frozen matched-pair contract is preserved; unavailable reference, censored run or absent current measurement remains open.");
            target.id.clone()
        }).collect();
    PlannedRequest {
        contract: request.clone(),
        resolved_status: request.resolved_status(&document.case_defaults).to_owned(),
        resource_policy_ids: request
            .resource_policy_ids(&document.case_defaults)
            .into_iter()
            .map(str::to_owned)
            .collect(),
        consumer_unit_ids,
        dataset_ids,
        performance_contract_ids,
        routes,
        blockers,
    }
}

fn declared_blockers(document: &InventoryDocument, request: &RequestContract) -> Vec<PlanBlocker> {
    document
        .blockers
        .iter()
        .filter(|blocker| blocker.request_ids.contains(&request.id))
        .map(|blocker| PlanBlocker {
            kind: BlockerKind::DeclaredInventoryBlocker,
            subject: blocker.id.clone(),
            detail: blocker.reason.clone(),
        })
        .collect()
}

fn input_blockers(
    document: &InventoryDocument,
    request: &RequestContract,
    blockers: &mut Vec<PlanBlocker>,
) {
    for input in document
        .stored_inputs
        .iter()
        .filter(|input| request.stored_input_ids.contains(&input.id))
    {
        if input.sha256.is_none()
            || input.size_bytes.is_none()
            || !(tracked(&input.availability) || super::input::archived(input))
        {
            add_blocker(blockers, BlockerKind::InputIdentityMissing, &input.id,
                "Required original bytes, full digest and size are not all available; no passing skip.");
        }
        if super::input::archived(input) {
            add_blocker(blockers, BlockerKind::ArchiveAdapterMissing, &input.id,
                "Container and member identities are retained; no authenticated bounded archive-to-private-input adapter has run. The archive itself is not an SMT input.");
        }
        if matches!(
            input.kind.as_deref(),
            Some("prepared-chc-normalized" | "typed-constraint-normalized")
        ) || input
            .metadata
            .get("not_smtlib_parser_input")
            .and_then(serde_json::Value::as_bool)
            == Some(true)
        {
            add_blocker(blockers, BlockerKind::TypedInputReconstructionMissing, &input.id,
                "Exact typed consumer reconstruction, original row grant and checked evidence are required; normalized display text cannot be parsed as standalone SMT.");
        }
        if input.kind.as_deref() == Some("emitted-no-solve-control") {
            add_blocker(blockers, BlockerKind::SolverInvocationAbsent, &input.id,
                "The compiler discharged this control without invoking AY; recorded source safety is not solver coverage.");
        }
        if input.kind.as_deref() != Some("rust-source")
            && SemanticExpectation::from_inventory(&input.expected_semantic_result).is_none()
        {
            add_blocker(
                blockers,
                BlockerKind::OracleUnresolved,
                &input.id,
                "Consumer oracle must be bound to the exact exported property before scoring.",
            );
        }
    }
}

pub(super) fn tracked(availability: &str) -> bool {
    matches!(availability, "tracked" | "tracked AY regression fixture")
}

fn add_blocker(blockers: &mut Vec<PlanBlocker>, kind: BlockerKind, subject: &str, detail: &str) {
    blockers.push(PlanBlocker {
        kind,
        subject: subject.to_owned(),
        detail: detail.to_owned(),
    });
}
