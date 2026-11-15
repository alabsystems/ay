// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Deterministic composite identity for source query-obligation sets.

use std::collections::{BTreeSet, HashSet};

use ay_chc::{ChcProofArtifactDigest, ChcPrunedQueryObligationId, ChcQueryObligationId};

use super::CHC_QUERY_OBLIGATION_SET_SCHEMA;

pub(super) struct ObligationSetIdentity {
    pub(super) content: String,
    pub(super) sha256: String,
}

pub(crate) fn source_order_is_complete<'a>(
    pruned_ids: &[ChcPrunedQueryObligationId],
    active_ids: impl IntoIterator<Item = &'a ChcQueryObligationId>,
) -> bool {
    if pruned_ids.iter().any(|id| !id.has_valid_content_digest())
        || pruned_ids
            .windows(2)
            .any(|pair| pair[0].ordinal() >= pair[1].ordinal())
    {
        return false;
    }
    let active_ids: Vec<_> = active_ids.into_iter().collect();
    let mut seen_active = HashSet::new();
    if active_ids.iter().any(|id| !seen_active.insert(*id)) {
        return false;
    }
    let active_ordinals: Vec<_> = active_ids
        .into_iter()
        .map(ChcQueryObligationId::source_query_ordinal)
        .collect();
    if active_ordinals.windows(2).any(|pair| pair[0] > pair[1]) {
        return false;
    }
    let pruned_ordinals: BTreeSet<_> = pruned_ids.iter().map(|id| id.ordinal()).collect();
    if active_ordinals
        .iter()
        .any(|ordinal| pruned_ordinals.contains(ordinal))
    {
        return false;
    }
    let all_ordinals: BTreeSet<_> = pruned_ordinals.into_iter().chain(active_ordinals).collect();
    all_ordinals
        .iter()
        .enumerate()
        .all(|(expected, actual)| expected == *actual)
}

pub(super) fn obligation_set_identity(
    source_normalized_input_schema: &str,
    source_normalized_input_sha256: &str,
    source_normalized_input_bytes: u64,
    pruned_ids: &[ChcPrunedQueryObligationId],
    source_has_stripped_body_forall: bool,
    ids: &[ChcQueryObligationId],
) -> ObligationSetIdentity {
    let mut identity = String::new();
    identity.push_str(CHC_QUERY_OBLIGATION_SET_SCHEMA);
    identity.push('\n');
    identity.push_str(&format!(
        "source_schema={}\n",
        serde_json::Value::String(source_normalized_input_schema.to_string())
    ));
    identity.push_str(&format!("source_sha256={source_normalized_input_sha256}\n"));
    identity.push_str(&format!("source_bytes={source_normalized_input_bytes}\n"));
    identity.push_str(&format!(
        "source_pruned_false_query_count={}\n",
        pruned_ids.len()
    ));
    for (ordinal, id) in pruned_ids.iter().enumerate() {
        identity.push_str(&format!("pruned[{ordinal}].ordinal={}\n", id.ordinal()));
        identity.push_str(&format!(
            "pruned[{ordinal}].content_schema={}\n",
            serde_json::Value::String(id.content_schema().to_string())
        ));
        identity.push_str(&format!(
            "pruned[{ordinal}].content_bytes={}\n",
            id.content_bytes().len()
        ));
        identity.push_str(&format!(
            "pruned[{ordinal}].content_sha256={}\n",
            id.content_sha256()
        ));
    }
    identity.push_str(&format!(
        "source_has_stripped_body_forall={source_has_stripped_body_forall}\n"
    ));
    identity.push_str(&format!("count={}\n", ids.len()));
    for (ordinal, id) in ids.iter().enumerate() {
        identity.push_str(&format!(
            "row[{ordinal}].source_query_ordinal={}\n",
            id.source_query_ordinal()
        ));
        identity.push_str(&format!(
            "row[{ordinal}].query_clause_index={}\n",
            id.query_clause_index()
        ));
        identity.push_str(&format!(
            "row[{ordinal}].defining_clause_index={}\n",
            id.defining_clause_index()
                .map_or_else(|| "none".to_string(), |index| index.to_string())
        ));
        identity.push_str(&format!(
            "row[{ordinal}].label={}\n",
            serde_json::Value::String(id.label().to_string())
        ));
        identity.push_str(&format!(
            "row[{ordinal}].content_sha256={}\n",
            id.content_sha256()
        ));
    }
    let sha256 =
        ChcProofArtifactDigest::from_bytes("query-obligation-set", identity.as_bytes()).sha256;
    ObligationSetIdentity {
        content: identity,
        sha256,
    }
}

pub(crate) fn obligation_set_sha256(
    source_normalized_input_schema: &str,
    source_normalized_input_sha256: &str,
    source_normalized_input_bytes: u64,
    pruned_ids: &[ChcPrunedQueryObligationId],
    source_has_stripped_body_forall: bool,
    ids: &[ChcQueryObligationId],
) -> String {
    obligation_set_identity(
        source_normalized_input_schema,
        source_normalized_input_sha256,
        source_normalized_input_bytes,
        pruned_ids,
        source_has_stripped_body_forall,
        ids,
    )
    .sha256
}
