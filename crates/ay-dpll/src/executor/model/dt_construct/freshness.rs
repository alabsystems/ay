// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extensional identity for W6 free-datatype candidate selection.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_model_check::ModelValue;

use super::super::datatype_array_fields::{
    normalize_datatype_array_value, NormalizedDatatypeArrayValue, SemanticNormalizationBudget,
};
use super::super::rendered_dt_limits::{MAX_RENDERED_DT_DEPTH, MAX_RENDERED_DT_NODES};

#[derive(Eq, Hash, PartialEq)]
enum FreeDatatypeIdentity {
    /// The existing identity remains authoritative outside the concrete W6
    /// datatype-with-scalar-array fragment.
    Canonical(String),
    /// Array stores have representation history: shadowed or default-valued
    /// writes do not make a second extensional value.
    ArraySemantic(NormalizedDatatypeArrayValue),
}

pub(super) struct FreeDatatypeFreshness {
    used: HashSet<FreeDatatypeIdentity>,
    semantic_budget: SemanticNormalizationBudget,
}

impl FreeDatatypeFreshness {
    pub(super) fn new() -> Self {
        Self {
            used: HashSet::default(),
            semantic_budget: SemanticNormalizationBudget::new(),
        }
    }

    pub(super) fn len(&self) -> usize {
        self.used.len()
    }

    /// Retain one already-constructed disequality neighbor. `None` means the
    /// bounded array-semantic identity could not be established, so candidate
    /// construction must fail closed and leave validation to return Unknown.
    pub(super) fn record(&mut self, value: &ModelValue, canonical: &str) -> Option<bool> {
        let identity = self.identity(value, canonical)?;
        Some(self.used.insert(identity))
    }

    /// Check one fully finished candidate without retaining its identity.
    pub(super) fn is_fresh(&mut self, value: &ModelValue, canonical: &str) -> Option<bool> {
        let identity = self.identity(value, canonical)?;
        Some(!self.used.contains(&identity))
    }

    fn identity(&mut self, value: &ModelValue, canonical: &str) -> Option<FreeDatatypeIdentity> {
        if bounded_value_contains_array(value)? {
            normalize_datatype_array_value(value, &mut self.semantic_budget)
                .map(FreeDatatypeIdentity::ArraySemantic)
        } else {
            Some(FreeDatatypeIdentity::Canonical(canonical.to_owned()))
        }
    }
}

/// Bound the borrowed discovery walk before semantic normalization allocates.
/// Once an array is found, `normalize_datatype_array_value` performs its own
/// complete node/payload preflight over the value.
fn bounded_value_contains_array(root: &ModelValue) -> Option<bool> {
    let mut stack = vec![(root, 0usize)];
    let mut nodes = 0usize;
    while let Some((value, depth)) = stack.pop() {
        nodes = nodes.checked_add(1)?;
        if nodes > MAX_RENDERED_DT_NODES || depth > MAX_RENDERED_DT_DEPTH {
            return None;
        }
        match value {
            ModelValue::Array(_) => return Some(true),
            ModelValue::Datatype { args, .. } => {
                if stack
                    .len()
                    .checked_add(args.len())
                    .is_none_or(|pending| pending > MAX_RENDERED_DT_NODES.saturating_sub(nodes))
                {
                    return None;
                }
                stack.extend(args.iter().map(|arg| (arg, depth + 1)));
            }
            ModelValue::Seq(elements) => {
                if stack
                    .len()
                    .checked_add(elements.len())
                    .is_none_or(|pending| pending > MAX_RENDERED_DT_NODES.saturating_sub(nodes))
                {
                    return None;
                }
                stack.extend(elements.iter().map(|element| (element, depth + 1)));
            }
            _ => {}
        }
    }
    Some(false)
}

#[cfg(test)]
mod tests {
    use super::super::super::rendered_dt_limits::MAX_RENDERED_DT_BYTES;
    use super::*;
    use ay_model_check::ArrayValue;

    fn cell(array: ArrayValue) -> ModelValue {
        ModelValue::Datatype {
            ctor: "mk".to_string(),
            args: vec![ModelValue::Array(Box::new(array))],
        }
    }

    #[test]
    fn redundant_default_store_is_not_fresh() {
        let canonical = cell(ArrayValue {
            default: ModelValue::Bool(false),
            store: Vec::new(),
        });
        let redundant = cell(ArrayValue {
            default: ModelValue::Bool(false),
            store: vec![(ModelValue::Bool(false), ModelValue::Bool(false))],
        });
        let changed = cell(ArrayValue {
            default: ModelValue::Bool(false),
            store: vec![(ModelValue::Bool(false), ModelValue::Bool(true))],
        });
        let mut freshness = FreeDatatypeFreshness::new();
        assert_eq!(freshness.record(&redundant, "redundant"), Some(true));
        assert_eq!(freshness.is_fresh(&canonical, "canonical"), Some(false));
        assert_eq!(freshness.is_fresh(&changed, "changed"), Some(true));
    }

    #[test]
    fn aggregate_semantic_normalization_budget_fails_closed() {
        let large = cell(ArrayValue {
            default: ModelValue::Str("x".repeat(MAX_RENDERED_DT_BYTES / 2)),
            store: Vec::new(),
        });
        let mut freshness = FreeDatatypeFreshness::new();
        for _ in 0..7 {
            assert!(freshness.record(&large, "unused").is_some());
        }
        assert_eq!(freshness.record(&large, "unused"), None);
    }
}
