// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Formula-adaptation explanations for startup capability decisions.

use crate::features::{InstanceClass, SatFeatures};

pub(super) fn adaptive_reason(
    capability: &str,
    features: &SatFeatures,
    instance_class: InstanceClass,
) -> String {
    match capability {
        "condition" => format!("clause_var_ratio={:.3} > 100", features.clause_var_ratio),
        "symmetry" | "backbone"
            if matches!(
                instance_class,
                InstanceClass::Random3Sat | InstanceClass::RandomKSat
            ) =>
        {
            format!("class={instance_class:?}")
        }
        "symmetry" => format!(
            "class={instance_class:?} num_vars={} < 4096",
            features.num_vars
        ),
        "reorder" => format!("class={instance_class:?} num_vars={}", features.num_vars),
        _ => format!("instance adaptation class={instance_class:?}"),
    }
}
