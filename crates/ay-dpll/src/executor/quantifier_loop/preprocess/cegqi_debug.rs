// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Debug rendering for CEGQI setup decisions.

use ay_core::{TermId, TermStore};

pub(super) fn setup_diagnostic(terms: &TermStore, quantifier: TermId) -> Option<String> {
    ay_core::misc_cli_flags().debug_cert.then(|| {
        format!(
            "CEGQI/setup quant={} no_mbqi={} render={}",
            quantifier.index(),
            terms.is_no_mbqi(quantifier),
            ay_proof::render_term_canonical(terms, quantifier)
        )
    })
}
