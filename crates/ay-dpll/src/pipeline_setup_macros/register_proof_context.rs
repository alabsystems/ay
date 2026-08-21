// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by pipeline_setup_macros to preserve item paths.

macro_rules! pipeline_register_proof_context {
    ($self:expr, $proof_enabled:expr, $tag:expr) => {{
        let problem_assertions = $self.proof_problem_assertions();
        pipeline_register_proof_context!(
            $self,
            $proof_enabled,
            $tag,
            problem_assertions: problem_assertions
        );
    }};
    ($self:expr, $proof_enabled:expr, $tag:expr, problem_assertions: $problem_assertions:expr) => {{
        pipeline_register_proof_context!(
            $self,
            $proof_enabled,
            $tag,
            problem_assertions: $problem_assertions,
            assumptions: &[]
        );
    }};
    ($self:expr, $proof_enabled:expr, $tag:expr,
     problem_assertions: $problem_assertions:expr, assumptions: $assumptions:expr) => {{
        // Read disjoint immutable self-fields into a Copy bool / owned Vec
        // BEFORE taking the &mut proof_tracker borrow (avoids E0502).
        let __prpc_has_provenance = $self.proof_problem_assertion_provenance.is_some();
        let __prpc_problem_assertions: Vec<ay_core::TermId> = $problem_assertions;
        let __prpc_assumptions: &[(ay_core::TermId, ay_core::TermId)] = $assumptions;
        // &mut $self.proof_tracker and &$self.ctx.assertions are DISJOINT fields,
        // so this simultaneous borrow is accepted by the borrow checker.
        $crate::pipeline_fns::register_proof_context(
            &mut $self.proof_tracker,
            $proof_enabled,
            $tag,
            __prpc_has_provenance,
            &$self.ctx.assertions,
            __prpc_problem_assertions,
            __prpc_assumptions,
        );
    }};
}
