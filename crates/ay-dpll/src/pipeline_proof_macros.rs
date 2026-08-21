// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Shared proof-recording expressions for the DPLL(T) pipeline macros.
//
// Keeping the datatype registry view next to the registry-aware recorder
// avoids repeating its temporary-borrow plumbing in every pipeline arm.

macro_rules! dt_conflict_proof {
    ($self:ident, $negations:ident, $conflict:expr, $dt_data:expr) => {
        $crate::theory_inference::record_theory_conflict_unsat_with_annotation_and_dt(
            &mut $self.proof_tracker,
            Some(&$self.ctx.terms),
            $negations.as_map(),
            $conflict,
            ($dt_data)
                .as_ref()
                .map($crate::theory_inference::DatatypeRegistries::from_data)
                .as_ref(),
        )
        .1
    };
}

macro_rules! dt_farkas_proof {
    ($self:ident, $negations:ident, $conflict:expr, $dt_data:expr) => {
        $crate::theory_inference::record_theory_conflict_unsat_with_farkas_and_annotation_and_dt(
            &mut $self.proof_tracker,
            Some(&$self.ctx.terms),
            $negations.as_map(),
            $conflict,
            ($dt_data)
                .as_ref()
                .map($crate::theory_inference::DatatypeRegistries::from_data)
                .as_ref(),
        )
        .1
    };
}
