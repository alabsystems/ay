// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
//! VeriPB v3 proof logging support.

mod cert;
mod context;
mod drat_lift;
mod koops;
mod optimum_check;
mod refutation_check;
mod reified_encoding;
mod route_budget;
mod steps;
pub(crate) mod tap;
mod veripb;

pub use self::cert::{
    certify_decision_unsat, certify_decision_unsat_interruptible,
    certify_opt_lin_any_interruptible, certify_opt_lin_bounds, certify_opt_lin_bounds_compact,
    certify_opt_lin_bounds_compact_interruptible, certify_opt_lin_bounds_interruptible,
    certify_opt_lin_bounds_pb, certify_opt_lin_bounds_pb_interruptible,
    certify_opt_lin_clique_coloring, certify_opt_lin_direct_aggregation_floor,
    certify_opt_lin_frustrated_cycle, certify_opt_lin_knapsack_cardinality,
    certify_opt_lin_lp_dual_floor, certify_opt_lin_trivial_zero_floor, lp_dual_floor_diagnosis,
    solution_only_sat_proof, OptLinCertRoute,
};
pub use self::drat_lift::{emit_decision_unsat_proof, parse_aux_free_drat};
#[cfg(test)]
pub(crate) use self::optimum_check::FLOOR_CERT_CALLS;
pub use self::optimum_check::{
    build_aggregation_floor_cert, build_covering_floor_cert, build_equality_affine_floor_cert,
    build_equality_affine_floor_cert_interruptible, certified_objective_floor,
    certified_objective_floor_interruptible, ObjectiveBound, OptError,
};
pub use self::refutation_check::{
    pb_eq_halves, pb_ge, LinConstraint, RefError, RefStep, Refutation,
};
pub use self::route_budget::CertRouteBudget;

pub use self::context::{
    FailClosedReason, InputRowIds, ObjectiveProofState, ProofConclusionState, ProofContext,
    ProofContextError, ProofContextResult, SourceRelation, SourceRelationProofMarker,
    SourceRelationProofSupport,
};
pub use self::koops::{
    emit_koops_identity_complement_red_capacity_proof,
    emit_koops_mat12_11_identity_complement_red_capacity_proof,
    KoopsIdentityComplementRedCapacityParams,
    KOOPS_MAT10_9_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS,
    KOOPS_MAT12_11_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS,
    KOOPS_MAT16_15_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS,
    KOOPS_MAT20_19_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS,
    KOOPS_MAT98_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS,
};
pub use self::reified_encoding::{
    emit_sinz_aux_introductions, encode_sinz_cardinality, encode_sinz_weighted,
    SinzCardinalityEncoding,
};
pub use self::steps::{ConstraintId, ProofStep};
pub use self::tap::ProofTapStats;
pub use self::veripb::{
    format_constraint, format_cp_constraint, format_lit, veripb_input_constraint_count,
    veripb_input_row_ids, ProofConclusionKind, ProofError, Result, VeriPbWriter,
};

#[cfg(test)]
mod tests {
    use super::{format_constraint, format_lit, ConstraintId, ProofStep, VeriPbWriter};
    use crate::PbLit;

    fn lit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }

    #[test]
    fn test_reexports_support_step_logging() {
        let mut writer =
            VeriPbWriter::new(Vec::new(), 2).expect("header writes to an in-memory buffer");

        let new_id = writer
            .log_step(ProofStep::Addition(
                ConstraintId::new(1).expect("proof IDs are 1-indexed"),
                ConstraintId::new(2).expect("proof IDs are 1-indexed"),
            ))
            .expect("addition allocates the next derived ID");

        assert_eq!(new_id.get(), 3);
        assert_eq!(
            String::from_utf8(writer.writer).expect("proof output is valid UTF-8"),
            "pseudo-Boolean proof version 3.0\nf 2 ;\npol 1 2 + ;\n",
        );
    }

    #[test]
    fn test_reexports_expose_format_helpers() {
        let formatted = format_constraint(&[(lit(1), 3), (lit(2), -2)], 4);

        assert_eq!(format_lit(lit(1)), "x1");
        assert_eq!(
            format_lit(PbLit {
                var: 2,
                negated: true,
            }),
            "~x2",
        );
        assert_eq!(formatted, "+3 x1 -2 x2 >= 4 ;");
    }
}
