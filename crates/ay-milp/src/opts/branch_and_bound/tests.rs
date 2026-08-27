// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Construction and profile-lowering tests for branch-and-bound options.

use super::*;

type RealBuilder = fn(EngineEconomics, f64) -> Result<EngineEconomics, EngineConfigError>;

fn assert_unit_share_builder(knob: Knob, builder: RealBuilder) {
    for value in [0.0, 1.0] {
        let engine = builder(EngineEconomics::new(), value).expect("unit boundary is valid");
        let _active = crate::tune::activate_caller(engine.profile());
        assert_eq!(crate::tune::real_opt(knob), Some(value));
    }
    for value in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY, -0.01, 1.01] {
        assert!(
            builder(EngineEconomics::new(), value).is_err(),
            "{} accepted {value}",
            knob.label()
        );
    }
}

#[test]
fn deadline_share_builders_accept_only_finite_unit_intervals() {
    for (knob, builder) in [
        (
            Knob::HeurShare,
            EngineEconomics::with_heur_share as RealBuilder,
        ),
        (Knob::PumpShare, EngineEconomics::with_pump_share),
        (Knob::RootProbeShare, EngineEconomics::with_root_probe_share),
    ] {
        assert_unit_share_builder(knob, builder);
    }
}

#[test]
fn certificate_grace_builder_checks_seconds_domain_boundaries() {
    for value in [0.0, MAX_KNOB_SECS] {
        let engine = EngineEconomics::new()
            .with_cert_grace_secs(value)
            .expect("seconds boundary is valid");
        let _active = crate::tune::activate_caller(engine.profile());
        assert_eq!(crate::tune::real_opt(Knob::CertGraceSecs), Some(value));
    }
    for value in [
        f64::NAN,
        f64::INFINITY,
        f64::NEG_INFINITY,
        -0.01,
        MAX_KNOB_SECS * 2.0,
    ] {
        assert!(
            EngineEconomics::new().with_cert_grace_secs(value).is_err(),
            "certificate grace accepted {value}"
        );
    }
}

#[test]
fn b13_switches_reach_the_profile_with_the_single_inversion() {
    use crate::tune::Knob;
    // B13 spot checks: one of each carrier shape in the bab layer, plus
    // the one dual-role builder (odd-cycle force vs disable are distinct
    // knobs behind one positive-sense builder).
    let engine = EngineEconomics::default()
        .with_clique(false)
        .with_odd_cycle(true)
        .with_submip_best_bound(true)
        .with_prop_sweeps(11)
        .with_splns_stall_secs(2.5)
        .expect("finite non-negative stall")
        .with_fc_mode(2)
        .expect("mode 2 in domain");
    let _active = crate::tune::activate_caller(engine.profile());
    assert!(crate::tune::on(Knob::NoClique));
    assert!(crate::tune::on(Knob::OddCycle));
    assert!(!crate::tune::on(Knob::NoOddCycle));
    assert!(crate::tune::on(Knob::SubmipBb));
    assert_eq!(crate::tune::count(Knob::PropSweeps, 3), 11);
    assert_eq!(crate::tune::real_opt(Knob::SplnsStall), Some(2.5));
    assert_eq!(crate::tune::count_opt(Knob::FcMode), Some(2));
    assert!(EngineEconomics::default().with_fc_mode(4).is_err());
    assert!(!EngineEconomics::default()
        .with_odd_cycle(false)
        .profile()
        .is_empty());
    // And the env layer is not a party to these knobs at all.
    for knob in [Knob::NoClique, Knob::FcMode] {
        assert_eq!(knob.env(), None, "{knob:?} must have no env spelling");
    }
}
