// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sparse-polynomial GCD and diagnostic checks.

use super::*;

// ---------------------------------------------------------------------------
// 3. GCD
// ---------------------------------------------------------------------------

/// Shared body of the two GCD checks: `which` selects the PRS or the modular
/// implementation, and the modular one additionally has to agree with the PRS.
fn gcd_body(z3: &Z3, g: &GenPm, sab: Sabotage, algorithm: GcdAlgorithm) -> Outcome {
    let name = algorithm.name();
    let mut manager = OPolyMgr::new();
    let planted = manager.mk(&g.g_terms);
    let a = manager.mk(&g.a_terms);
    let b = manager.mk(&g.b_terms);
    if manager.is_zero(&planted) || manager.is_zero(&a) || manager.is_zero(&b) {
        return Outcome::Skipped("degenerate factor");
    }
    let u = manager.mul(&planted, &a);
    let v = manager.mul(&planted, &b);
    if manager.is_zero(&u) || manager.is_zero(&v) {
        return Outcome::Skipped("degenerate product");
    }
    let Some(prs) = manager.gcd_via_prs(&u, &v) else {
        return Outcome::Declined("prs gcd refused");
    };
    let mut answer = match algorithm {
        GcdAlgorithm::Prs => prs.clone(),
        GcdAlgorithm::Modular => match manager.mod_gcd(&u, &v) {
            Some(value) => value,
            None => return Outcome::Declined("modular gcd could not certify a candidate"),
        },
    };
    if sab.on() {
        let factor = saboteur(&mut manager);
        answer = manager.mul(&answer, &factor);
    }
    let case = GcdCase {
        name,
        planted: &planted,
        u: &u,
        v: &v,
        prs: &prs,
        answer: &answer,
    };
    let mut comparisons = 0;
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_algorithm_agreement(&manager, algorithm, &case),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_divisor_sandwich(&mut manager, &case),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_gcd_roots(z3, g, &mut manager, &case),
    ) {
        return outcome;
    }
    Outcome::Match(comparisons)
}

#[derive(Clone, Copy)]
enum GcdAlgorithm {
    Prs,
    Modular,
}

impl GcdAlgorithm {
    fn name(self) -> &'static str {
        match self {
            Self::Prs => "pm-gcd",
            Self::Modular => "pm-mod-gcd",
        }
    }
}

struct GcdCase<'a> {
    name: &'static str,
    planted: &'a OMgrPoly,
    u: &'a OMgrPoly,
    v: &'a OMgrPoly,
    prs: &'a OMgrPoly,
    answer: &'a OMgrPoly,
}

fn check_algorithm_agreement(
    manager: &OPolyMgr,
    algorithm: GcdAlgorithm,
    case: &GcdCase<'_>,
) -> Outcome {
    if matches!(algorithm, GcdAlgorithm::Prs) {
        return Outcome::Match(0);
    }
    if case.answer != case.prs {
        return Divergence::outcome(
            case.name,
            "identity",
            "modular gcd disagrees with the subresultant PRS gcd".to_string(),
            vec![
                ("u".to_string(), render(manager, case.u)),
                ("v".to_string(), render(manager, case.v)),
                ("prs".to_string(), render(manager, case.prs)),
                ("modular".to_string(), render(manager, case.answer)),
            ],
        );
    }
    Outcome::Match(1)
}

fn check_divisor_sandwich(manager: &mut OPolyMgr, case: &GcdCase<'_>) -> Outcome {
    if !manager.divides(case.answer, case.u) {
        return gcd_divergence(manager, case, "the gcd does not divide u");
    }
    if !manager.divides(case.answer, case.v) {
        return gcd_divergence(manager, case, "the gcd does not divide v");
    }
    if !manager.divides(case.planted, case.answer) {
        return Divergence::outcome(
            case.name,
            "identity",
            "the planted common factor does not divide the gcd".to_string(),
            vec![
                ("planted".to_string(), render(manager, case.planted)),
                ("u".to_string(), render(manager, case.u)),
                ("v".to_string(), render(manager, case.v)),
                ("g".to_string(), render(manager, case.answer)),
            ],
        );
    }
    Outcome::Match(3)
}

fn gcd_divergence(manager: &OPolyMgr, case: &GcdCase<'_>, message: &str) -> Outcome {
    Divergence::outcome(
        case.name,
        "identity",
        message.to_string(),
        vec![
            ("u".to_string(), render(manager, case.u)),
            ("v".to_string(), render(manager, case.v)),
            ("g".to_string(), render(manager, case.answer)),
        ],
    )
}

fn check_gcd_roots(z3: &Z3, g: &GenPm, manager: &mut OPolyMgr, case: &GcdCase<'_>) -> Outcome {
    let (Some(u_bar), Some(v_bar), Some(gcd_bar)) = (
        manager.specialize(case.u, X, &g.point),
        manager.specialize(case.v, X, &g.point),
        manager.specialize(case.answer, X, &g.point),
    ) else {
        return Outcome::Skipped("specialization left a variable standing");
    };
    if gcd_bar.len() < 2 || u_bar.is_empty() || v_bar.is_empty() {
        return Outcome::Skipped("specialized gcd has no roots to test");
    }
    let Some(roots) = z3.roots(&to_rationals(&gcd_bar)) else {
        return Outcome::Skipped("z3 declined the specialized gcd");
    };
    let mut comparisons = 0;
    for root in roots {
        for (label, coefficients) in [("u", &u_bar), ("v", &v_bar)] {
            let Some(sign) = z3.eval_sign(&to_rationals(coefficients), root) else {
                return Outcome::Skipped("z3 declined an evaluation");
            };
            comparisons += 1;
            if sign != 0 {
                return Divergence::outcome(
                    case.name,
                    "z3",
                    format!("a real gcd root is not a root of {label} (sign {sign})"),
                    vec![
                        ("u".to_string(), render(manager, case.u)),
                        ("v".to_string(), render(manager, case.v)),
                        ("g".to_string(), render(manager, case.answer)),
                        ("u_bar".to_string(), render_dense(&u_bar)),
                        ("v_bar".to_string(), render_dense(&v_bar)),
                        ("g_bar".to_string(), render_dense(&gcd_bar)),
                    ],
                );
            }
        }
    }
    Outcome::Match(comparisons)
}

/// The subresultant-PRS GCD.
pub(crate) fn check_pm_gcd(z3: &Z3, g: &GenPm, sab: Sabotage) -> Outcome {
    gcd_body(z3, g, sab, GcdAlgorithm::Prs)
}

/// The modular (Brown) GCD, against the PRS GCD and against z3.
pub(crate) fn check_pm_mod_gcd(z3: &Z3, g: &GenPm, sab: Sabotage) -> Outcome {
    gcd_body(z3, g, sab, GcdAlgorithm::Modular)
}

/// The INSTRUMENTED modular GCD: the decline diagnosis, and the `Z_p[x]`
/// content split the recovery step now rests on.
///
/// Three statements, none of which the plain `pm-mod-gcd` check makes:
///
/// 1. **The instrumentation is inert.** `mod_gcd_diag` and `mod_gcd` must
///    return byte-identical answers on the same inputs. The counters are
///    written on every decline path inside the manager, so a counter write
///    that accidentally short-circuited a branch — the obvious way to break a
///    diagnosis harness — changes the answer, and this catches it.
///
/// 2. **The diagnosis matches the outcome.** `certified()` must agree with
///    `is_some()`, and the `primary()` label must say `"certified"` exactly
///    when the call certified. A diagnosis that disagrees with what happened is
///    worse than none, because the fix it points at is chosen from it.
///
/// 3. **The certified answer is MAXIMAL, not merely a divisor.** It must equal
///    the subresultant PRS answer exactly, and the planted common factor must
///    divide it. This is the statement that pins the content split: the
///    recovery step divides the interpolant by its `Z_p[x]` content, and if the
///    matching split at the top of the level were wrong the answer would come
///    back as `G / cont_Y(G)` — a PROPER DIVISOR of the true GCD, which still
///    divides both inputs and would therefore sail through the exact
///    certificate. Only a comparison against an independent implementation, or
///    against the planted factor, can see that. Both are made here.
pub(crate) fn check_pm_mod_gcd_diag(g: &GenPm, sab: Sabotage) -> Outcome {
    let mut manager = OPolyMgr::new();
    let planted = manager.mk(&g.g_terms);
    let a = manager.mk(&g.a_terms);
    let b = manager.mk(&g.b_terms);
    if manager.is_zero(&planted) || manager.is_zero(&a) || manager.is_zero(&b) {
        return Outcome::Skipped("degenerate factor");
    }
    let u = manager.mul(&planted, &a);
    let v = manager.mul(&planted, &b);
    if manager.is_zero(&u) || manager.is_zero(&v) {
        return Outcome::Skipped("degenerate product");
    }
    let plain = manager.mod_gcd(&u, &v);
    let (instrumented, diagnosis) = manager.mod_gcd_diag(&u, &v);
    let case = DiagnosticCase {
        planted: &planted,
        u: &u,
        v: &v,
    };
    let mut comparisons = 0;
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_instrumentation(&manager, &case, &plain, &instrumented),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_diagnosis(&manager, &case, &instrumented, &diagnosis),
    ) {
        return outcome;
    }
    let Some(mut answer) = instrumented else {
        if diagnosis.primary().is_empty() || diagnosis.primary() == "certified" {
            return Divergence::outcome(
                "pm-mod-gcd-diag",
                "identity",
                "a decline carries no decline reason".to_string(),
                diagnostic_inputs(&manager, &case),
            );
        }
        return Outcome::Declined("modular gcd could not certify a candidate");
    };
    if sab.on() {
        let factor = saboteur(&mut manager);
        answer = manager.mul(&answer, &factor);
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_work_counters(&mut manager, sab, &case, &diagnosis),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_diagnostic_maximality(&mut manager, &case, &answer),
    ) {
        return outcome;
    }
    Outcome::Match(comparisons)
}

struct DiagnosticCase<'a> {
    planted: &'a OMgrPoly,
    u: &'a OMgrPoly,
    v: &'a OMgrPoly,
}

fn diagnostic_inputs(manager: &OPolyMgr, case: &DiagnosticCase<'_>) -> Vec<(String, String)> {
    vec![
        ("u".to_string(), render(manager, case.u)),
        ("v".to_string(), render(manager, case.v)),
    ]
}

fn check_instrumentation(
    manager: &OPolyMgr,
    case: &DiagnosticCase<'_>,
    plain: &Option<OMgrPoly>,
    instrumented: &Option<OMgrPoly>,
) -> Outcome {
    if plain != instrumented {
        let mut details = diagnostic_inputs(manager, case);
        details.push((
            "plain".to_string(),
            plain
                .as_ref()
                .map_or_else(|| "None".to_string(), |value| render(manager, value)),
        ));
        details.push((
            "instrumented".to_string(),
            instrumented
                .as_ref()
                .map_or_else(|| "None".to_string(), |value| render(manager, value)),
        ));
        return Divergence::outcome(
            "pm-mod-gcd-diag",
            "identity",
            "mod_gcd_diag and mod_gcd disagree".to_string(),
            details,
        );
    }
    Outcome::Match(1)
}

fn check_diagnosis(
    manager: &OPolyMgr,
    case: &DiagnosticCase<'_>,
    answer: &Option<OMgrPoly>,
    diagnosis: &ay_nra::oracle_api::OModGcdDiag,
) -> Outcome {
    if diagnosis.certified() != answer.is_some() {
        let mut details = diagnostic_inputs(manager, case);
        details.push(("primary".to_string(), diagnosis.primary().to_string()));
        return Divergence::outcome(
            "pm-mod-gcd-diag",
            "identity",
            format!(
                "diag.certified() = {}, but mod_gcd returned {}",
                diagnosis.certified(),
                if answer.is_some() { "Some" } else { "None" }
            ),
            details,
        );
    }
    if (diagnosis.primary() == "certified") != diagnosis.certified() {
        return Divergence::outcome(
            "pm-mod-gcd-diag",
            "identity",
            format!(
                "diag.primary() = {:?} contradicts certified = {}",
                diagnosis.primary(),
                diagnosis.certified()
            ),
            diagnostic_inputs(manager, case),
        );
    }
    Outcome::Match(2)
}

fn check_work_counters(
    manager: &mut OPolyMgr,
    sab: Sabotage,
    case: &DiagnosticCase<'_>,
    diagnosis: &ay_nra::oracle_api::OModGcdDiag,
) -> Outcome {
    if sab.on() || diagnosis.shortcuts() != 0 {
        return Outcome::Match(0);
    }
    if diagnosis.cert_accepted() == 0 {
        return diagnostic_divergence(
            manager,
            case,
            "an answer was certified but no accept site fired",
        );
    }
    if diagnosis.primes_used() == 0 {
        return diagnostic_divergence(manager, case, "the certificate used no prime");
    }
    let mut variables = manager.vars(case.u);
    for variable in manager.vars(case.v) {
        if !variables.contains(&variable) {
            variables.push(variable);
        }
    }
    if variables.len() >= 2 && diagnosis.rec_points_tried() == 0 {
        return diagnostic_divergence(
            manager,
            case,
            &format!(
                "a {}-variable problem consumed no evaluation point",
                variables.len()
            ),
        );
    }
    Outcome::Match(if variables.len() >= 2 { 3 } else { 2 })
}

fn diagnostic_divergence(manager: &OPolyMgr, case: &DiagnosticCase<'_>, message: &str) -> Outcome {
    Divergence::outcome(
        "pm-mod-gcd-diag",
        "identity",
        message.to_string(),
        diagnostic_inputs(manager, case),
    )
}

fn check_diagnostic_maximality(
    manager: &mut OPolyMgr,
    case: &DiagnosticCase<'_>,
    answer: &OMgrPoly,
) -> Outcome {
    let Some(prs) = manager.gcd_via_prs(case.u, case.v) else {
        return Outcome::Declined("prs gcd refused");
    };
    if *answer != prs {
        return Divergence::outcome(
            "pm-mod-gcd-diag",
            "identity",
            "certified modular gcd differs from PRS gcd".to_string(),
            vec![
                ("u".to_string(), render(manager, case.u)),
                ("v".to_string(), render(manager, case.v)),
                ("prs".to_string(), render(manager, &prs)),
                ("modular".to_string(), render(manager, answer)),
            ],
        );
    }
    if !manager.divides(case.planted, answer) {
        return Divergence::outcome(
            "pm-mod-gcd-diag",
            "identity",
            "planted factor does not divide certified gcd".to_string(),
            vec![
                ("planted".to_string(), render(manager, case.planted)),
                ("u".to_string(), render(manager, case.u)),
                ("v".to_string(), render(manager, case.v)),
                ("g".to_string(), render(manager, answer)),
            ],
        );
    }
    if !manager.divides(answer, case.u) || !manager.divides(answer, case.v) {
        return Divergence::outcome(
            "pm-mod-gcd-diag",
            "identity",
            "certified gcd does not divide both inputs".to_string(),
            vec![
                ("u".to_string(), render(manager, case.u)),
                ("v".to_string(), render(manager, case.v)),
                ("g".to_string(), render(manager, answer)),
            ],
        );
    }
    Outcome::Match(3)
}
