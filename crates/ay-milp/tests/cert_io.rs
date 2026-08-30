// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `.ayc` certificate emission, parsing, and — the part that matters — the
//! independent checker's ability to FAIL.
//!
//! A checker that cannot reject is worthless, so most of this file is tampering:
//! flip a witness value, rescale a multiplier, swap the model digest, promote a
//! REPLAY claim to SUCCINCT, or point the checker at a different model, and
//! assert the exit status is not `VERIFIED`.

use ay_milp::cert_io::{self, CheckStatus, ClaimStanding, EvidenceKind};
use ay_milp::{BabSession, EngineEconomics, Outcome, SolveOpts};
use num_rational::BigRational;
use num_traits::One;

/// `min x + 2y` s.t. `x + y >= 3`, `x <= 2`, `0 <= x,y <= 10`, continuous.
/// The optimum is `x = 2, y = 1`, value 4 — and a continuous model is the one
/// verdict shape this build certifies on BOTH halves.
const LP: &str = "NAME          LP1
ROWS
 N  COST
 G  R1
 L  R2
COLUMNS
    X         COST      1.0        R1        1.0
    X         R2        1.0
    Y         COST      2.0        R1        1.0
RHS
    RHS       R1        3.0        R2        2.0
BOUNDS
 UP BND       X         10.0
 UP BND       Y         10.0
ENDATA
";

/// `min x + y` s.t. `x + y >= 3`, `x <= 2`, both INTEGER. Optimum 3.
///
/// A MILP optimum has no dual-side object UNLESS a whole-tree optimality proof
/// is supplied alongside it, and `solve_and_emit` deliberately supplies none —
/// so this fixture goes on pinning the `NONE` dual path exactly as before. The
/// tree lane is exercised separately, in section (g).
const MILP: &str = "NAME          MILP1
ROWS
 N  COST
 G  R1
 L  R2
COLUMNS
    MARKER                 'MARKER'                 'INTORG'
    X         COST      1.0        R1        1.0
    X         R2        1.0
    Y         COST      1.0        R1        1.0
    MARKER                 'MARKER'                 'INTEND'
RHS
    RHS       R1        3.0        R2        2.0
BOUNDS
 UP BND       X         10.0
 UP BND       Y         10.0
ENDATA
";

/// `x >= 3` and `x <= 2` over one continuous column. Keeping this fixture
/// continuous makes the test exercise the exact-LP Farkas lane instead of an
/// earlier exact PB route, whose independently checkable artifact is a BDD.
const INF: &str = "NAME          INF1
ROWS
 N  COST
 G  R1
 L  R2
COLUMNS
    X         COST      1.0        R1        1.0
    X         R2        1.0
RHS
    RHS       R1        3.0        R2        2.0
BOUNDS
 UP BND       X         10.0
ENDATA
";

/// ONE BINARY column with `X >= 2`. This is the exact model whose default
/// posture regressed: Direct-CNF admits it (a Boolean row with an unsatisfiable
/// side), refutes it by CDCL, and exports NOTHING — so `--require witness`
/// emitted `REPLAY direct-cnf-unsat` and `ay-milp verify` exited 10 UNVERIFIED,
/// while `--require full` refuted the same model with a succinct single-row DP
/// proof and exited 0.
///
/// `INF` above cannot show this: its column is a general integer in `[0, 10]`,
/// which Direct-CNF declines, so a PB proof route always owned it.
const BIN_INF: &str = "NAME          BININF
ROWS
 N  COST
 G  R1
COLUMNS
    MARKER                 'MARKER'                 'INTORG'
    X         COST      1.0        R1        1.0
    MARKER                 'MARKER'                 'INTEND'
RHS
    RHS       R1        2.0
BOUNDS
 BV BND       X
ENDATA
";

/// Two exact parity equalities demand opposite parities from the same binary.
/// Their source-row sum is `2 X - 2 Y0 - 2 Y1 = -1`, an independently
/// checkable even-equals-odd contradiction.  The LP relaxation is feasible,
/// so a Farkas certificate cannot stand in for the parity artifact.
const PARITY_INF: &str = "NAME          PARITYINF
ROWS
 N  COST
 E  R0
 E  R1
COLUMNS
    MARKER                 'MARKER'                 'INTORG'
    X         COST      1          R0        1
    X         R1        1
    Y0        R0       -2
    Y1        R1       -2
    MARKER                 'MARKER'                 'INTEND'
RHS
    RHS       R1       -1
BOUNDS
 BV BND       X
ENDATA
";

/// One exact weighted Boolean row whose target sum is unreachable.  This is
/// deliberately not a clause, so the independently replayable single-row DP
/// proof route owns it rather than Direct-CNF.
const DP_INF: &str = "NAME          DPINF
ROWS
 N  COST
 E  R1
COLUMNS
    X         R1        6
    Y         R1        10
    Z         R1        14
RHS
    RHS       R1        18
BOUNDS
 BV BND       X
 BV BND       Y
 BV BND       Z
ENDATA
";

/// Three genuinely distinct weighted Boolean rows.  The first forces X=Y=1,
/// the second forces Y=Z=1, and the third permits at most two selected
/// variables.  Direct-CNF and the one-row DP both decline this shape, so the
/// general residual-state decision DAG owns the infeasibility proof.  A
/// nonzero objective pins the `--require full`/objective-model posture too.
const BDD_INF: &str = "NAME          BDDINF
ROWS
 N  COST
 G  R1
 G  R2
 L  R3
COLUMNS
    MARKER                 'MARKER'                 'INTORG'
    X         COST      1          R1        2
    X         R3        2
    Y         COST      1          R1        3
    Y         R2        2          R3        2
    Z         COST      1          R2        3
    Z         R3        2
    MARKER                 'MARKER'                 'INTEND'
RHS
    RHS       R1        4          R2        4
    RHS       R3        5
BOUNDS
 BV BND       X
 BV BND       Y
 BV BND       Z
ENDATA
";

/// An open nonnegative integer column occurs only helpfully in a lower row.
/// Eliminating it leaves the contradictory binary residual `X >= 1, X <= 0`.
/// The objective is deliberately nonzero: source infeasibility, not a bounded
/// objective assumption, licenses the exported residual refutation.
const OPEN_INF: &str = "NAME          OPENINF
ROWS
 N  COST
 G  ROPEN
 G  RLOW
 L  RUP
COLUMNS
    MARKER                 'MARKER'                 'INTORG'
    X         COST      1          RLOW      1
    X         RUP       1
    OPEN      COST      1          ROPEN     1
    MARKER                 'MARKER'                 'INTEND'
RHS
    RHS       ROPEN     2          RLOW      1
    RHS       RUP       0
BOUNDS
 BV BND       X
ENDATA
";

/// One Boolean master column and one continuous recourse column.  The two
/// rows require `Y-X >= 1` and `Y-X <= 0`, so every master assignment has an
/// exact Farkas contradiction.  Direct PB and monotone open-domain projection
/// both decline; the typed hybrid cut ledger owns the exported refutation.
const HYBRID_INF: &str = "NAME          HYBRIDINF
ROWS
 N  COST
 G  RLOW
 L  RUP
COLUMNS
    X         RLOW      -1         RUP       -1
    Y         RLOW       1         RUP        1
RHS
    RHS       RLOW       1         RUP        0
BOUNDS
 BV BND       X
 FR BND       Y
ENDATA
";

/// The same contradictory recourse system with a bounded three-valued master integer.
/// The checker must rebuild the radix lift before replaying the nested hybrid certificate.
const HYBRID_INTEGER_INF: &str = "NAME          HYBRIDINTINF
ROWS
 N  COST
 G  RLOW
 L  RUP
COLUMNS
    MARKER                 'MARKER'                 'INTORG'
    X         RLOW      -1         RUP       -1
    MARKER                 'MARKER'                 'INTEND'
    Y         RLOW       1         RUP        1
RHS
    RHS       RLOW       1         RUP        0
BOUNDS
 UP BND       X           2
 FR BND       Y
ENDATA
";

/// A monotone open integer is projected away before the residual binary-master
/// / continuous-recourse contradiction is proved.  The exported hybrid object
/// is valid only for that residual, so the checker must rebuild the projection.
const OPEN_HYBRID_INF: &str = "NAME          OPENHYBRIDINF
ROWS
 N  COST
 G  ROPEN
 G  RLOW
 L  RUP
COLUMNS
    MARKER                 'MARKER'                 'INTORG'
    X         COST       1         RLOW      -1
    X         RUP       -1
    OPEN      COST       1         ROPEN      1
    MARKER                 'MARKER'                 'INTEND'
    Y         RLOW       1         RUP        1
RHS
    RHS       ROPEN      2         RLOW       1
    RHS       RUP        0
BOUNDS
 BV BND       X
 FR BND       Y
ENDATA
";

/// The projected residual keeps a bounded three-valued master integer rather
/// than a Boolean master.  This exercises the complete composition that is
/// distinct from `OPEN_HYBRID_INF`: rebuild the monotone open-domain
/// projection, rebuild and validate the radix lift, then replay the nested
/// hybrid cut ledger against that transformed residual.
const OPEN_HYBRID_INTEGER_INF: &str = "NAME          OPENHYBRIDINTINF
ROWS
 N  COST
 G  ROPEN
 G  RLOW
 L  RUP
COLUMNS
    MARKER                 'MARKER'                 'INTORG'
    X         COST       1         RLOW      -1
    X         RUP       -1
    OPEN      COST       1         ROPEN      1
    MARKER                 'MARKER'                 'INTEND'
    Y         RLOW       1         RUP        1
RHS
    RHS       ROPEN      2         RLOW       1
    RHS       RUP        0
BOUNDS
 UP BND       X           2
 FR BND       Y
ENDATA
";

/// One fixed-charge arc with an exact continuous objective singleton.  The
/// Hoffman master contains only ENABLE, requires it to be one, and has optimum
/// five.  This is the smallest end-to-end network certificate fixture.
const NETWORK_OPT: &str = "NAME          NETOPT
ROWS
 N  COST
 E  OBJDEF
 E  BAL
 L  VUB
COLUMNS
    FLOW      BAL       1          VUB       1
    OBJ       COST      1          OBJDEF    1
    MARKER                 'MARKER'                 'INTORG'
    ENABLE    OBJDEF   -5          VUB      -1
    MARKER                 'MARKER'                 'INTEND'
RHS
    RHS       BAL       1
BOUNDS
 FR BND       OBJ
 BV BND       ENABLE
ENDATA
";

/// The same exact network with its sole capacity controller fixed off.
const NETWORK_INF: &str = "NAME          NETINF
ROWS
 N  COST
 E  OBJDEF
 E  BAL
 L  VUB
COLUMNS
    FLOW      BAL       1          VUB       1
    OBJ       COST      1          OBJDEF    1
    MARKER                 'MARKER'                 'INTORG'
    ENABLE    OBJDEF   -5          VUB      -1
    MARKER                 'MARKER'                 'INTEND'
RHS
    RHS       BAL       1
BOUNDS
 FR BND       OBJ
 BV BND       ENABLE
 FX BND       ENABLE    0
ENDATA
";

/// Two-job disjunctive single-machine scheduling model. The exact optimum is
/// order T0,T1 with starts 0,2 and objective 2. It is intentionally tiny so
/// certificate round-trip tests exercise the production route without making
/// the general certificate suite expensive.
const SCHEDULING_OPT: &str = "NAME          SCHEDOPT
ROWS
 N  COST
 E  COMP
 G  PREC01
 G  PREC10
 L  TARD0
 L  TARD1
 L  STARTAGG
 L  TARDAGG
COLUMNS
    S0        TARD0    -1          TARDAGG   1
    S1        TARD1    -1          TARDAGG   1
    AT        COST      1          TARDAGG  -1
    AS        COST      1          STARTAGG  -1
    X01       COMP      1          PREC01   100
    X10       COMP      1          PREC10   100
    MARKER                 'MARKER'                 'INTORG'
    T0        PREC01   -1          PREC10     1
    T0        TARD0     1          STARTAGG   1
    T1        PREC01    1          PREC10    -1
    T1        TARD1     1          STARTAGG   1
    MARKER                 'MARKER'                 'INTEND'
RHS
    RHS       COMP      1          PREC01     2
    RHS       PREC10    3          TARD0      2
    RHS       TARD1     4
BOUNDS
 FR BND       AT
 FR BND       AS
 BV BND       X01
 BV BND       X10
 LO BND       T0        0
 LO BND       T1        0
ENDATA
";

/// Two one-chain source blocks coupled by one covering row. The block-angular
/// route must choose E1 at cost 1 rather than E2 at cost 2.
const BLOCK_ANGULAR_OPT: &str = "NAME          BLOCKANG
ROWS
 N  COST
 E  B1ROOT
 E  B1FLOW
 L  B1CAP
 E  B2ROOT
 E  B2FLOW
 L  B2CAP
 G  DEMAND
COLUMNS
    MARKER                 'MARKER'                 'INTORG'
    R1        B1ROOT    1          B1CAP     1
    S1        B1ROOT   -1          B1FLOW    1
    S1        DEMAND    1
    E1        COST      1          B1FLOW   -1
    R2        B2ROOT    1          B2CAP     1
    S2        B2ROOT   -1          B2FLOW    1
    S2        DEMAND    1
    E2        COST      2          B2FLOW   -1
    MARKER                 'MARKER'                 'INTEND'
RHS
    RHS       B1CAP     1          B2CAP     1
    RHS       DEMAND    1
BOUNDS
 UP BND       R1        1
 UP BND       S1        1
 UP BND       E1        1
 UP BND       R2        1
 UP BND       S2        1
 UP BND       E2        1
ENDATA
";

/// Renders from a temporary context so every borrow of `session` ends on
/// return.
fn emit_session_certificate(
    session: &BabSession,
    model_text: &str,
    col_names: &[String],
    obj_scale: &BigRational,
    outcome: &Outcome,
) -> String {
    emit_session_certificate_with_tree(session, model_text, col_names, obj_scale, outcome, None)
}

/// As [`emit_session_certificate`], plus the whole-tree optimality artifact the
/// CLI derives after the verdict. Passing `None` is what every pre-existing
/// test does, which is why those tests still pin the `NONE` dual path.
fn emit_session_certificate_with_tree(
    session: &BabSession,
    model_text: &str,
    col_names: &[String],
    obj_scale: &BigRational,
    outcome: &Outcome,
    opt_tree: Option<&ay_milp::MilpOptimalityCertificate>,
) -> String {
    let ctx = cert_io::EmitCtx {
        model: session.model(),
        model_text,
        col_names,
        obj_scale,
        provenance: "host=test",
        replay_claims: session.replay_claims(),
        affine_aggregation_certificate: session.affine_aggregation_certificate(),
        parity_infeasibility_certificate: session.parity_infeasibility_certificate(),
        sat_relu_infeasibility_certificate: session.sat_relu_infeasibility_certificate(),
        network_design_infeasibility_certificate: session
            .network_design_infeasibility_certificate(),
        network_design_optimality_certificate: session.network_design_optimality_certificate(),
        block_angular_optimality_certificate: session.block_angular_optimality_certificate(),
        milp_optimality_tree_certificate: opt_tree,
        root_dual_bound_certificate: None,
        single_machine_scheduling_optimality_certificate: session
            .single_machine_scheduling_optimality_certificate(),
        single_row_dp_infeasibility_certificate: session.single_row_dp_infeasibility_certificate(),
        multi_row_bdd_infeasibility_certificate: session.multi_row_bdd_infeasibility_certificate(),
        open_domain_single_row_dp_infeasibility_certificate: session
            .open_domain_single_row_dp_infeasibility_certificate(),
        open_domain_multi_row_bdd_infeasibility_certificate: session
            .open_domain_multi_row_bdd_infeasibility_certificate(),
        open_domain_hybrid_pb_lp_infeasibility_certificate: session
            .open_domain_hybrid_pb_lp_infeasibility_certificate(),
        open_domain_hybrid_integer_lift_infeasibility_certificate: session
            .open_domain_hybrid_integer_lift_infeasibility_certificate(),
        hybrid_pb_lp_infeasibility_certificate: session.hybrid_pb_lp_infeasibility_certificate(),
        hybrid_integer_lift_infeasibility_certificate: session
            .hybrid_integer_lift_infeasibility_certificate(),
        max_bytes: None,
    };
    cert_io::emit(&ctx, outcome)
}

fn solve_with_opts_and_emit(text: &str, opts: &SolveOpts) -> (String, Outcome) {
    let p = ay_milp::read_mps(text).expect("model parses");
    let names = p.col_names.clone();
    let scale = p.obj_scale.clone();
    let mut session = BabSession::new(p.model, opts).expect("session");
    let outcome = session.check().expect("solve");
    let ayc = emit_session_certificate(&session, text, &names, &scale, &outcome);
    (ayc, outcome)
}

/// The DEFAULT shipped posture: structure routing on, `--require witness`.
fn solve_and_emit(text: &str) -> (String, Outcome) {
    solve_with_opts_and_emit(
        text,
        &SolveOpts::new().with_time_limit(std::time::Duration::from_secs(20)),
    )
}

fn solve_full_and_emit(text: &str) -> (String, Outcome) {
    solve_with_opts_and_emit(
        text,
        &SolveOpts::new()
            .with_time_limit(std::time::Duration::from_secs(20))
            .with_require_certificates(true),
    )
}

/// Pin the solve on NATIVE branch-and-bound.
///
/// The exact structure-recognition routes answer many small models before the
/// LP relaxation is ever built, and they prove infeasibility with a PB decision
/// DAG rather than a Farkas combination. That is a different — not weaker —
/// artifact, but it means a test whose SUBJECT is the root-Farkas lane or the
/// whole-tree case-split lane must say so, or it silently stops exercising the
/// lane named in its own function name.
///
/// Every such test here is paired with a companion asserting the DEFAULT routed
/// posture still emits verifying evidence on the same model, so opting out
/// never buys green by dropping coverage of what actually ships.
fn solve_native_and_emit(text: &str) -> (String, Outcome) {
    solve_with_opts_and_emit(
        text,
        &SolveOpts::new()
            .with_time_limit(std::time::Duration::from_secs(20))
            .with_structure_routing(false),
    )
}

/// Re-seal a hand-edited certificate so the `%END` digest still matches. Used
/// by every tamper test that wants to prove the CONTENT check fires rather than
/// merely tripping the body digest.
fn reseal(text: &str) -> String {
    let mut body = String::new();
    for l in text
        .lines()
        .take_while(|l| !l.trim_start().starts_with("%END"))
    {
        body.push_str(l);
        body.push('\n');
    }
    let digest = cert_io::sha256_hex(body.as_bytes());
    format!("{body}%END sha256:{digest}\n")
}

#[derive(Clone, Copy)]
struct LineReplacement<'a> {
    from: &'a str,
    to: &'a str,
}

/// Filters certificate lines, replaces every occurrence requested, and keeps
/// the original pipelines' trailing newline for every retained line.
fn rewrite_certificate_lines(
    text: &str,
    mut keep: impl FnMut(&str) -> bool,
    replacement: Option<LineReplacement<'_>>,
) -> String {
    let mut rewritten = String::with_capacity(text.len());
    for line in text.lines() {
        if !keep(line) {
            continue;
        }
        match replacement {
            Some(replacement) => {
                for (index, part) in line.split(replacement.from).enumerate() {
                    if index != 0 {
                        rewritten.push_str(replacement.to);
                    }
                    rewritten.push_str(part);
                }
            }
            None => rewritten.push_str(line),
        }
        rewritten.push('\n');
    }
    rewritten
}

// ---------------------------------------------------------------------------
// (a) Emission and the happy path.
// ---------------------------------------------------------------------------

#[test]
fn continuous_optimum_is_fully_verified() {
    let (ayc, _) = solve_and_emit(LP);
    let r = cert_io::check(&ayc, LP);
    assert_eq!(r.status(), CheckStatus::Verified, "{r:#?}");
    assert_eq!(r.status().exit_code(), 0);
    assert_eq!(r.claims().len(), 2);
    assert!(r
        .claims()
        .iter()
        .all(|c| c.is_verified() && c.kind() == EvidenceKind::Succinct));
}

#[test]
fn network_optimality_artifact_round_trips_and_value_tampering_fails() {
    let (ayc, outcome) = solve_full_and_emit(NETWORK_OPT);
    assert!(matches!(outcome, Outcome::Optimal { .. }));
    assert!(ayc.contains("evidence dual SUCCINCT network-design-optimality"));
    let parsed = cert_io::parse(&ayc).expect("network optimality certificate parses");
    assert!(parsed.network_design_optimality.is_some());
    let report = cert_io::check(&ayc, NETWORK_OPT);
    assert_eq!(report.status(), CheckStatus::Verified, "{report:#?}");

    let tampered = reseal(&ayc.replacen(
        "network-design-optimality value=5 frame=model",
        "network-design-optimality value=6 frame=model",
        1,
    ));
    let rejected = cert_io::check(&tampered, NETWORK_OPT);
    assert_ne!(rejected.status(), CheckStatus::Verified, "{rejected:#?}");
}

#[test]
fn block_angular_artifact_is_verified_end_to_end_and_tampering_is_refuted() {
    let (ayc, outcome) = solve_full_and_emit(BLOCK_ANGULAR_OPT);
    match outcome {
        Outcome::Optimal { value, .. } => {
            assert_eq!(value, BigRational::from_integer(1.into()));
        }
        other => panic!("block-angular fixture did not solve optimally: {other:?}"),
    }
    assert!(ayc.contains("evidence dual SUCCINCT block-angular-optimality"));
    let parsed = cert_io::parse(&ayc).expect("block-angular certificate parses");
    assert!(parsed.block_angular_optimality.is_some());
    let report = cert_io::check(&ayc, BLOCK_ANGULAR_OPT);
    assert_eq!(report.status(), CheckStatus::Verified, "{report:#?}");

    let master_line = ayc
        .lines()
        .find(|line| line.starts_with("master "))
        .expect("block-angular multiplier");
    let row = master_line
        .split_whitespace()
        .nth(1)
        .expect("master row index");
    let tampered = reseal(&ayc.replacen(master_line, &format!("master {row} -1"), 1));
    let rejected = cert_io::check(&tampered, BLOCK_ANGULAR_OPT);
    assert_eq!(rejected.status(), CheckStatus::Refuted, "{rejected:#?}");
}

#[test]
fn block_angular_exact_decimal_side_store_reaches_the_public_checker() {
    // Clearing decimal denominators normally makes MPS objectives f64-exact.
    // This odd 54-bit significand remains inexact even after that scaling and
    // the power-of-two normalizer, forcing an authoritative side-store entry.
    // Prove that premise directly before exercising route/emitter/checker.
    let exact_decimal = BLOCK_ANGULAR_OPT
        .replacen(
            "E1        COST      1",
            "E1        COST      0.10000000000000001",
            1,
        )
        .replacen("E2        COST      2", "E2        COST      0.2", 1);
    let parsed_input = ay_milp::read_mps(&exact_decimal).expect("exact decimal model parses");
    let e1 = parsed_input
        .col_names
        .iter()
        .position(|name| name == "E1")
        .expect("E1 column");
    let e1_column = parsed_input.model.col_at(e1).expect("E1 handle");
    let mut e1_point = vec![BigRational::from_integer(0.into()); parsed_input.model.num_cols()];
    e1_point[e1] = BigRational::one();
    let exact_model_cost = parsed_input.model.objective_value_at(&e1_point);
    let proxy_model_cost = BigRational::from_float(parsed_input.model.obj_coeff(e1_column))
        .expect("finite objective proxy");
    assert_ne!(exact_model_cost, proxy_model_cost);
    let exact_file_cost = BigRational::new(
        10_000_000_000_000_001_i64.into(),
        100_000_000_000_000_000_i64.into(),
    );
    assert_eq!(&exact_model_cost / &parsed_input.obj_scale, exact_file_cost);

    let (ayc, outcome) = solve_full_and_emit(&exact_decimal);
    match outcome {
        Outcome::Optimal { value, .. } => {
            assert_eq!(value, exact_model_cost);
        }
        other => panic!("exact-decimal block-angular fixture did not solve: {other:?}"),
    }
    assert!(ayc.contains("evidence dual SUCCINCT block-angular-optimality"));
    assert!(ayc.contains("verdict optimal value=10000000000000001/100000000000000000 frame=file"));
    let parsed = cert_io::parse(&ayc).expect("exact-decimal artifact parses");
    assert!(parsed.block_angular_optimality.is_some());
    let checked = cert_io::check(&ayc, &exact_decimal);
    assert_eq!(checked.status(), CheckStatus::Verified, "{checked:#?}");
}

#[test]
fn block_angular_public_parser_rejects_oversized_rationals_fail_closed() {
    fn assert_resource_rejection(artifact: &str, expected_field: &str) {
        match cert_io::parse(artifact) {
            Err(cert_io::CertIoError::RationalBitLimit {
                line,
                field,
                max_bits,
            }) => {
                assert!(line > 0);
                assert_eq!(field, expected_field);
                assert_eq!(max_bits, 4_096);
            }
            Err(other) => panic!("wrong parser rejection: {other}"),
            Ok(_) => panic!("oversized block-angular rational parsed"),
        }
        let checked = cert_io::check(artifact, BLOCK_ANGULAR_OPT);
        assert_eq!(checked.status(), CheckStatus::Refuted, "{checked:#?}");
        assert!(
            checked
                .notes()
                .iter()
                .any(|note| note.contains(expected_field) && note.contains("4096-bit")),
            "the public checker must report its bounded parser rejection: {checked:#?}"
        );
    }

    let (ayc, outcome) = solve_full_and_emit(BLOCK_ANGULAR_OPT);
    assert!(matches!(outcome, Outcome::Optimal { .. }));
    let allocation_attack = "9".repeat(100_000);

    let block_header = ayc
        .lines()
        .find(|line| line.starts_with("block-angular-optimality "))
        .expect("block-angular header");
    let value_field = block_header
        .split_whitespace()
        .find(|field| field.starts_with("value="))
        .expect("block-angular value");
    let oversized_value_header =
        block_header.replacen(value_field, &format!("value={allocation_attack}/2"), 1);
    let oversized_numerator = reseal(&ayc.replacen(block_header, &oversized_value_header, 1));
    assert_resource_rejection(&oversized_numerator, "block-angular optimum value");

    let master = ayc
        .lines()
        .find(|line| line.starts_with("master "))
        .expect("block-angular master multiplier");
    let master_row = master
        .split_whitespace()
        .nth(1)
        .expect("block-angular master row");
    let oversized_master = format!("master {master_row} 1/{allocation_attack}");
    let oversized_denominator = reseal(&ayc.replacen(master, &oversized_master, 1));
    assert_resource_rejection(&oversized_denominator, "block-angular master multiplier");
}

#[test]
fn scheduling_optimality_artifact_round_trips_and_tampering_fails() {
    let (ayc, outcome) = solve_full_and_emit(SCHEDULING_OPT);
    assert!(matches!(outcome, Outcome::Optimal { .. }));
    assert!(ayc.contains("evidence dual SUCCINCT single-machine-scheduling-optimality"));
    let parsed = cert_io::parse(&ayc).expect("scheduling optimality certificate parses");
    assert!(parsed.single_machine_scheduling_optimality.is_some());
    let report = cert_io::check(&ayc, SCHEDULING_OPT);
    assert_eq!(report.status(), CheckStatus::Verified, "{report:#?}");

    let sequence_line = ayc
        .lines()
        .find(|line| line.starts_with("sequence "))
        .expect("sequence block");
    let sequence_fields: Vec<_> = sequence_line.split_whitespace().collect();
    assert_eq!(sequence_fields.len(), 3);
    let repeated_sequence = format!("sequence {0} {0}", sequence_fields[1]);
    let sequence_tamper = reseal(&ayc.replacen(sequence_line, &repeated_sequence, 1));
    let rejected = cert_io::check(&sequence_tamper, SCHEDULING_OPT);
    assert_eq!(rejected.status(), CheckStatus::Refuted, "{rejected:#?}");

    let proof_line = ayc
        .lines()
        .find(|line| line.starts_with("single-machine-scheduling-optimality "))
        .expect("scheduling proof header");
    let value_tamper_line = proof_line
        .split_whitespace()
        .map(|field| {
            if field.starts_with("value=") {
                "value=999"
            } else {
                field
            }
        })
        .collect::<Vec<_>>()
        .join(" ");
    let value_tamper = reseal(&ayc.replacen(proof_line, &value_tamper_line, 1));
    let rejected = cert_io::check(&value_tamper, SCHEDULING_OPT);
    assert_eq!(rejected.status(), CheckStatus::Refuted, "{rejected:#?}");

    let changed_model = SCHEDULING_OPT.replacen("TARD0      2", "TARD0      1", 1);
    assert_ne!(changed_model, SCHEDULING_OPT);
    let rejected = cert_io::check(&ayc, &changed_model);
    assert_eq!(rejected.status(), CheckStatus::Mismatch, "{rejected:#?}");
}

#[test]
fn network_infeasibility_artifact_round_trips_and_corruption_fails() {
    let (ayc, outcome) = solve_full_and_emit(NETWORK_INF);
    assert!(matches!(outcome, Outcome::Infeasible { .. }), "{outcome:?}");
    assert!(ayc.contains("evidence infeasible SUCCINCT network-design-infeasibility"));
    let parsed = cert_io::parse(&ayc).expect("network infeasibility certificate parses");
    assert!(parsed.network_design_infeasibility.is_some());
    let report = cert_io::check(&ayc, NETWORK_INF);
    assert_eq!(report.status(), CheckStatus::Verified, "{report:#?}");

    let tampered = reseal(&ayc.replacen("\"format\":\"", "\"format\":\"tampered-", 1));
    let rejected = cert_io::check(&tampered, NETWORK_INF);
    assert_ne!(rejected.status(), CheckStatus::Verified, "{rejected:#?}");
}

#[test]
fn parity_infeasibility_artifact_round_trips_and_row_tampering_fails() {
    let (ayc, outcome) = solve_full_and_emit(PARITY_INF);
    assert!(matches!(outcome, Outcome::Infeasible { .. }), "{outcome:?}");
    assert!(ayc.contains("evidence infeasible SUCCINCT parity-gf2"));
    assert!(ayc.contains("parity-gf2 rows=2\nrow 0\nrow 1\nend\n"));

    let parsed = cert_io::parse(&ayc).expect("parity certificate parses");
    assert!(parsed.parity_infeasibility.is_some());
    let report = cert_io::check(&ayc, PARITY_INF);
    assert_eq!(report.status(), CheckStatus::Verified, "{report:#?}");

    // Keep the wire format canonical and re-seal it, but point the proof at a
    // source row that does not exist.  The model-bound replay, not the body
    // checksum or parser, must reject the forged contradiction.
    let tampered = reseal(&ayc.replacen("row 1\nend\n", "row 2\nend\n", 1));
    let rejected = cert_io::check(&tampered, PARITY_INF);
    assert_ne!(rejected.status(), CheckStatus::Verified, "{rejected:#?}");
}

#[test]
fn single_row_dp_infeasibility_artifact_verifies_and_tampering_fails() {
    let (ayc, outcome) = solve_and_emit(DP_INF);
    assert!(matches!(outcome, Outcome::Infeasible { .. }), "{outcome:?}");
    assert!(ayc.contains("evidence infeasible SUCCINCT single-row-dp"));
    let parsed = cert_io::parse(&ayc).expect("single-row DP certificate parses");
    assert!(parsed.single_row_dp.is_some());
    let report = cert_io::check(&ayc, DP_INF);
    assert_eq!(report.status(), CheckStatus::Verified, "{report:#?}");

    let needle = "\"reachable_words\":[1";
    assert!(
        ayc.contains(needle),
        "fixture must contain its initial DP bitset"
    );
    let corrupted = reseal(&ayc.replacen(needle, "\"reachable_words\":[0", 1));
    let rejected = cert_io::check(&corrupted, DP_INF);
    assert_eq!(rejected.status(), CheckStatus::Refuted, "{rejected:#?}");
    assert_eq!(
        rejected.claims_in(ClaimStanding::Refuted),
        vec!["infeasible"]
    );
}

#[test]
fn full_posture_multi_row_bdd_artifact_verifies_and_corruption_fails() {
    let p = ay_milp::read_mps(BDD_INF).expect("model parses");
    let names = p.col_names.clone();
    let scale = p.obj_scale.clone();
    let opts = SolveOpts::new()
        .with_time_limit(std::time::Duration::from_secs(20))
        .with_require_certificates(true);
    let mut session = BabSession::new(p.model, &opts).expect("session");
    let outcome = session.check().expect("full-posture solve");
    assert!(matches!(outcome, Outcome::Infeasible { .. }), "{outcome:?}");
    assert!(session.single_row_dp_infeasibility_certificate().is_none());
    assert!(session.multi_row_bdd_infeasibility_certificate().is_some());
    assert!(session.replay_claims().is_empty());
    let ayc = emit_session_certificate(&session, BDD_INF, &names, &scale, &outcome);
    assert!(ayc.contains("evidence infeasible SUCCINCT multi-row-bdd"));
    let parsed = cert_io::parse(&ayc).expect("multi-row BDD certificate parses");
    assert!(parsed.multi_row_bdd.is_some());
    let report = cert_io::check(&ayc, BDD_INF);
    assert_eq!(report.status(), CheckStatus::Verified, "{report:#?}");
    let format = "ay.multi-row-bdd-infeasible.v1";
    assert!(ayc.contains(format));
    let corrupted = reseal(&ayc.replacen(format, "ay.multi-row-bdd-infeasible.x1", 1));
    let rejected = cert_io::check(&corrupted, BDD_INF);
    assert_eq!(rejected.status(), CheckStatus::Refuted, "{rejected:#?}");
    assert_eq!(
        rejected.claims_in(ClaimStanding::Refuted),
        vec!["infeasible"]
    );
    session.push().expect("scope");
    session
        .add_row(f64::NEG_INFINITY, f64::INFINITY, &[])
        .expect("model mutation");
    assert!(session.multi_row_bdd_infeasibility_certificate().is_none());
    session.pop().expect("scope pop");
    assert!(session.multi_row_bdd_infeasibility_certificate().is_none());
}

#[test]
fn cli_full_accepts_certified_nonzero_objective_infeasibility() {
    use std::process::Command;
    use std::time::{SystemTime, UNIX_EPOCH};

    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock")
        .as_nanos();
    let model_path = std::env::temp_dir().join(format!(
        "ay-milp-full-bdd-{}-{nonce}.mps",
        std::process::id()
    ));
    std::fs::write(&model_path, BDD_INF).expect("write CLI fixture");
    let output = Command::new(env!("CARGO_BIN_EXE_ay-milp"))
        .arg("solve")
        .arg(&model_path)
        .args(["--require", "full", "--time-limit", "20", "--no-emit-cert"])
        .output()
        .expect("run ay-milp CLI");
    let _ = std::fs::remove_file(&model_path);

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "stdout={stdout}\nstderr={stderr}");
    assert!(stdout.starts_with("INFEASIBLE "), "stdout={stdout}");
    assert!(!stderr.contains("REFUSED"), "stderr={stderr}");
}

#[test]
fn open_domain_residual_artifact_rebuilds_and_verifies() {
    let p = ay_milp::read_mps(OPEN_INF).expect("model parses");
    let names = p.col_names.clone();
    let scale = p.obj_scale.clone();
    let opts = SolveOpts::new()
        .with_time_limit(std::time::Duration::from_secs(20))
        .with_require_certificates(true);
    let mut session = BabSession::new(p.model, &opts).expect("session");
    let outcome = session.check().expect("full-posture open-domain solve");
    assert!(matches!(outcome, Outcome::Infeasible { .. }), "{outcome:?}");
    assert!(session.replay_claims().is_empty());
    assert!(
        session
            .open_domain_single_row_dp_infeasibility_certificate()
            .is_some()
            || session
                .open_domain_multi_row_bdd_infeasibility_certificate()
                .is_some()
    );
    let ayc = emit_session_certificate(&session, OPEN_INF, &names, &scale, &outcome);
    assert!(
        ayc.contains("evidence infeasible SUCCINCT open-domain-dp")
            || ayc.contains("evidence infeasible SUCCINCT open-domain-bdd"),
        "{ayc}"
    );
    let parsed = cert_io::parse(&ayc).expect("open-domain certificate parses");
    assert!(parsed.open_domain_dp.is_some() || parsed.open_domain_bdd.is_some());
    let report = cert_io::check(&ayc, OPEN_INF);
    assert_eq!(report.status(), CheckStatus::Verified, "{report:#?}");

    let corrupted = if ayc.contains("ay.multi-row-bdd-infeasible.v1") {
        ayc.replacen(
            "ay.multi-row-bdd-infeasible.v1",
            "ay.multi-row-bdd-infeasible.x1",
            1,
        )
    } else {
        ayc.replacen(
            "ay.single-row-dp-infeasible.v1",
            "ay.single-row-dp-infeasible.x1",
            1,
        )
    };
    let rejected = cert_io::check(&reseal(&corrupted), OPEN_INF);
    assert_eq!(rejected.status(), CheckStatus::Refuted, "{rejected:#?}");

    session.push().expect("scope");
    session
        .add_row(f64::NEG_INFINITY, f64::INFINITY, &[])
        .expect("model mutation");
    assert!(session
        .open_domain_single_row_dp_infeasibility_certificate()
        .is_none());
    assert!(session
        .open_domain_multi_row_bdd_infeasibility_certificate()
        .is_none());
}

#[test]
fn open_domain_hybrid_artifact_rebuilds_projection_and_verifies() {
    let p = ay_milp::read_mps(OPEN_HYBRID_INF).expect("model parses");
    let names = p.col_names.clone();
    let scale = p.obj_scale.clone();
    let opts = SolveOpts::new()
        .with_time_limit(std::time::Duration::from_secs(20))
        .with_require_certificates(true);
    let mut session = BabSession::new(p.model, &opts).expect("session");
    let outcome = session
        .check()
        .expect("full-posture open-domain hybrid solve");
    assert!(matches!(outcome, Outcome::Infeasible { .. }), "{outcome:?}");
    assert!(session.replay_claims().is_empty());
    assert!(session
        .open_domain_hybrid_pb_lp_infeasibility_certificate()
        .is_some());
    let ayc = emit_session_certificate(&session, OPEN_HYBRID_INF, &names, &scale, &outcome);
    assert!(
        ayc.contains("evidence infeasible SUCCINCT open-domain-hybrid-pb-lp"),
        "{ayc}"
    );
    let parsed = cert_io::parse(&ayc).expect("open-domain hybrid certificate parses");
    assert!(parsed.open_domain_hybrid_pb_lp.is_some());
    let report = cert_io::check(&ayc, OPEN_HYBRID_INF);
    assert_eq!(report.status(), CheckStatus::Verified, "{report:#?}");

    let corrupted = reseal(&ayc.replacen(
        "ay.hybrid-pb-lp-infeasible.v1",
        "ay.hybrid-pb-lp-infeasible.x1",
        1,
    ));
    let rejected = cert_io::check(&corrupted, OPEN_HYBRID_INF);
    assert_eq!(rejected.status(), CheckStatus::Refuted, "{rejected:#?}");

    session.push().expect("scope");
    session
        .add_row(f64::NEG_INFINITY, f64::INFINITY, &[])
        .expect("model mutation");
    assert!(session
        .open_domain_hybrid_pb_lp_infeasibility_certificate()
        .is_none());
}

#[test]
fn open_domain_integer_lift_hybrid_artifact_rebuilds_both_transforms() {
    let p = ay_milp::read_mps(OPEN_HYBRID_INTEGER_INF).expect("model parses");
    let names = p.col_names.clone();
    let scale = p.obj_scale.clone();
    let opts = SolveOpts::new()
        .with_time_limit(std::time::Duration::from_secs(20))
        .with_require_certificates(true);
    let mut session = BabSession::new(p.model, &opts).expect("session");
    let outcome = session
        .check()
        .expect("full-posture open-domain integer-lift hybrid solve");
    assert!(matches!(outcome, Outcome::Infeasible { .. }), "{outcome:?}");
    assert!(session.replay_claims().is_empty());
    assert!(session
        .open_domain_hybrid_pb_lp_infeasibility_certificate()
        .is_none());
    assert!(session
        .open_domain_hybrid_integer_lift_infeasibility_certificate()
        .is_some());
    let ayc = emit_session_certificate(&session, OPEN_HYBRID_INTEGER_INF, &names, &scale, &outcome);
    assert!(
        ayc.contains("evidence infeasible SUCCINCT open-domain-hybrid-integer-lift"),
        "{ayc}"
    );
    let parsed = cert_io::parse(&ayc).expect("open-domain integer-lift certificate parses");
    assert!(parsed.open_domain_hybrid_integer_lift.is_some());
    let report = cert_io::check(&ayc, OPEN_HYBRID_INTEGER_INF);
    assert_eq!(report.status(), CheckStatus::Verified, "{report:#?}");

    let corrupted = reseal(&ayc.replacen(
        "ay.hybrid-integer-lift-infeasible.v1",
        "ay.hybrid-integer-lift-infeasible.x1",
        1,
    ));
    let rejected = cert_io::check(&corrupted, OPEN_HYBRID_INTEGER_INF);
    assert_eq!(rejected.status(), CheckStatus::Refuted, "{rejected:#?}");

    session.push().expect("scope");
    session
        .add_row(f64::NEG_INFINITY, f64::INFINITY, &[])
        .expect("model mutation");
    assert!(session
        .open_domain_hybrid_integer_lift_infeasibility_certificate()
        .is_none());
}

#[test]
fn hybrid_cut_ledger_artifact_rebuilds_and_verifies() {
    let p = ay_milp::read_mps(HYBRID_INF).expect("model parses");
    let names = p.col_names.clone();
    let scale = p.obj_scale.clone();
    let opts = SolveOpts::new()
        .with_time_limit(std::time::Duration::from_mins(5)) // Hang guard, not a performance limit.
        .with_require_certificates(true);
    let mut session = BabSession::new(p.model, &opts).expect("session");
    let outcome = session.check().expect("full-posture hybrid solve");
    assert!(matches!(outcome, Outcome::Infeasible { .. }), "{outcome:?}");
    assert!(session.replay_claims().is_empty());
    assert!(session.hybrid_pb_lp_infeasibility_certificate().is_some());
    assert!(session
        .hybrid_integer_lift_infeasibility_certificate()
        .is_none());
    let ayc = emit_session_certificate(&session, HYBRID_INF, &names, &scale, &outcome);
    assert!(
        ayc.contains("evidence infeasible SUCCINCT hybrid-pb-lp"),
        "{ayc}"
    );
    let parsed = cert_io::parse(&ayc).expect("hybrid certificate parses");
    assert!(parsed.hybrid_pb_lp.is_some());
    let report = cert_io::check(&ayc, HYBRID_INF);
    assert_eq!(report.status(), CheckStatus::Verified, "{report:#?}");
    let format = "ay.hybrid-pb-lp-infeasible.v1";
    assert!(ayc.contains(format));
    let corrupted = reseal(&ayc.replacen(format, "ay.hybrid-pb-lp-infeasible.x1", 1));
    let rejected = cert_io::check(&corrupted, HYBRID_INF);
    assert_eq!(rejected.status(), CheckStatus::Refuted, "{rejected:#?}");

    session.push().expect("scope");
    session
        .add_row(f64::NEG_INFINITY, f64::INFINITY, &[])
        .expect("model mutation");
    assert!(session.hybrid_pb_lp_infeasibility_certificate().is_none());
}

#[test]
fn hybrid_integer_lift_artifact_rebuilds_and_verifies() {
    let p = ay_milp::read_mps(HYBRID_INTEGER_INF).expect("model parses");
    let names = p.col_names.clone();
    let scale = p.obj_scale.clone();
    let opts = SolveOpts::new()
        .with_time_limit(std::time::Duration::from_secs(20))
        .with_require_certificates(true)
        .with_engine(EngineEconomics::new().with_hybrid_pb_lp(true));
    let mut session = BabSession::new(p.model, &opts).expect("session");
    let outcome = session
        .check()
        .expect("full-posture integer-lift hybrid solve");
    assert!(matches!(outcome, Outcome::Infeasible { .. }), "{outcome:?}");
    assert!(session.replay_claims().is_empty());
    assert!(session.hybrid_pb_lp_infeasibility_certificate().is_none());
    assert!(session
        .hybrid_integer_lift_infeasibility_certificate()
        .is_some());
    let ayc = emit_session_certificate(&session, HYBRID_INTEGER_INF, &names, &scale, &outcome);
    assert!(
        ayc.contains("evidence infeasible SUCCINCT hybrid-integer-lift"),
        "{ayc}"
    );
    let parsed = cert_io::parse(&ayc).expect("integer-lift certificate parses");
    assert!(parsed.hybrid_integer_lift.is_some());
    let report = cert_io::check(&ayc, HYBRID_INTEGER_INF);
    assert_eq!(report.status(), CheckStatus::Verified, "{report:#?}");

    let format = "ay.hybrid-integer-lift-infeasible.v1";
    assert!(ayc.contains(format));
    let corrupted = reseal(&ayc.replacen(format, "ay.hybrid-integer-lift-infeasible.x1", 1));
    let rejected = cert_io::check(&corrupted, HYBRID_INTEGER_INF);
    assert_eq!(rejected.status(), CheckStatus::Refuted, "{rejected:#?}");

    session.push().expect("scope");
    session
        .add_row(f64::NEG_INFINITY, f64::INFINITY, &[])
        .expect("model mutation");
    assert!(session
        .hybrid_integer_lift_infeasibility_certificate()
        .is_none());
}

#[test]
fn milp_optimum_emits_the_witness_and_admits_the_missing_dual() {
    // THE HONESTY REQUIREMENT, end to end. An `Optimal` is TWO claims: the
    // primal half is succinctly checkable and the dual half has no exported
    // independently checkable object in this build. `Outcome::Optimal {
    // cert: None }` cannot distinguish a replay annotation from no dual-side
    // evidence; the emitted claim must.
    let (ayc, out) = solve_and_emit(MILP);
    assert!(matches!(out, Outcome::Optimal { cert: None, .. }));
    let r = cert_io::check(&ayc, MILP);
    // PARTIAL, not UNVERIFIED: the primal half re-derived exactly. See
    // `three_outcomes_a_consumer_must_be_able_to_tell_apart` for why the
    // distinction is load-bearing and `CheckStatus::Partial` for the ny
    // measurement that forced it.
    assert_eq!(r.status(), CheckStatus::Partial, "{r:#?}");
    assert_eq!(r.status().exit_code(), 11);
    assert_ne!(r.status().exit_code(), 0, "VERIFIED stays reserved");
    let primal = r
        .claims()
        .iter()
        .find(|c| c.name() == "primal")
        .expect("primal");
    assert!(primal.is_verified() && primal.kind() == EvidenceKind::Succinct);
    let dual = &r.claims()[1];
    assert!(!dual.is_verified() && dual.name() == "dual", "{dual:#?}");
    // The KIND may be `None` (no device ran) or `Replay` (a device exhausted
    // the space and said so, e.g. `pb-projection-optimal` when the PB route
    // owns the optimum). Replay is strictly MORE information than None and the
    // test must not forbid it. What must never happen is the dual half being
    // dressed as checkable evidence: `Succinct` is the only kind that can earn
    // exit 0, and there is no exported dual object in this build.
    assert_ne!(
        dual.kind(),
        EvidenceKind::Succinct,
        "an unproved dual bound must never be labelled succinct: {dual:#?}"
    );
    assert!(
        matches!(dual.kind(), EvidenceKind::None | EvidenceKind::Replay),
        "unexpected dual evidence kind: {dual:#?}"
    );
    // The witness IS in the file — the thing the old `AY_DUMP_SOL` could not do
    // on an `Optimal` at all.
    assert!(ayc.contains("witness cols="));
}

// ---------------------------------------------------------------------------
// (a2) CLAIM-SET POLICY. The obligations come from the VERDICT, not from
// whichever records survive in the file.
//
// These four are the attacks two independent adversarial reviewers used to make
// the checker print VERIFIED / exit 0 for demonstrably wrong answers. The
// checker validated the claims PRESENT and started at `Verified`, so deleting a
// line deleted the obligation it named — and since `%END` is a body checksum,
// not a signature, `reseal()` (used by every tamper test above) made the edit
// look pristine. Each of these MUST stay refuted.
// ---------------------------------------------------------------------------

#[test]
fn deleting_the_required_dual_claim_cannot_bless_an_optimum() {
    // The misc07 attack in miniature: take an honest certificate, drop the
    // record that carries the unmet obligation, re-seal. Before the claim-set
    // policy this checked VERIFIED with exit 0.
    let (ayc, _) = solve_and_emit(MILP);
    assert!(
        ayc.contains("evidence dual"),
        "fixture must carry a dual record"
    );
    let stripped = rewrite_certificate_lines(
        &ayc,
        |line| !line.trim_start().starts_with("evidence dual"),
        None,
    );
    let forged = reseal(&stripped);
    assert_ne!(forged, ayc, "the deletion must actually apply");
    let r = cert_io::check(&forged, MILP);
    // REFUTED, not merely Unverified: a missing REQUIRED claim is a forged or
    // truncated certificate, which is a stronger failure than an unproven one.
    assert_eq!(r.status(), CheckStatus::Refuted, "{r:#?}");
    assert_eq!(r.status().exit_code(), 20);
    assert!(
        r.notes().iter().any(|n| n.contains("CLAIM-SET VIOLATION")),
        "the refusal must name the claim-set violation: {r:#?}"
    );
}

#[test]
fn promoting_a_feasible_verdict_to_optimal_cannot_bless_a_wrong_value() {
    // The exact misc07 forgery: an honest FEASIBLE certificate whose verdict
    // word is rewritten to `optimal` and whose dual record is dropped. The
    // witness is genuinely feasible, so every check that EXISTS passes; only
    // the claim set catches it.
    let (ayc, _) = solve_and_emit(MILP);
    let promoted = rewrite_certificate_lines(
        &ayc,
        |line| !line.trim_start().starts_with("evidence dual"),
        Some(LineReplacement {
            from: "verdict feasible",
            to: "verdict optimal",
        }),
    );
    let forged = reseal(&promoted);
    let r = cert_io::check(&forged, MILP);
    assert_ne!(
        r.status(),
        CheckStatus::Verified,
        "a promoted verdict with its dual obligation deleted must never verify: {r:#?}"
    );
}

#[test]
fn an_infeasible_verdict_carrying_a_primal_witness_is_self_contradictory() {
    // The checker blessed INFEASIBLE while its own primal check proved a point
    // of that very model feasible. A verdict and its claims must be consistent.
    let (ayc, _) = solve_and_emit(MILP);
    let flipped = reseal(&ayc.replace("verdict optimal", "verdict infeasible"));
    let r = cert_io::check(&flipped, MILP);
    assert_ne!(r.status(), CheckStatus::Verified, "{r:#?}");
    assert!(
        r.notes().iter().any(|n| n.contains("CLAIM-SET VIOLATION")),
        "a primal claim under an infeasible verdict must be rejected: {r:#?}"
    );
}

#[test]
fn deleting_a_replay_claim_cannot_launder_it_into_a_proof() {
    // The markshare1 attack. A REPLAY claim is the checker's honest "I did not
    // check this"; deleting it must not silently upgrade the file to VERIFIED.
    // Synthesised on the MILP fixture so the test does not depend on the
    // lattice device arming.
    let (ayc, _) = solve_and_emit(MILP);
    let stripped = rewrite_certificate_lines(
        &ayc,
        |line| !line.trim_start().starts_with("evidence dual"),
        None,
    );
    let r = cert_io::check(&reseal(&stripped), MILP);
    assert_ne!(
        r.status(),
        CheckStatus::Verified,
        "deleting an unmet obligation must never produce a pass: {r:#?}"
    );
}

#[test]
fn a_bound_verdict_is_unverified_not_refuted_when_its_dual_is_unbacked() {
    // REGRESSION. `Outcome::Bound` is what the solver returns when the budget
    // expires with a rigorous dual bound and no incumbent, and `bound` was
    // absent from the required/forbidden table — so it hit the
    // unrecognised-verdict trap and every ordinary timeout was reported
    // REFUTED / exit 20, indistinguishable from a detected forgery. Found on
    // cod105 by the Gurobi closure benchmark.
    //
    // An honest `bound` certificate must never be REFUTED. It may be
    // Unverified (its dual is typically exported unchecked) or Verified (if the
    // dual is genuinely backed) — but not the alarm reserved for forgeries.
    let (ayc, _) = solve_and_emit(MILP);
    let bounded = rewrite_certificate_lines(
        &ayc,
        |line| !line.trim_start().starts_with("evidence primal"),
        Some(LineReplacement {
            from: "verdict optimal",
            to: "verdict bound",
        }),
    );
    let r = cert_io::check(&reseal(&bounded), MILP);
    assert_ne!(
        r.status(),
        CheckStatus::Refuted,
        "an honest bound verdict must not be REFUTED: {r:#?}"
    );
    assert!(
        !r.notes().iter().any(|n| n.contains("UNRECOGNISED VERDICT")),
        "`bound` must be a RECOGNISED verdict word: {r:#?}"
    );
}

#[test]
fn a_bound_verdict_with_its_dual_record_deleted_is_still_refuted() {
    // The forgery shape must still be caught: `dual` is REQUIRED under `bound`,
    // so deleting it is a truncated certificate, not merely an unproven one.
    // This is what stops the new arm from becoming its own bypass.
    let (ayc, _) = solve_and_emit(MILP);
    let stripped = rewrite_certificate_lines(
        &ayc,
        |line| {
            let t = line.trim_start();
            !t.starts_with("evidence dual") && !t.starts_with("evidence primal")
        },
        Some(LineReplacement {
            from: "verdict optimal",
            to: "verdict bound",
        }),
    );
    let r = cert_io::check(&reseal(&stripped), MILP);
    assert_eq!(r.status(), CheckStatus::Refuted, "{r:#?}");
    assert_eq!(r.status().exit_code(), 20);
    assert!(
        r.notes().iter().any(|n| n.contains("CLAIM-SET VIOLATION")),
        "the refusal must name the claim-set violation: {r:#?}"
    );
}

#[test]
fn a_bound_verdict_carrying_a_primal_witness_is_self_contradictory() {
    // `bound` asserts there is NO incumbent. A primal claim under it is the
    // same class of contradiction as a primal witness under `infeasible`:
    // keeping the honest optimal certificate's primal record while relabelling
    // the verdict must be refused.
    let (ayc, _) = solve_and_emit(MILP);
    let forged = reseal(&ayc.replace("verdict optimal", "verdict bound"));
    let r = cert_io::check(&forged, MILP);
    assert_ne!(r.status(), CheckStatus::Verified, "{r:#?}");
    assert!(
        r.notes().iter().any(|n| n.contains("CLAIM-SET VIOLATION")),
        "a primal claim under a bound verdict must be rejected: {r:#?}"
    );
}

#[test]
fn an_unrecognised_verdict_word_fails_closed() {
    // The claim-set policy's OWN first bypass, found by attacking the fix
    // rather than trusting it. The required/forbidden table keyed on the exact
    // lowercase verdict words and fell through to "no obligations" for anything
    // else, so `Optimal`, `optimum` and `opt` all dodged it and checked
    // VERIFIED / exit 0 on the very misc07 forgery the policy was written to
    // stop. "I do not know what this claims" must never mean "this is fine".
    let (ayc, _) = solve_and_emit(MILP);
    for word in ["Optimal", "optimum", "opt", "OPTIMAL", "optimal_x", ""] {
        let forged = reseal(&ayc.replace("verdict optimal", &format!("verdict {word}")));
        let r = cert_io::check(&forged, MILP);
        assert_ne!(
            r.status(),
            CheckStatus::Verified,
            "verdict `{word}` must not verify: {r:#?}"
        );
    }
}

#[test]
fn root_infeasibility_emits_a_verifying_farkas() {
    // SUBJECT: the root Farkas lane. Pin the solve on native branch-and-bound —
    // see `solve_native_and_emit`. The routed default is covered directly by
    // `root_infeasibility_under_the_shipped_default_still_verifies` below.
    let (ayc, _) = solve_native_and_emit(INF);
    assert!(
        ayc.contains("evidence infeasible SUCCINCT farkas"),
        "the native lane must still export a root Farkas: {ayc}"
    );
    let r = cert_io::check(&ayc, INF);
    assert_eq!(r.status(), CheckStatus::Verified, "{r:#?}");
}

/// The shipped CLI default is `--require witness` with structure routing ON.
/// Whichever lane claims the model, that posture must never emit WEAKER
/// evidence than `--require full` — the exact defect this pair exists to catch:
/// `witness` once emitted `REPLAY direct-cnf-unsat` (verify exit 10) on a model
/// `full` refuted with a succinct, third-party-checkable proof (exit 0).
///
/// SCOPE, measured by sabotage: this test pins the `.ayc` OUTCOME (both postures
/// verify at exit 0) and is not sensitive to lane ORDER — re-gating the
/// proof-exporting routes back behind `require_certificates` leaves it green,
/// because the ordinary-posture PB route publishes the same artifact for these
/// fixtures. The tripwire for the ordering itself is
/// `tree_cert::routed_infeasibility_still_carries_replayable_evidence`, which
/// does fail under that sabotage. Keep both: this one guards the emitted file,
/// that one guards which lane is allowed to own the verdict.
#[test]
fn root_infeasibility_under_the_shipped_default_still_verifies() {
    for model in [BIN_INF, INF, DP_INF, BDD_INF, PARITY_INF] {
        let (default_ayc, _) = solve_and_emit(model);
        let default_report = cert_io::check(&default_ayc, model);
        assert_eq!(
            default_report.status(),
            CheckStatus::Verified,
            "the shipped default posture must emit verifying evidence: {default_report:#?}"
        );
        assert!(
            default_ayc.contains("evidence infeasible SUCCINCT"),
            "a REPLAY-only claim under the default posture is an evidence \
             downgrade, not a posture: {default_ayc}"
        );
        let (full_ayc, _) = solve_full_and_emit(model);
        let full_report = cert_io::check(&full_ayc, model);
        assert_eq!(
            full_report.status(),
            CheckStatus::Verified,
            "certificate posture must verify too: {full_report:#?}"
        );
    }
}

#[test]
fn every_verdict_shape_emits_something_parseable() {
    for text in [LP, MILP, INF] {
        let (ayc, _) = solve_and_emit(text);
        let parsed = cert_io::parse(&ayc).expect("emitted certificates parse");
        assert!(parsed.end_digest_ok, "the emitter seals what it writes");
        assert!(!parsed.claims.is_empty());
    }
}

// ---------------------------------------------------------------------------
// (b) TAMPERING. A checker that cannot fail is worthless.
// ---------------------------------------------------------------------------

#[test]
fn tamper_witness_value_is_refuted() {
    let (ayc, _) = solve_and_emit(LP);
    // `x 0 X 2` is the optimum's first coordinate. Move it and the point either
    // stops being feasible or stops attaining the claimed value.
    let tampered = reseal(&ayc.replace("x 0 X 2\n", "x 0 X 1\n"));
    assert_ne!(tampered, ayc, "the tamper must actually apply");
    let r = cert_io::check(&tampered, LP);
    assert_eq!(r.status(), CheckStatus::Refuted, "{r:#?}");
    assert_eq!(r.status().exit_code(), 20);
}

#[test]
fn tamper_claimed_optimum_is_refuted() {
    let (ayc, _) = solve_and_emit(LP);
    // Claim a better optimum than the point attains. Both halves must catch it:
    // the witness no longer attains the value, and the dual bound no longer
    // meets it.
    let tampered = reseal(&ayc.replace("value=4 frame=file", "value=3 frame=file"));
    assert_ne!(tampered, ayc);
    let r = cert_io::check(&tampered, LP);
    assert_eq!(r.status(), CheckStatus::Refuted, "{r:#?}");
    assert!(r
        .claims()
        .iter()
        .filter(|c| c.name() == "primal" || c.name() == "dual")
        .all(|c| !c.is_verified()));
}

/// A `.replace` that MUST change something.
///
/// `assert_ne!(tampered, ayc)` is not that guard: it fires only after
/// `reseal()`, which rewrites the `%END` digest over the (unchanged) body and
/// can still differ for reasons unrelated to the edit — and when it does not
/// differ the test reads as "the tamper was refuted" while having tampered with
/// nothing. Both multiplier tests below silently became no-ops exactly this way
/// once a routed lane started answering `INF` with a decision DAG that has no
/// `mult` lines at all. Guard the NEEDLE, before the edit.
fn tamper(ayc: &str, needle: &str, replacement: &str) -> String {
    assert!(
        ayc.contains(needle),
        "VACUOUS TAMPER: `{needle}` is not present, so this test would pass \
         without exercising anything. The fixture or the emitting lane changed \
         shape; re-point the tamper, do not delete it.\n{ayc}"
    );
    let tampered = reseal(&ayc.replace(needle, replacement));
    assert_ne!(tampered, ayc, "the tamper must actually apply");
    tampered
}

#[test]
fn tamper_multiplier_is_refuted() {
    // SUBJECT: Farkas multipliers, so this must run on a certificate that HAS
    // them — see `solve_native_and_emit`. The routed lanes' own formats each
    // get a semantic tamper battery in section (b2).
    let (ayc, _) = solve_native_and_emit(INF);
    // Rescale one Farkas multiplier: the combination stops being the identity
    // `0·x >= positive`.
    let tampered = tamper(&ayc, "mult row 1 upper 1\n", "mult row 1 upper 2\n");
    let r = cert_io::check(&tampered, INF);
    assert_eq!(r.status(), CheckStatus::Refuted, "{r:#?}");
}

#[test]
fn tamper_dropped_multiplier_is_refuted() {
    let (ayc, _) = solve_native_and_emit(INF);
    let tampered = tamper(&ayc, "mult row 0 lower 1\n", "");
    let r = cert_io::check(&tampered, INF);
    assert_eq!(r.status(), CheckStatus::Refuted, "{r:#?}");
}

#[test]
fn tamper_model_file_digest_is_a_mismatch() {
    let (ayc, _) = solve_and_emit(LP);
    let parsed = cert_io::parse(&ayc).expect("parses");
    let forged = "0".repeat(64);
    let tampered = reseal(&ayc.replace(&parsed.header.file_digest, &forged));
    assert_ne!(tampered, ayc);
    let r = cert_io::check(&tampered, LP);
    assert_eq!(r.status(), CheckStatus::Mismatch, "{r:#?}");
    assert_eq!(r.status().exit_code(), 30);
}

#[test]
fn tamper_canonical_model_digest_is_a_mismatch() {
    let (ayc, _) = solve_and_emit(LP);
    let parsed = cert_io::parse(&ayc).expect("parses");
    let forged = "1".repeat(64);
    let tampered = reseal(&ayc.replace(&parsed.header.canon_digest, &forged));
    let r = cert_io::check(&tampered, LP);
    assert_eq!(r.status(), CheckStatus::Mismatch, "{r:#?}");
}

#[test]
fn tamper_end_digest_is_a_mismatch() {
    let (ayc, _) = solve_and_emit(LP);
    // Edit the body WITHOUT resealing: the trailing digest catches it even when
    // the edited content would still verify.
    let tampered = ayc.replace("solver ay-milp", "solver not-ay-milp");
    assert_ne!(tampered, ayc);
    let r = cert_io::check(&tampered, LP);
    assert_eq!(r.status(), CheckStatus::Mismatch, "{r:#?}");
}

#[test]
fn certificate_checked_against_a_different_model_is_a_mismatch() {
    let (ayc, _) = solve_and_emit(LP);
    let r = cert_io::check(&ayc, MILP);
    assert_eq!(r.status(), CheckStatus::Mismatch, "{r:#?}");
}

// ---------------------------------------------------------------------------
// (c) MISLABELLING. The one failure that would make the format worse than
//     emitting nothing.
// ---------------------------------------------------------------------------

#[test]
fn a_replay_claim_relabelled_succinct_is_rejected_by_the_parser() {
    // Hand-build the exact forgery the format exists to prevent: a replay block
    // (an exhaustive sweep, no exported object) whose evidence record claims
    // SUCCINCT. This must fail at PARSE time — not merely fail verification —
    // because the source-token set for each kind is closed.
    let forged = "%AYC 1
model file sha256:"
        .to_string()
        + &"0".repeat(64)
        + " bytes=1 form=text
model canon v1 sha256:"
        + &"0".repeat(64)
        + "
model shape rows=0 cols=0 intcols=0 sense=min obj_scale=1
solver ay-milp test
verdict optimal value=1 frame=file
evidence dual SUCCINCT objective-face-empty
replay objective-face-empty
device lattice-cvp
method ahl-hnf-lll+bkz+schnorr-euchner
arithmetic outward-rounded-f64-interval
nodes-visited 1
node-budget 4000000000
outcome exhausted
tcb crates/ay-milp/src/lattice.rs
end
";
    let sealed = reseal(&forged);
    let err = cert_io::parse(&sealed).expect_err("a mislabelled evidence record must not parse");
    assert!(
        matches!(err, cert_io::CertIoError::MislabelledEvidence { .. }),
        "{err:?}"
    );
    // And the checker reports it as REFUTED, never as a pass.
    let r = cert_io::check(&sealed, LP);
    assert_eq!(r.status(), CheckStatus::Refuted, "{r:#?}");
}

#[test]
fn a_succinct_source_relabelled_replay_is_rejected_by_the_parser() {
    let (ayc, _) = solve_and_emit(LP);
    let forged = reseal(&ayc.replace(
        "evidence primal SUCCINCT witness",
        "evidence primal REPLAY witness",
    ));
    let err = cert_io::parse(&forged).expect_err("REPLAY cannot name a succinct block");
    assert!(
        matches!(err, cert_io::CertIoError::MislabelledEvidence { .. }),
        "{err:?}"
    );
}

#[test]
fn a_succinct_claim_whose_block_is_missing_is_refuted() {
    let (ayc, _) = solve_and_emit(INF);
    // Delete the farkas block but keep the SUCCINCT claim.
    let mut body = String::new();
    for l in ayc
        .lines()
        .filter(|l| !l.starts_with("farkas ") && !l.starts_with("mult ") && *l != "end")
    {
        body.push_str(l);
        body.push('\n');
    }
    let forged = reseal(&body);
    let r = cert_io::check(&forged, INF);
    assert_eq!(r.status(), CheckStatus::Refuted, "{r:#?}");
}

#[test]
fn a_certificate_bounding_a_different_objective_is_refuted() {
    // THE CHECK A TRUSTING CHECKER WOULD SKIP.
    //
    // For `min x + 2y` s.t. `x + y >= 3`, the single multiplier `1 ×
    // (row0 lower)` combines to exactly `x + y - 3`. That is a PERFECTLY VALID
    // optimality certificate — for the objective `x + y` with bound 3. It
    // verifies. It says nothing about the model's `x + 2y`, and
    // `tighten_col_bounds` legitimately produces certificates over other
    // objectives, so this is not a hypothetical shape. The checker must compare
    // the certificate's own named objective against the model's and reject.
    let forged = format!(
        "%AYC 1
model file sha256:{} bytes={} form=text
model canon v1 sha256:{}
model shape rows=2 cols=2 intcols=0 sense=min obj_scale=1
solver ay-milp test
verdict optimal value=3 frame=file
evidence dual SUCCINCT optcert
optcert sense=min bound=3 frame=model trivial=0
obj 0 1
obj 1 1
mult row 0 lower 1
end
",
        cert_io::sha256_hex(LP.as_bytes()),
        LP.len(),
        cert_io::canonical_digest(&ay_milp::read_mps(LP).expect("parses").model),
    );
    let sealed = reseal(&forged);
    let r = cert_io::check(&sealed, LP);
    assert_eq!(r.status(), CheckStatus::Refuted, "{r:#?}");
    let dual = &r.claims()[0];
    assert!(
        dual.detail().contains("DIFFERENT objective"),
        "the rejection must name the reason: {}",
        dual.detail()
    );
}

// ---------------------------------------------------------------------------
// (d) Wire-format strictness. A canonical format keeps the seal meaningful.
// ---------------------------------------------------------------------------

#[test]
fn non_canonical_rationals_do_not_parse() {
    let (ayc, _) = solve_and_emit(LP);
    for bad in ["2/4", "6/3", "4/1", "1/0", "2/-1"] {
        let forged = reseal(&ayc.replace("value=4 frame=file", &format!("value={bad} frame=file")));
        assert!(
            cert_io::parse(&forged).is_err(),
            "`{bad}` must not parse as a canonical wire rational"
        );
    }
}

#[test]
fn a_reordered_witness_does_not_parse() {
    let (ayc, _) = solve_and_emit(LP);
    let forged = reseal(&ayc.replace("x 0 X", "x 1 X"));
    assert!(
        cert_io::parse(&forged).is_err(),
        "a witness whose indices do not match their position must be rejected"
    );
}

#[test]
fn an_unknown_record_does_not_parse() {
    let (ayc, _) = solve_and_emit(LP);
    let forged = reseal(&format!("{ayc}\nsurprise 1\n").replace("%END", "#END"));
    assert!(cert_io::parse(&forged).is_err());
}

#[test]
fn a_future_format_version_is_refused() {
    let (ayc, _) = solve_and_emit(LP);
    let forged = reseal(&ayc.replace("%AYC 1", "%AYC 2"));
    assert!(cert_io::parse(&forged).is_err());
    assert_eq!(cert_io::check(&forged, LP).status(), CheckStatus::Refuted);
}

// ---------------------------------------------------------------------------
// (e) Truncation DOWNGRADES; it never silently drops evidence.
// ---------------------------------------------------------------------------

#[test]
fn a_size_cap_downgrades_the_claim_it_drops() {
    let p = ay_milp::read_mps(LP).expect("parses");
    let names = p.col_names.clone();
    let scale = p.obj_scale.clone();
    let opts = SolveOpts::new();
    let mut s = BabSession::new(p.model, &opts).expect("session");
    let outcome = s.check().expect("solve");
    let ctx = cert_io::EmitCtx {
        model: s.model(),
        model_text: LP,
        col_names: &names,
        obj_scale: &scale,
        provenance: "host=test",
        replay_claims: s.replay_claims(),
        affine_aggregation_certificate: s.affine_aggregation_certificate(),
        parity_infeasibility_certificate: s.parity_infeasibility_certificate(),
        sat_relu_infeasibility_certificate: s.sat_relu_infeasibility_certificate(),
        network_design_infeasibility_certificate: s.network_design_infeasibility_certificate(),
        network_design_optimality_certificate: s.network_design_optimality_certificate(),
        block_angular_optimality_certificate: s.block_angular_optimality_certificate(),
        milp_optimality_tree_certificate: None,
        root_dual_bound_certificate: None,
        single_machine_scheduling_optimality_certificate: s
            .single_machine_scheduling_optimality_certificate(),
        single_row_dp_infeasibility_certificate: s.single_row_dp_infeasibility_certificate(),
        multi_row_bdd_infeasibility_certificate: s.multi_row_bdd_infeasibility_certificate(),
        open_domain_single_row_dp_infeasibility_certificate: s
            .open_domain_single_row_dp_infeasibility_certificate(),
        open_domain_multi_row_bdd_infeasibility_certificate: s
            .open_domain_multi_row_bdd_infeasibility_certificate(),
        open_domain_hybrid_pb_lp_infeasibility_certificate: s
            .open_domain_hybrid_pb_lp_infeasibility_certificate(),
        open_domain_hybrid_integer_lift_infeasibility_certificate: s
            .open_domain_hybrid_integer_lift_infeasibility_certificate(),
        hybrid_pb_lp_infeasibility_certificate: s.hybrid_pb_lp_infeasibility_certificate(),
        hybrid_integer_lift_infeasibility_certificate: s
            .hybrid_integer_lift_infeasibility_certificate(),
        // Small enough that no block fits.
        max_bytes: Some(1),
    };
    let ayc = cert_io::emit(&ctx, &outcome);
    assert!(ayc.contains("truncated witness"), "{ayc}");
    assert!(ayc.contains("evidence primal NONE truncated"), "{ayc}");
    let r = cert_io::check(&ayc, LP);
    // Downgraded, not passed and not silently shortened.
    assert_eq!(r.status(), CheckStatus::Unverified, "{r:#?}");
}

// ---------------------------------------------------------------------------
// (f) The canonical model digest binds the MODEL, not the file.
// ---------------------------------------------------------------------------

#[test]
fn canonical_digest_separates_models_the_file_digest_cannot() {
    let a = ay_milp::read_mps(LP).expect("parses").model;
    let mut b = a.clone();
    // A bound change the file digest would only notice as "different bytes";
    // the canonical digest notices it as "different model".
    let c = b.col_at(0).expect("col 0");
    b.fix_col(c, 1.0);
    assert_ne!(cert_io::canonical_digest(&a), cert_io::canonical_digest(&b));
    // And it is a pure function of the model, not of how it was built.
    assert_eq!(
        cert_io::canonical_digest(&a),
        cert_io::canonical_digest(&a.clone())
    );
}

#[test]
fn value_frames_are_named_and_honoured() {
    // The reported optimum is in FILE units; an `OptimalityCertificate`'s bound
    // is in MODEL units (post-`obj_scale`). A checker that divided once and one
    // that divided twice would both look right, so the frame is on the wire.
    let (ayc, _) = solve_and_emit(LP);
    let parsed = cert_io::parse(&ayc).expect("parses");
    assert_eq!(parsed.value_frame, "file");
    assert_eq!(parsed.header.obj_scale, BigRational::one());
    assert!(
        ayc.contains("frame=model"),
        "the optcert bound names its frame"
    );
}

// ---------------------------------------------------------------------------
// (g) THE THREE OUTCOMES. A consumer must be able to tell them apart.
// ---------------------------------------------------------------------------

/// The original failure that motivated this status split was the downstream optimization consumer's captured W1
/// corpus: an exactly checked primal half was indistinguishable from a file
/// where nothing checked out. W1's zero-objective SAT verdicts now also export
/// the exact empty-multiplier bound and therefore verify completely; this test
/// retains the still-real generic case where a nonzero-objective MILP has a
/// checked incumbent but no exported whole-tree optimality proof.
///
/// This pins the three cases apart on BOTH channels a consumer can read — the
/// exit code and the census line — and pins the reservation of exit 0 while
/// doing it.
#[test]
fn three_outcomes_a_consumer_must_be_able_to_tell_apart() {
    // (a) A witness verified exactly, and something else has no object.
    let (ayc, _) = solve_and_emit(MILP);
    let a = cert_io::check(&ayc, MILP);
    assert_eq!(a.status(), CheckStatus::Partial, "{a:#?}");
    assert_eq!(a.status().exit_code(), 11);
    assert_eq!(a.claims_in(ClaimStanding::Verified), vec!["primal"]);
    assert!(a.claims_in(ClaimStanding::Refuted).is_empty());
    assert_eq!(a.census(), "CLAIMS verified=primal refuted=- unbacked=dual");

    // (b) NOTHING verified. The shape every uncertified `Infeasible` takes:
    // one `infeasible` claim, downgraded to `NONE`, no exported block at all.
    let (inf_ayc, _) = solve_and_emit(INF);
    let stripped = reseal(
        &inf_ayc
            .lines()
            .take_while(|l| !l.starts_with("farkas"))
            .map(|l| {
                if l.starts_with("evidence infeasible") {
                    "evidence infeasible NONE".to_owned()
                } else {
                    (*l).to_owned()
                }
            })
            .collect::<Vec<_>>()
            .join("\n"),
    );
    let b = cert_io::check(&stripped, INF);
    assert_eq!(b.status(), CheckStatus::Unverified, "{b:#?}");
    assert_eq!(b.status().exit_code(), 10);
    assert!(b.claims_in(ClaimStanding::Verified).is_empty());
    assert_eq!(
        b.census(),
        "CLAIMS verified=- refuted=- unbacked=infeasible",
        "an UNSAT that exported nothing must read as nothing verified"
    );

    // (c) REFUTED, and it must stay unmistakable: a SUCCINCT block that does
    // not hold is a different animal from one that was never exported.
    let (lp_ayc, _) = solve_and_emit(LP);
    let broken = reseal(
        &lp_ayc
            .lines()
            .map(|l| {
                if let Some(rest) = l.strip_prefix("x 0 X ") {
                    let _ = rest;
                    "x 0 X 999".to_owned()
                } else {
                    (*l).to_owned()
                }
            })
            .collect::<Vec<_>>()
            .join("\n"),
    );
    let c = cert_io::check(&broken, LP);
    assert_eq!(c.status(), CheckStatus::Refuted, "{c:#?}");
    assert_eq!(c.status().exit_code(), 20);
    assert_eq!(c.claims_in(ClaimStanding::Refuted), vec!["primal"]);
    assert!(
        c.census().contains("refuted=primal"),
        "a refuted claim must be named as refuted, never as merely unbacked: {}",
        c.census()
    );
}

/// The reservation, stated as a test rather than as a comment: no status this
/// checker can produce other than `Verified` exits 0, and `Partial` is one of
/// them.
#[test]
fn only_verified_earns_exit_zero() {
    for s in [
        CheckStatus::Verified,
        CheckStatus::Partial,
        CheckStatus::Unverified,
        CheckStatus::Refuted,
        CheckStatus::Mismatch,
    ] {
        assert_eq!(
            s.exit_code() == 0,
            s == CheckStatus::Verified,
            "{s:?} must not share exit 0 with VERIFIED"
        );
    }
    // And the codes are distinct, so a consumer can switch on them.
    let codes = [
        CheckStatus::Verified.exit_code(),
        CheckStatus::Partial.exit_code(),
        CheckStatus::Unverified.exit_code(),
        CheckStatus::Refuted.exit_code(),
        CheckStatus::Mismatch.exit_code(),
    ];
    let mut sorted = codes.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    assert_eq!(sorted.len(), codes.len(), "exit codes must be distinct");
}

// ---------------------------------------------------------------------------
// (b2) PER-FORMAT SEMANTIC TAMPER BATTERY.
//
// The structure-recognition routes answer with proof objects the Farkas and
// tree lanes never emitted: decision DAGs, reachability checkpoints, cut
// ledgers, Hoffman projections. Nine of them ship on the CLI default.
//
// The corruption tests those formats arrived with flip `.v1` -> `.x1`, which
// exercises ONE string compare (e.g. `certificate.format != …_FORMAT` in
// `ay-pb-core/src/multi_row_bdd.rs`) and would keep passing if the replay
// verifier were stubbed to `Ok(())`. This battery mutates the PROOF BODY
// instead, one literal at a time, and repairs the declared `json_bytes` so the
// length record cannot absorb the edit before the verifier is ever reached.
//
// Two properties per format:
//   * SOUNDNESS  — no mutation of the proof body may ever produce `Verified`.
//   * FAIL-CAPABILITY — at least one of them must reach `Refuted`, so "never
//     verified" cannot be satisfied by a checker that refuses everything.
// Plus the cross-model probe the tree lane used to carry alone: a GENUINE proof
// re-headered onto a same-shape FEASIBLE variant must be REFUTED.
// ---------------------------------------------------------------------------

/// Rewrite one full line of an MPS fixture, asserting the edit applies.
fn model_variant(model: &str, needle: &str, replacement: &str) -> String {
    assert!(
        model.contains(needle),
        "fixture variant needle `{needle}` not found; the fixture changed shape"
    );
    model.replace(needle, replacement)
}

/// The `<source> … json_bytes=N` header line index, the JSON payload line that
/// follows it, and the declared length.
fn json_block(ayc: &str, source: &str) -> (usize, String, usize) {
    let lines: Vec<&str> = ayc.lines().collect();
    let idx = lines
        .iter()
        .position(|l| l.starts_with(source) && l.contains("json_bytes="))
        .unwrap_or_else(|| panic!("no `{source}` json block in:\n{ayc}"));
    let declared: usize = lines[idx]
        .split("json_bytes=")
        .nth(1)
        .expect("json_bytes record")
        .split_whitespace()
        .next()
        .expect("json_bytes value")
        .parse()
        .expect("json_bytes is a number");
    let payload = lines[idx + 1].to_owned();
    assert_eq!(
        declared,
        payload.len(),
        "the block must declare its own payload length"
    );
    (idx, payload, declared)
}

/// Swap in a mutated payload AND repair the declared `json_bytes`.
///
/// Repairing the length is what makes this a SEMANTIC tamper. Leave it stale
/// and the parser rejects on the length record, the replay verifier is never
/// entered, and the test proves nothing at all about the proof checker.
fn retarget_payload(ayc: &str, source: &str, payload: &str) -> String {
    let (idx, old, declared) = json_block(ayc, source);
    assert_ne!(old, payload, "a payload mutation must change the payload");
    let mut lines: Vec<String> = ayc.lines().map(str::to_owned).collect();
    lines[idx] = lines[idx].replace(
        &format!("json_bytes={declared}"),
        &format!("json_bytes={}", payload.len()),
    );
    lines[idx + 1] = payload.to_owned();
    reseal(&lines.join("\n"))
}

/// Every single-literal mutation of a JSON proof payload.
///
/// Deliberately skips the `"format"` VALUE: that token is what `.v1` -> `.x1`
/// already covers, and a battery that lands there measures a string compare
/// rather than the refutation.
fn payload_mutations(payload: &str) -> Vec<(usize, String, String)> {
    let body = payload
        .find("\"format\":\"")
        .and_then(|i| payload[i + 10..].find('"').map(|j| i + 10 + j + 1))
        .unwrap_or(0);
    let bytes = payload.as_bytes();
    let mut out: Vec<(usize, String, String)> = Vec::new();
    let mut i = body;
    while i < bytes.len() && out.len() < 48 {
        if bytes[i].is_ascii_digit() {
            let start = i;
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            if let Ok(n) = payload[start..i].parse::<u128>() {
                let mut bumped = payload.to_owned();
                bumped.replace_range(start..i, &(n + 1).to_string());
                out.push((start, format!("int@{start}:{n}->{}", n + 1), bumped));
            }
            continue;
        }
        if payload[i..].starts_with("true") {
            let mut flipped = payload.to_owned();
            flipped.replace_range(i..i + 4, "false");
            out.push((i, format!("bool@{i}:true->false"), flipped));
            i += 4;
            continue;
        }
        if payload[i..].starts_with("false") {
            let mut flipped = payload.to_owned();
            flipped.replace_range(i..i + 5, "true");
            out.push((i, format!("bool@{i}:false->true"), flipped));
            i += 5;
            continue;
        }
        // A decision-DAG terminal. Turning a `null` child into a real child
        // index rewires the refutation's control flow.
        if payload[i..].starts_with("null") {
            let mut linked = payload.to_owned();
            linked.replace_range(i..i + 4, "0");
            out.push((i, format!("null@{i}->0"), linked));
            i += 4;
            continue;
        }
        i += 1;
    }
    // Structural truncations: empty out the array that CARRIES the proof. A
    // checker that only validates the records present would accept these.
    for container in [
        "\"layers\":[",
        "\"checkpoints\":[",
        "\"cuts\":[",
        "\"multipliers\":[",
        "\"items\":[",
        "\"variable_order\":[",
    ] {
        if let Some(start) = payload.find(container) {
            let open = start + container.len() - 1;
            let mut depth = 0i32;
            let bytes = payload.as_bytes();
            let mut end = open;
            for (offset, &b) in bytes[open..].iter().enumerate() {
                match b {
                    b'[' => depth += 1,
                    b']' => {
                        depth -= 1;
                        if depth == 0 {
                            end = open + offset;
                            break;
                        }
                    }
                    _ => {}
                }
            }
            if end > open + 1 {
                let mut emptied = payload.to_owned();
                emptied.replace_range(open + 1..end, "");
                out.push((open, format!("emptied {container}"), emptied));
            }
        }
    }
    out
}

/// Byte spans of the `assignment` array of a CERTIFIED hybrid cut.
///
/// THE ONE DOCUMENTED PROVENANCE FIELD in any shipped proof body, and the only
/// literal in this battery whose mutation is allowed to keep verifying.
///
/// Why it is sound to allow it. A `Certified` cut carries a projected Benders
/// row proven globally valid from its OWN Farkas multipliers against the
/// original model (`CertifiedRow::verify`), and the master constraint the cut
/// contributes is rebuilt from `row` alone (`matches_restriction`'s Certified
/// arm destructures `Self::Certified { row, .. }`). `assignment` feeds exactly
/// one check, `cut_violated` — `lhs < row.lb`, the PROGRESS property that the
/// row really does exclude the point that generated it. That check does run on
/// the verify path; a flipped bit survives here only because this fixture's row
/// is the globally infeasible `0 >= 1`, which excludes EVERY assignment. So the
/// mutated certificate is not an unchecked certificate — it is a different,
/// still-true one.
///
/// This is not a licence to leave the guard untested: `cut_violated` is covered
/// directly by `hybrid_pb_lp::certified_hybrid_rejects_cut_bound_to_another_assignment`,
/// on a master where the projected row separates only SOME assignments so the
/// bit is load-bearing. A `NoGood` cut's `assignment` is NOT in this span and
/// is fully bound — it defines the no-good inequality itself.
fn certified_assignment_spans(payload: &str) -> Vec<(usize, usize)> {
    const NEEDLE: &str = "\"kind\":\"certified\",\"assignment\":[";
    let mut spans = Vec::new();
    let mut from = 0usize;
    while let Some(rel) = payload[from..].find(NEEDLE) {
        let start = from + rel + NEEDLE.len();
        let end = payload[start..]
            .find(']')
            .map_or(start, |offset| start + offset);
        spans.push((start, end));
        from = end.max(start + 1);
    }
    spans
}

/// Replace the three model-binding header lines of `proof` with `target`'s, so
/// a genuine refutation is presented as a refutation of a DIFFERENT model.
fn splice_model_header(proof: &str, target: &str) -> String {
    let take = |doc: &str, key: &str| -> String {
        doc.lines()
            .find(|l| l.starts_with(key))
            .unwrap_or_else(|| panic!("no `{key}` header in:\n{doc}"))
            .to_owned()
    };
    let mut out: Vec<String> = Vec::new();
    for line in proof.lines() {
        if line.starts_with("model file ") {
            out.push(take(target, "model file "));
        } else if line.starts_with("model canon ") {
            out.push(take(target, "model canon "));
        } else if line.starts_with("model shape ") {
            out.push(take(target, "model shape "));
        } else {
            out.push(line.to_owned());
        }
    }
    reseal(&out.join("\n"))
}

/// A fixture, the evidence `source` its shipped lane emits, and a same-shape
/// FEASIBLE variant its genuine proof must refuse to prove.
struct FormatCase {
    source: &'static str,
    model: String,
    feasible: String,
    /// False for `parity-gf2`, whose body is a line-oriented `row i` list, not
    /// a JSON payload. Its own body tamper lives in
    /// `parity_infeasibility_artifact_round_trips_and_row_tampering_fails`,
    /// which points the proof at a source row that does not exist — a real
    /// semantic tamper, not a format-string flip. The cross-model probe below
    /// still covers it, because that one is body-agnostic.
    json_body: bool,
}

fn format_cases() -> Vec<FormatCase> {
    vec![
        FormatCase {
            json_body: true,
            source: "single-row-dp",
            model: DP_INF.to_owned(),
            // 6+10 = 16 is reachable; 18 is not.
            feasible: model_variant(
                DP_INF,
                "    RHS       R1        18",
                "    RHS       R1        16",
            ),
        },
        FormatCase {
            json_body: true,
            source: "multi-row-bdd",
            model: BDD_INF.to_owned(),
            // R3 is the "at most two selected" cap that makes the pair of lower
            // rows unsatisfiable. Relax it and X=Y=Z=1 is feasible.
            feasible: model_variant(
                BDD_INF,
                "    RHS       R3        5",
                "    RHS       R3        9",
            ),
        },
        FormatCase {
            json_body: false,
            source: "parity-gf2",
            model: PARITY_INF.to_owned(),
            // -1 is the odd right-hand side; -2 restores an even system.
            feasible: model_variant(
                PARITY_INF,
                "    RHS       R1       -1",
                "    RHS       R1       -2",
            ),
        },
        FormatCase {
            json_body: true,
            source: "open-domain-dp",
            model: OPEN_INF.to_owned(),
            // RLOW 1 vs RUP 0 is the residual contradiction on X.
            feasible: model_variant(
                OPEN_INF,
                "    RHS       ROPEN     2          RLOW      1",
                "    RHS       ROPEN     2          RLOW      0",
            ),
        },
        FormatCase {
            json_body: true,
            source: "hybrid-pb-lp",
            model: HYBRID_INF.to_owned(),
            feasible: model_variant(
                HYBRID_INF,
                "    RHS       RLOW       1         RUP        0",
                "    RHS       RLOW       0         RUP        0",
            ),
        },
        FormatCase {
            json_body: true,
            source: "hybrid-integer-lift",
            model: HYBRID_INTEGER_INF.to_owned(),
            feasible: model_variant(
                HYBRID_INTEGER_INF,
                "    RHS       RLOW       1         RUP        0",
                "    RHS       RLOW       0         RUP        0",
            ),
        },
        FormatCase {
            json_body: true,
            source: "open-domain-hybrid-pb-lp",
            model: OPEN_HYBRID_INF.to_owned(),
            feasible: model_variant(
                OPEN_HYBRID_INF,
                "    RHS       ROPEN      2         RLOW       1",
                "    RHS       ROPEN      2         RLOW       0",
            ),
        },
        FormatCase {
            json_body: true,
            source: "open-domain-hybrid-integer-lift",
            model: OPEN_HYBRID_INTEGER_INF.to_owned(),
            feasible: model_variant(
                OPEN_HYBRID_INTEGER_INF,
                "    RHS       ROPEN      2         RLOW       1",
                "    RHS       ROPEN      2         RLOW       0",
            ),
        },
        FormatCase {
            json_body: true,
            source: "network-design-infeasibility",
            model: NETWORK_INF.to_owned(),
            // The same exact network with its capacity controller free again.
            feasible: NETWORK_OPT.to_owned(),
        },
    ]
}

#[test]
fn every_shipped_infeasibility_format_refutes_a_semantic_payload_tamper() {
    let mut covered = 0usize;
    for case in format_cases() {
        if !case.json_body {
            continue;
        }
        covered += 1;
        let (ayc, _) = solve_and_emit(&case.model);
        assert!(
            ayc.contains(&format!("evidence infeasible SUCCINCT {}", case.source)),
            "fixture must still emit `{}` on the SHIPPED default posture; if the \
             route moved, re-point this case — do not drop the format's only \
             semantic tamper coverage:\n{ayc}",
            case.source
        );
        let baseline = cert_io::check(&ayc, &case.model);
        assert_eq!(
            baseline.status(),
            CheckStatus::Verified,
            "{}: honest certificate must verify: {baseline:#?}",
            case.source
        );

        let (_, payload, _) = json_block(&ayc, case.source);
        let mutations = payload_mutations(&payload);
        assert!(
            mutations.len() >= 3,
            "{}: a proof body with fewer than three mutable literals is not a \
             proof body — the battery would be vacuous",
            case.source
        );

        let provenance = certified_assignment_spans(&payload);
        let mut refuted = 0usize;
        let mut inert: Vec<String> = Vec::new();
        for (pos, label, mutated) in &mutations {
            let doc = retarget_payload(&ayc, case.source, mutated);
            let r = cert_io::check(&doc, &case.model);
            match r.status() {
                CheckStatus::Refuted => refuted += 1,
                CheckStatus::Verified if provenance.iter().any(|&(a, b)| *pos >= a && *pos < b) => {
                    // The documented provenance field; see
                    // `certified_assignment_spans`. Nothing else may land here.
                    assert!(
                        case.source.starts_with("hybrid-")
                            || case.source.starts_with("open-domain-hybrid-"),
                        "{} [{label}]: only the hybrid cut ledger has a \
                         provenance field; a new format must not inherit the \
                         allowlist",
                        case.source
                    );
                }
                CheckStatus::Verified => inert.push(format!("{}[{label}]", case.source)),
                _ => {}
            }
        }
        assert!(
            inert.is_empty(),
            "these proof-body literals are INERT — the checker verified a \
             mutated proof. Either the field is load-bearing and the verifier \
             must bind it, or it is provenance and belongs on the documented \
             allowlist with a named test covering the guard it stands in for: \
             {inert:?}"
        );
        assert!(
            refuted > 0,
            "{}: no payload mutation reached REFUTED. `never Verified` is also \
             satisfied by a checker that refuses everything; this half proves \
             the refutation is the guard firing.",
            case.source
        );
    }
    // A `continue` in a table-driven test is how a battery quietly stops
    // covering anything. Pin the count.
    assert_eq!(
        covered, 8,
        "expected eight JSON-bodied infeasibility formats under semantic tamper"
    );
}

#[test]
fn every_shipped_infeasibility_format_refutes_a_feasible_variant() {
    for case in format_cases() {
        let (proof, _) = solve_and_emit(&case.model);
        assert!(
            proof.contains(&format!("evidence infeasible SUCCINCT {}", case.source)),
            "{}: fixture must emit the format under test",
            case.source
        );
        // A genuine, untouched refutation — re-addressed to a model that is
        // FEASIBLE. This is the property `emitted_certificate_refutes_on_a
        // _feasible_variant` carried for the tree lane and nothing carried for
        // these nine: a proof must be evidence about ONE model.
        let (target, _) = solve_and_emit(&case.feasible);
        let spliced = splice_model_header(&proof, &target);
        assert_ne!(spliced, proof, "{}: the splice must apply", case.source);
        let r = cert_io::check(&spliced, &case.feasible);
        assert_eq!(
            r.status(),
            CheckStatus::Refuted,
            "{}: a refutation of an infeasible model must not prove a feasible \
             one infeasible: {r:#?}",
            case.source
        );
        assert_eq!(r.status().exit_code(), 20);
    }
}

/// The variants above must really be feasible, or the previous test proves
/// nothing: refuting a proof of an INFEASIBLE model is no achievement.
#[test]
fn the_feasible_variants_are_actually_feasible() {
    for case in format_cases() {
        let p = ay_milp::read_mps(&case.feasible).expect("variant parses");
        let opts = SolveOpts::new().with_time_limit(std::time::Duration::from_secs(20));
        let mut s = BabSession::new(p.model, &opts).expect("session");
        let outcome = s.check().expect("solve");
        assert!(
            !matches!(outcome, Outcome::Infeasible { .. }),
            "{}: the `feasible` variant is infeasible, so the cross-model probe \
             is vacuous: {outcome:?}",
            case.source
        );
    }
}

// ---------------------------------------------------------------------------
// (g) THE WHOLE-TREE OPTIMALITY BLOCK (`opttree`). A branched MILP's dual half.
//
// These use the MILP fixture above, whose optimum is 3 (x = 2, y = 1) and whose
// root LP relaxation already reaches 3 — so the derived tree is small enough to
// read, while the model is still a genuine integer program with two columns.
// ---------------------------------------------------------------------------

/// The derived tree, and the emission that carries it.
fn milp_with_tree() -> (String, ay_milp::MilpOptimalityCertificate) {
    let p = ay_milp::read_mps(MILP).expect("parses");
    let names = p.col_names.clone();
    let scale = p.obj_scale.clone();
    let opts = SolveOpts::new().with_time_limit(std::time::Duration::from_secs(20));
    let mut session = BabSession::new(p.model, &opts).expect("session");
    let outcome = session.check().expect("solve");
    let Outcome::Optimal {
        value,
        model_values,
        ..
    } = &outcome
    else {
        panic!("MILP fixture must solve to optimality: {outcome:?}");
    };
    let tree = ay_milp::derive_optimality_tree(
        session.model(),
        value,
        model_values,
        &ay_milp::OptimalityTreeBudget::new(4096),
    )
    .expect("the certifying descent closes this two-column integer program");
    tree.verify(session.model())
        .expect("the derived tree stands on its own");
    let ayc =
        emit_session_certificate_with_tree(&session, MILP, &names, &scale, &outcome, Some(&tree));
    (ayc, tree)
}

#[test]
fn a_milp_optimum_with_a_tree_verifies_on_both_halves() {
    // THE HEADLINE. Without the tree this same verdict is PARTIAL / exit 11
    // with `unbacked=dual` — pinned by
    // `a_milp_optimum_reports_partial_with_an_unbacked_dual_claim` below, which
    // emits the SAME model with no tree.
    let (ayc, _) = milp_with_tree();
    assert!(
        ayc.contains("evidence dual SUCCINCT optimality-tree"),
        "{ayc}"
    );
    assert!(ayc.contains("\nopttree\n"), "{ayc}");
    assert!(ayc.contains("\nboundleaf\n"), "{ayc}");
    let r = cert_io::check(&ayc, MILP);
    assert_eq!(r.status(), CheckStatus::Verified, "{r:#?}");
    assert_eq!(r.status().exit_code(), 0);
    for claim in r.claims() {
        assert_eq!(
            claim.standing(),
            ClaimStanding::Verified,
            "claim {} is not verified: {claim:#?}",
            claim.name()
        );
        assert_eq!(claim.kind(), EvidenceKind::Succinct);
    }
}

#[test]
fn the_same_milp_without_a_tree_does_not_verify() {
    // THE CONTROL for the test above: identical model, identical verdict, no
    // tree — so the Verified there is attributable to the tree and nothing
    // else.
    //
    // What this model reaches WITHOUT a tree is a REPLAY claim
    // (pb-portfolio-projection-optimal): the PB route exhausted the projection
    // but exported no object, so the dual half is re-verifiable only by
    // re-running the solver. A REPLAY claim can never earn exit 0, which is
    // exactly the gap the tree closes — and note the tree does not merely
    // relabel that claim, it replaces it with a SUCCINCT one whose evidence the
    // checker re-derives.
    let (ayc, _) = solve_and_emit(MILP);
    let dual = ayc
        .lines()
        .find(|l| l.starts_with("evidence dual "))
        .expect("an optimal verdict always emits a dual claim");
    assert!(
        !dual.contains("SUCCINCT"),
        "without a tree this MILP has no succinct dual evidence, got: {dual}"
    );
    let r = cert_io::check(&ayc, MILP);
    assert_ne!(r.status(), CheckStatus::Verified, "{r:#?}");
    assert_ne!(r.status().exit_code(), 0);
}

#[test]
fn a_tree_priced_against_a_tampered_verdict_value_is_refuted() {
    // THE SINGLE-SOURCE PROPERTY, both directions. The tree carries no value of
    // its own; it is priced at the number on the `verdict` line, which is the
    // same number the witness is pinned to. So moving that number breaks one
    // half or the other, and there is no third place to move it to.
    let (ayc, _) = milp_with_tree();
    assert!(ayc.contains("verdict optimal value=3 frame=file"), "{ayc}");

    // Claiming a BETTER optimum (2): the witness no longer attains it.
    let better = reseal(&ayc.replace(
        "verdict optimal value=3 frame=file",
        "verdict optimal value=2 frame=file",
    ));
    let r = cert_io::check(&better, MILP);
    assert_ne!(r.status(), CheckStatus::Verified, "{r:#?}");

    // Claiming a WORSE optimum (4): the witness attains 3, not 4, so the primal
    // half fails here too — and the tree, which proves `obj >= 3`, cannot reach
    // 4 either. Both halves refuse.
    let worse = reseal(&ayc.replace(
        "verdict optimal value=3 frame=file",
        "verdict optimal value=4 frame=file",
    ));
    let r = cert_io::check(&worse, MILP);
    assert_ne!(r.status(), CheckStatus::Verified, "{r:#?}");
}

#[test]
fn a_bound_tree_offered_as_an_infeasibility_proof_is_refuted() {
    // THE FATAL CONFLATION, and the reason the token and the parsed field are
    // both distinct. A Farkas tree backing `dual` is merely vacuous; a BOUND
    // tree backing `infeasible` would assert that a model with a known feasible
    // point has none. The MILP fixture is feasible — x = 2, y = 1 — so this
    // certificate is a lie about a model whose witness it also carries.
    let (ayc, _) = milp_with_tree();
    let forged = reseal(
        &ayc.replace(
            "evidence dual SUCCINCT optimality-tree",
            "evidence infeasible SUCCINCT optimality-tree",
        )
        .replace("verdict optimal value=3 frame=file", "verdict infeasible"),
    );
    let r = cert_io::check(&forged, MILP);
    assert_eq!(r.status(), CheckStatus::Refuted, "{r:#?}");
    assert_eq!(r.status().exit_code(), 20);
}

#[test]
fn a_boundleaf_inside_an_infeasibility_tree_does_not_parse() {
    // The other half of the same conflation, at the token level: `boundleaf`
    // has no arm in `parse_tree`, so a bound leaf cannot be smuggled into a
    // `tree` block and read as a proof of emptiness.
    let (ayc, _) = solve_and_emit(INF);
    assert!(ayc.contains("farkas "), "{ayc}");
    let forged = reseal(&ayc.replace("farkas mults=2", "tree\nboundleaf"));
    let r = cert_io::check(&forged, INF);
    assert_ne!(r.status(), CheckStatus::Verified, "{r:#?}");
}

#[test]
fn an_opttree_claim_whose_block_is_missing_is_refuted() {
    let (ayc, _) = milp_with_tree();
    let mut body = String::new();
    let mut in_tree = false;
    for l in ayc.lines() {
        if l == "opttree" {
            in_tree = true;
            continue;
        }
        if in_tree {
            if l == "end" {
                in_tree = false;
            }
            continue;
        }
        body.push_str(l);
        body.push('\n');
    }
    let forged = reseal(&body);
    assert!(!forged.contains("opttree"), "{forged}");
    assert!(
        forged.contains("evidence dual SUCCINCT optimality-tree"),
        "{forged}"
    );
    let r = cert_io::check(&forged, MILP);
    assert_eq!(r.status(), CheckStatus::Refuted, "{r:#?}");
}

#[test]
fn deleting_a_split_from_the_tree_is_refuted() {
    // A tree that no longer tiles the domain. Dropping one `split` line leaves
    // the pre-order with an extra node, which the parser rejects outright; the
    // point is that the certificate cannot be quietly shrunk into one that
    // covers less.
    let (ayc, _) = milp_with_tree();
    let Some(split) = ayc.lines().find(|l| l.starts_with("split ")) else {
        // A tree with no split still exercises every other test here; skip the
        // splice rather than assert on the shape of a derived artifact.
        return;
    };
    let forged = reseal(&ayc.replacen(&format!("{split}\n"), "", 1));
    let r = cert_io::check(&forged, MILP);
    assert_ne!(r.status(), CheckStatus::Verified, "{r:#?}");
}

#[test]
fn rescaling_one_leaf_multiplier_is_refuted() {
    // The identity is exact: every leaf's combination must BE the model's
    // objective. Doubling any single multiplier breaks it.
    let (ayc, _) = milp_with_tree();
    let mut lines: Vec<String> = ayc.lines().map(str::to_string).collect();
    let mut patched = false;
    for l in &mut lines {
        if l.starts_with("mult ") && l.ends_with(" 1") {
            *l = l.replace(" 1", " 2");
            patched = true;
            break;
        }
    }
    assert!(
        patched,
        "the derived tree has no unit multiplier to rescale"
    );
    let forged = reseal(&(lines.join("\n") + "\n"));
    let r = cert_io::check(&forged, MILP);
    assert_ne!(r.status(), CheckStatus::Verified, "{r:#?}");
}

#[test]
fn a_tree_checked_against_a_different_model_is_not_verified() {
    let (ayc, _) = milp_with_tree();
    let r = cert_io::check(&ayc, LP);
    assert_ne!(r.status(), CheckStatus::Verified, "{r:#?}");
}
