// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Durable CLI-level differential fuzz gate for Real optimization
//! (#opt-epsilon; close-the-gaps handoff §4 gate 3).
//!
//! Generates random pure-Real QF_LRA optimization instances (strict + weak
//! bounds, difference constraints, single-variable objectives, lex and box
//! priorities), runs BOTH the `ay` binary and `z3` at the SMT-LIB CLI level,
//! and requires **DISAGREE = 0 outside the enumerated deviation classes**.
//!
//! Why CLI-level and not the `ayz3_fuzz` harness: the FFI surface maps an
//! epsilon outcome to "no scalar available" (`ObjectiveOutcome::Epsilon →
//! None` in Phase A), so only the `(get-objectives)` text carries the ε
//! shapes — the CLI is the ONLY medium where the epsilon grammar is
//! observable and comparable.
//!
//! ## Deviation classes (1-4 each measured and pinned in `opt_epsilon.rs`;
//! everything else must match byte-for-byte after normalization)
//!
//! 1. `CosmeticIntegralReal` — normalization handles it: AY prints integral
//!    Real optima as `2.0`, z3 as `2`; both sides are normalized by
//!    rewriting `N.0` → `N` before comparison (z3's own epsilon shapes
//!    (`3.0`) normalize identically on both sides, so equality is
//!    preserved).
//! 2. `Z3BoxStrict` — box mode with ANY strict bound: z3 4.15.4 reported
//!    demonstrably false optima (interior points / bogus `oo`; evidence
//!    `m5`/`m8` fixtures). z3 5.0.0 FIXED this defect, so AY now AGREES with
//!    z3 5.0.0 on box-strict objectives; the skip is retained conservatively
//!    (a coverage gap, not a soundness risk — the `sat` verdict is still
//!    always compared) pending a follow-up that tightens it to compare the
//!    box-strict objective text now that both sides match.
//! 3. `Z3LexUnattainedPrefix` — lex with a non-final unattained/unbounded
//!    objective: z3 4.15.4 emitted an interval plus a false successor scalar
//!    (evidence `g5`/`adv7`). z3 5.0.0 now decides the suffix correctly, but
//!    AY still fail-closes it (sound-but-incomplete); detected via AY's honest
//!    unavailable-suffix error, so the skip stays valid. Verdicts still must
//!    agree.
//! 4. `AySoundUnknown` — AY answers `unknown` where z3 decides: a
//!    completeness miss, never a wrong verdict (§0: fail-close is always
//!    sound). Counted and bounded: the run fails if AY fail-closes on more
//!    than half the instances, so the gate cannot silently degrade into
//!    vacuity.
//! 5. `Z3PreCalibrationStrictBound` — only with a z3 older than
//!    [`OLDEST_CALIBRATED_Z3`]; classes 1-4 were measured on 4.15.4 and 5.0.0.
//!    z3 4.8.12 reports an unattained strict-bound optimum as the bound moved
//!    one unit inward: `(x1 0)` for `x1 < 1` maximize, where the supremum is
//!    `1`, not attained, and AY's `1 - ε` is exact. On a host whose PATH
//!    carried that release this gate failed on AY's correct answers. A text
//!    mismatch is excused ONLY when the semantic oracle below refutes z3's own
//!    printed objective; wherever z3 is right, the byte-for-byte comparison
//!    still runs, and the run fails if more than a quarter of the compared
//!    instances need the excuse.
//!
//! A `sat`-vs-`unsat` split, or any objective-value mismatch outside classes
//! 2/3/5, is a hard failure printing the full instance for reproduction.
//!
//! ## Every AY objective is also checked against its definition
//!
//! Independently of z3's OPTIMIZER, `semantic.rs` re-derives every objective
//! AY prints from z3's satisfiability answers alone, which no release gets
//! wrong on these instances. A wrong optimum, or a lexicographic successor
//! printed after an unattained predecessor (class 3's contract is to refuse
//! it), fails the gate whatever z3 release is on PATH, including on the
//! box-strict instances class 2 exempts from the text comparison.

use std::io::Write;
use std::process::{Command, Stdio};

use ntest::timeout;

#[path = "opt_epsilon_differential/semantic.rs"]
mod semantic;

use semantic::ObjectiveError;

/// Oldest z3 release whose optimizer the deviation classes were measured
/// against (`opt_epsilon/README.md`: 4.15.4, then 5.0.0).
const OLDEST_CALIBRATED_Z3: (u32, u32, u32) = (4, 15, 4);

/// Deterministic xorshift64* PRNG — no external crates, reproducible seeds.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed.max(1))
    }
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// The z3 this gate compares against: reached by path and proved to be z3
/// (`ay_test_support::z3`), or `None` after a visible skip line.
fn z3_oracle() -> Option<&'static ay_test_support::z3::Z3Oracle> {
    ay_test_support::z3::optional_z3("ay opt_epsilon_differential")
}

fn run_stdin(cmd: &mut Command, script: &str) -> String {
    let mut child = cmd
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn solver");
    child
        .stdin
        .as_mut()
        .expect("stdin")
        .write_all(script.as_bytes())
        .expect("write stdin");
    let output = child.wait_with_output().expect("wait solver");
    String::from_utf8_lossy(&output.stdout).into_owned()
}

/// The oracle's version, as `(major, minor, patch)`, from its banner.
fn z3_version() -> Option<(u32, u32, u32)> {
    z3_oracle()?.version()
}

fn run_ay(script: &str) -> String {
    run_stdin(
        Command::new(env!("CARGO_BIN_EXE_ay"))
            .arg("--z3-mode")
            .arg("-in"),
        script,
    )
}

fn run_z3(script: &str) -> String {
    let z3 = z3_oracle().expect("run_z3 is only reached with a resolved oracle");
    run_stdin(z3.command().args(["-in", "-T:20"]), script)
}

/// Normalize a solver output for comparison: keep non-empty lines, apply the
/// `CosmeticIntegralReal` rewrite `N.0` → `N` uniformly to BOTH sides.
fn normalize(out: &str) -> Vec<String> {
    out.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let mut s = String::with_capacity(l.len());
            let bytes = l.as_bytes();
            let mut i = 0;
            while i < bytes.len() {
                if bytes[i].is_ascii_digit() {
                    let start = i;
                    while i < bytes.len() && bytes[i].is_ascii_digit() {
                        i += 1;
                    }
                    // `N.0` (not followed by another digit) → `N`.
                    if i + 1 < bytes.len()
                        && bytes[i] == b'.'
                        && bytes[i + 1] == b'0'
                        && (i + 2 >= bytes.len() || !bytes[i + 2].is_ascii_digit())
                    {
                        s.push_str(&l[start..i]);
                        i += 2;
                    } else {
                        s.push_str(&l[start..i]);
                    }
                } else {
                    s.push(bytes[i] as char);
                    i += 1;
                }
            }
            s
        })
        .collect()
}

struct Instance {
    script: String,
    box_mode: bool,
    has_strict: bool,
    /// The `declare-const` lines of `script`.
    declarations: String,
    constraints: Vec<Constraint>,
    /// `(maximize?, variable)` in priority order.
    objectives: Vec<(bool, String)>,
}

/// One `(assert (op lhs constant))` of an instance.
struct Constraint {
    op: &'static str,
    lhs: String,
    constant: String,
}

impl Constraint {
    /// The atom, or with `relaxed` its closure (strict bounds made weak).
    fn render(&self, relaxed: bool) -> String {
        let op = match self.op {
            "<" if relaxed => "<=",
            ">" if relaxed => ">=",
            op => op,
        };
        format!("({op} {} {})", self.lhs, self.constant)
    }
}

/// Generate one random pure-Real optimization instance. Objectives are
/// SINGLE VARIABLES so the `(get-objectives)` term strings are identical on
/// both solvers (expression-term formatting is a separate, pinned cosmetic
/// class — see `opt_epsilon.rs` m12/adv1/adv5).
fn generate(rng: &mut Rng) -> Instance {
    let nvars = 1 + rng.below(3) as usize;
    let vars: Vec<String> = (0..nvars).map(|i| format!("x{i}")).collect();
    let box_mode = rng.below(4) == 0;
    let mut script = String::new();
    if box_mode {
        script.push_str("(set-option :opt.priority box)\n");
    }
    let mut declarations = String::new();
    for v in &vars {
        declarations.push_str(&format!("(declare-const {v} Real)\n"));
    }
    script.push_str(&declarations);
    let mut constraints = Vec::new();

    let ops = ["<", "<=", ">", ">="];
    let mut has_strict = false;
    let nconstraints = 1 + rng.below(4);
    for _ in 0..nconstraints {
        let op = ops[rng.below(4) as usize];
        if op == "<" || op == ">" {
            has_strict = true;
        }
        // Constants in [-5, 5], sometimes half-integral.
        let num = rng.below(21) as i64 - 10;
        let constant = if rng.below(3) == 0 {
            format!("(/ {}.0 2.0)", num.abs())
        } else {
            format!("{}.0", num.abs())
        };
        let constant = if num < 0 {
            format!("(- {constant})")
        } else {
            constant
        };
        let lhs = if nvars >= 2 && rng.below(3) == 0 {
            // Difference constraint (chains epsilon through rows).
            let a = rng.below(nvars as u64) as usize;
            let mut b = rng.below(nvars as u64) as usize;
            if a == b {
                b = (b + 1) % nvars;
            }
            format!("(- {} {})", vars[a], vars[b])
        } else {
            vars[rng.below(nvars as u64) as usize].clone()
        };
        script.push_str(&format!("(assert ({op} {lhs} {constant}))\n"));
        constraints.push(Constraint { op, lhs, constant });
    }

    let nobjs = 1 + rng.below(2);
    let mut objectives = Vec::new();
    for _ in 0..nobjs {
        let dir = if rng.below(2) == 0 {
            "maximize"
        } else {
            "minimize"
        };
        let v = &vars[rng.below(nvars as u64) as usize];
        script.push_str(&format!("({dir} {v})\n"));
        objectives.push((dir == "maximize", v.clone()));
    }
    script.push_str("(check-sat)\n(get-objectives)\n");
    Instance {
        script,
        box_mode,
        has_strict,
        declarations,
        constraints,
        objectives,
    }
}

fn first_verdict(lines: &[String]) -> Option<&str> {
    lines
        .iter()
        .map(String::as_str)
        .find(|l| matches!(*l, "sat" | "unsat" | "unknown"))
}

/// What the objective stage of one `sat` instance added to the run's counts.
struct ObjectiveStage {
    /// Objectives the semantic oracle checked (none if it was undecided).
    checked: usize,
    /// Whether a text mismatch was excused as deviation class 5.
    z3_refuted: bool,
}

/// The objective stage of one `sat` instance outside class 3: every objective
/// AY printed is checked against its definition, then its text against z3's.
fn compare_objectives(
    seed: u64,
    i: usize,
    instance: &Instance,
    ay_out: &[String],
    z3_out: &[String],
    z3_calibrated: bool,
) -> ObjectiveStage {
    // Every printed objective must be the optimum its definition names,
    // whatever z3 release is on PATH.
    let checked = match semantic::check_objectives(instance, ay_out) {
        Ok(checked) => checked,
        Err(ObjectiveError::Wrong(why)) => panic!(
            "WRONG OBJECTIVE at seed={seed} instance={i}: {why}\n{}\nAY: {ay_out:?}",
            instance.script
        ),
        Err(ObjectiveError::Malformed(why)) => panic!(
            "MALFORMED OBJECTIVES at seed={seed} instance={i}: {why}\n{}\nAY: {ay_out:?}",
            instance.script
        ),
        // The oracle, not AY, failed: like a z3 `unknown`, this decides
        // nothing about AY; the text comparison below still runs.
        Err(ObjectiveError::Undecided(why)) => {
            eprintln!("seed={seed} instance={i}: objective oracle undecided: {why}");
            0
        }
    };
    let mut stage = ObjectiveStage {
        checked,
        z3_refuted: false,
    };
    // Deviation class 2: box-mode-with-strict. z3 4.15.4 emitted false
    // optima here; z3 5.0.0 fixed it and AY now agrees, but the objective
    // text is still skipped conservatively (verdict already compared).
    if instance.box_mode && instance.has_strict {
        return stage;
    }
    // Deviation class 5: an uncalibrated z3 whose own printed objective the
    // semantic oracle refutes. Nowhere else is a text mismatch excused.
    if !z3_calibrated
        && ay_out != z3_out
        && matches!(
            semantic::check_objectives(instance, z3_out),
            Err(ObjectiveError::Wrong(_))
        )
    {
        stage.z3_refuted = true;
        return stage;
    }
    assert_eq!(
        ay_out, z3_out,
        "DISAGREE (objectives) at seed={seed} instance={i}:\n{}",
        instance.script
    );
    stage
}

fn run_gate(seed: u64, count: usize) {
    if z3_oracle().is_none() {
        return;
    }
    let z3_calibrated = z3_version().is_some_and(|version| version >= OLDEST_CALIBRATED_Z3);
    let mut rng = Rng::new(seed);
    let mut ay_unknowns = 0usize;
    let mut compared = 0usize;
    let mut objectives_checked = 0usize;
    let mut z3_refuted = 0usize;
    for i in 0..count {
        let instance = generate(&mut rng);
        let ay_out = normalize(&run_ay(&instance.script));
        let z3_out = normalize(&run_z3(&instance.script));
        let ay_verdict = first_verdict(&ay_out).unwrap_or("MISSING");
        let z3_verdict = first_verdict(&z3_out).unwrap_or("MISSING");

        // Deviation class 4: AY fail-closing to unknown is sound; z3 unknown
        // (or timeout) likewise skips. Never a wrong verdict.
        if ay_verdict == "unknown" {
            ay_unknowns += 1;
            continue;
        }
        if z3_verdict == "unknown" || z3_verdict == "MISSING" {
            continue;
        }

        // Verdicts must AGREE in every class — z3's defect classes corrupt
        // its objective VALUES, never the sat/unsat verdict.
        assert_eq!(
            ay_verdict, z3_verdict,
            "DISAGREE (verdict) at seed={seed} instance={i}:\n{}\nAY: {ay_out:?}\nZ3: {z3_out:?}",
            instance.script
        );
        if ay_verdict != "sat" {
            compared += 1;
            continue;
        }

        // Deviation class 3: lex with an unattained/unbounded non-final
        // objective — AY honestly refuses the suffix (sound-but-incomplete);
        // z3 4.15.4 fabricated one, z3 5.0.0 now decides it.
        if ay_out
            .iter()
            .any(|l| l.contains("unavailable after a lexicographic predecessor"))
        {
            continue;
        }
        let stage = compare_objectives(seed, i, &instance, &ay_out, &z3_out, z3_calibrated);
        objectives_checked += stage.checked;
        z3_refuted += usize::from(stage.z3_refuted);
        compared += 1;
    }
    // Anti-vacuity: the gate must actually compare a majority of instances.
    assert!(
        ay_unknowns * 2 <= count,
        "AY failed closed on {ay_unknowns}/{count} instances — the differential \
         gate has degraded into vacuity; investigate the completeness regression"
    );
    assert!(
        compared > 0 && objectives_checked > 0,
        "differential gate compared zero instances at seed={seed}"
    );
    if z3_refuted > 0 {
        eprintln!(
            "seed={seed}: {z3_refuted}/{compared} objective mismatches excused: z3 {:?} \
             (older than {OLDEST_CALIBRATED_Z3:?}) printed a refuted optimum",
            z3_version()
        );
    }
    assert!(
        z3_refuted * 4 <= compared,
        "z3 {:?} printed a refuted optimum on {z3_refuted}/{compared} instances at \
         seed={seed}: too few comparisons remain; put a z3 >= {OLDEST_CALIBRATED_Z3:?} \
         on PATH",
        z3_version()
    );
}

#[test]
fn z3_version_banners_parse() {
    use ay_test_support::z3::parse_banner_version;
    assert_eq!(
        parse_banner_version("Z3 version 4.8.12 - 64 bit\n"),
        Some((4, 8, 12))
    );
    assert_eq!(
        parse_banner_version("Z3 version 5.0.0 - 64 bit"),
        Some((5, 0, 0))
    );
    assert_eq!(
        parse_banner_version("Z3 version 4.15 - 64 bit"),
        Some((4, 15, 0))
    );
    assert_eq!(parse_banner_version("not z3"), None);
    let calibrated =
        |banner| parse_banner_version(banner).is_some_and(|v| v >= OLDEST_CALIBRATED_Z3);
    assert!(!calibrated("Z3 version 4.8.12 - 64 bit"));
    assert!(calibrated("Z3 version 4.15.4 - 64 bit"));
    assert!(calibrated("Z3 version 5.0.0 - 64 bit"));
}

#[test]
#[timeout(600_000)]
fn opt_epsilon_differential_seed1() {
    run_gate(1, 120);
}

#[test]
#[timeout(600_000)]
fn opt_epsilon_differential_seed2() {
    run_gate(2, 120);
}
