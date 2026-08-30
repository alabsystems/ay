// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::types::{PbConstraint, PbLit, PbObjective, PbTerm};

fn term(coeff: i128, var: u32) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![PbLit {
            var,
            negated: false,
        }],
    }
}

fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
    PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs,
    }
}

/// The family's two header counts at `(n, t)`.
fn counts(n: u64, t: u64) -> (u64, u64) {
    let c2 = n * (n - 1) / 2;
    (n * n + n + n * t + c2, 3 * n + c2 * n * (n - 1) + c2 * t)
}

/// Builds the canonical clique-coloring OPB for `(n, t)` in the corpus's exact
/// variable order: edges over pairs `i<i'`, then `o[j]`, then `M[i][j]`
/// row-major, then `C[v][k]`. This is the layout the normalized PB25 instances
/// use and the one `detect_shape` recognises.
fn canonical(n: usize, t: usize) -> PbInstance {
    let c = n * (n - 1) / 2;
    let base_g1 = c + n;
    let base_g2 = base_g1 + n * n;
    let edge = |a: usize, b: usize| -> u32 {
        // a < b, both 1-based
        ((a - 1) * n - (a - 1) * a / 2 + (b - a)) as u32
    };
    let obj = |i: usize| (c + i) as u32;
    let g1 = |b: usize, s: usize| (base_g1 + n * (b - 1) + s) as u32;
    let g2 = |b: usize, k: usize| (base_g2 + t * (b - 1) + k) as u32;

    let mut rows = Vec::new();
    for i in 1..=n {
        let mut terms = vec![term(1, obj(i))];
        for b in 1..=n {
            terms.push(term(1, g1(b, i)));
        }
        rows.push(ge(terms, 1));
    }
    for b in 1..=n {
        rows.push(ge((1..=n).map(|s| term(-1, g1(b, s))).collect(), -1));
    }
    for a in 1..=n {
        for b in (a + 1)..=n {
            for p in 1..=n {
                for q in 1..=n {
                    if p != q {
                        rows.push(ge(
                            vec![term(1, edge(a, b)), term(-1, g1(a, p)), term(-1, g1(b, q))],
                            -1,
                        ));
                    }
                }
            }
        }
    }
    for b in 1..=n {
        rows.push(ge((1..=t).map(|k| term(1, g2(b, k))).collect(), 1));
    }
    for a in 1..=n {
        for b in (a + 1)..=n {
            for k in 1..=t {
                rows.push(ge(
                    vec![term(-1, edge(a, b)), term(-1, g2(a, k)), term(-1, g2(b, k))],
                    -2,
                ));
            }
        }
    }
    let num_vars = (base_g2 + n * t) as u32;
    PbInstance {
        num_vars,
        num_constraints: rows.len() as u32,
        constraints: rows,
        objective: Some(PbObjective {
            terms: (1..=n).map(|j| term(1, obj(j))).collect(),
        }),
    }
}

/// The colouring upper-bound witness: vertex `b` takes slot and colour
/// `((b-1) mod t) + 1`, so exactly slots `1..=t` are occupied.
fn incumbent_for(instance: &PbInstance, n: usize, t: usize) -> Vec<bool> {
    let c = n * (n - 1) / 2;
    let base_g1 = c + n;
    let base_g2 = base_g1 + n * n;
    let edge = |a: usize, b: usize| ((a - 1) * n - (a - 1) * a / 2 + (b - a)) as u32;
    let mut values = vec![false; instance.num_vars as usize];
    let mut set = |v: u32| values[(v as usize) - 1] = true;
    let s = |b: usize| ((b - 1) % t) + 1;
    for a in 1..=n {
        for b in (a + 1)..=n {
            if s(a) != s(b) {
                set(edge(a, b));
            }
        }
    }
    for b in 1..=n {
        set((base_g1 + n * (b - 1) + s(b)) as u32);
        set((base_g2 + t * (b - 1) + s(b)) as u32);
    }
    for i in (t + 1)..=n {
        set((c + i) as u32);
    }
    values
}

fn certify(n: usize, t: usize) -> Option<String> {
    let instance = canonical(n, t);
    let incumbent = incumbent_for(&instance, n, t);
    certify_opt_lin_clique_coloring(&instance, &incumbent, (n as i128) - (t as i128))
}

// ---------------------------------------------------------------------------
// Layer 1: the O(1) pre-gate.
// ---------------------------------------------------------------------------

/// The pre-gate must recover `(n, t)` from the header counts ALONE, with no
/// aliasing anywhere in the reachable range: two different family members must
/// never share a `(#variable, #constraint)` pair. If they did, the entry point's
/// `objective.terms.len() == n` cross-check would decline a genuine member.
#[test]
fn pre_gate_recovers_n_and_t_with_no_aliasing_in_range() {
    for n in 2u64..=60 {
        for t in 1u64..=60 {
            let (nvar, ncon) = counts(n, t);
            assert_eq!(
                header_candidate(nvar, ncon),
                Some((n as usize, t as usize)),
                "header counts for n={n} t={t} must recover exactly (n, t)"
            );
        }
    }
}

/// Neighbouring counts must be rejected: the gate is an equality test on both
/// numbers, not a range.
#[test]
fn pre_gate_rejects_off_by_one_counts() {
    for n in 2u64..=20 {
        for t in 1u64..=8 {
            let (nvar, ncon) = counts(n, t);
            for delta in [-1i64, 1] {
                let bumped_con = (ncon as i64 + delta) as u64;
                assert_ne!(
                    header_candidate(nvar, bumped_con),
                    Some((n as usize, t as usize)),
                    "n={n} t={t}: constraint count {bumped_con} must not pass as (n, t)"
                );
            }
        }
    }
}

/// A knapsack-shaped header (one row, many variables) must be rejected without
/// the gate scanning anything.
#[test]
fn pre_gate_rejects_off_family_headers() {
    assert_eq!(header_candidate(1000, 1), None);
    assert_eq!(header_candidate(0, 0), None);
    assert_eq!(header_candidate(1, 1), None);
    assert_eq!(header_candidate(50_000, 120_000), None);
}

// ---------------------------------------------------------------------------
// End-to-end emission.
// ---------------------------------------------------------------------------

#[test]
fn certifies_the_family_and_concludes_the_optimum() {
    for (n, t) in [(3usize, 1usize), (3, 2), (4, 2), (4, 3), (5, 3), (6, 4)] {
        let proof = certify(n, t)
            .unwrap_or_else(|| panic!("n={n} t={t} is in the family and must certify"));
        let optimum = n - t;
        assert!(proof.starts_with("pseudo-Boolean proof version 3.0\n"));
        assert!(
            proof.contains(&format!("conclusion BOUNDS {optimum} : ")),
            "n={n} t={t} must conclude BOUNDS {optimum}"
        );
        assert!(proof.trim_end().ends_with("end pseudo-Boolean proof;"));
    }
}

/// The emitted proof must use exactly the rules this module models — anything
/// else and the self-check's replay would be a different proof from the one the
/// checker sees.
#[test]
fn emitted_proof_uses_only_modelled_rules() {
    let proof = certify(4, 2).expect("n=4 t=2 certifies");
    for line in proof.lines() {
        let ok = line.starts_with("pol ")
            || line.starts_with("red ")
            || line.starts_with("soli ")
            || line.starts_with("conclusion ")
            || line == "output NONE;"
            || line == "end pseudo-Boolean proof;"
            || line == "pseudo-Boolean proof version 3.0"
            || line.starts_with("f ");
        assert!(ok, "unmodelled proof line: {line}");
    }
}

// ---------------------------------------------------------------------------
// Layers 2 and 3: fail-closed on anything that is not exactly this family.
// ---------------------------------------------------------------------------

#[test]
fn declines_when_the_solver_optimum_disagrees_with_the_structure() {
    let instance = canonical(4, 2);
    let incumbent = incumbent_for(&instance, 4, 2);
    // True optimum is 2; every other claimed value must be refused.
    for claimed in [0i128, 1, 3, 4, -1] {
        assert!(
            certify_opt_lin_clique_coloring(&instance, &incumbent, claimed).is_none(),
            "claimed optimum {claimed} must be refused"
        );
    }
}

#[test]
fn declines_on_an_infeasible_or_suboptimal_incumbent() {
    let instance = canonical(4, 2);
    let good = incumbent_for(&instance, 4, 2);
    // All-false: violates the slot-cover rows.
    assert!(certify_opt_lin_clique_coloring(&instance, &vec![false; good.len()], 2).is_none());
    // All-true: feasible for nothing, and objective 4 != 2.
    assert!(certify_opt_lin_clique_coloring(&instance, &vec![true; good.len()], 2).is_none());
    // A truncated incumbent must not be padded silently.
    assert!(certify_opt_lin_clique_coloring(&instance, &good[..good.len() - 1], 2).is_none());
}

#[test]
fn declines_when_a_family_row_is_missing_or_extra() {
    let n = 4;
    let t = 2;
    let base = canonical(n, t);
    let incumbent = incumbent_for(&base, n, t);

    // Drop a proper-colouring row: the instance's true optimum can only fall,
    // so `n - t` may no longer be the optimum and nothing may be emitted.
    let mut missing = base.clone();
    missing.constraints.pop();
    assert!(certify_opt_lin_clique_coloring(&missing, &incumbent, (n - t) as i128).is_none());

    // Duplicate a row: the count no longer matches the family.
    let mut extra = base.clone();
    let dup = extra.constraints[0].clone();
    extra.constraints.push(dup);
    assert!(certify_opt_lin_clique_coloring(&extra, &incumbent, (n - t) as i128).is_none());

    // Replace a row with a lookalike of the same shape but the wrong variables:
    // the counts still pass the pre-gate, the exact multiset match does not.
    let mut swapped = base.clone();
    let last = swapped.constraints.len() - 1;
    swapped.constraints[last] = ge(vec![term(-1, 1), term(-1, 1), term(-1, 2)], -2);
    assert!(certify_opt_lin_clique_coloring(&swapped, &incumbent, (n - t) as i128).is_none());
}

#[test]
fn declines_on_an_unrelated_instance() {
    // A knapsack: one row, linear objective. Must cost the pre-gate and stop.
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints: vec![ge(vec![term(-2, 1), term(-3, 2), term(-4, 3)], -5)],
        objective: Some(PbObjective {
            terms: vec![term(-3, 1), term(-4, 2), term(-5, 3)],
        }),
    };
    assert!(certify_opt_lin_clique_coloring(&instance, &[true, false, false], -3).is_none());
}

// ---------------------------------------------------------------------------
// Layer 4: the self-check must reject adversarial edits of a VALID proof.
// ---------------------------------------------------------------------------

/// Rebuilds everything the self-check needs for `(n, t)`, plus a known-good proof.
struct Fixture {
    instance: PbInstance,
    lay: Layout,
    text: String,
    floor_id: u64,
    probes: Vec<Vec<bool>>,
}

fn fixture(n: usize, t: usize) -> Fixture {
    let instance = canonical(n, t);
    let incumbent = incumbent_for(&instance, n, t);
    let objective = instance.objective.clone().expect("objective");
    let shape = detect_shape(&instance, &objective).expect("canonical instance is detected");
    let lay = resolve_layout(&instance, &shape).expect("layout resolves");
    let (text, floor_id) = emit(&instance, &lay, &incumbent).expect("emission succeeds");
    let mut probes = vec![incumbent];
    if let Some(point) = two_in_a_slot(&instance, &lay) {
        probes.push(point);
    }
    Fixture {
        instance,
        lay,
        text,
        floor_id,
        probes,
    }
}

impl Fixture {
    fn accepts(&self, text: &str) -> bool {
        self_check(text, &self.instance, &self.lay, self.floor_id, &self.probes)
    }
}

#[test]
fn self_check_accepts_the_unmodified_emission() {
    for (n, t) in [(3usize, 1usize), (3, 2), (4, 2), (5, 3)] {
        let f = fixture(n, t);
        assert!(
            f.accepts(&f.text),
            "n={n} t={t}: honest proof must self-check"
        );
    }
}

/// The `two_in_a_slot` point is the one that shows the at-most-one is NOT an LP
/// cut. It must be feasible — if it were not, the probe would be vacuous.
#[test]
fn two_in_a_slot_is_a_genuinely_feasible_point() {
    for (n, t) in [(3usize, 1usize), (4, 2), (5, 3), (6, 4)] {
        let f = fixture(n, t);
        assert_eq!(
            f.probes.len(),
            2,
            "n={n} t={t}: the second probe must exist"
        );
        assert!(crate::eval::verify_all_constraints(
            &f.instance.constraints,
            &f.probes[1]
        ));
    }
}

/// THE MUTATION BATTERY, CALIBRATED AGAINST THE PINNED CHECKER.
///
/// Every entry below was first run through the pinned VeriPB on a real emitted
/// proof, and the three classes are kept apart on purpose — a battery that
/// counts no-ops as "caught" overstates its own coverage:
///
/// * **Checker-rejected (16).** The pinned checker refuses these outright. The
///   self-check must refuse them too, so a broken proof never reaches the disk.
/// * **AY-stricter (4).** The pinned checker ACCEPTS these as valid proofs, but
///   AY must still refuse them because they do not certify the optimum AY
///   reports (`bound_down` proves the weaker `1 <= obj`), rest the floor on the
///   objective-improving assumption (`floor_uses_soli`), or drift from the
///   emitted shape in ways that make the replay stop modelling the proof
///   (`hint_off`, `witness_wrong`).
/// * **A genuine no-op (1), asserted ACCEPTED in a separate test.** Saturating a
///   clause that the preceding division already saturated leaves the derivation
///   intact, and the checker verifies it. Listing that as a "rejected mutation"
///   would be a false claim of coverage.
///
/// Calibration is per FIXTURE, not per family: dropping a saturation is a no-op
/// at `(n=3, t=1)`, where the row it acts on is already saturated, and a REAL
/// defect at `(n=4, t=2)`, where the pinned checker rejects it
/// (`Error: Checking error at ...:481`). This battery runs at `(4, 2)`.
#[test]
fn self_check_rejects_adversarial_mutations() {
    let f = fixture(4, 2);
    let lines: Vec<&str> = f.text.lines().collect();
    let optimum = 2;
    let soli_id = f.instance.constraints.len() as u64 + 1;

    let edit = |idx: usize, replacement: &str| -> String {
        let mut edited: Vec<String> = lines.iter().map(|l| (*l).to_string()).collect();
        edited[idx] = replacement.to_string();
        edited.join("\n") + "\n"
    };
    let find = |pred: &dyn Fn(&str) -> bool| -> usize {
        lines
            .iter()
            .position(|l| pred(l))
            .expect("the emitted proof has a line of this kind")
    };
    let rfind = |pred: &dyn Fn(&str) -> bool| -> usize {
        lines
            .iter()
            .rposition(|l| pred(l))
            .expect("the emitted proof has a line of this kind")
    };

    let mut mutations: Vec<(&str, String)> = Vec::new();

    // --- class 1: the pinned checker rejects these too -------------------
    mutations.push((
        "conclusion claims a larger bound",
        f.text.replacen(
            &format!("conclusion BOUNDS {optimum} : "),
            &format!("conclusion BOUNDS {} : ", optimum + 1),
            1,
        ),
    ));
    mutations.push((
        "division no longer recovers the clause (2 d -> 1 d)",
        f.text.replacen(" 2 d ;", " 1 d ;", 1),
    ));
    mutations.push((
        "division replaced by multiplication",
        f.text.replacen(" 2 d ;", " 2 * ;", 1),
    ));
    mutations.push((
        "dropped a load-bearing saturation",
        f.text.replacen(" s ;", " ;", 1),
    ));
    mutations.push((
        "wrong f count",
        f.text.replacen(
            &format!("f {} ;", f.instance.constraints.len()),
            &format!("f {} ;", f.instance.constraints.len() + 1),
            1,
        ),
    ));
    {
        let idx = find(&|l| l.starts_with("pol ") && l.contains(" + "));
        let toks: Vec<&str> = lines[idx].split_whitespace().collect();
        let first: u64 = toks[1].parse().expect("first operand is an id");
        mutations.push((
            "pol operand shifted by one",
            edit(
                idx,
                &lines[idx].replacen(&first.to_string(), &(first + 1).to_string(), 1),
            ),
        ));
    }
    {
        let idx = find(&|l| l.starts_with("red "));
        let mut edited: Vec<&str> = lines.clone();
        edited.remove(idx);
        mutations.push(("deleted a red", edited.join("\n") + "\n"));
    }
    {
        // Delete the OR-definition of a `z`, which the ladder depends on.
        let idx = find(&|l| {
            l.starts_with("red ") && l.contains("-> 0 ;") && l.matches("+1 x").count() >= 3
        });
        let mut edited: Vec<&str> = lines.clone();
        edited.remove(idx);
        mutations.push(("deleted a z definition", edited.join("\n") + "\n"));
    }
    {
        let idx = find(&|l| l.starts_with("pol "));
        let mut edited: Vec<&str> = lines.clone();
        edited.insert(idx, lines[idx]);
        mutations.push(("duplicated a pol", edited.join("\n") + "\n"));
    }
    {
        let idx = rfind(&|l| l.starts_with("pol "));
        let mut edited: Vec<&str> = lines.clone();
        edited.swap(idx - 1, idx);
        mutations.push(("swapped two pol lines", edited.join("\n") + "\n"));
    }
    {
        // The forgery that matters most: a `red` asserting something about the
        // INSTANCE's own variables rather than defining a fresh one.
        let idx = find(&|l| l.starts_with("red "));
        mutations.push((
            "red over original variables only",
            edit(idx, "red +1 x1 >= 1 : x1 -> 1 ;"),
        ));
    }
    {
        let idx = find(&|l| l.starts_with("red ") && l.contains(">= 1 :"));
        mutations.push((
            "red degree raised above a definition",
            edit(idx, &lines[idx].replacen(">= 1 :", ">= 2 :", 1)),
        ));
    }
    {
        let idx = find(&|l| l.starts_with("pol ") && l.ends_with(" w ;"));
        let toks: Vec<&str> = lines[idx].split_whitespace().collect();
        let var = toks[toks.len() - 2];
        mutations.push((
            "weakened the wrong variable",
            edit(idx, &lines[idx].replacen(var, "x1", 1)),
        ));
    }
    {
        // The LAST `pol` is the contradiction `floor + soli`; removing it leaves
        // the conclusion hinting at a row that proves nothing.
        let idx = rfind(&|l| l.starts_with("pol "));
        let mut edited: Vec<&str> = lines.clone();
        edited.remove(idx);
        mutations.push(("removed the contradiction step", edited.join("\n") + "\n"));
    }
    {
        let idx = find(&|l| l.starts_with("soli "));
        let forged = if lines[idx].contains(" ~x1 ") {
            lines[idx].replacen(" ~x1 ", " x1 ", 1)
        } else {
            lines[idx].replacen(" x1 ", " ~x1 ", 1)
        };
        mutations.push(("flipped a solution literal", edit(idx, &forged)));
    }
    {
        let idx = find(&|l| l.starts_with("pol "));
        let mut edited: Vec<&str> = lines.clone();
        edited.insert(idx, "rup >= 1 ;");
        mutations.push(("unmodelled rule inserted", edited.join("\n") + "\n"));
    }

    // --- class 2: the checker accepts, AY must not -----------------------
    mutations.push((
        "conclusion claims a weaker bound than AY reports",
        f.text.replacen(
            &format!("conclusion BOUNDS {optimum} : "),
            &format!("conclusion BOUNDS {} : ", optimum - 1),
            1,
        ),
    ));
    {
        // Fold the improving assumption into the floor. Still a valid VeriPB
        // proof of the same bound, but the floor would then rest on the very
        // assumption it exists to discharge, so AY refuses to emit it.
        let idx = rfind(&|l| l.starts_with("pol ") && !l.ends_with(" w ;"));
        let forged = format!("{} {soli_id} + ;", lines[idx].trim_end_matches(" ;"));
        mutations.push((
            "floor folded with the improving assumption",
            edit(idx, &forged),
        ));
    }
    {
        let idx = find(&|l| l.starts_with("conclusion "));
        let toks: Vec<&str> = lines[idx].split_whitespace().collect();
        let hint: u64 = toks[4].parse().expect("hint id");
        mutations.push((
            "conclusion hints a row that is not the contradiction",
            edit(
                idx,
                &lines[idx].replacen(&hint.to_string(), &(hint - 1).to_string(), 1),
            ),
        ));
    }
    {
        let idx = find(&|l| l.starts_with("red ") && l.contains(" -> 1 ;"));
        let colon = lines[idx].find(':').expect("witness separator");
        mutations.push((
            "witness names a variable the red does not define",
            edit(idx, &format!("{}: x1 -> 1 ;", &lines[idx][..colon])),
        ));
    }

    for (name, text) in &mutations {
        assert!(
            !f.accepts(text),
            "MUTATION ACCEPTED (this is the worst possible defect): {name}"
        );
    }
    assert_eq!(
        mutations.len(),
        20,
        "the mutation battery must not shrink silently"
    );
    // The honest proof still passes, so the battery is not rejecting everything.
    assert!(f.accepts(&f.text));
}

/// The two edits the pinned checker ACCEPTS and that really are valid proofs of
/// the same bound. Asserting they still self-check is what keeps the battery
/// above honest: a self-check that refused everything would "catch" all 19
/// mutations and be worthless.
///
/// It is an arithmetic no-op on the row it touches: the `2 d` row normalizes to
/// `2 ~p + 2 ~p >= 1`, so saturating it caps 2 at the degree 1 exactly as the
/// division already did. Verified against the pinned checker on this fixture's
/// own emission: `s VERIFIED BOUNDS 2 <= obj <= 2`.
#[test]
fn self_check_accepts_the_checker_verified_no_ops() {
    let f = fixture(4, 2);
    for (name, text) in [(
        "spurious saturation after a division",
        f.text.replacen(" 2 d ;", " 2 d s ;", 1),
    )] {
        assert!(
            f.accepts(&text),
            "{name}: the pinned checker verifies this; refusing it would make the \
             mutation battery meaningless"
        );
    }
}

/// The floor row is the load-bearing claim: it must be the objective vector at
/// exactly `n - t`, over exactly the objective variables and nothing else.
#[test]
fn self_check_pins_the_floor_row_to_the_objective() {
    for (n, t) in [(3usize, 1usize), (4, 2), (5, 3)] {
        let f = fixture(n, t);
        // Re-point the self-check at a DIFFERENT row: it must refuse, because
        // no other row in the derivation is the objective floor.
        assert!(
            !self_check(&f.text, &f.instance, &f.lay, f.floor_id - 1, &f.probes),
            "n={n} t={t}: only the true floor row may satisfy the floor test"
        );
        assert!(
            !self_check(&f.text, &f.instance, &f.lay, f.floor_id + 1, &f.probes),
            "n={n} t={t}: the contradiction row is not the floor"
        );
    }
}

/// The floor must be derivable WITHOUT the objective-improving assumption. A
/// proof that reached `Σ o >= n - t` only by assuming `Σ o < n - t` would be
/// circular, and the self-check must say so.
#[test]
fn self_check_rejects_a_floor_that_depends_on_the_improving_assumption() {
    let f = fixture(4, 2);
    let lines: Vec<&str> = f.text.lines().collect();
    let floor_idx = lines
        .iter()
        .rposition(|l| l.starts_with("pol ") && !l.ends_with(" w ;"))
        .expect("the floor line exists");
    // Fold the soli row into the floor: still a valid CP step, but now the
    // "floor" is conditional on the incumbent being beatable.
    let soli_id = f.instance.constraints.len() as u64 + 1;
    let forged = format!("{} {soli_id} + ;", lines[floor_idx].trim_end_matches(" ;"));
    let mut edited = lines.clone();
    edited[floor_idx] = &forged;
    assert!(
        !f.accepts(&(edited.join("\n") + "\n")),
        "a floor derived from the improving assumption must be refused"
    );
}
