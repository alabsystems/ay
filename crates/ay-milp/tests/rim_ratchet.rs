// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! **THE EXACT-RIM RATCHET'S OWN GATE** — the half of the rim regression gate
//! a default `cargo test` run can enforce, modelled line for line on its
//! sibling `node_ratchet.rs` and existing for the same reason one step further
//! down.
//!
//! # What went wrong
//!
//! `scripts/milp_node_gate.py --check --tier all` and
//! `scripts/corpus_guard.py --check` **both pass, clean**, on a change measured
//! at 4.9x on `dcmulti`, 3.9x on `gen`, 3.45x on `qnet1` and 2.24x on
//! `khb05250`. Not because either gate is loose — because both exercise the
//! float-first MILP lane, and that lane enters `exact::` about **once per 1.36M
//! nodes**. Everything under `crates/ay-milp/src/exact/` was ungated: the
//! representation switch could be moved, disabled, or made to fire on the class
//! it must never fire on, and nineteen exact node pins would have said nothing.
//!
//! # Why this file does not solve that
//!
//! Same reason as `node_ratchet.rs`: the pinned models are MIPLIB files and
//! this repository ships seven tiny `.mps` fixtures. The measurement lane is
//! `target/release/examples/milp_rim_gate --check`, which needs a corpus
//! directory and costs 17s (`--tier fast`) or 105s (`--tier all`). Having this
//! test look for a corpus and silently pass when it is absent would be a **dead
//! gate**, and is not done.
//!
//! # What it does instead, for free
//!
//! It gates the ratchet FILE, and specifically the three properties that decay
//! silently:
//!
//! * **both classes are still present.** A rim gate with no `reduced`-class
//!   member cannot catch a false fire, and a rim gate with no `fraction-free`
//!   member cannot catch a lost or delayed switch. Either half alone is a gate
//!   that passes the change it exists to catch.
//! * **every `reduced` pin is `switch_at = 0` and every `fraction-free` pin is
//!   not.** This is the class contract in one line: ratcheting a reduced-class
//!   model to a nonzero switch point is exactly how a false fire would be
//!   laundered into a "measured improvement".
//! * **every optimum is an exact rational, not a float.** `value` must match
//!   `-?\d+(/\d+)?`. An `f64` print carries a `.` or an `e` and is rejected
//!   here, because the rim's entire claim is that its answer is exact and
//!   `mas74`'s optimum is a 101-digit numerator that no float pin could tell
//!   from a wrong one.
//!
//! Cost: two file reads. Microseconds.

use std::collections::BTreeMap;
use std::path::PathBuf;

fn ratchet_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(".milp_rim_baseline.toml")
}

/// The models measured to CONVERT under the shipped policy and reachable from
/// the sha256-manifested corpus. Restated here rather than derived from the
/// file: "the file agrees with itself" is not a gate — deleting a pin has to
/// fail somewhere.
const FRACTION_FREE: &[&str] = &["blend2", "mas74", "mas76", "pk1"];

/// The models measured to write **100.000%** of their tableau entries on the
/// inline `i64` path — exactly, not approximately — and which therefore must
/// never convert. These are the false-fire tripwires.
const REDUCED: &[&str] = &["dcmulti", "gt2", "lseu", "p0201", "p0282", "p0548", "qiu"];

/// Named in the campaign's class lists and deliberately NOT pinned. Each must
/// still appear in the ratchet with a stated reason, so "why isn't it gated" is
/// answered by the file rather than by archaeology.
const EXCLUDED: &[(&str, &str)] = &[
    ("qnet1", "not_finished"),
    ("harp2", "absent"),
    ("domset_mw19_13..23", "not_pinned"),
];

#[derive(Debug, Default, Clone)]
struct Pin {
    class: Option<String>,
    status: Option<String>,
    form: Option<String>,
    switch_at: Option<i64>,
    p1_pivots: Option<i64>,
    pivots: Option<i64>,
    value: Option<String>,
    tier: Option<String>,
    wall_s: Option<f64>,
}

struct Ratchet {
    instances: BTreeMap<String, Pin>,
    notes: BTreeMap<String, BTreeMap<String, String>>,
}

/// Reader for the grammar the Rust `milp_rim_gate --ratchet` tool writes:
/// `[[instance]]` tables of `key = value`, then named note tables of
/// `name = "reason"`. Deliberately not a general TOML parser — `ay-milp` takes
/// no `toml` dependency, and keeping both readers on the same small grammar is
/// what stops the script and this test from drifting apart.
///
/// `value` is taken between the FIRST and LAST quote rather than trimmed, so a
/// rational can never be silently reshaped on the way in.
fn parse(text: &str) -> Ratchet {
    let mut instances: BTreeMap<String, Pin> = BTreeMap::new();
    let mut notes: BTreeMap<String, BTreeMap<String, String>> = BTreeMap::new();
    let mut pending: Option<Pin> = None;
    let mut pending_name: Option<String> = None;
    let mut table: Option<String> = None;
    let flush =
        |name: &mut Option<String>, pin: &mut Option<Pin>, into: &mut BTreeMap<String, Pin>| {
            if let (Some(n), Some(p)) = (name.take(), pin.take()) {
                assert!(
                    into.insert(n.clone(), p).is_none(),
                    "{n} is pinned twice in the rim ratchet"
                );
            }
        };
    for raw in text.lines() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line == "[[instance]]" {
            flush(&mut pending_name, &mut pending, &mut instances);
            pending = Some(Pin::default());
            table = None;
            continue;
        }
        if line.starts_with('[') && line.ends_with(']') {
            flush(&mut pending_name, &mut pending, &mut instances);
            let name = line[1..line.len() - 1].to_string();
            notes.entry(name.clone()).or_default();
            table = Some(name);
            continue;
        }
        let (key, value) = line
            .split_once('=')
            .unwrap_or_else(|| panic!("not a `key = value` line: {line}"));
        let key = key.trim();
        let value = value.trim();
        let value = match (value.find('"'), value.rfind('"')) {
            (Some(a), Some(b)) if b > a => &value[a + 1..b],
            _ => value,
        };
        if let Some(t) = &table {
            notes
                .entry(t.clone())
                .or_default()
                .insert(key.to_string(), value.to_string());
            continue;
        }
        let pin = pending
            .as_mut()
            .unwrap_or_else(|| panic!("key `{key}` outside any table"));
        match key {
            "name" => pending_name = Some(value.to_string()),
            "class" => pin.class = Some(value.to_string()),
            "status" => pin.status = Some(value.to_string()),
            "form" => pin.form = Some(value.to_string()),
            "switch_at" => pin.switch_at = Some(value.parse().expect("switch_at is an integer")),
            "p1_pivots" => pin.p1_pivots = Some(value.parse().expect("p1_pivots is an integer")),
            "pivots" => pin.pivots = Some(value.parse().expect("pivots is an integer")),
            "value" => pin.value = Some(value.to_string()),
            "tier" => pin.tier = Some(value.to_string()),
            "wall_s" => pin.wall_s = Some(value.parse().expect("wall_s is a number")),
            other => panic!("unknown key `{other}` in the rim ratchet"),
        }
    }
    flush(&mut pending_name, &mut pending, &mut instances);
    Ratchet { instances, notes }
}

fn load() -> Ratchet {
    let path = ratchet_path();
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "the rim ratchet is missing at {}: {e}\n\
             It is not optional: the Rust `milp_rim_gate` reads it, and without \
             it NOTHING under crates/ay-milp/src/exact/ is gated at all — which is \
             the state that let a 4.9x rim regression clear both shipped gates.",
            path.display()
        )
    });
    parse(&text)
}

/// A rim gate with only one class is a gate that passes the change it exists to
/// catch: no `reduced` member and a false fire is invisible; no
/// `fraction-free` member and a lost switch is invisible.
#[test]
fn the_pinned_set_covers_both_representation_classes() {
    let r = load();
    let have: Vec<&str> = r.instances.keys().map(String::as_str).collect();
    let mut want: Vec<&str> = FRACTION_FREE.iter().chain(REDUCED).copied().collect();
    want.sort_unstable();
    assert_eq!(
        have, want,
        "the rim ratchet's instance set drifted. A pin may only be removed by a \
         decision that also removes it here — deleting one to turn a red gate \
         green is the defect this file exists to stop."
    );
    let ff = r
        .instances
        .values()
        .filter(|p| p.class.as_deref() == Some("fraction-free"))
        .count();
    let red = r
        .instances
        .values()
        .filter(|p| p.class.as_deref() == Some("reduced"))
        .count();
    assert!(
        ff >= 4 && red >= 6,
        "both classes must be represented with margin: {ff} fraction-free, \
         {red} reduced"
    );
}

/// THE CLASS CONTRACT, in one line each way.
#[test]
fn every_class_agrees_with_its_switch_point() {
    let r = load();
    for name in REDUCED {
        let p = &r.instances[*name];
        assert_eq!(
            p.class.as_deref(),
            Some("reduced"),
            "{name} is a reduced-class tripwire"
        );
        assert_eq!(
            p.switch_at,
            Some(0),
            "{name} writes 100.000% of its tableau entries on the inline i64 \
             path, so no census threshold below 100% can fire on it. A nonzero \
             switch point here is a FALSE FIRE being ratcheted in as a result."
        );
        assert_eq!(
            p.form.as_deref(),
            Some("reduced"),
            "{name} must finish in the reduced form it started in"
        );
    }
    for name in FRACTION_FREE {
        let p = &r.instances[*name];
        assert_eq!(
            p.class.as_deref(),
            Some("fraction-free"),
            "{name} is a converting model"
        );
        let at = p
            .switch_at
            .unwrap_or_else(|| panic!("{name}: no switch_at"));
        assert!(
            at > 0,
            "{name} converts under the shipped policy; `switch_at = 0` means the \
             switch was LOST, which is a 2x-24x regression this gate must not \
             let through as a tuning result"
        );
        assert_eq!(
            p.form.as_deref(),
            Some("fraction-free"),
            "{name} must finish in the fraction-free form"
        );
        assert!(
            at < p.pivots.unwrap_or(0) || p.pivots == p.p1_pivots,
            "{name}: switch point {at} is not inside the solve"
        );
    }
}

/// THE PIN THAT IS NEVER A RATCHET. Two representations of the same tableau
/// denote the same numbers, so the optimum is the one number no rim change may
/// move — and it may only ever be recorded exactly.
#[test]
fn every_optimum_is_an_exact_rational_and_never_a_float() {
    let r = load();
    for (name, p) in &r.instances {
        let v = p
            .value
            .as_deref()
            .unwrap_or_else(|| panic!("{name}: no `value` pin"));
        assert!(!v.is_empty(), "{name}: empty optimum");
        let body = v.strip_prefix('-').unwrap_or(v);
        let (num, den) = match body.split_once('/') {
            Some((n, d)) => (n, Some(d)),
            None => (body, None),
        };
        assert!(
            !num.is_empty() && num.bytes().all(|b| b.is_ascii_digit()),
            "{name}: numerator {num:?} is not an integer — an f64 print carries a \
             `.` or an `e` and is exactly what this pin must never become"
        );
        if let Some(d) = den {
            assert!(
                !d.is_empty() && d.bytes().all(|b| b.is_ascii_digit()) && d != "0",
                "{name}: denominator {d:?} is not a positive integer"
            );
            assert_ne!(
                d, "1",
                "{name}: a rational in lowest terms never prints `/1`; this pin \
                 was not produced by the probe"
            );
        }
    }
    // And the one that proves the point: a 101-digit numerator is in the file.
    let mas74 = r.instances["mas74"].value.as_deref().expect("mas74 value");
    assert!(
        mas74.len() > 150,
        "mas74's optimum is a ~100-digit numerator over a ~94-digit denominator; \
         {} bytes means something truncated or rounded it",
        mas74.len()
    );
}

/// The exclusions are the load-bearing half, exactly as in `node_ratchet.rs`:
/// a gate that cries wolf gets muted, and a gate that quietly drops what it
/// cannot measure is worse.
#[test]
fn every_excluded_model_is_named_with_a_reason() {
    let r = load();
    for (name, table) in EXCLUDED {
        assert!(
            !r.instances.contains_key(*name),
            "{name} is excluded by decision and must not be pinned"
        );
        let t = r
            .notes
            .get(*table)
            .unwrap_or_else(|| panic!("the rim ratchet has no [{table}] table"));
        let reason = t
            .get(*name)
            .unwrap_or_else(|| panic!("{name} must be listed in [{table}] with its reason"));
        assert!(
            reason.len() > 30,
            "{name}'s [{table}] entry must state WHY, not merely appear: {reason:?}"
        );
    }
    assert!(
        r.notes.contains_key("not_finished"),
        "the [not_finished] table is where a model whose pivot count is a \
         function of the DEADLINE goes; losing it invites pinning the box"
    );
}

/// Every record complete, every tier a lane the script understands, and the
/// cost claim in the script's header kept honest.
#[test]
fn every_pin_is_well_formed_and_the_fast_lane_stays_a_lane() {
    let r = load();
    for (name, p) in &r.instances {
        assert_eq!(
            p.status.as_deref(),
            Some("OPTIMAL"),
            "{name}: only a solve that REACHES an optimum has a deadline-free \
             pivot count; a NONOPTIMAL pin is a pin on the wall clock"
        );
        for (key, got) in [
            ("switch_at", p.switch_at),
            ("p1_pivots", p.p1_pivots),
            ("pivots", p.pivots),
        ] {
            let v = got.unwrap_or_else(|| panic!("{name}: no `{key}` pin"));
            assert!(v >= 0, "{name}: negative {key} {v}");
        }
        assert!(
            p.pivots >= p.p1_pivots,
            "{name}: total pivots {:?} below phase-1 pivots {:?}",
            p.pivots,
            p.p1_pivots
        );
        let tier = p
            .tier
            .as_deref()
            .unwrap_or_else(|| panic!("{name}: no `tier`"));
        assert!(
            tier == "fast" || tier == "slow",
            "{name}: tier must be fast or slow, got {tier:?}"
        );
        let wall = p.wall_s.unwrap_or_else(|| panic!("{name}: no `wall_s`"));
        assert!(wall >= 0.0 && wall.is_finite(), "{name}: bad wall {wall}");
        // The rim is bignum arithmetic and its instances are an order of
        // magnitude apart in cost, so the fast lane's bound is looser than the
        // node gate's 2.5s — but it still binds: blend2, the slowest fast
        // member, is 7.9s and qiu at 88s is why `slow` exists.
        if tier == "fast" {
            assert!(
                wall <= 12.0,
                "{name}: {wall}s is not `fast`. Re-tier it to `slow` rather than \
                 letting the pre-push lane grow ten seconds at a time."
            );
        }
    }
    let fast_wall: f64 = r
        .instances
        .values()
        .filter(|p| p.tier.as_deref() == Some("fast"))
        .filter_map(|p| p.wall_s)
        .sum();
    assert!(
        fast_wall <= 30.0,
        "the fast lane now costs {fast_wall:.1}s of rim solving; that is a \
         nightly, not a pre-push gate. Re-tier before widening."
    );
    let fast_ff = r
        .instances
        .values()
        .filter(|p| p.tier.as_deref() == Some("fast"))
        .filter(|p| p.class.as_deref() == Some("fraction-free"))
        .count();
    assert!(
        fast_ff >= 4,
        "only {fast_ff} converting models in the fast lane — a pre-push rim gate \
         that cannot see the switch point is not watching the rim"
    );
}

/// EVERY PINNED NAME MUST HAVE A MODEL RECORDED SOMEWHERE DURABLE — the same
/// contract `node_ratchet.rs` enforces, for the same reason: a pin whose model
/// exists only on one laptop becomes `SETUP: model not found`, exit 2, forever.
#[test]
fn every_pinned_instance_has_a_corpus_manifest_row() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(".milp_gate_corpus.tsv");
    let text = std::fs::read_to_string(&path).expect("gate corpus manifest");
    let names: Vec<&str> = text
        .lines()
        .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
        .filter_map(|l| l.split('\t').next())
        .collect();
    let r = load();
    for name in r.instances.keys() {
        assert!(
            names.contains(&name.as_str()),
            "{name} is pinned in .milp_rim_baseline.toml but has no row in \
             .milp_gate_corpus.tsv. Everything this gate pins must be rebuildable \
             from this repository alone — that is why the ten domset_mw19 \
             relaxations are in [not_pinned] instead."
        );
    }
}

/// The parser is small enough to be wrong quietly, so it is exercised directly.
#[test]
fn the_rim_ratchet_reader_rejects_a_malformed_file() {
    let good = parse(
        "# comment\n[[instance]]\nname = \"pk1\"\nclass = \"fraction-free\"\n\
         status = \"OPTIMAL\"\nform = \"fraction-free\"\nswitch_at = 688\n\
         p1_pivots = 1396\npivots = 1396\nvalue = \"0\"\ntier = \"fast\"\n\
         wall_s = 2.579\n[not_finished]\nqnet1 = \"times out\"\n",
    );
    assert_eq!(good.instances["pk1"].switch_at, Some(688));
    assert_eq!(good.instances["pk1"].value.as_deref(), Some("0"));
    assert_eq!(good.notes["not_finished"]["qnet1"], "times out");
    let doubled = std::panic::catch_unwind(|| {
        parse(
            "[[instance]]\nname = \"pk1\"\npivots = 1\n[[instance]]\nname = \"pk1\"\npivots = 2\n",
        );
    });
    assert!(doubled.is_err(), "a doubled pin must not parse silently");
}
