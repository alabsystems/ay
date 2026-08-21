// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! **THE NODE RATCHET'S OWN GATE** — the half of the corpus regression gate
//! that a default `cargo test` run can actually enforce.
//!
//! # What went wrong
//!
//! A deterministic **2.34x node regression** on `blend2` (3,882 -> 9,070,
//! bisected to `dd591eb1b` "big-M indicator cut economy") landed on `main` and
//! cleared the standing gate **untouched**. Not because the gate was loose —
//! because the gate was four instances (`gt2` / `mas76` / `pk1` / `p0548`)
//! re-measured by hand, and `blend2` was not one of them. Fifteen more
//! instances are just as deterministic on this hardware and were watching
//! nothing at all.
//!
//! # Why this file does not solve anything
//!
//! The nineteen pinned models are MIPLIB files. This repository contains seven
//! `.mps` files in total, all tiny fixtures, and shipping MIPLIB into the tree
//! is not on the table — so `cargo test -p ay-milp` can never measure them.
//! The measurement lane is `scripts/milp_node_gate.py --check --corpus DIR`,
//! which needs a corpus directory and costs seconds-to-minutes.
//!
//! The tempting shortcut — have this test look for a corpus directory and
//! silently pass when it is absent — is a **dead gate**, the exact failure
//! family this round is cleaning up (a lane that reports success while
//! measuring nothing). It is not taken.
//!
//! # What this file does instead, for free
//!
//! It gates the RATCHET FILE, which is the part that decays silently:
//!
//! * the pinned set is **exactly** the deterministic nineteen — an instance
//!   cannot be quietly dropped to make a red gate go green, and a new one
//!   cannot be added without a decision;
//! * none of the five **budget-coupled** instances is smuggled in, because a
//!   gate that flakes gets muted and a muted gate is worse than none;
//! * the four instances the old standing gate pinned are all still there, so
//!   the new gate strictly widens the old one rather than replacing it;
//! * every record is well-formed and every pin is a real measurement.
//!
//! Cost: it reads one file. Microseconds. It belongs in the default test run
//! precisely because it costs nothing; the solving does not, and does not
//! pretend to.

use std::collections::BTreeMap;
use std::path::PathBuf;

/// The repo-root ratchet, alongside the `.code_quality_*_baseline.toml` family
/// it is modelled on.
fn ratchet_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(".milp_node_baseline.toml")
}

/// EVERY deterministic instance, by name. Restated here rather than derived
/// from the file, because "the file agrees with itself" is not a gate: the
/// point is that deleting a pin has to fail somewhere.
const DETERMINISTIC: &[&str] = &[
    "air03", "blend2", "dcmulti", "enigma", "gt2", "lseu", "mas76", "misc03", "mod008", "mod010",
    "p0033", "p0201", "p0282", "p0548", "pk1", "qnet1", "rout", "stein27", "stein45",
];

/// The instances that MOVE run-to-run at a fixed configuration on a quiet box,
/// and therefore may never be pinned. `misc07`'s root cut loop is wall-deadline
/// bounded (measured spread 30.4% over five repeats); `nw04` is budget-coupled
/// at short limits and already fooled one round by agreeing across two quiet
/// runs before moving.
const NEVER_GATE: &[&str] = &["mas74", "misc07", "nw04", "p2756", "qiu"];

/// The four the standing gate pinned before this file existed. The new gate
/// must be a superset: a wider gate that dropped one of the originals would be
/// a regression dressed as an improvement.
const THE_OLD_FOUR: &[&str] = &["gt2", "mas76", "pk1", "p0548"];

#[derive(Debug, Default, Clone)]
struct Pin {
    nodes: Option<i64>,
    obj: Option<f64>,
    status: Option<String>,
    tier: Option<String>,
    wall_s: Option<f64>,
}

struct Ratchet {
    instances: BTreeMap<String, Pin>,
    flaky: BTreeMap<String, String>,
}

/// Reader for the fixed grammar `scripts/milp_node_gate.py --ratchet` writes:
/// `[[instance]]` tables of `key = value`, then one `[flaky]` table of
/// `name = "reason"`. Deliberately not a general TOML parser — `ay-milp` takes
/// no `toml` dependency, and keeping both readers on the same small grammar is
/// what stops the script and this test from drifting apart.
fn parse(text: &str) -> Ratchet {
    let mut instances: BTreeMap<String, Pin> = BTreeMap::new();
    let mut flaky = BTreeMap::new();
    let mut pending: Option<Pin> = None;
    let mut pending_name: Option<String> = None;
    let mut in_flaky = false;
    let flush =
        |name: &mut Option<String>, pin: &mut Option<Pin>, into: &mut BTreeMap<String, Pin>| {
            if let (Some(n), Some(p)) = (name.take(), pin.take()) {
                assert!(
                    into.insert(n.clone(), p).is_none(),
                    "{n} is pinned twice in the ratchet"
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
            in_flaky = false;
            continue;
        }
        if line == "[flaky]" {
            flush(&mut pending_name, &mut pending, &mut instances);
            in_flaky = true;
            continue;
        }
        assert!(
            !line.starts_with('['),
            "unexpected table `{line}` — the ratchet grammar is [[instance]] and [flaky] only"
        );
        let (key, value) = line
            .split_once('=')
            .unwrap_or_else(|| panic!("not a `key = value` line: {line}"));
        let (key, value) = (key.trim(), value.trim().trim_matches('"'));
        if in_flaky {
            flaky.insert(key.to_string(), value.to_string());
            continue;
        }
        let pin = pending
            .as_mut()
            .unwrap_or_else(|| panic!("key `{key}` outside any table"));
        match key {
            "name" => pending_name = Some(value.to_string()),
            "nodes" => pin.nodes = Some(value.parse().expect("nodes is an integer")),
            "obj" => pin.obj = Some(value.parse().expect("obj is a number")),
            "status" => pin.status = Some(value.to_string()),
            "tier" => pin.tier = Some(value.to_string()),
            "wall_s" => pin.wall_s = Some(value.parse().expect("wall_s is a number")),
            other => panic!("unknown key `{other}` in the ratchet"),
        }
    }
    flush(&mut pending_name, &mut pending, &mut instances);
    Ratchet { instances, flaky }
}

fn load() -> Ratchet {
    let path = ratchet_path();
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "the node ratchet is missing at {}: {e}\n\
             It is not optional: `scripts/milp_node_gate.py` reads it, and without \
             it the corpus regression gate measures nothing.",
            path.display()
        )
    });
    parse(&text)
}

/// The regression that motivated all of this must be pinned by name. If someone
/// widens the gate again and drops `blend2`, that is the same defect returning.
#[test]
fn the_pinned_set_is_exactly_the_deterministic_corpus() {
    let r = load();
    let have: Vec<&str> = r.instances.keys().map(String::as_str).collect();
    let mut want: Vec<&str> = DETERMINISTIC.to_vec();
    want.sort_unstable();
    assert_eq!(
        have, want,
        "the ratchet's instance set drifted from the deterministic corpus.\n\
         A pin may only be removed by a decision that also removes it from \
         DETERMINISTIC here — deleting one to turn a red gate green is the \
         defect this file exists to stop."
    );
    assert!(
        r.instances.contains_key("blend2"),
        "blend2 is the instance whose 2.34x regression (3,882 -> 9,070) shipped \
         unnoticed. It is the reason this gate exists and it is never optional."
    );
}

/// The exclusion is the load-bearing half: a gate that cries wolf gets muted.
#[test]
fn no_budget_coupled_instance_is_pinned_and_each_is_named() {
    let r = load();
    for name in NEVER_GATE {
        assert!(
            !r.instances.contains_key(*name),
            "{name} moves run-to-run at a fixed configuration; pinning it makes \
             the gate fail with no code change behind it"
        );
        assert!(
            r.flaky.contains_key(*name),
            "{name} must be listed in the ratchet's [flaky] table with its reason, \
             so `why isn't {name} gated` is answered by the file and not by archaeology"
        );
        assert!(
            r.flaky[*name].len() > 20,
            "{name}'s [flaky] entry must state WHY, not merely appear: {:?}",
            r.flaky[*name]
        );
    }
}

/// A wider gate that quietly dropped one of the four it replaces would be a
/// regression wearing an improvement's clothes.
#[test]
fn the_new_gate_is_a_superset_of_the_standing_four() {
    let r = load();
    for name in THE_OLD_FOUR {
        assert!(
            r.instances.contains_key(*name),
            "{name} was pinned by the standing gate; the corpus gate must not lose it"
        );
    }
    assert!(
        r.instances.len() > THE_OLD_FOUR.len() * 4,
        "the whole point was to stop gating four instances: {} pinned",
        r.instances.len()
    );
}

/// Every record complete, every pin a real measurement, every tier a lane that
/// `scripts/milp_node_gate.py --tier` understands.
#[test]
fn every_pin_is_well_formed() {
    let r = load();
    for (name, p) in &r.instances {
        let nodes = p.nodes.unwrap_or_else(|| panic!("{name}: no `nodes` pin"));
        assert!(nodes >= 0, "{name}: negative node count {nodes}");
        assert!(
            p.obj.is_some(),
            "{name}: no `obj` pin — the correctness half"
        );
        assert!(
            p.obj.expect("checked").is_finite(),
            "{name}: non-finite objective pin"
        );
        let status = p
            .status
            .as_deref()
            .unwrap_or_else(|| panic!("{name}: no `status` pin"));
        assert_eq!(
            status, "OPTIMAL",
            "{name}: only proved-optimal solves are deterministic enough to pin \
             exactly; a FEASIBLE pin is an incumbent race, not a measurement"
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
        // The tier split is a COST claim the script's header quotes (7.2s for
        // the fast lane, 44.8s for all nineteen). Keep it honest: a `fast`
        // instance that takes ten seconds silently turns the pre-merge lane into
        // the nightly one, and the slowest fast instance today is blend2 at
        // 1.6s, so this bound has real margin and still binds.
        if tier == "fast" {
            assert!(
                wall <= 2.5,
                "{name}: {wall}s is not `fast`. Re-tier it to `slow` rather than \
                 letting the pre-merge lane grow a second at a time."
            );
        }
    }
    // And the fast lane must stay a lane, not a corpus sweep with a nice name.
    let fast_wall: f64 = r
        .instances
        .values()
        .filter(|p| p.tier.as_deref() == Some("fast"))
        .filter_map(|p| p.wall_s)
        .sum();
    assert!(
        fast_wall <= 20.0,
        "the fast lane now costs {fast_wall:.1}s of solving; that is a nightly, \
         not a pre-merge gate. Re-tier before widening."
    );
    let fast = r
        .instances
        .values()
        .filter(|p| p.tier.as_deref() == Some("fast"))
        .count();
    assert!(
        fast >= 10,
        "only {fast} instances in the fast lane — the pre-merge gate has to be \
         wide enough to be worth running"
    );
}

/// EVERY PINNED NAME MUST HAVE A MODEL RECORDED SOMEWHERE DURABLE.
///
/// Until 2026-08-20 the nineteen models lived in two per-session scratch
/// directories under `/private/tmp/.../scratchpad/`. A pin whose model exists
/// only on one laptop is a pin that becomes `SETUP: model not found` — exit 2,
/// forever — the moment that scratch is reaped, and the sibling
/// `scripts/corpus_guard.py` had already been in exactly that state (its
/// `--corpus` default, `~/ay-corpus`, has never existed on this box) without
/// anybody noticing.
///
/// `.milp_gate_corpus.tsv` records a sha256 and an upstream URL per instance, so
/// `scripts/milp_gate_corpus.py --build` can reconstruct the corpus from this
/// repository alone. This test costs one more file read and makes it impossible
/// to add a pin without also recording where its model comes from.
#[test]
fn every_pinned_and_flaky_instance_has_a_manifest_row() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(".milp_gate_corpus.tsv");
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "the gate corpus manifest is missing at {}: {e}\n\
             Without it the pinned models are reconstructible from nothing.",
            path.display()
        )
    });
    let mut have: BTreeMap<String, String> = BTreeMap::new();
    for line in text.lines() {
        let line = line.trim_end();
        if line.trim().is_empty() || line.starts_with('#') {
            continue;
        }
        let f: Vec<&str> = line.split('\t').collect();
        assert_eq!(
            f.len(),
            5,
            "manifest row must be name/sha256/bytes/source/roles: {line:?}"
        );
        assert_eq!(f[1].len(), 64, "{}: sha256 must be 64 hex chars", f[0]);
        assert!(
            f[1].chars().all(|c| c.is_ascii_hexdigit()),
            "{}: sha256 is not hex",
            f[0]
        );
        assert!(
            f[2].parse::<u64>().is_ok_and(|n| n > 0),
            "{}: byte count must be a positive integer",
            f[0]
        );
        assert!(
            f[3] == "miplib2017-webdata" || f[3] == "miplib3",
            "{}: unknown source {:?} — scripts/milp_gate_corpus.py must know how \
             to fetch it or the manifest is decoration",
            f[0],
            f[3]
        );
        have.insert(f[0].to_string(), f[3].to_string());
    }
    let r = load();
    for name in r.instances.keys().chain(r.flaky.keys()) {
        assert!(
            have.contains_key(name),
            "{name} is named in .milp_node_baseline.toml but has no row in \
             .milp_gate_corpus.tsv. Add it (sha256 + upstream URL) before pinning \
             it: a pin whose model nobody can fetch is a gate that exits 2 forever."
        );
    }
}

/// The parser is small enough to be wrong quietly, so it is exercised directly.
#[test]
fn the_ratchet_reader_rejects_a_malformed_file() {
    let good = parse(
        "# comment\n[[instance]]\nname = \"gt2\"\nnodes = 4954\nobj = 21166.0\n\
         status = \"OPTIMAL\"\ntier = \"fast\"\nwall_s = 0.165\n[flaky]\nqiu = \"moves\"\n",
    );
    assert_eq!(good.instances["gt2"].nodes, Some(4954));
    assert_eq!(good.flaky["qiu"], "moves");
    let doubled = std::panic::catch_unwind(|| {
        parse("[[instance]]\nname = \"gt2\"\nnodes = 1\n[[instance]]\nname = \"gt2\"\nnodes = 2\n");
    });
    assert!(doubled.is_err(), "a doubled pin must not parse silently");
}
