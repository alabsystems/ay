// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The env-var ledger must stay complete.
//!
//! This is the test that stops the count growing silently. Adding an `AY_*`
//! switch without adding it to `knobs.rs` fails here, which means:
//!
//! * `ay-milp knobs --list` never goes out of date, and
//! * the unknown-name guard keeps working — a name outside the ledger is
//!   reported as a probable typo, and that report is only trustworthy while the
//!   ledger is exhaustive.
//!
//! It is deliberately a source scan rather than a macro: the point is to catch
//! a knob added by hand at a fresh `env::var` site, which no macro can see.

use ay_test_support::env::with_env_edits;
use std::collections::BTreeSet;
use std::path::Path;

#[path = "env_ledger/audit_policy.rs"]
mod audit_policy;
#[path = "env_ledger/census_history.rs"]
mod census_history;
#[path = "env_ledger/source_scan.rs"]
mod source_scan;

use census_history::assert_census_matches_survey;
use source_scan::{retired_in_comments, scan};

/// Names that appear in source as ILLUSTRATIONS and are meant not to exist.
///
/// `AY_MILP_NO_CUTZ` is the worked example of the bug the guard exists to
/// catch: a plausible-looking misspelling that is a silent no-op, so a campaign
/// that sets it measures the wrong arm and records the result as a finding.
/// The trailing-underscore entries are PROSE PREFIXES, not names: documentation
/// that writes "every `AY_MILP_NO_*` switch" leaves an `AY_MILP_NO_` token
/// behind. They are listed rather than filtered by shape, because
/// `AY_MILP_SB_` is a real (dead) ledger entry of exactly that shape and a
/// shape filter would make the ledger look stale.
const DOC_EXAMPLES: &[&str] = &["AY_MILP_NO_CUTZ", "AY_", "AY_MILP_NO_", "AY_MILP_"];

#[test]
fn every_ay_env_name_in_source_is_in_the_ledger() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut found = BTreeSet::new();
    scan(&root.join("src"), &mut found);
    scan(&root.join("examples"), &mut found);
    let ledger: BTreeSet<&str> = ay_milp::KNOBS.iter().map(|k| k.name).collect();
    let missing: Vec<&String> = found
        .iter()
        .filter(|n| {
            !ledger.contains(n.as_str())
                && !DOC_EXAMPLES.contains(&n.as_str())
                && !retired_in_comments().contains(n.as_str())
        })
        .collect();
    assert!(
        missing.is_empty(),
        "these AY_* names appear in source but not in knobs.rs's ledger: {missing:?}\n\
         Add them (with a bucket) so `ay-milp knobs --list` stays complete and the \
         unknown-name guard stays trustworthy."
    );
}

#[test]
fn the_ledger_does_not_invent_names() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut found = BTreeSet::new();
    scan(&root.join("src"), &mut found);
    scan(&root.join("examples"), &mut found);
    let stale: Vec<&str> = ay_milp::KNOBS
        .iter()
        .map(|k| k.name)
        .filter(|n| !found.contains(*n))
        .collect();
    assert!(
        stale.is_empty(),
        "the ledger lists names that no longer appear in source: {stale:?}"
    );
}

#[test]
fn the_census_matches_the_survey() {
    // Regression guard on the two numbers the debt triage rests on: if either
    // moves, the chronology in `env_ledger/census_history.md` needs re-reading.
    let total = ay_milp::KNOBS.len();
    let dead = ay_milp::KNOBS
        .iter()
        .filter(|k| k.bucket == ay_milp::Bucket::Dead)
        .count();
    assert_census_matches_survey(total, dead);
}

#[test]
fn kill_switches_are_never_marked_deprecated() {
    // `AY_MILP_NO_*` is the A/B mechanism every measured result in the journal
    // rests on. Collapsing it into a flag is fine; retiring the NAMES is not.
    for d in ay_milp::DEPRECATED {
        let k = ay_milp::KNOBS
            .iter()
            .find(|k| k.name == d.env)
            .expect("deprecation names a ledger entry");
        assert_ne!(
            k.bucket,
            ay_milp::Bucket::KillSwitch,
            "{} is a kill switch and must not be deprecated",
            d.env
        );
    }
}

#[test]
fn env_audit_flags_an_unknown_name() {
    // The audit is a pure function of the process environment, so this test
    // sets one through the shared, restore-on-unwind environment boundary.
    let name = "AY_MILP_LEDGER_TEST_TYPO_DO_NOT_ADD";
    let audit = with_env_edits(|env| {
        env.set(name, "1");
        ay_milp::env_audit()
    });
    assert!(
        audit.unknown.iter().any(|n| n == name),
        "a name outside the ledger must be reported: {:?}",
        audit.unknown
    );
}

/// Count literal `env::var("NAME")` / `env::var_os("NAME")` call sites per name.
fn literal_read_sites(dir: &Path, into: &mut std::collections::BTreeMap<String, u32>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            literal_read_sites(&p, into);
            continue;
        }
        if p.extension().is_none_or(|x| x != "rs") {
            continue;
        }
        // The ledger describes the rest of the crate, not itself.
        if p.file_name().is_some_and(|f| f == "knobs.rs") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(&p) else {
            continue;
        };
        for (i, _) in text.match_indices("env::var") {
            let rest = &text[i + "env::var".len()..];
            let rest = rest.strip_prefix("_os").unwrap_or(rest);
            let rest = rest.trim_start();
            let Some(rest) = rest.strip_prefix('(') else {
                continue;
            };
            let rest = rest.trim_start();
            let Some(rest) = rest.strip_prefix('"') else {
                continue;
            };
            let Some(end) = rest.find('"') else { continue };
            let name = &rest[..end];
            if name.starts_with("AY_") {
                *into.entry(name.to_string()).or_default() += 1;
            }
        }
    }
}

/// THE LEDGER'S NUMBERS ARE DERIVED, NOT DECLARED.
///
/// `read_sites` was hand-typed, checked by nothing, and cited as evidence. When
/// this test was written **23 of 353 entries disagreed with the source**, and the
/// disagreement was structured rather than random:
///
/// * twelve were exactly the knobs `EngineEconomics` moved into `tune` — their
///   literal reads were deleted by the M1 migration and the ledger went on
///   claiming one apiece;
/// * three (`AY_MILP_COND_TIGHTEN`, `AY_ALLOCSTAT`, `AY_SEPSTAT`) were read by
///   **nothing at all**, one of them documented in `presolve.rs` as *"kept as the
///   explicit-on A/B arm"* — an arm that does nothing, which is the
///   `AY_MILP_NO_CUTZ` defect this whole ledger exists to prevent, sitting inside
///   the ledger;
/// * the rest were plain undercounts, including `AY_MILP_TRACE` at 58 for 59.
///
/// A number that no test derives is not evidence, and a debt census quoting this
/// column reported "404 read sites" against a column that summed to 432.
#[test]
fn read_site_counts_are_derived() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut actual = std::collections::BTreeMap::new();
    literal_read_sites(&root.join("src"), &mut actual);
    literal_read_sites(&root.join("examples"), &mut actual);

    let mut wrong = Vec::new();
    for k in ay_milp::KNOBS {
        let a = actual.get(k.name).copied().unwrap_or(0);
        if a != k.read_sites {
            wrong.push(format!(
                "  {:38} declared {:3}  actual {:3}",
                k.name, k.read_sites, a
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "{} ledger entries declare a read-site count the source does not support.\n{}\n\
         Re-derive the column; do not hand-edit it. A knob that legitimately reads \
         zero literal sites belongs in `knobs::ROUTED` with its mechanism.",
        wrong.len(),
        wrong.join("\n")
    );
}

/// A RETIRED NAME MAY NOT COME BACK TO LIFE BEHIND ITS OWN DOCUMENTATION.
///
/// `retired_env_names.txt` was already load-bearing in ONE direction:
/// `every_ay_env_name_in_source_is_in_the_ledger` excuses a name from the ledger
/// BECAUSE it is listed there. Nothing checked the other direction, and the gap
/// had a live occupant. B6 deleted the `AY_MILP_TALL_LU_ROWS` read on the
/// decision table's explicit "delete the read" verdict — a threshold that DEFINES
/// a class must not be settable per process, or the gate in `bab.rs` that mirrors
/// the same number drifts away from it silently — but the two doc comments over
/// the constant went on advertising the override ("=1200 restores the historical
/// behavior byte-for-byte") for as long as the file existed. Two independent
/// audits then read that promise as a defect in the CODE and proposed restoring
/// the read. Restoring it would have re-broken the invariant the verdict was
/// protecting and passed every test in this file.
///
/// So: listed there means NO literal read site, full stop. Re-arming one is a
/// deliberate act — take the name off the list and give it a ledger row in the
/// same change — not something a stale doc comment can imply back into existence.
#[test]
fn retired_names_have_no_read_sites() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut actual = std::collections::BTreeMap::new();
    literal_read_sites(&root.join("src"), &mut actual);
    literal_read_sites(&root.join("examples"), &mut actual);

    let resurrected: Vec<String> = retired_in_comments()
        .iter()
        .filter_map(|n| actual.get(*n).map(|c| format!("  {n:38} {c} read site(s)")))
        .collect();
    assert!(
        resurrected.is_empty(),
        "{} name(s) listed in tests/retired_env_names.txt have literal read sites \
         again:\n{}\n\
         Retired means the read is gone and the surviving comments say what replaced \
         it. To re-arm one, delete it from that file and add a `knobs.rs` ledger row \
         (bucket + derived read-site count) in the same change — and re-read why it \
         was retired first.",
        resurrected.len(),
        resurrected.join("\n")
    );
}

/// THE `=0` TRAP MAY NOT GROW IN SILENCE.
///
/// `env::var(K).ok().and_then(parse).filter(|&n| n > 0).unwrap_or(DEFAULT)` means
/// `K=0` resolves to `DEFAULT` — the one value the operator was trying to move
/// away from. `AY_MILP_NG_CAP=0` reads as `NOGOOD_CAP_*`; `AY_MILP_COLD_LU_ROWS=0`,
/// which is the natural way to ask for "no row floor, always take the LU lane",
/// reads as the measured floor.
///
/// Fourteen sites do this today and each is declared in `knobs::ZERO_IGNORED`
/// with what an operator would expect `0` to mean. Deciding which of them should
/// honour zero is a per-site change with its own measurement; what this test buys
/// now is that a fifteenth cannot appear without someone writing down that it has.
#[test]
fn zero_ignored_sites_are_declared() {
    fn scan_zero_filters(dir: &Path, into: &mut BTreeSet<String>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                scan_zero_filters(&p, into);
                continue;
            }
            if p.extension().is_none_or(|x| x != "rs")
                || p.file_name().is_some_and(|f| f == "knobs.rs")
            {
                continue;
            }
            let Ok(text) = std::fs::read_to_string(&p) else {
                continue;
            };
            for (i, _) in text.match_indices("env::var") {
                let rest = &text[i..];
                let Some(q1) = rest.find('"') else { continue };
                let Some(q2) = rest[q1 + 1..].find('"') else {
                    continue;
                };
                let name = &rest[q1 + 1..q1 + 1 + q2];
                if !name.starts_with("AY_") {
                    continue;
                }
                // The chain is a few lines at most; look at the window after it.
                // The window is THIS statement only, not a fixed byte count: the
                // parse chain ends at the first `;`, and a fixed window reaches
                // into the NEXT knob's chain -- which reported AY_MILP_NODE_GMI,
                // _MARGIN and _ONLY as zero-discarding because they sit beside
                // _ROUNDS and _EVERY, which are.
                let stmt_end = rest.find(';').map_or(rest.len(), |n| n + 1);
                let window = &rest[..stmt_end];
                let filters_zero = window.lines().any(|l| {
                    let l = l.trim();
                    l.starts_with(".filter(") && l.contains("> 0)") && !l.contains("len()")
                });
                if filters_zero {
                    into.insert(name.to_string());
                }
            }
        }
    }
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut found = BTreeSet::new();
    scan_zero_filters(&root.join("src"), &mut found);

    let declared: BTreeSet<String> = ay_milp::ZERO_IGNORED
        .iter()
        .map(|z| z.env.to_string())
        .collect();
    let undeclared: Vec<&String> = found.difference(&declared).collect();
    let stale: Vec<&String> = declared.difference(&found).collect();
    assert!(
        undeclared.is_empty(),
        "these knobs silently discard `=0` and are not in knobs::ZERO_IGNORED: {undeclared:?}\n\
         Setting one of them to 0 resolves to the COMPILED DEFAULT, so a campaign that does \
         so measures the default and records the result as a finding. Declare it (with what \
         an operator would expect 0 to mean) or make the site honour zero."
    );
    assert!(
        stale.is_empty(),
        "knobs::ZERO_IGNORED lists knobs whose call site no longer discards 0: {stale:?}"
    );
}

/// Every `AY_*` in `knobs::ZERO_IGNORED` must be a real ledger entry.
#[test]
fn zero_ignored_names_are_in_the_ledger() {
    for z in ay_milp::ZERO_IGNORED {
        assert!(
            ay_milp::KNOBS.iter().any(|k| k.name == z.env),
            "{} is in ZERO_IGNORED but not in the ledger",
            z.env
        );
        assert!(
            !z.zero_would_mean.is_empty(),
            "{} needs a note saying what an operator would expect 0 to mean",
            z.env
        );
    }
}

/// Count `env::var` reads, split by whether a `OnceLock` caches them.
fn count_env_reads(dir: &Path, live: &mut usize, cached: &mut usize) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            count_env_reads(&p, live, cached);
            continue;
        }
        if p.extension().is_none_or(|x| x != "rs") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(&p) else {
            continue;
        };
        for (i, _) in text.match_indices("env::var") {
            let rest = &text[i + "env::var".len()..];
            let rest = rest.strip_prefix("_os").unwrap_or(rest);
            let Some(rest) = rest.trim_start().strip_prefix('(') else {
                continue;
            };
            let Some(rest) = rest.trim_start().strip_prefix('"') else {
                continue;
            };
            if !rest.starts_with("AY_") {
                continue;
            }
            // Char-boundary safe: this source is full of non-ASCII (— × ≤ ⚠).
            let lo = (i.saturating_sub(400)..=i)
                .find(|&n| text.is_char_boundary(n))
                .unwrap_or(i);
            let back = &text[lo..i];
            // CACHED means "inside a `OnceLock::get_or_init` initializer", and the
            // test is deliberately TIGHT rather than a plain look-back. A bare
            // "is there a OnceLock somewhere behind me" rule misclassifies a LIVE
            // read that merely sits near a cached accessor — which would silently
            // defeat this ratchet, since a misclassified live read stops counting
            // against the ceiling.
            //
            // Measured over the whole crate: every one of the 91 genuinely cached
            // reads is on the SAME LINE as its `get_or_init` (62) or exactly one
            // line after it (29); none is further. The accessors are all the shape
            // `*ON.get_or_init(|| env::var("...")...)`, often a brace-less closure.
            // Two lines is that pattern plus margin.
            // Strip `//` comments from the look-back before classifying. This file's
            // OWN doc comments contain the words `OnceLock` and `get_or_init`, so a
            // live read written just below one of them would be scored as cached and
            // would stop counting against the ceiling — the ratchet quietly failing
            // open. A review caught that; it is not hypothetical, the strings are
            // right here.
            let code: String = back
                .lines()
                .map(|l| match l.find("//") {
                    Some(c) => &l[..c],
                    None => l,
                })
                .collect::<Vec<_>>()
                .join("\n");
            // And require a closure to actually open at the `get_or_init`, so a
            // completed expression elsewhere on the line cannot qualify.
            let cached_here = code.rfind("get_or_init").is_some_and(|gi| {
                code.contains("OnceLock")
                    && code[gi..].starts_with("get_or_init(|")
                    && code[gi..].matches('\n').count() <= 2
            });
            if cached_here {
                *cached += 1;
            } else {
                *live += 1;
            }
        }
    }
}

/// THE RESIDUAL RACE SURFACE MAY NOT GROW.
///
/// `tune.rs` advertises that the environment is read once and never again. That is
/// true of the `tune` layer and **false of this crate**: most `AY_*` reads are LIVE
/// — a fresh `env::var` on every invocation, at any depth, on any thread — and a
/// consumer that rewrites its environment between window solves can race any one of
/// them. `bab::prime_env_all` forces the `OnceLock`-cached subset at solve entry;
/// nothing can force a live read, because there is no cache to force.
///
/// So this is a RATCHET, not an assertion of correctness. The counts are pinned so
/// that the migration to a typed per-solve config can only move them down. A new
/// live read fails here and has to be justified or routed through `tune`.
///
/// Derived, never declared — the same rule `read_site_counts_are_derived` enforces
/// for the ledger, applied to the thing the ledger does not cover.
#[test]
fn the_live_env_read_surface_does_not_grow() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let (mut live, mut cached) = (0usize, 0usize);
    count_env_reads(&root.join("src"), &mut live, &mut cached);

    // Measured 2026-08-01 BY THIS SCANNER, after `prime_env_all` landed. `cached` is
    // the primed set; `live` is the part priming cannot reach and is the real
    // remaining exposure.
    //
    // The number is whatever the scanner above says, deliberately: an ad-hoc script
    // reported 318 for the same tree because it took a different look-back window
    // when deciding "is this read inside a OnceLock initializer". One classifier has
    // to be the definition, and it should be the one that enforces the bound. That
    // is the same rule as `read_site_counts_are_derived` -- the checker defines the
    // number, and no hand-carried figure is allowed to compete with it.
    // 319 -> 321 when the classifier was TIGHTENED (>=2 lines from `get_or_init`).
    // Not new reads: two that the looser look-back had been counting as cached are
    // in fact live, and a ratchet that miscounts in the permissive direction is
    // worse than a slightly higher honest number.
    //
    // 321 -> 325 (2026-08-01). The structure-recognition lanes arrived with NINE new
    // bare `env::var_os("AY_MILP_TRACE")` predicates, one per module — exactly the
    // shape this ratchet asks to be cached. All nine were routed through a
    // module-local `OnceLock` (`direct_cnf`, `pb_route`, `sat_relu`,
    // `network_design_route`, `network_design_benders`, `hybrid_pb_lp`, `parity`,
    // `presolve::binary_complement`, `presolve::objective_singleton`), so they cost
    // the ratchet nothing.
    //
    // The four that remain are ARM SELECTORS and must stay live:
    //   AY_MILP_AMO_MULTIWAY   x2  (bab.rs)
    //   AY_MILP_ORBITOPE_DYN   x1  (bab.rs, the new dynamic-orbitope site)
    //   AY_MILP_HYBRID_PB_LP   x1  (session.rs)
    // `bab.rs` tests flip AMO_MULTIWAY and ORBITOPE_DYN with `ScopedEnvVar` inside a
    // single process. A `OnceLock` would latch the first value read and silently make
    // the arm unswitchable — the A/B campaign would then measure one arm twice and
    // record the result as a finding, which is the `AY_MILP_NO_CUTZ` failure mode this
    // whole ledger exists to prevent. Caching them would be the WRONG way to make this
    // number go down.
    //
    // 325 -> 326 (2026-08-02): `AY_MILP_CUT_SHADOW`, the perturbation-matched cut
    // control (`bab::shadow_control_model`). It is the FIFTH arm selector on the list
    // above and takes the list's rule, not an exception to it: an arm cached in a
    // `OnceLock` latches the first value the process reads, and a three-arm cut
    // measurement whose C arm silently re-runs B is precisely the `AY_MILP_NO_CUTZ`
    // failure this ledger exists to catch. It is read ONCE per `add_root_cuts` and
    // threaded to its two use sites as a local, so the count is one and not two.
    //
    // 326 -> 327 (2026-08-03): `AY_MILP_PUMP_WORK_MULT`, the multiplier on the pump's new
    // root-LP-denominated budget cap (`bab::pump_window`). It is the SIXTH entry on the arm-selector
    // list and takes the list's rule, not an exception to it. `bab.rs`'s own
    // `pump_share_override_bypasses_the_work_cap_and_mult_rejects_nonfinite` flips this knob and
    // `AY_MILP_PUMP_SHARE` several times inside ONE process with `ScopedEnvVar`; a `OnceLock` would
    // latch the first value and make the cap unswitchable, so a sweep would silently measure one arm
    // repeatedly and record it as a finding — the `AY_MILP_NO_CUTZ` failure this ledger exists to
    // catch. Net growth is one, not two: `pump_window` needs to distinguish a PINNED share from an
    // unset one, and rather than add a second `AY_MILP_PUMP_SHARE` read for that, the existing
    // `pump_share()` was refactored onto a single `pump_share_override()` site that both callers use.
    const LIVE_CEILING: usize = 327;
    // 90 -> 100 (2026-08-01): the ten accessors moved off the live count above
    // land here. Growth in THIS number is the ratchet working — a cached read is
    // forced once at solve entry by `bab::prime_env_all` and cannot be raced
    // afterwards. Every one of the ten is registered there.
    const CACHED_AT_LAST_MEASURE: usize = 100;

    assert!(
        live <= LIVE_CEILING,
        "live (uncached) AY_* env reads grew {live} > {LIVE_CEILING}. Every one is a \
         fresh getenv on the solve path that a concurrent set_var can race, and that \
         priming cannot help. Route it through `tune` or justify it here."
    );
    assert!(
        cached <= CACHED_AT_LAST_MEASURE + 8,
        "cached env reads grew to {cached}; add the accessor to its module's \
         `prime_env()` so it is forced at solve entry, then raise this bound"
    );
}
