// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn table_has_no_duplicates_and_is_sorted() {
    for w in KNOBS.windows(2) {
        assert!(w[0].name < w[1].name, "KNOBS not sorted at {}", w[0].name);
    }
}

#[test]
fn every_deprecation_names_a_known_knob() {
    for d in DEPRECATED {
        assert!(
            KNOBS.iter().any(|k| k.name == d.env),
            "{} is deprecated but not in the ledger",
            d.env
        );
    }
}

/// Dead means no reads. The converse is NOT true, and assuming it was is how
/// three unread names kept a read site each in the table: the twelve knobs
/// `EngineEconomics` migrated to `tune` also read zero literal sites, so the
/// old `Dead == (read_sites == 0)` biconditional could not have held once M1
/// landed. It is now an implication plus [`ROUTED`].
#[test]
fn dead_knobs_have_no_read_sites() {
    for k in KNOBS {
        if k.bucket == Bucket::Dead {
            assert_eq!(k.read_sites, 0, "{} is Dead but claims a read site", k.name);
        }
    }
}

/// Every zero is accounted for: a knob reads nothing because it is dead, or
/// because it is reached another way and [`ROUTED`] says how. An unexplained
/// zero is the retired cond-tighten shape — a name documented as *"kept as
/// the explicit-on A/B arm"* (`presolve.rs`) that no code reads, so a campaign
/// setting it measures the default arm and records the result as a finding.
#[test]
fn every_zero_read_knob_is_dead_or_routed() {
    for k in KNOBS {
        if k.read_sites == 0 && k.bucket != Bucket::Dead {
            assert!(
                ROUTED.iter().any(|r| r.env == k.name),
                "{} has no literal read site, is not Dead, and is not in ROUTED — \
                 setting it does nothing and nothing says so",
                k.name
            );
        }
    }
}

/// A routed knob must be live and in the table. A stale `ROUTED` entry would
/// re-open the hole it exists to close.
#[test]
fn routed_names_are_live_ledger_entries() {
    for r in ROUTED {
        let k = KNOBS
            .iter()
            .find(|k| k.name == r.env)
            .unwrap_or_else(|| panic!("{} is ROUTED but not in the ledger", r.env));
        assert_ne!(k.bucket, Bucket::Dead, "{} is both ROUTED and Dead", r.env);
        assert_eq!(
            k.read_sites, 0,
            "{} is ROUTED but has literal read sites; drop the ROUTED entry",
            r.env
        );
    }
}
