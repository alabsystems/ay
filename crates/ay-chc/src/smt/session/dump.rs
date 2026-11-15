// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--chc-session-dump <dir>` query recorder (design §10.1; owner WP-4 / D).
//!
//! Hooked in the router gate (`smt/check_sat/horn_session.rs`). Writes each
//! routed query as a self-contained SMT-LIB script `q_<seq>_<thread>.smt2`
//! (sort-unique declarations, one `(assert ..)` per top-level conjunct) plus
//! `index.tsv` rows
//! `seq thread lane_result elapsed_us n_conj n_delta n_assumptions decisions unknown_reason`
//! — the layout of the microbenchmark's `query_dump.rs` extended by the
//! session columns, so `scripts/chc_session_replay.py` and
//! `session/tests/replay.rs` read both (the replay reads only the script
//! files and the first four columns).
//!
//! `--chc-session-dump-max` caps the number of script files (default 5000);
//! index rows keep flowing past the cap so the verdict census is complete.
//!
//! The serializer ([`script_for`]) is shared with the differential harness
//! (`session/harness.rs`), which feeds the same text to z3.

use std::fmt::Write as _;
use std::fs::{File, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};
use std::time::Duration;

use crate::smt::sort_unique::SortUniqueRenaming;
use crate::{ChcExpr, ChcSort, ChcVar, InvariantModel};

pub(crate) struct SessionDump {
    dir: PathBuf,
    seq: u64,
    index: File,
    max_files: u64,
    files_written: u64,
}

/// One routed query, as the router saw it.
pub(crate) struct DumpRecord<'a> {
    pub(crate) thread: u64,
    pub(crate) expr: &'a ChcExpr,
    /// `sat` | `unsat` | `unknown` | `fallthrough`.
    pub(crate) lane_result: &'a str,
    pub(crate) elapsed: Duration,
    pub(crate) n_conj: usize,
    pub(crate) n_delta: u64,
    pub(crate) n_assumptions: u64,
    pub(crate) decisions: u64,
    /// `-` when the query was decided; else the `UnknownReason` class.
    pub(crate) unknown_reason: &'a str,
}

/// SMT-LIB sort text for the sorts a routed query can carry.
fn sort_text(sort: &ChcSort) -> String {
    match sort {
        ChcSort::Bool => "Bool".to_owned(),
        ChcSort::Int => "Int".to_owned(),
        ChcSort::Real => "Real".to_owned(),
        ChcSort::BitVec(w) => format!("(_ BitVec {w})"),
        ChcSort::Array(k, v) => format!("(Array {} {})", sort_text(k), sort_text(v)),
        ChcSort::Uninterpreted(name) | ChcSort::Datatype { name, .. } => {
            ay_core::quote_symbol(name)
        }
    }
}

fn logic_for(vars: &[ChcVar]) -> &'static str {
    let mut int = false;
    let mut real = false;
    for v in vars {
        match v.sort {
            ChcSort::Int => int = true,
            ChcSort::Real => real = true,
            _ => {}
        }
    }
    match (int, real) {
        (true, true) => "QF_LIRA",
        (true, false) => "QF_LIA",
        (false, true) => "QF_LRA",
        (false, false) => "QF_UF",
    }
}

/// A self-contained SMT-LIB script for `expr`: `set-logic`, sort-unique
/// `declare-const`s, one `assert` per top-level conjunct, `check-sat`.
/// `produce_models` adds the option and a trailing `(get-model)`.
pub(crate) fn script_for(expr: &ChcExpr, produce_models: bool) -> String {
    let vars = expr.vars();
    let renaming = SortUniqueRenaming::plan(&vars);
    let renamed_expr;
    let (expr, vars) = match &renaming {
        Some(r) => {
            renamed_expr = r.apply(expr);
            (&renamed_expr, r.renamed_vars(&vars))
        }
        None => (expr, vars),
    };
    let mut s = String::with_capacity(512);
    let _ = writeln!(s, "(set-logic {})", logic_for(&vars));
    if produce_models {
        s.push_str("(set-option :produce-models true)\n");
    }
    for v in &vars {
        let _ = writeln!(
            s,
            "(declare-const {} {})",
            ay_core::quote_symbol(&v.name),
            sort_text(&v.sort)
        );
    }
    for c in expr.conjuncts() {
        let _ = writeln!(s, "(assert {})", InvariantModel::expr_to_smtlib(c));
    }
    s.push_str("(check-sat)\n");
    if produce_models {
        s.push_str("(get-model)\n");
    }
    s
}

impl SessionDump {
    /// `None` unless `--chc-session-dump <dir>` names a directory that can be
    /// created and written.
    pub(crate) fn from_cli() -> Option<Self> {
        let flags = ay_core::misc_cli_flags();
        let dir = flags.chc_session_dump.as_ref()?;
        if dir.is_empty() {
            return None;
        }
        let max_files = flags.chc_session_dump_max.unwrap_or(5_000);
        Self::open(Path::new(dir), max_files)
    }

    /// Open (create) a dump directory; the index is appended to.
    pub(crate) fn open(dir: &Path, max_files: u64) -> Option<Self> {
        if std::fs::create_dir_all(dir).is_err() {
            tracing::warn!("--chc-session-dump: cannot create {}", dir.display());
            return None;
        }
        let index_path = dir.join("index.tsv");
        let fresh = !index_path.exists();
        let mut index = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&index_path)
            .ok()?;
        if fresh {
            let _ = writeln!(
                index,
                "seq\tthread\tlane_result\telapsed_us\tn_conj\tn_delta\tn_assumptions\tdecisions\tunknown_reason"
            );
        }
        Some(Self {
            dir: dir.to_path_buf(),
            seq: 0,
            index,
            max_files,
            files_written: 0,
        })
    }

    /// The process-wide recorder (opened once from the CLI flags).
    pub(crate) fn global() -> Option<&'static Mutex<SessionDump>> {
        static DUMP: OnceLock<Option<Mutex<SessionDump>>> = OnceLock::new();
        DUMP.get_or_init(|| SessionDump::from_cli().map(Mutex::new))
            .as_ref()
    }

    pub(crate) fn record(&mut self, q: &DumpRecord<'_>) {
        let seq = self.seq;
        self.seq += 1;
        if self.files_written < self.max_files {
            let path = self.dir.join(format!("q_{seq:06}_{}.smt2", q.thread));
            if std::fs::write(&path, script_for(q.expr, true)).is_ok() {
                self.files_written += 1;
            }
        }
        let _ = writeln!(
            self.index,
            "{seq}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            q.thread,
            q.lane_result,
            q.elapsed.as_micros(),
            q.n_conj,
            q.n_delta,
            q.n_assumptions,
            q.decisions,
            q.unknown_reason,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ChcVar;

    fn real(name: &str) -> ChcExpr {
        ChcExpr::var(ChcVar::new(name, ChcSort::Real))
    }

    #[test]
    fn script_declares_each_variable_once_and_asserts_per_conjunct() {
        let x = real("x");
        let y = real("y");
        let e = ChcExpr::and_all([
            ChcExpr::le(x.clone(), ChcExpr::Real(3, 2)),
            ChcExpr::lt(y.clone(), x.clone()),
            ChcExpr::ge(y, ChcExpr::Int(0)),
        ]);
        let s = script_for(&e, false);
        assert!(s.starts_with("(set-logic QF_LRA)\n"), "{s}");
        assert_eq!(s.matches("(declare-const x Real)").count(), 1, "{s}");
        assert_eq!(s.matches("(declare-const y Real)").count(), 1, "{s}");
        assert_eq!(s.matches("(assert ").count(), 3, "{s}");
        assert!(s.ends_with("(check-sat)\n"), "{s}");
        assert!(!s.contains("get-model"));
        let with_models = script_for(&e, true);
        assert!(with_models.contains("(set-option :produce-models true)"));
        assert!(with_models.ends_with("(get-model)\n"));
    }

    #[test]
    fn script_renames_a_name_shared_by_two_sorts() {
        let j_int = ChcExpr::var(ChcVar::new("J", ChcSort::Int));
        let j_bool = ChcExpr::var(ChcVar::new("J", ChcSort::Bool));
        let e = ChcExpr::and(j_bool, ChcExpr::ge(j_int, ChcExpr::Int(1)));
        let s = script_for(&e, false);
        // Two declarations with distinct names, both used in the body.
        assert_eq!(s.matches("(declare-const ").count(), 2, "{s}");
        assert!(
            s.contains("J!") || s.contains("|J!"),
            "sort-unique rename expected: {s}"
        );
        assert!(s.starts_with("(set-logic QF_LIA)"), "{s}");
    }

    #[test]
    fn recorder_writes_scripts_up_to_the_cap_and_every_index_row() {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        let dir = std::env::temp_dir().join(format!(
            "ay-session-dump-test-{}-{nanos}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        let mut dump = SessionDump::open(&dir, 2).expect("open");
        let e = ChcExpr::le(real("x"), ChcExpr::Int(1));
        for i in 0..3u64 {
            dump.record(&DumpRecord {
                thread: 7,
                expr: &e,
                lane_result: if i == 0 { "sat" } else { "unknown" },
                elapsed: Duration::from_micros(10 + i),
                n_conj: 1,
                n_delta: i,
                n_assumptions: 1,
                decisions: 0,
                unknown_reason: if i == 0 { "-" } else { "budget" },
            });
        }
        drop(dump);
        let files: Vec<_> = std::fs::read_dir(&dir)
            .unwrap()
            .filter_map(Result::ok)
            .map(|e| e.file_name().to_string_lossy().into_owned())
            .collect();
        assert!(files.contains(&"q_000000_7.smt2".to_owned()), "{files:?}");
        assert!(files.contains(&"q_000001_7.smt2".to_owned()), "{files:?}");
        assert!(
            !files.contains(&"q_000002_7.smt2".to_owned()),
            "cap: {files:?}"
        );
        let index = std::fs::read_to_string(dir.join("index.tsv")).unwrap();
        let rows: Vec<&str> = index.lines().collect();
        assert_eq!(rows.len(), 4, "{index}");
        assert!(rows[0].starts_with("seq\tthread\tlane_result"));
        assert_eq!(rows[1], "0\t7\tsat\t10\t1\t0\t1\t0\t-");
        assert_eq!(rows[3], "2\t7\tunknown\t12\t1\t2\t1\t0\tbudget");
        let _ = std::fs::remove_dir_all(&dir);
    }
}
