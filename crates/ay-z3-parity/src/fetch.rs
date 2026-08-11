// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `fetch` subcommand — materialize the SMT-LIB test corpus in-tree.
//!
//! Queries the Zenodo API for a record (default `11061097` = SMT-LIB release
//! 2024, non-incremental), lists the per-division `<DIV>.tar.zst` archives with
//! their published md5 + size, downloads each, verifies the md5, extracts the
//! zstd tarball, and writes its `.smt2` files flat into `<dest>/<DIV>/`
//! (archive-relative `/` → `__`).
//!
//! # Coverage is complete by default
//!
//! **Every division, every file.** There is no default size cap and no default
//! sampling. This matters more than it sounds: this tool previously defaulted to
//! a 60 MB archive cap, which silently dropped the ten largest divisions —
//! `QF_BV` (1.7 GB), `QF_LIA` (689 MB), `QF_IDL`, `QF_LRA`, `QF_NIA`, `QF_NRA`,
//! `QF_ABV`, `BV`, `AUFBV`, `QF_UFBV` — i.e. exactly the logics z3 is most used
//! for. Every AY-vs-z3 completeness and speed number measured against such a
//! corpus silently excluded them, and nothing in the output said so.
//!
//! Narrowing is therefore always opt-in (`--sample`, `--max-mb`, `--divisions`)
//! and always **loudly reported**: a `coverage:` line up front, and a
//! `!! INCOMPLETE COVERAGE` block naming every excluded division at the end. A
//! run whose output carries no such block fetched the whole record.
//!
//! Use `--list` to inspect what a given option set would include or exclude
//! without touching the network beyond the record metadata.
//!
//! Determinism (only relevant under `--sample`): list every `*.smt2` path in
//! the archive, sort byte-wise (`LC_ALL=C`), then take `n` files at indices
//! `floor(i*total/n)` for `i` in `0..n`, de-duplicated. The same archive
//! therefore yields the same sample and byte-identical output files. This is the
//! rule the retired `fetch.sh` / `fetch-all.sh` shell scripts used, so
//! `--divisions QF_AX,QF_S,QF_SLIA,QF_UF,QF_UFLIA --sample 300` reproduces the
//! historical 1,500-file `benchmarks/smtlib-sample` tree byte-for-byte.
//!
//! Robustness: a failed download, metadata mismatch, unsafe archive, extract
//! failure, or empty division skips ONLY that division with a warning — the run
//! continues and exits non-zero after attempting the remaining divisions.
//! Destination replacement is staged, collision-checked, and stale-file-free.
//! Network and extraction are done by shelling out to `curl`, `md5`/`md5sum`,
//! and `tar --use-compress-program=unzstd` (no new dependencies); the API JSON
//! is parsed with the crate's existing `serde_json`.

use std::collections::BTreeSet;
use std::io::Read;
use std::path::{Component, Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{SystemTime, UNIX_EPOCH};

const DEFAULT_RECORD: &str = "11061097";
/// Files sampled per division when `--sample N` is given. There is no default
/// sample: omitting the flag takes every file in the division.
const DEFAULT_SAMPLE: usize = 500;
// Bound decompressed regular-file bytes so a caller-selected `--record` cannot
// expand without limit. All three numbers are MEASURED against SMT-LIB 2024
// non-incremental (Zenodo 11061097), all 84 divisions extracted 2026-07-24:
//
//   * worst expansion ratio: UFBV at >=741x (1.7 MB compressed -> >1.26 GB).
//     zstd on highly repetitive SMT-LIB text routinely exceeds 100x; 12 of 84
//     divisions exceed 45x.
//   * largest single division: QF_BV at 37.3 GB extracted.
//
// The previous 256x / 1 GB pair was a guess, and it rejected UFBV - a legitimate
// division - by 8.7 KB, silently costing one of 84 divisions on every fetch. A
// ratio alone is also the wrong shape: 4096x on a 1.7 GB archive would authorize
// 7 TB, so the ratio is paired with an absolute ceiling.
/// Per-byte-of-archive expansion allowance (~5.5x headroom over the worst
/// measured division).
const MAX_ARCHIVE_EXPANSION_RATIO: u64 = 4096;
/// Floor, so a SMALL archive with a large legitimate ratio still fits: UFBV
/// needs >1.26 GB from 1.7 MB, which `size * ratio` alone would not grant.
const MIN_ARCHIVE_EXPANSION_BUDGET: u64 = 8_000_000_000;
/// Absolute ceiling regardless of archive size (~3.4x the largest measured
/// division), so the ratio cannot authorize a disk-filling expansion.
const MAX_ARCHIVE_EXPANSION_BYTES: u64 = 128_000_000_000;

/// One `<DIV>.tar.zst` archive as advertised by the Zenodo record.
#[derive(Debug)]
struct DivEntry {
    div: String,
    size: u64,
    /// Required published md5 with the `md5:` algorithm prefix removed.
    md5: String,
}

#[derive(Debug)]
struct FetchArgs {
    dest: Option<PathBuf>,
    sample: usize,
    all: bool,
    /// `None` means NO size cap, which is the default. `Some(m)` is an explicit
    /// caller-selected cap and is reported as incomplete coverage.
    max_mb: Option<u64>,
    divisions: Option<Vec<String>>,
    record: String,
    list: bool,
}

fn usage() -> &'static str {
    "\
ay-z3-parity fetch <dest-dir> [--sample N | --all] [--max-mb M]
                   [--divisions d1,d2,...] [--record ID] [--list]

  Materialize the SMT-LIB corpus from Zenodo into <dest-dir>/<DIVISION>/,
  verifying each archive against its published md5.

  DEFAULT IS COMPLETE: every division, every file, no size cap. SMT-LIB 2024
  non-incremental is 84 divisions / ~4.8 GB compressed. Narrowing is opt-in and
  is always reported as INCOMPLETE COVERAGE, because a corpus that silently
  omits divisions produces AY-vs-z3 numbers that silently mean nothing.

  Selection (all optional; each one narrows coverage):
    --divisions d1,d2,...  only these divisions (default: all in the record)
    --sample N             evenly-spaced N files per division (default: all).
                           Deterministic: byte-wise sort, indices
                           floor(i*total/N), de-duplicated — the same archive
                           always yields the same sample.
    --all                  explicitly take every file (the default; accepted so
                           existing invocations keep working)
    --max-mb M             skip archives over M MB. NOT set by default. At M=60
                           this drops QF_BV, QF_LIA, QF_IDL, QF_LRA, QF_NIA,
                           QF_NRA, QF_ABV, BV, AUFBV and QF_UFBV — the logics z3
                           is most used for.

  Other:
    --record ID            Zenodo record id (default 11061097 = SMT-LIB 2024
                           non-incremental)
    --list                 print the divisions, sizes, and exactly what the
                           current options would include or exclude, then exit
                           without downloading anything

  Examples:
    # the whole corpus, which is what a parity claim needs
    ay-z3-parity fetch benchmarks/smtlib-all

    # see what you would get, download nothing
    ay-z3-parity fetch --list

    # a fast smoke corpus, knowingly incomplete
    ay-z3-parity fetch /tmp/smoke --divisions QF_UF,QF_AX --sample 50

  Then: ay-z3-parity scoreboard <dest-dir> --ay <libay_ffi> --jobs 4
"
}

/// Entry point for `ay-z3-parity fetch ...`. Parses its own flags (they diverge
/// from the shared parser) and returns a process exit code.
pub(crate) fn run(rest: &[String]) -> i32 {
    if rest.iter().any(|a| a == "-h" || a == "--help") {
        print!("{}", usage());
        return 0;
    }
    let args = match parse_args(rest) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("error: {e}\n\n{}", usage());
            return 2;
        }
    };

    let api = format!("https://zenodo.org/api/records/{}", args.record);
    println!("== querying Zenodo record {} ...", args.record);
    let body = match curl_capture(&api, "120") {
        Ok(b) => b,
        Err(e) => {
            eprintln!("error: {e}");
            return 1;
        }
    };
    let mut entries = match parse_records(&body) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("error: {e}");
            return 1;
        }
    };
    entries.sort_by(|a, b| a.div.cmp(&b.div));
    let selected = match selected_entries(&args, &entries) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("error: {e}");
            return 2;
        }
    };

    if args.list {
        print_list(&args, &selected, entries.len());
        return 0;
    }

    let dest = match &args.dest {
        Some(d) => d.clone(),
        None => {
            eprintln!(
                "error: fetch needs a <dest-dir> (or use --list)\n\n{}",
                usage()
            );
            return 2;
        }
    };
    if let Err(e) = std::fs::create_dir_all(&dest) {
        eprintln!("error: mkdir {}: {e}", dest.display());
        return 1;
    }
    let swept = sweep_stale_fetch_dirs(&dest);
    if swept > 0 {
        println!(
            "== swept {swept} stale .fetch-staging/.fetch-backup dir(s) from {}",
            dest.display()
        );
    }

    let per = if args.all {
        "all files".to_string()
    } else {
        format!("{} files", args.sample)
    };
    let cap = match args.max_mb {
        None => "no size cap".to_string(),
        Some(m) => format!("max {m}MB"),
    };
    println!(
        "== {} divisions ({}/division, {}) -> {}",
        selected.len(),
        per,
        cap,
        dest.display()
    );
    let notes = narrowing_notes(&args, selected.len(), entries.len());
    if notes.is_empty() {
        println!("   coverage: COMPLETE — every division and every file in the record");
    } else {
        println!("   coverage: NARROWED by caller options (see the summary at the end)");
    }

    let mut done = 0usize;
    let mut excluded_by_cap: Vec<String> = Vec::new();
    let mut failed = 0usize;
    for e in selected {
        let size_mb = e.size / 1_000_000;
        if archive_exceeds_cap(e.size, args.max_mb) {
            // Unwrap-free: archive_exceeds_cap is only true when a cap is set.
            let m = args.max_mb.unwrap_or_default();
            println!(
                "-- {}: {}MB > {}MB cap — SKIPPED (raise --max-mb)",
                e.div, size_mb, m
            );
            excluded_by_cap.push(format!("{} ({}MB)", e.div, size_mb));
            continue;
        }
        match fetch_one(&api, e, &dest, args.sample, args.all) {
            Ok(_) => done += 1,
            Err(msg) => {
                failed += 1;
                println!("   {msg} — skipping {}", e.div);
            }
        }
    }

    println!(
        "== done: {done} divisions fetched into {} ({} skipped by --max-mb, {failed} failed)",
        dest.display(),
        excluded_by_cap.len()
    );
    // The original sin this block exists to prevent: a 60 MB default cap dropped
    // the ten largest divisions and NOTHING in the output said so, so every
    // downstream parity number silently excluded them. Never let a narrowed
    // corpus look complete.
    if notes.is_empty() && failed == 0 {
        println!("== COVERAGE COMPLETE: the whole record is materialized.");
    } else {
        println!("\n!! INCOMPLETE COVERAGE — this corpus does NOT represent the full record.");
        for n in &notes {
            println!("!!   {n}");
        }
        if !excluded_by_cap.is_empty() {
            println!("!!   divisions excluded by --max-mb:");
            for d in &excluded_by_cap {
                println!("!!     - {d}");
            }
        }
        if failed > 0 {
            println!("!!   {failed} division(s) failed to fetch (see the log above)");
        }
        println!(
            "!! Any AY-vs-z3 completeness or speed number measured on this tree must state \
             these exclusions alongside it."
        );
    }
    println!(
        "   run: ay-z3-parity scoreboard {} --ay <libay_ffi> --jobs 4",
        dest.display()
    );
    if failed == 0 {
        0
    } else {
        1
    }
}

fn parse_args(rest: &[String]) -> Result<FetchArgs, String> {
    let mut dest = None;
    let mut sample = DEFAULT_SAMPLE;
    let mut sample_explicit = false;
    // Complete by default: every file, no size cap. Both are narrowed only by an
    // explicit flag, and any narrowing is reported as incomplete coverage.
    let mut all = true;
    let mut all_explicit = false;
    let mut max_mb = None;
    let mut divisions = None;
    let mut record = DEFAULT_RECORD.to_string();
    let mut list = false;

    let mut it = rest.iter();
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--sample" => {
                sample_explicit = true;
                all = false;
                sample = it
                    .next()
                    .ok_or("--sample needs a number")?
                    .parse()
                    .map_err(|_| "--sample must be a positive integer")?;
                if sample == 0 {
                    return Err("--sample must be at least 1".to_string());
                }
            }
            "--all" => {
                all = true;
                all_explicit = true;
            }
            "--max-mb" => {
                max_mb = Some(
                    it.next()
                        .ok_or("--max-mb needs a number")?
                        .parse()
                        .map_err(|_| "--max-mb must be an integer number of MB")?,
                );
            }
            "--divisions" => {
                let listv = it
                    .next()
                    .ok_or("--divisions needs a comma-separated list")?;
                let parsed: Vec<String> = listv
                    .split(',')
                    .map(str::trim)
                    .filter(|s| !s.is_empty())
                    .map(str::to_string)
                    .collect();
                if parsed.is_empty() {
                    return Err("--divisions needs at least one division".to_string());
                }
                if let Some(invalid) = parsed.iter().find(|d| !valid_division_name(d)) {
                    return Err(format!("invalid division name `{invalid}`"));
                }
                divisions = Some(parsed);
            }
            "--record" => record = it.next().ok_or("--record needs an id")?.clone(),
            "--list" => list = true,
            other if other.starts_with("--") => return Err(format!("unknown flag: {other}")),
            other => {
                if dest.is_some() {
                    return Err(format!(
                        "unexpected extra argument: {other} (fetch takes one <dest-dir>)"
                    ));
                }
                dest = Some(PathBuf::from(other));
            }
        }
    }
    if all_explicit && sample_explicit {
        return Err("--sample and --all are mutually exclusive".to_string());
    }
    if record.is_empty() || !record.bytes().all(|b| b.is_ascii_digit()) {
        return Err("--record must be a numeric Zenodo record id".to_string());
    }
    Ok(FetchArgs {
        dest,
        sample,
        all,
        max_mb,
        divisions,
        record,
        list,
    })
}

fn selected_entries<'a>(
    args: &FetchArgs,
    entries: &'a [DivEntry],
) -> Result<Vec<&'a DivEntry>, String> {
    let Some(allow) = &args.divisions else {
        return Ok(entries.iter().collect());
    };
    let available: BTreeSet<&str> = entries.iter().map(|e| e.div.as_str()).collect();
    let missing: Vec<&str> = allow
        .iter()
        .map(String::as_str)
        .filter(|d| !available.contains(d))
        .collect();
    if !missing.is_empty() {
        return Err(format!(
            "requested division(s) absent from record {}: {}",
            args.record,
            missing.join(", ")
        ));
    }
    Ok(entries
        .iter()
        .filter(|e| allow.iter().any(|d| d == &e.div))
        .collect())
}

/// Decompression-bomb budget for one archive of `archive_bytes`: a generous
/// per-byte ratio, floored so tiny-but-legitimately-expansive divisions fit, and
/// capped absolutely so the ratio cannot authorize filling the disk.
fn expansion_budget(archive_bytes: u64) -> u64 {
    archive_bytes
        .saturating_mul(MAX_ARCHIVE_EXPANSION_RATIO)
        .clamp(MIN_ARCHIVE_EXPANSION_BUDGET, MAX_ARCHIVE_EXPANSION_BYTES)
}

/// No cap (`None`, the default) never excludes anything. A caller-selected cap
/// excludes strictly-larger archives.
fn archive_exceeds_cap(size: u64, max_mb: Option<u64>) -> bool {
    match max_mb {
        None => false,
        Some(m) => size > m.saturating_mul(1_000_000),
    }
}

/// Human-readable description of every active narrowing option, or `None` when
/// the run covers the whole record. Drives both the up-front `coverage:` line
/// and the closing `!! INCOMPLETE COVERAGE` block.
fn narrowing_notes(args: &FetchArgs, selected: usize, in_record: usize) -> Vec<String> {
    let mut notes = Vec::new();
    if selected < in_record {
        notes.push(format!(
            "--divisions restricted this run to {selected} of {in_record} divisions in the record"
        ));
    }
    if !args.all {
        notes.push(format!(
            "--sample {} kept only an evenly-spaced subset of each division's files",
            args.sample
        ));
    }
    if let Some(m) = args.max_mb {
        notes.push(format!("--max-mb {m} skipped every archive over {m} MB"));
    }
    notes
}

/// `--list`: the dry-run control surface. Shows every selected division and
/// marks the ones the current options would exclude, so a caller can confirm
/// coverage BEFORE spending the download.
fn print_list(args: &FetchArgs, entries: &[&DivEntry], in_record: usize) {
    println!(
        "== {} of {} divisions in Zenodo record {}:",
        entries.len(),
        in_record,
        args.record
    );
    let mut included = 0usize;
    let mut included_bytes = 0u64;
    let mut excluded_bytes = 0u64;
    for e in entries {
        let mb = e.size as f64 / 1_000_000.0;
        let over = if archive_exceeds_cap(e.size, args.max_mb) {
            excluded_bytes += e.size;
            "  EXCLUDED (over --max-mb)"
        } else {
            included += 1;
            included_bytes += e.size;
            ""
        };
        println!(
            "  {:<22} {:>10.2} MB  {:>14} B  {}{}",
            e.div, mb, e.size, e.md5, over
        );
    }
    println!(
        "== would fetch {} divisions, {:.2} GB compressed",
        included,
        included_bytes as f64 / 1e9
    );
    let notes = narrowing_notes(args, entries.len(), in_record);
    if notes.is_empty() {
        println!("== coverage: COMPLETE — every division and every file in the record");
    } else {
        println!("!! coverage: INCOMPLETE");
        for n in &notes {
            println!("!!   {n}");
        }
        if excluded_bytes > 0 {
            println!(
                "!!   {:.2} GB of archives would be skipped by the size cap",
                excluded_bytes as f64 / 1e9
            );
        }
    }
}

/// Download, verify, extract, and sample one division. Prints per-division
/// progress; the temp working dir is always removed. On any failure returns a
/// short reason string; the caller reports it and moves on to the next.
fn fetch_one(
    api: &str,
    e: &DivEntry,
    dest: &Path,
    sample: usize,
    all: bool,
) -> Result<usize, String> {
    let size_mb = e.size / 1_000_000;
    println!("== {} ({}MB): downloading ...", e.div, size_mb);
    let tmp = make_tmpdir(&e.div)?;
    let result = fetch_one_inner(api, e, dest, sample, all, &tmp);
    let _ = std::fs::remove_dir_all(&tmp);
    result
}

fn fetch_one_inner(
    api: &str,
    e: &DivEntry,
    dest: &Path,
    sample: usize,
    all: bool,
    tmp: &Path,
) -> Result<usize, String> {
    let archive = tmp.join(format!("{}.tar.zst", e.div));
    let url = format!("{api}/files/{}.tar.zst/content", e.div);
    if curl_to_file(&url, &archive, "1800").is_err() {
        return Err("download failed".to_string());
    }
    let got_size = std::fs::metadata(&archive)
        .map_err(|err| format!("stat downloaded archive: {err}"))?
        .len();
    if got_size != e.size {
        return Err(format!(
            "size mismatch (got {got_size} bytes, want {} bytes)",
            e.size
        ));
    }

    let got = md5_of(&archive)?;
    if !got.eq_ignore_ascii_case(&e.md5) {
        return Err(format!("md5 mismatch (got {got} want {})", e.md5));
    }
    println!("   md5 ok ({got})");

    let xd = tmp.join("x");
    std::fs::create_dir_all(&xd).map_err(|_| "extract failed".to_string())?;
    extract(&archive, &xd, expansion_budget(e.size))?;

    let mut keys = collect_smt2(&xd).map_err(|_| "extract failed".to_string())?;
    sort_keys(&mut keys);
    let total = keys.len();
    if total == 0 {
        return Err("no .smt2".to_string());
    }

    let n = if all { total } else { sample.min(total) };
    let idxs = sample_indices(total, n);
    install_sample(&xd, dest, &e.div, &keys, &idxs)?;
    println!("   sampled {}/{}", idxs.len(), total);
    Ok(idxs.len())
}

/// Install one complete division sample without mixing it with a prior run.
///
/// Files are copied into a sibling staging directory first. Flattened-name
/// collisions are rejected before any destination mutation; the completed
/// staging tree then replaces the old division directory with rollback on a
/// failed rename. A successful refresh is therefore an exact snapshot rather
/// than "new files plus stale leftovers".
fn install_sample(
    extracted: &Path,
    dest: &Path,
    div: &str,
    keys: &[String],
    idxs: &[usize],
) -> Result<(), String> {
    let mut outputs = BTreeSet::new();
    for &i in idxs {
        let key = keys
            .get(i)
            .ok_or_else(|| format!("sample index {i} is out of bounds"))?;
        let output = flat_name(key);
        if !outputs.insert(output.clone()) {
            return Err(format!(
                "flattened sample name collision at `{output}`; refusing overwrite"
            ));
        }
    }

    let nonce = unique_nonce();
    let staging = dest.join(format!(
        ".{div}.fetch-staging-{}-{nonce}",
        std::process::id()
    ));
    let backup = dest.join(format!(
        ".{div}.fetch-backup-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir(&staging).map_err(|err| format!("mkdir {}: {err}", staging.display()))?;

    let copy_result = idxs.iter().try_for_each(|&i| {
        let key = &keys[i];
        std::fs::copy(extracted.join(key), staging.join(flat_name(key)))
            .map(|_| ())
            .map_err(|err| format!("copy {key}: {err}"))
    });
    if let Err(err) = copy_result {
        let _ = std::fs::remove_dir_all(&staging);
        return Err(err);
    }

    let dest_div = dest.join(div);
    let had_old = std::fs::symlink_metadata(&dest_div).is_ok();
    if had_old {
        if let Err(err) = std::fs::rename(&dest_div, &backup) {
            let _ = std::fs::remove_dir_all(&staging);
            return Err(format!(
                "move old sample {} aside: {err}",
                dest_div.display()
            ));
        }
    }
    if let Err(err) = std::fs::rename(&staging, &dest_div) {
        if had_old {
            let _ = std::fs::rename(&backup, &dest_div);
        }
        let _ = std::fs::remove_dir_all(&staging);
        return Err(format!("install sample {}: {err}", dest_div.display()));
    }
    if had_old {
        if let Err(err) = remove_path_retrying(&backup) {
            eprintln!(
                "warning: installed {}, but could not remove backup {} after retries: {err}. \
                 It will be swept at the start of the next fetch into this root; until then, \
                 corpus scanners that do not skip dot-directories may double-count its files.",
                dest_div.display(),
                backup.display()
            );
        }
    }
    Ok(())
}

fn remove_path(path: &Path) -> std::io::Result<()> {
    let metadata = std::fs::symlink_metadata(path)?;
    if metadata.file_type().is_dir() {
        std::fs::remove_dir_all(path)
    } else {
        std::fs::remove_file(path)
    }
}

/// `remove_dir_all` intermittently fails with `ENOTEMPTY` on APFS even when this
/// process is the only writer (readdir/unlink interleaving), so retry briefly.
///
/// This is not cosmetic. A leaked `.{div}.fetch-backup-*` directory sits inside
/// the corpus root, and corpus scanners walk `<root>/*` — so a leftover is
/// picked up as if it were a real division and silently duplicates its files
/// into a measurement. That happened: 4 of 84 divisions leaked on the
/// 2026-07-24 full fetch and the scoreboard began scoring
/// `.AUFDTLIRA.fetch-backup-...` as a division.
fn remove_path_retrying(path: &Path) -> std::io::Result<()> {
    let mut last: Option<std::io::Error> = None;
    for attempt in 0..5u32 {
        match remove_path(path) {
            Ok(()) => return Ok(()),
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => return Ok(()),
            Err(err) => {
                last = Some(err);
                std::thread::sleep(std::time::Duration::from_millis(
                    50 * u64::from(attempt + 1),
                ));
            }
        }
    }
    Err(last.unwrap_or_else(|| std::io::Error::other("remove failed")))
}

/// Sweep `.{div}.fetch-staging-*` / `.{div}.fetch-backup-*` left behind by an
/// earlier interrupted or partially-failed run, so a leak is self-healing rather
/// than permanently poisoning every later scan of this corpus root.
fn sweep_stale_fetch_dirs(dest: &Path) -> usize {
    let Ok(entries) = std::fs::read_dir(dest) else {
        return 0;
    };
    let mut swept = 0;
    for entry in entries.flatten() {
        let name = entry.file_name();
        let Some(name) = name.to_str() else { continue };
        if !name.starts_with('.') {
            continue;
        }
        if !(name.contains(".fetch-staging-") || name.contains(".fetch-backup-")) {
            continue;
        }
        if remove_path_retrying(&entry.path()).is_ok() {
            swept += 1;
        }
    }
    swept
}

// ---------------------------------------------------------------------------
// Deterministic sampling primitives (pure — unit tested)
// ---------------------------------------------------------------------------

/// The evenly-spaced sample index set: `sorted({ i*total/n : i in 0..n })`,
/// with `n` capped at `total`. Mirrors the shell/python rule exactly.
fn sample_indices(total: usize, n: usize) -> Vec<usize> {
    let n = n.min(total);
    if n == 0 {
        return Vec::new();
    }
    let set: BTreeSet<usize> = (0..n)
        .map(|i| {
            // The mathematical result is < `total` and therefore fits usize;
            // widen the intermediate product so a huge archive inventory
            // cannot wrap before division.
            ((i as u128) * (total as u128) / (n as u128)) as usize
        })
        .collect();
    set.into_iter().collect()
}

/// Flatten an archive-relative path to its on-disk sample name (`/` → `__`).
fn flat_name(key: &str) -> String {
    key.replace('/', "__")
}

/// Byte-wise (`LC_ALL=C`) sort of the archive-relative `.smt2` paths.
fn sort_keys(keys: &mut [String]) {
    keys.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
}

/// Recursively collect every `*.smt2` path under `root`, as `/`-joined
/// archive-relative keys (the `find . -name '*.smt2' | sed 's|^\./||'` of the
/// script). Directories and non-`.smt2` files are ignored; symlinks are not
/// followed.
fn collect_smt2(root: &Path) -> Result<Vec<String>, String> {
    let mut out = Vec::new();
    walk(root, root, &mut out).map_err(|e| format!("walk {}: {e}", root.display()))?;
    Ok(out)
}

fn walk(base: &Path, dir: &Path, out: &mut Vec<String>) -> std::io::Result<()> {
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let ft = entry.file_type()?;
        let path = entry.path();
        if ft.is_dir() {
            walk(base, &path, out)?;
        } else if ft.is_file() && path.extension().and_then(|x| x.to_str()) == Some("smt2") {
            if let Ok(rel) = path.strip_prefix(base) {
                let key = rel
                    .components()
                    .map(|c| {
                        c.as_os_str().to_str().ok_or_else(|| {
                            std::io::Error::new(
                                std::io::ErrorKind::InvalidData,
                                "non-UTF-8 extracted path",
                            )
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?
                    .join("/");
                out.push(key);
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// External tools (shelled out, mirroring the fetch scripts)
// ---------------------------------------------------------------------------

/// `curl -fSL --retry 3 --max-time <max> <url>` capturing stdout (API query).
fn curl_capture(url: &str, max_time: &str) -> Result<Vec<u8>, String> {
    let out = Command::new("curl")
        .args(["-fSL", "--retry", "3", "--max-time", max_time])
        .arg(url)
        .output()
        .map_err(|e| format!("failed to run curl (is it installed?): {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "curl {url} failed ({}): {}",
            out.status,
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    Ok(out.stdout)
}

/// `curl -fSL --retry 3 --max-time <max> <url> -o <out>` (archive download).
fn curl_to_file(url: &str, out_path: &Path, max_time: &str) -> Result<(), String> {
    let status = Command::new("curl")
        .args(["-fSL", "--retry", "3", "--max-time", max_time])
        .arg(url)
        .arg("-o")
        .arg(out_path)
        .status()
        .map_err(|e| format!("failed to run curl: {e}"))?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("curl {url} failed ({status})"))
    }
}

/// md5 of a file: prefer `md5 -q` (macOS/BSD), fall back to `md5sum` (Linux).
fn md5_of(path: &Path) -> Result<String, String> {
    match Command::new("md5").arg("-q").arg(path).output() {
        Ok(out) if out.status.success() => {
            Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
        }
        Ok(out) => Err(format!(
            "md5 -q failed: {}",
            String::from_utf8_lossy(&out.stderr).trim()
        )),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            let out = Command::new("md5sum")
                .arg(path)
                .output()
                .map_err(|e| format!("failed to run md5sum: {e}"))?;
            if !out.status.success() {
                return Err(format!(
                    "md5sum failed: {}",
                    String::from_utf8_lossy(&out.stderr).trim()
                ));
            }
            String::from_utf8_lossy(&out.stdout)
                .split_whitespace()
                .next()
                .map(str::to_string)
                .ok_or_else(|| "md5sum produced no output".to_string())
        }
        Err(e) => Err(format!("failed to run md5: {e}")),
    }
}

/// Validate member paths, extract, then reject links and special files.
///
/// The record id is caller-selected, so a record is not implicitly trusted to
/// contain the official corpus. Both the pre-extraction path check and the
/// post-extraction file-type walk are required: the former blocks `..`/absolute
/// writes, while the latter prevents a sampled path from traversing a link.
fn extract(archive: &Path, into: &Path, max_expanded_bytes: u64) -> Result<(), String> {
    validate_archive_members(archive)?;
    validate_expanded_size(archive, max_expanded_bytes)?;
    let status = Command::new("tar")
        .arg("--use-compress-program=unzstd")
        .arg("-xf")
        .arg(archive)
        .arg("-C")
        .arg(into)
        .stderr(Stdio::null())
        .status()
        .map_err(|err| format!("failed to run tar: {err}"))?;
    if !status.success() {
        return Err(format!("extract failed ({status})"));
    }
    validate_extracted_tree(into)?;
    Ok(())
}

/// Stream every regular member to stdout without writing it, bounding the
/// total expanded payload before the real extraction mutates disk.
fn validate_expanded_size(archive: &Path, max_expanded_bytes: u64) -> Result<(), String> {
    let mut child = Command::new("tar")
        .arg("--use-compress-program=unzstd")
        .arg("-xOf")
        .arg(archive)
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|err| format!("failed to preflight archive expansion: {err}"))?;
    let mut stdout = child
        .stdout
        .take()
        .ok_or_else(|| "archive expansion preflight has no stdout".to_string())?;
    let mut total = 0u64;
    let mut buffer = vec![0u8; 64 * 1024].into_boxed_slice();
    loop {
        let read = match stdout.read(&mut buffer) {
            Ok(read) => read,
            Err(err) => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(format!("archive expansion preflight read failed: {err}"));
            }
        };
        if read == 0 {
            break;
        }
        total = total.saturating_add(read as u64);
        if total > max_expanded_bytes {
            let _ = child.kill();
            let _ = child.wait();
            return Err(format!(
                "archive expands past safety bound ({total} > {max_expanded_bytes} bytes)"
            ));
        }
    }
    let status = child
        .wait()
        .map_err(|err| format!("archive expansion preflight wait failed: {err}"))?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("archive expansion preflight failed ({status})"))
    }
}

fn validate_archive_members(archive: &Path) -> Result<(), String> {
    let names = Command::new("tar")
        .arg("--use-compress-program=unzstd")
        .arg("-tf")
        .arg(archive)
        .output()
        .map_err(|err| format!("failed to list archive: {err}"))?;
    if !names.status.success() {
        return Err(format!(
            "archive listing failed ({}): {}",
            names.status,
            String::from_utf8_lossy(&names.stderr).trim()
        ));
    }
    let listing = String::from_utf8(names.stdout)
        .map_err(|_| "archive contains a non-UTF-8 member name".to_string())?;
    for member in listing.lines() {
        if !archive_member_is_safe(member) {
            return Err(format!("unsafe archive member path `{member}`"));
        }
    }

    // A safe member pathname is insufficient when an earlier symlink/hardlink
    // can redirect a later extraction. Reject every archive object except a
    // regular file or directory before extracting anything. Both bsdtar and
    // GNU tar begin a verbose-list row with the Unix type/mode character.
    let verbose = Command::new("tar")
        .arg("--use-compress-program=unzstd")
        .arg("-tvf")
        .arg(archive)
        .output()
        .map_err(|err| format!("failed to inspect archive entry types: {err}"))?;
    if !verbose.status.success() {
        return Err(format!(
            "archive type listing failed ({}): {}",
            verbose.status,
            String::from_utf8_lossy(&verbose.stderr).trim()
        ));
    }
    let type_listing = String::from_utf8(verbose.stdout)
        .map_err(|_| "archive type listing is not UTF-8".to_string())?;
    for row in type_listing.lines() {
        if !archive_listing_type_is_safe(row) {
            return Err(format!("archive contains a link or special entry: `{row}`"));
        }
    }
    Ok(())
}

fn archive_member_is_safe(member: &str) -> bool {
    !member.is_empty()
        && Path::new(member)
            .components()
            .all(|component| matches!(component, Component::Normal(_) | Component::CurDir))
}

fn archive_listing_type_is_safe(row: &str) -> bool {
    matches!(row.trim_start().as_bytes().first(), Some(b'-' | b'd'))
}

fn validate_extracted_tree(root: &Path) -> Result<(), String> {
    fn visit(dir: &Path) -> Result<(), String> {
        for entry in std::fs::read_dir(dir)
            .map_err(|err| format!("inspect extracted tree {}: {err}", dir.display()))?
        {
            let entry = entry.map_err(|err| format!("inspect extracted entry: {err}"))?;
            let path = entry.path();
            let file_type = entry
                .file_type()
                .map_err(|err| format!("inspect {}: {err}", path.display()))?;
            if file_type.is_symlink() {
                return Err(format!(
                    "archive contains symlink `{}`; refusing extraction",
                    path.display()
                ));
            }
            if file_type.is_dir() {
                visit(&path)?;
            } else if !file_type.is_file() {
                return Err(format!(
                    "archive contains unsupported entry `{}`",
                    path.display()
                ));
            }
        }
        Ok(())
    }
    visit(root)
}

/// Create a fresh per-division temp working directory under the system tempdir.
fn make_tmpdir(tag: &str) -> Result<PathBuf, String> {
    let dir = std::env::temp_dir().join(format!(
        "ay-z3-parity-fetch-{}-{}-{}",
        std::process::id(),
        tag,
        unique_nonce()
    ));
    std::fs::create_dir(&dir).map_err(|e| format!("mkdir {}: {e}", dir.display()))?;
    Ok(dir)
}

fn unique_nonce() -> u128 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0)
}

fn valid_division_name(div: &str) -> bool {
    !div.is_empty()
        && div
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'-' | b'+'))
}

/// Parse the Zenodo record JSON into the list of `<DIV>.tar.zst` archives.
fn parse_records(json: &[u8]) -> Result<Vec<DivEntry>, String> {
    let v: serde_json::Value =
        serde_json::from_slice(json).map_err(|e| format!("parsing Zenodo API JSON: {e}"))?;
    let files = v
        .get("files")
        .and_then(serde_json::Value::as_array)
        .ok_or("Zenodo API JSON has no `files` array")?;
    let mut out = Vec::new();
    let mut divisions = BTreeSet::new();
    for f in files {
        let Some(key) = f.get("key").and_then(serde_json::Value::as_str) else {
            continue;
        };
        let Some(div) = key.strip_suffix(".tar.zst") else {
            continue;
        };
        if !valid_division_name(div) {
            return Err(format!("unsafe division archive key `{key}`"));
        }
        let size = f
            .get("size")
            .and_then(serde_json::Value::as_u64)
            .ok_or_else(|| format!("archive `{key}` has no byte size"))?;
        if size == 0 {
            return Err(format!("archive `{key}` has invalid zero byte size"));
        }
        let checksum = f
            .get("checksum")
            .and_then(serde_json::Value::as_str)
            .ok_or_else(|| format!("archive `{key}` has no checksum"))?;
        let md5 = checksum
            .strip_prefix("md5:")
            .ok_or_else(|| format!("archive `{key}` checksum is not md5"))?
            .to_ascii_lowercase();
        if md5.len() != 32 || !md5.bytes().all(|b| b.is_ascii_hexdigit()) {
            return Err(format!("archive `{key}` has malformed md5 checksum"));
        }
        if !divisions.insert(div.to_string()) {
            return Err(format!("Zenodo record repeats division archive `{key}`"));
        }
        out.push(DivEntry {
            div: div.to_string(),
            size,
            md5,
        });
    }
    if out.is_empty() {
        return Err("Zenodo record contains no division archives".to_string());
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn sample_indices_matches_python_rule() {
        // sorted({ i*total//n for i in range(n) })
        assert_eq!(sample_indices(10, 3), vec![0, 3, 6]);
        assert_eq!(sample_indices(20, 5), vec![0, 4, 8, 12, 16]);
        // n is capped at total
        assert_eq!(sample_indices(4, 10), vec![0, 1, 2, 3]);
        // --all => identity over every index
        assert_eq!(sample_indices(5, 5), vec![0, 1, 2, 3, 4]);
        // colliding indices de-duplicate: {0*3//2, 1*3//2} = {0, 1}
        assert_eq!(sample_indices(3, 2), vec![0, 1]);
        // realistic: QF_AX-shaped (551 files, N=50) yields exactly 50 uniques
        assert_eq!(sample_indices(551, 50).len(), 50);
        // Widened multiplication: the intermediate must not wrap at usize::MAX.
        assert_eq!(sample_indices(usize::MAX, 2), vec![0, usize::MAX / 2]);
    }

    #[test]
    fn flat_name_maps_slash_to_double_underscore() {
        assert_eq!(
            flat_name("non-incremental/QF_AX/cvc/read5.smt2"),
            "non-incremental__QF_AX__cvc__read5.smt2"
        );
        assert_eq!(flat_name("a.smt2"), "a.smt2");
    }

    #[test]
    fn parse_args_rejects_ambiguous_or_unsafe_fetch_selectors() {
        let both = vec![
            "out".to_string(),
            "--all".to_string(),
            "--sample".to_string(),
            "2".to_string(),
        ];
        assert!(parse_args(&both)
            .unwrap_err()
            .contains("mutually exclusive"));

        let traversal = vec![
            "--list".to_string(),
            "--divisions".to_string(),
            "../QF_AX".to_string(),
        ];
        assert!(parse_args(&traversal)
            .unwrap_err()
            .contains("invalid division"));

        let bad_record = vec![
            "--list".to_string(),
            "--record".to_string(),
            "../../x".to_string(),
        ];
        assert!(parse_args(&bad_record).unwrap_err().contains("numeric"));
    }

    /// Regression pin for a real loss: at 256x / 1 GB the budget rejected UFBV
    /// (1,707,837 B compressed, >1.26 GB extracted) by 8.7 KB, dropping 1 of 84
    /// divisions from every fetch. Uses UFBV's real archive size.
    #[test]
    fn expansion_budget_admits_the_worst_measured_real_division() {
        const UFBV_ARCHIVE: u64 = 1_707_837;
        const UFBV_EXTRACTED_LOWER_BOUND: u64 = 1_265_403_520;
        assert!(
            expansion_budget(UFBV_ARCHIVE) > UFBV_EXTRACTED_LOWER_BOUND,
            "UFBV must fit: budget {} <= observed {}",
            expansion_budget(UFBV_ARCHIVE),
            UFBV_EXTRACTED_LOWER_BOUND
        );
        // QF_BV: largest measured division, 37.3 GB extracted from 1.73 GB.
        assert!(expansion_budget(1_734_941_977) > 37_342_277_361);
    }

    /// The ratio must never authorize an unbounded expansion on a big archive.
    #[test]
    fn expansion_budget_is_absolutely_capped() {
        assert_eq!(expansion_budget(u64::MAX), MAX_ARCHIVE_EXPANSION_BYTES);
        assert_eq!(expansion_budget(0), MIN_ARCHIVE_EXPANSION_BUDGET);
        assert!(expansion_budget(u64::MAX / 2) <= MAX_ARCHIVE_EXPANSION_BYTES);
    }

    #[test]
    fn exact_byte_cap_does_not_admit_a_sub_megabyte_archive_at_zero() {
        assert!(archive_exceeds_cap(1, Some(0)));
        assert!(!archive_exceeds_cap(1_000_000, Some(1)));
        assert!(archive_exceeds_cap(1_000_001, Some(1)));
    }

    /// A leaked `.{div}.fetch-backup-*` sits INSIDE the corpus root, so any
    /// scanner that walks `<root>/*` double-counts that division under a bogus
    /// name. 4 of 84 divisions leaked on the 2026-07-24 full fetch (APFS
    /// `remove_dir_all` -> ENOTEMPTY) and the scoreboard began scoring them.
    /// The sweep makes it self-healing; real divisions must survive untouched.
    #[test]
    fn sweep_removes_only_stale_fetch_dirs() {
        let root = make_tmpdir("sweep-test").expect("tmpdir");
        let real = root.join("QF_UF");
        let backup = root.join(".QF_UF.fetch-backup-123-456");
        let staging = root.join(".QF_AX.fetch-staging-123-456");
        let other_hidden = root.join(".git");
        for d in [&real, &backup, &staging, &other_hidden] {
            fs::create_dir_all(d).expect("mkdir");
        }
        // Non-empty, because ENOTEMPTY is the failure being defended against.
        fs::write(backup.join("a.smt2"), b"(check-sat)").expect("write");
        fs::write(real.join("a.smt2"), b"(check-sat)").expect("write");

        assert_eq!(sweep_stale_fetch_dirs(&root), 2);
        assert!(real.is_dir(), "a real division must not be swept");
        assert!(real.join("a.smt2").is_file());
        assert!(
            other_hidden.is_dir(),
            "unrelated dot-dirs must not be swept"
        );
        assert!(!backup.exists());
        assert!(!staging.exists());
        // Idempotent: a clean root sweeps nothing.
        assert_eq!(sweep_stale_fetch_dirs(&root), 0);
        let _ = fs::remove_dir_all(&root);
    }

    /// The default must admit EVERY archive. A 60 MB default cap silently
    /// dropped the ten largest SMT-LIB divisions (QF_BV 1.7 GB, QF_LIA 689 MB,
    /// ...) out of every corpus this tool built, so "no cap unless asked" is a
    /// pinned contract, not a preference.
    #[test]
    fn no_cap_is_the_default_and_admits_the_largest_division() {
        let args = parse_args(&["out".to_string()]).expect("bare dest parses");
        assert_eq!(args.max_mb, None, "a size cap must never be defaulted on");
        assert!(
            !archive_exceeds_cap(1_734_941_977, args.max_mb),
            "QF_BV (1.7GB) must be admitted by default"
        );
        assert!(args.all, "every file per division must be the default");
        assert!(
            narrowing_notes(&args, 84, 84).is_empty(),
            "a default run must report COMPLETE coverage"
        );
    }

    /// Every narrowing option must surface in the coverage report, so a
    /// partial corpus can never read as a complete one.
    #[test]
    fn each_narrowing_option_is_reported_as_incomplete_coverage() {
        let sampled = parse_args(&["out".to_string(), "--sample".to_string(), "50".to_string()])
            .expect("sample parses");
        assert!(!sampled.all);
        let notes = narrowing_notes(&sampled, 84, 84);
        assert_eq!(notes.len(), 1, "{notes:?}");
        assert!(notes[0].contains("--sample 50"), "{notes:?}");

        let capped = parse_args(&["out".to_string(), "--max-mb".to_string(), "60".to_string()])
            .expect("max-mb parses");
        assert_eq!(capped.max_mb, Some(60));
        let notes = narrowing_notes(&capped, 84, 84);
        assert!(notes.iter().any(|n| n.contains("--max-mb 60")), "{notes:?}");

        // A division subset is narrowing even with no other flag set.
        let subset = parse_args(&[
            "out".to_string(),
            "--divisions".to_string(),
            "QF_UF".to_string(),
        ])
        .expect("divisions parses");
        let notes = narrowing_notes(&subset, 1, 84);
        assert!(notes.iter().any(|n| n.contains("1 of 84")), "{notes:?}");
    }

    /// `--all` is the default, but must stay accepted so existing invocations
    /// keep working — and must still conflict with `--sample`.
    #[test]
    fn explicit_all_is_accepted_and_still_conflicts_with_sample() {
        let a = parse_args(&["out".to_string(), "--all".to_string()]).expect("--all parses");
        assert!(a.all);
        assert!(narrowing_notes(&a, 84, 84).is_empty());
        let both = vec![
            "out".to_string(),
            "--all".to_string(),
            "--sample".to_string(),
            "2".to_string(),
        ];
        assert!(parse_args(&both)
            .unwrap_err()
            .contains("mutually exclusive"));
    }

    #[test]
    fn archive_members_fail_closed_on_paths_links_and_special_files() {
        for safe in ["QF_AX/a.smt2", "./QF_AX/a.smt2", "one"] {
            assert!(archive_member_is_safe(safe), "{safe}");
        }
        for unsafe_path in [
            "",
            "/absolute.smt2",
            "../escape.smt2",
            "QF_AX/../../escape.smt2",
        ] {
            assert!(!archive_member_is_safe(unsafe_path), "{unsafe_path}");
        }
        for safe_row in [
            "-rw-r--r-- user/group 10 Jan 1 00:00 QF_AX/a.smt2",
            "drwxr-xr-x user/group 0 Jan 1 00:00 QF_AX/",
        ] {
            assert!(archive_listing_type_is_safe(safe_row), "{safe_row}");
        }
        for unsafe_row in [
            "lrwxr-xr-x user/group 0 Jan 1 00:00 link -> /tmp",
            "hrw-r--r-- user/group 0 Jan 1 00:00 hard link to target",
            "prw-r--r-- user/group 0 Jan 1 00:00 fifo",
            "",
        ] {
            assert!(!archive_listing_type_is_safe(unsafe_row), "{unsafe_row}");
        }
    }

    #[test]
    fn parse_records_filters_non_archives_and_strips_md5_prefix() {
        // A trimmed capture of the real Zenodo record 11061097 shape.
        let json = br#"{"files":[
            {"key":"QF_AX.tar.zst","size":131549,"checksum":"md5:6d323ea02eb4d74e8ac77420bf94e3cb"},
            {"key":"README.md","size":10,"checksum":"md5:deadbeefdeadbeefdeadbeefdeadbeef"},
            {"key":"QF_S.tar.zst","size":2909837,"checksum":"md5:e7a201b1fff6c952f278154d6513a0c0"}
        ]}"#;
        let e = parse_records(json).unwrap();
        assert_eq!(e.len(), 2, "only .tar.zst archives are kept");
        assert_eq!(e[0].div, "QF_AX");
        assert_eq!(e[0].size, 131549);
        assert_eq!(e[0].md5, "6d323ea02eb4d74e8ac77420bf94e3cb");
        assert_eq!(e[1].div, "QF_S");
    }

    #[test]
    fn parse_records_rejects_unsafe_or_unverifiable_archives() {
        let unsafe_key = br#"{"files":[
            {"key":"../escape.tar.zst","size":10,
             "checksum":"md5:6d323ea02eb4d74e8ac77420bf94e3cb"}
        ]}"#;
        assert!(parse_records(unsafe_key).unwrap_err().contains("unsafe"));

        let no_checksum = br#"{"files":[
            {"key":"QF_AX.tar.zst","size":10}
        ]}"#;
        assert!(parse_records(no_checksum)
            .unwrap_err()
            .contains("no checksum"));

        let duplicate = br#"{"files":[
            {"key":"QF_AX.tar.zst","size":10,
             "checksum":"md5:6d323ea02eb4d74e8ac77420bf94e3cb"},
            {"key":"QF_AX.tar.zst","size":11,
             "checksum":"md5:e7a201b1fff6c952f278154d6513a0c0"}
        ]}"#;
        assert!(parse_records(duplicate).unwrap_err().contains("repeats"));
    }

    #[test]
    fn requested_divisions_must_exist_in_the_record() {
        let entries = vec![DivEntry {
            div: "QF_AX".to_string(),
            size: 1,
            md5: "00000000000000000000000000000000".to_string(),
        }];
        let args = FetchArgs {
            dest: None,
            sample: 1,
            all: false,
            max_mb: Some(1),
            divisions: Some(vec!["QF_BV".to_string()]),
            record: "1".to_string(),
            list: true,
        };
        assert!(selected_entries(&args, &entries)
            .unwrap_err()
            .contains("absent"));
    }

    #[test]
    fn install_replaces_stale_sample_and_rejects_flattening_collision() {
        let tmp = make_tmpdir("test-install").unwrap();
        let extracted = tmp.join("extracted");
        let dest = tmp.join("dest");
        fs::create_dir_all(extracted.join("a")).unwrap();
        fs::create_dir_all(&dest).unwrap();
        fs::write(extracted.join("a/fresh.smt2"), "(check-sat)").unwrap();

        let old = dest.join("QF_AX");
        fs::create_dir_all(&old).unwrap();
        fs::write(old.join("stale.smt2"), "stale").unwrap();
        install_sample(
            &extracted,
            &dest,
            "QF_AX",
            &["a/fresh.smt2".to_string()],
            &[0],
        )
        .unwrap();
        assert!(!old.join("stale.smt2").exists());
        assert_eq!(
            fs::read_to_string(old.join("a__fresh.smt2")).unwrap(),
            "(check-sat)"
        );

        fs::write(extracted.join("a/b.smt2"), "one").unwrap();
        fs::write(extracted.join("a__b.smt2"), "two").unwrap();
        let collision = install_sample(
            &extracted,
            &dest,
            "QF_AX",
            &["a/b.smt2".to_string(), "a__b.smt2".to_string()],
            &[0, 1],
        )
        .unwrap_err();
        assert!(collision.contains("collision"));
        assert!(
            old.join("a__fresh.smt2").exists(),
            "collision must leave the prior complete sample untouched"
        );

        let _ = fs::remove_dir_all(&tmp);
    }

    #[test]
    fn sampler_is_deterministic_on_a_local_tree() {
        // Build a fixture archive tree: non-incremental/DIV/f00.smt2 .. f19.smt2
        let tmp = make_tmpdir("test-sampler").unwrap();
        let src = tmp.join("x/non-incremental/DIV");
        fs::create_dir_all(&src).unwrap();
        for k in 0..20 {
            fs::write(src.join(format!("f{k:02}.smt2")), format!("(assert {k})")).unwrap();
        }
        // A non-.smt2 sibling must be ignored (like `find -name '*.smt2'`).
        fs::write(src.join("skip.txt"), "x").unwrap();

        let root = tmp.join("x");
        let mut keys = collect_smt2(&root).unwrap();
        sort_keys(&mut keys);
        assert_eq!(keys.len(), 20, ".txt file excluded");
        assert_eq!(keys[0], "non-incremental/DIV/f00.smt2");
        assert_eq!(keys[19], "non-incremental/DIV/f19.smt2");

        // Re-walking the same tree is byte-for-byte reproducible.
        let mut keys2 = collect_smt2(&root).unwrap();
        sort_keys(&mut keys2);
        assert_eq!(keys, keys2);

        // Sampling 5 of 20 selects the exact even-spaced indices.
        let idxs = sample_indices(keys.len(), 5);
        assert_eq!(idxs, vec![0, 4, 8, 12, 16]);
        let picked: Vec<&String> = idxs.iter().map(|&i| &keys[i]).collect();
        assert_eq!(picked[0], "non-incremental/DIV/f00.smt2");
        assert_eq!(picked[1], "non-incremental/DIV/f04.smt2");

        let _ = fs::remove_dir_all(&tmp);
    }
}
