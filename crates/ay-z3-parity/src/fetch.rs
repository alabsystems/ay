// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `fetch` subcommand — re-download and DETERMINISTICALLY sample the SMT-LIB
//! test corpus, in-tree.
//!
//! This is a faithful Rust port of `benchmarks/smtlib-sample/fetch-all.sh`:
//! it queries the Zenodo API for a record (default `11061097` = SMT-LIB release
//! 2024, non-incremental), lists the per-division `<DIV>.tar.zst` archives with
//! their published md5 + size, downloads each, verifies the md5, extracts the
//! zstd tarball, and writes an evenly-spaced sample of its `.smt2` files flat
//! into `<dest>/<DIV>/` (archive-relative `/` → `__`).
//!
//! Determinism (identical rule to both fetch scripts): list every `*.smt2`
//! path in the archive, sort byte-wise (`LC_ALL=C`), then take `n` files at
//! indices `floor(i*total/n)` for `i` in `0..n`, de-duplicated. The same
//! archive therefore yields the same sample and byte-identical output files.
//!
//! Robustness: a failed download, metadata mismatch, unsafe archive, extract
//! failure, or empty division skips ONLY that division with a warning — the run
//! continues and exits non-zero after attempting the remaining divisions.
//! Destination replacement is staged, collision-checked, and stale-file-free.
//! Network and extraction are done by shelling out to `curl`, `md5`/`md5sum`,
//! and `tar --use-compress-program=unzstd`, exactly as the shell scripts do
//! (no new dependencies); the API JSON is parsed with the crate's existing
//! `serde_json`.

use std::collections::BTreeSet;
use std::io::Read;
use std::path::{Component, Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{SystemTime, UNIX_EPOCH};

const DEFAULT_RECORD: &str = "11061097";
const DEFAULT_SAMPLE: usize = 500;
const DEFAULT_MAX_MB: u64 = 60;
/// Bound decompressed regular-file bytes relative to the checksum-pinned
/// archive. SMT-LIB text compresses well, so keep generous headroom while
/// still preventing an unbounded decompression bomb from a caller-selected
/// record.
const MAX_ARCHIVE_EXPANSION_RATIO: u64 = 256;
const MIN_ARCHIVE_EXPANSION_BUDGET: u64 = 1_000_000_000;

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
    max_mb: u64,
    divisions: Option<Vec<String>>,
    record: String,
    list: bool,
}

fn usage() -> &'static str {
    "\
ay-z3-parity fetch <dest-dir> [--sample N | --all] [--max-mb M]
                   [--divisions d1,d2,...] [--record ID] [--list]

  Re-download & DETERMINISTICALLY sample the SMT-LIB corpus from Zenodo into
  <dest-dir>/<DIVISION>/. In-tree equivalent of fetch-all.sh.

  --sample N     files sampled per division (default 500)
  --all          sample every file (no per-division cap)
  --max-mb M     skip archives larger than M MB (default 60; excludes the
                 giants QF_BV/QF_LIA/QF_IDL/AUFBV unless raised)
  --divisions    comma-separated allowlist of divisions
  --record ID    Zenodo record id (default 11061097)
  --list         print available divisions + sizes, download nothing
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
        print_list(&args, &selected);
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

    let per = if args.all {
        "all".to_string()
    } else {
        args.sample.to_string()
    };
    println!(
        "== {} divisions (max {}MB each, {}/division) -> {}",
        selected.len(),
        args.max_mb,
        per,
        dest.display()
    );

    let mut done = 0usize;
    let mut skipped_cap = 0usize;
    let mut failed = 0usize;
    for e in selected {
        let size_mb = e.size / 1_000_000;
        if archive_exceeds_cap(e.size, args.max_mb) {
            println!(
                "-- {}: {}MB > {}MB cap — skipped (raise --max-mb to include)",
                e.div, size_mb, args.max_mb
            );
            skipped_cap += 1;
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
        "== done: {done} divisions fetched into {} \
         ({skipped_cap} over the {}MB cap, {failed} failed)",
        dest.display(),
        args.max_mb
    );
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
    let mut all = false;
    let mut max_mb = DEFAULT_MAX_MB;
    let mut divisions = None;
    let mut record = DEFAULT_RECORD.to_string();
    let mut list = false;

    let mut it = rest.iter();
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--sample" => {
                sample_explicit = true;
                sample = it
                    .next()
                    .ok_or("--sample needs a number")?
                    .parse()
                    .map_err(|_| "--sample must be a positive integer")?;
                if sample == 0 {
                    return Err("--sample must be at least 1".to_string());
                }
            }
            "--all" => all = true,
            "--max-mb" => {
                max_mb = it
                    .next()
                    .ok_or("--max-mb needs a number")?
                    .parse()
                    .map_err(|_| "--max-mb must be an integer number of MB")?;
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
    if all && sample_explicit {
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

fn archive_exceeds_cap(size: u64, max_mb: u64) -> bool {
    size > max_mb.saturating_mul(1_000_000)
}

fn print_list(args: &FetchArgs, entries: &[&DivEntry]) {
    println!(
        "== {} divisions in Zenodo record {}:",
        entries.len(),
        args.record
    );
    for e in entries {
        let mb = e.size as f64 / 1_000_000.0;
        let over = if archive_exceeds_cap(e.size, args.max_mb) {
            "  (over --max-mb)"
        } else {
            ""
        };
        println!(
            "  {:<22} {:>10.2} MB  {:>14} B  {}{}",
            e.div, mb, e.size, e.md5, over
        );
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
    extract(
        &archive,
        &xd,
        e.size
            .saturating_mul(MAX_ARCHIVE_EXPANSION_RATIO)
            .max(MIN_ARCHIVE_EXPANSION_BUDGET),
    )?;

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
        if let Err(err) = remove_path(&backup) {
            eprintln!(
                "warning: installed {}, but could not remove backup {}: {err}",
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

    #[test]
    fn exact_byte_cap_does_not_admit_a_sub_megabyte_archive_at_zero() {
        assert!(archive_exceeds_cap(1, 0));
        assert!(!archive_exceeds_cap(1_000_000, 1));
        assert!(archive_exceeds_cap(1_000_001, 1));
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
            max_mb: 1,
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
