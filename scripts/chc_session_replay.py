#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
"""HornSmt session query-replay tool (CHC-COMP 2026 Rung 1, design §10.1; WP-4).

A query corpus is a directory of self-contained SMT-LIB scripts `q_<seq>_<thread>.smt2`
plus an `index.tsv`, written either by the session recorder
(`AY_CHC_SESSION=1 AY_CHC_SESSION_DUMP=<dir> ay --chc ...`, columns
`seq thread lane_result elapsed_us n_conj n_delta n_assumptions decisions unknown_reason`)
or by the 2026-09-18 microbenchmark dumper (`seq thread path result elapsed_ms ...`).

Subcommands
  pack <dumpdir> <key> [--fixtures DIR]
      Pack a dump into crates/ay-chc/tests/fixtures/session_replay/<key>/
      (queries.smt2.gz with `;; @file <name>` separators + index.tsv), the form
      `session/tests/replay.rs` reads.
  unpack <key|fixture-dir> <outdir>
      The inverse (plain q_*.smt2 + index.tsv).
  run <dumpdir|key> [--test-bin PATH] [--limit N]
      Replay through the Rust harness (warm session via the production router vs a
      fresh legacy context vs z3 vs the recorded verdict) by running the ay-chc lib
      test binary's `replay_dir_from_env` with AY_REPLAY_DIR. Prints its summary
      line; exit status = the harness's 0-disagreement verdict. Build the test binary
      first (Trust override recipe; see the Rung-1 WP-4 report).
  z3 <dumpdir|key> [--z3 PATH] [--timeout S] [--jobs N]
      Verdict census of every script under z3 against the recorded verdicts
      (independent of the Rust side). Reports agree / disagree / unknown.
  summarize <dumpdir|index.tsv> [--json]
      Board columns from a SESSION dump's index.tsv (design §10.4): n, verdict mix,
      unknown classes, the unknown_theory_incomplete + unknown_unsupported share,
      elapsed median/p90/p99/max, delta/assumption/decision medians.
"""
import argparse
import glob
import gzip
import json
import os
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FIXTURES = os.path.join(REPO, "crates", "ay-chc", "tests", "fixtures", "session_replay")
VERDICT_RE = re.compile(r"^\s*(sat|unsat|unknown)\s*$", re.M)


def resolve_corpus(arg):
    """A dump directory, a fixture key, or a fixture directory -> a plain directory
    (unpacked into a temp dir when needed). Returns (dir, cleanup_dir_or_None)."""
    if os.path.isdir(arg) and glob.glob(os.path.join(arg, "q_*.smt2")):
        return arg, None
    fixture = arg if os.path.isdir(arg) else os.path.join(FIXTURES, arg)
    if os.path.exists(os.path.join(fixture, "queries.smt2.gz")):
        tmp = tempfile.mkdtemp(prefix="chc-session-replay-")
        unpack(fixture, tmp)
        return tmp, tmp
    sys.exit(f"not a corpus: {arg}")


def pack(dumpdir, key, fixtures=FIXTURES):
    out = os.path.join(fixtures, key)
    os.makedirs(out, exist_ok=True)
    files = sorted(glob.glob(os.path.join(dumpdir, "q_*.smt2")))
    with gzip.open(os.path.join(out, "queries.smt2.gz"), "wt", compresslevel=9) as gz:
        for f in files:
            gz.write(f";; @file {os.path.basename(f)}\n")
            with open(f) as fh:
                gz.write(fh.read())
    idx = os.path.join(dumpdir, "index.tsv")
    if os.path.exists(idx):
        shutil.copy(idx, os.path.join(out, "index.tsv"))
    print(f"packed {len(files)} scripts -> {out}")


def unpack(fixture, outdir):
    os.makedirs(outdir, exist_ok=True)
    name, body = None, []

    def flush():
        if name:
            with open(os.path.join(outdir, name), "w") as fh:
                fh.write("".join(body))

    with gzip.open(os.path.join(fixture, "queries.smt2.gz"), "rt") as gz:
        for line in gz:
            if line.startswith(";; @file "):
                flush()
                name, body = line[len(";; @file "):].strip(), []
            else:
                body.append(line)
    flush()
    idx = os.path.join(fixture, "index.tsv")
    if os.path.exists(idx):
        shutil.copy(idx, os.path.join(outdir, "index.tsv"))


def recorded_verdicts(corpus):
    """seq -> sat|unsat|unknown from either index layout."""
    out = {}
    idx = os.path.join(corpus, "index.tsv")
    if not os.path.exists(idx):
        return out
    with open(idx) as fh:
        for line in fh:
            cols = line.rstrip("\n").split("\t")
            if not cols or not cols[0].isdigit():
                continue
            for c in (cols[3] if len(cols) > 3 else "", cols[2] if len(cols) > 2 else ""):
                if c in ("sat", "unsat", "unknown"):
                    out[int(cols[0])] = c
                    break
    return out


def seq_of(path):
    m = re.match(r"q_(\d+)_", os.path.basename(path))
    return int(m.group(1)) if m else None


def resolve_z3(requested):
    """`--z3 PATH` identity-checked as given, else the z3 oracle
    (scripts/_z3_oracle.py: Z3_PATH, else the first z3 on PATH that proves it is
    z3, reached past reroute stubs and AY drop-ins)."""
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import _z3_oracle

    try:
        return _z3_oracle.resolve_z3_spelling(requested or "z3")
    except _z3_oracle.Z3Unavailable as error:
        sys.exit(f"no usable z3: {error}")


def find_test_bin():
    cands = []
    for prof in ("debug", "release"):
        for p in glob.glob(os.path.join(REPO, "target", prof, "deps", "ay_chc-*")):
            if os.access(p, os.X_OK) and not p.endswith((".d", ".rlib", ".rmeta")):
                cands.append(p)
    if not cands:
        sys.exit("no ay_chc lib test binary under target/*/deps; build it with --no-run first")
    return max(cands, key=os.path.getmtime)


def cmd_run(a):
    corpus, tmp = resolve_corpus(a.corpus)
    try:
        env = dict(os.environ, AY_REPLAY_DIR=corpus)
        if a.limit:
            env["AY_REPLAY_LIMIT"] = str(a.limit)
        env["PATH"] = "/opt/homebrew/bin:" + env.get("PATH", "")
        binp = a.test_bin or find_test_bin()
        p = subprocess.run(
            [binp, "smt::session::wp_tests::replay::replay_dir_from_env", "--ignored",
             "--nocapture", "--test-threads=1"],
            env=env, capture_output=True, text=True)
        for line in (p.stdout + p.stderr).splitlines():
            if line.startswith("[replay-dir") or "test result" in line or "panicked" in line:
                print(line)
        return p.returncode
    finally:
        if tmp:
            shutil.rmtree(tmp, ignore_errors=True)


def cmd_z3(a):
    corpus, tmp = resolve_corpus(a.corpus)
    try:
        rec = recorded_verdicts(corpus)
        files = sorted(glob.glob(os.path.join(corpus, "q_*.smt2")))
        z3 = resolve_z3(a.z3)
        print(f"z3: {z3.identity()}")

        def one(f):
            try:
                p = subprocess.run([z3.path, f"-T:{a.timeout}", f], capture_output=True,
                                   text=True, timeout=a.timeout + 5)
                m = VERDICT_RE.findall(p.stdout)
                return f, (m[0] if m else "error")
            except subprocess.TimeoutExpired:
                return f, "unknown"

        with ThreadPoolExecutor(max_workers=a.jobs) as ex:
            res = list(ex.map(one, files))
        agree = disagree = unknown = 0
        for f, v in res:
            r = rec.get(seq_of(f))
            if v not in ("sat", "unsat") or r not in ("sat", "unsat"):
                unknown += 1
            elif v == r:
                agree += 1
            else:
                disagree += 1
                print(f"DISAGREE {os.path.basename(f)}: z3={v} recorded={r}")
        print(f"z3 census: n={len(res)} agree={agree} disagree={disagree} no-evidence={unknown}")
        return 1 if disagree else 0
    finally:
        if tmp:
            shutil.rmtree(tmp, ignore_errors=True)


def pct(xs, q):
    if not xs:
        return 0
    xs = sorted(xs)
    i = max(0, min(len(xs) - 1, int(-(-q * len(xs) // 1)) - 1))
    return xs[i]


def summarize(index_path):
    rows = []
    with open(index_path) as fh:
        for line in fh:
            cols = line.rstrip("\n").split("\t")
            if len(cols) < 9 or not cols[0].isdigit():
                continue
            rows.append(cols)
    n = len(rows)
    res = {}
    reasons = {}
    for r in rows:
        res[r[2]] = res.get(r[2], 0) + 1
        if r[8] != "-":
            reasons[r[8]] = reasons.get(r[8], 0) + 1
    el = [int(r[3]) for r in rows]
    ti_un = reasons.get("theory_incomplete", 0) + reasons.get("unsupported", 0)
    return {
        "n": n,
        "results": res,
        "unknown_reasons": reasons,
        "ti_plus_unsupported_pct": round(100.0 * ti_un / n, 2) if n else 0.0,
        "elapsed_us": {"median": pct(el, 0.5), "p90": pct(el, 0.9), "p99": pct(el, 0.99),
                       "max": max(el) if el else 0},
        "delta_median": statistics.median([int(r[5]) for r in rows]) if rows else 0,
        "assumptions_median": statistics.median([int(r[6]) for r in rows]) if rows else 0,
        "decisions_median": statistics.median([int(r[7]) for r in rows]) if rows else 0,
    }


def cmd_summarize(a):
    path = a.index if a.index.endswith(".tsv") else os.path.join(a.index, "index.tsv")
    s = summarize(path)
    if a.json:
        print(json.dumps(s, indent=2, sort_keys=True))
    else:
        print(" ".join(f"{k}={v}" for k, v in s.items()))
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("pack"); p.add_argument("dumpdir"); p.add_argument("key")
    p.add_argument("--fixtures", default=FIXTURES)
    p = sub.add_parser("unpack"); p.add_argument("fixture"); p.add_argument("outdir")
    p = sub.add_parser("run"); p.add_argument("corpus"); p.add_argument("--test-bin")
    p.add_argument("--limit", type=int, default=0)
    p = sub.add_parser("z3"); p.add_argument("corpus")
    p.add_argument("--z3", default=None, help="z3 path (default: the z3 oracle)")
    p.add_argument("--timeout", type=int, default=10); p.add_argument("--jobs", type=int, default=2)
    p = sub.add_parser("summarize"); p.add_argument("index"); p.add_argument("--json", action="store_true")
    a = ap.parse_args()
    if a.cmd == "pack":
        pack(a.dumpdir, a.key, a.fixtures); return 0
    if a.cmd == "unpack":
        fx = a.fixture if os.path.isdir(a.fixture) else os.path.join(FIXTURES, a.fixture)
        unpack(fx, a.outdir); return 0
    return {"run": cmd_run, "z3": cmd_z3, "summarize": cmd_summarize}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
