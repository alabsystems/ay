#!/usr/bin/env python3
# ay-script: smtlib2025-fetch
"""Fetch the SMT-LIB 2025 benchmark corpus used by SMT-COMP 2025.

Why this exists (and why download_smtcomp_benchmarks.sh does NOT do this job):
that script hardcodes Zenodo record 11061097 -- SMT-LIB **2024** -- and extracts
*flattened* into benchmarks/smtcomp/<LOGIC>/. The 2025 selections resolve against
benchmarks/smtlib-2025/{non-incremental,incremental}/<LOGIC>/<family>/<file>, so
they need the 2025 records and the archive's own tree layout.

    non-incremental   Zenodo 15493090
    incremental       Zenodo 15493096

Two traps this script handles so you do not have to:

1. PREFIX. Some archives carry the `non-incremental/` (or `incremental/`) prefix
   inside them and some do not. Extracting at the wrong root silently produces
   `non-incremental/non-incremental/QF_BV/...` and every selection path check
   still reports "missing" -- with no error anywhere. We read the archive's first
   member and pick the extraction root so the final path is always
   benchmarks/smtlib-2025/<kind>/<LOGIC>/...

2. ABSENT LOGICS. A logic named in defs.py may have no archive in the record at
   all (e.g. incremental UFDT). That is not an error: the track genuinely has no
   benchmarks for it. We report those as `absent` and keep going.

Idempotent and resumable: tar runs with -k (keep existing), already-complete
logics are skipped by a marker, and a partial download is re-fetched next run.

Usage:
    scripts/fetch_smtlib2025_corpus.py                 # every missing logic
    scripts/fetch_smtlib2025_corpus.py --kind non-incremental
    scripts/fetch_smtlib2025_corpus.py --logic QF_BV --logic QF_FP
    scripts/fetch_smtlib2025_corpus.py --dry-run
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / "benchmarks" / "smtlib-2025"
DEFS = ROOT / ".competitors" / "smtcomp-io" / "smtcomp" / "defs.py"
RECORDS = {"non-incremental": "15493090", "incremental": "15493096"}
MARKER = ".fetched"


def logics_by_kind() -> dict[str, set[str]]:
    """Every logic named by a 2025 division, split by incremental-ness."""
    src = DEFS.read_text()
    i = src.find("tracks:")
    seg = src[i:i + 40000]
    out: dict[str, set[str]] = {"non-incremental": set(), "incremental": set()}
    for track, kind in (("SingleQuery", "non-incremental"),
                        ("UnsatCore", "non-incremental"),
                        ("ModelValidation", "non-incremental"),
                        ("Incremental", "incremental")):
        j = seg.find("Track." + track)
        if j < 0:
            continue
        for m in re.finditer(r"Logic\.(\w+)", seg[j:j + 9000]):
            out[kind].add(m.group(1))
    return out


def record_files(record: str) -> dict[str, int]:
    with urllib.request.urlopen(
            f"https://zenodo.org/api/records/{record}", timeout=120) as fh:
        data = json.load(fh)
    return {f["key"]: f["size"] for f in data.get("files", [])}


def archive_root(tar_path: Path, kind: str) -> Path:
    """Extraction root such that members land at <CORPUS>/<kind>/<LOGIC>/...

    Decided by the archive's own first member, never by assumption -- this is
    trap #1 in the module docstring.
    """
    first = subprocess.run(["tar", "-tf", str(tar_path)],
                           capture_output=True, text=True, check=True)
    for line in first.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        top = line.split("/", 1)[0]
        return CORPUS if top == kind else CORPUS / kind
    raise RuntimeError(f"{tar_path.name}: archive is empty")


def fetch_one(logic: str, kind: str, size: int, dry: bool) -> tuple[str, str]:
    dest = CORPUS / kind / logic
    if (dest / MARKER).exists():
        return "skip", "already fetched"
    if dry:
        return "would-fetch", f"{size / 1e6:.1f} MB"

    url = (f"https://zenodo.org/api/records/{RECORDS[kind]}"
           f"/files/{logic}.tar.zst/content")
    with tempfile.TemporaryDirectory(prefix=f"smtlib25-{logic}-") as td:
        tar_zst = Path(td) / f"{logic}.tar.zst"
        rc = subprocess.run(
            ["curl", "-fsSL", "--retry", "5", "--retry-delay", "5",
             "--max-time", "3600", url, "-o", str(tar_zst)])
        if rc.returncode != 0 or not tar_zst.exists():
            return "fail", "download failed"
        # Decompress to a plain tar so we can inspect the prefix before extracting.
        plain = Path(td) / f"{logic}.tar"
        if subprocess.run(["zstd", "-dqf", str(tar_zst), "-o", str(plain)]).returncode != 0:
            return "fail", "zstd decompress failed"
        try:
            root = archive_root(plain, kind)
        except Exception as exc:  # noqa: BLE001 - report and continue the sweep
            return "fail", f"cannot read archive: {exc}"
        root.mkdir(parents=True, exist_ok=True)
        # -k keeps existing files, so re-running never clobbers a vendored file.
        subprocess.run(["tar", "-xkf", str(plain), "-C", str(root)],
                       stderr=subprocess.DEVNULL)

    n = sum(1 for _ in dest.rglob("*.smt2")) if dest.is_dir() else 0
    if n == 0:
        return "fail", "extracted 0 .smt2 (prefix mismatch?)"
    dest.mkdir(parents=True, exist_ok=True)
    (dest / MARKER).write_text(f"{RECORDS[kind]} {logic} {n}\n")
    return "ok", f"{n} .smt2"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--kind", choices=sorted(RECORDS), action="append")
    ap.add_argument("--logic", action="append")
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    kinds = args.kind or sorted(RECORDS)
    want = logics_by_kind()
    total_ok = total_fail = total_absent = 0

    for kind in kinds:
        have = {p.name for p in (CORPUS / kind).iterdir()} if (CORPUS / kind).is_dir() else set()
        missing = sorted(want[kind] - have) if not args.logic else sorted(args.logic)
        try:
            avail = record_files(RECORDS[kind])
        except Exception as exc:  # noqa: BLE001
            print(f"{kind}: cannot query Zenodo {RECORDS[kind]}: {exc}", file=sys.stderr)
            return 1
        todo = [(L, avail[L + ".tar.zst"]) for L in missing if L + ".tar.zst" in avail]
        absent = [L for L in missing if L + ".tar.zst" not in avail]
        total_absent += len(absent)
        todo.sort(key=lambda t: t[1])  # small first: quick wins, fail fast on setup bugs
        mb = sum(s for _, s in todo) / 1e6
        print(f"\n=== {kind}: {len(todo)} archives, {mb:.0f} MB "
              f"({len(absent)} logics absent from record {RECORDS[kind]}) ===",
              flush=True)
        for i, (logic, size) in enumerate(todo, 1):
            t0 = time.time()
            status, note = fetch_one(logic, kind, size, args.dry_run)
            total_ok += status in ("ok", "skip")
            total_fail += status == "fail"
            print(f"  [{i:>3}/{len(todo)}] {logic:16s} {size/1e6:8.1f} MB  "
                  f"{status:11s} {note}  ({time.time()-t0:.0f}s)", flush=True)

    print(f"\nfetched/present={total_ok} failed={total_fail} absent-from-record={total_absent}")
    return 1 if total_fail else 0


if __name__ == "__main__":
    sys.exit(main())
