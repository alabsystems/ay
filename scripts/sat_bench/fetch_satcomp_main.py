#!/usr/bin/env python3
"""Provision the pinned SAT-COMP Main-track corpora (2025 and 2026).

Both corpora are pinned in-repo by md5 hash + size + sha256:
  benchmarks/sat/satcomp2025-main/SC2025.pinned.tsv   (url, size_bytes, sha256)
  benchmarks/sat/satcomp2026-main/SC2026.pinned.csv   (hash, local_path, size_bytes, sha256, ...)

The .cnf.xz payloads are intentionally not committed (benchmarks/.gitignore
excludes *.cnf / *.cnf.xz); this script is the provisioning step the manifests
were designed for. Downloads come from the public GBD mirror
https://benchmark-database.de/file/<md5> and every file is verified against the
pinned sha256 before being accepted (partial/corrupt downloads are discarded and
retried).

Usage:
  python scripts/sat_bench/fetch_satcomp_main.py --year 2025 --jobs 6
  python scripts/sat_bench/fetch_satcomp_main.py --year 2026 --jobs 6
  python scripts/sat_bench/fetch_satcomp_main.py --year both --jobs 6
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import os
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
MIRROR = "https://benchmark-database.de/file/"
CHUNK = 1 << 20

_print_lock = threading.Lock()


def log(msg: str) -> None:
    with _print_lock:
        print(msg, flush=True)


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for block in iter(lambda: fh.read(CHUNK), b""):
            h.update(block)
    return h.hexdigest()


def targets_2025() -> list[tuple[str, Path, int, str]]:
    """Return (url, dest, size, sha256) for the 2025 Main corpus."""
    src = REPO / "benchmarks/sat/satcomp2025-main/SC2025.pinned.tsv"
    out = REPO / "benchmarks/sat/satcomp2025-main/instances"
    rows = []
    with src.open(newline="") as fh:
        for row in csv.reader(fh, delimiter="\t"):
            if len(row) < 3:
                continue
            url, size, sha = row[0], int(row[1]), row[2]
            md5 = url.rstrip("/").rsplit("/", 1)[-1]
            rows.append((url, out / f"{md5}.cnf.xz", size, sha))
    return rows


def targets_2026() -> list[tuple[str, Path, int, str]]:
    """Return (url, dest, size, sha256) for the 2026 Main corpus."""
    src = REPO / "benchmarks/sat/satcomp2026-main/SC2026.pinned.csv"
    rows = []
    with src.open(newline="") as fh:
        for r in csv.DictReader(fh):
            rows.append(
                (
                    MIRROR + r["hash"],
                    REPO / r["local_path"],
                    int(r["size_bytes"]),
                    r["sha256"],
                )
            )
    return rows


def fetch_one(url: str, dest: Path, size: int, sha: str, retries: int = 3) -> str:
    """Download dest unless it already verifies. Returns 'skip' | 'ok' | 'FAIL: ...'."""
    if dest.exists() and dest.stat().st_size == size:
        # Trust size on re-runs; full re-hash of 5 GB every invocation is wasteful.
        return "skip"
    dest.parent.mkdir(parents=True, exist_ok=True)
    last = ""
    for attempt in range(1, retries + 1):
        tmp_fd, tmp_name = tempfile.mkstemp(dir=str(dest.parent), suffix=".part")
        tmp = Path(tmp_name)
        try:
            os.close(tmp_fd)
            # curl (Schannel) validates the chain against the Windows trust store.
            # --ssl-no-revoke skips ONLY the revocation check, which cannot succeed
            # when a locally-installed TLS-scanning AV (Norton Web/Mail Shield)
            # re-signs the connection with a synthetic CA that publishes no CRL/OCSP.
            # Content integrity does not rest on TLS here: every payload is verified
            # below against the sha256 pinned in the in-repo manifest.
            proc = subprocess.run(
                [
                    "curl", "-sS", "--fail", "--location", "--ssl-no-revoke",
                    "--max-time", "1800", "--retry", "2",
                    "-A", "ay-bench/1.0", "-o", str(tmp), url,
                ],
                capture_output=True,
                text=True,
            )
            if proc.returncode != 0:
                last = f"curl rc={proc.returncode}: {proc.stderr.strip()[:200]}"
                tmp.unlink(missing_ok=True)
                time.sleep(2 * attempt)
                continue
            got_size = tmp.stat().st_size
            if got_size != size:
                last = f"size {got_size} != pinned {size}"
                tmp.unlink(missing_ok=True)
                continue
            got_sha = sha256_file(tmp)
            if got_sha != sha:
                last = f"sha256 {got_sha[:16]} != pinned {sha[:16]}"
                tmp.unlink(missing_ok=True)
                continue
            tmp.replace(dest)
            return "ok"
        except Exception as exc:  # noqa: BLE001 - report any transport failure
            last = f"{type(exc).__name__}: {exc}"
            tmp.unlink(missing_ok=True)
            time.sleep(2 * attempt)
    return f"FAIL: {last}"


def run(rows: list[tuple[str, Path, int, str]], jobs: int, label: str) -> int:
    total = len(rows)
    done = {"n": 0, "ok": 0, "skip": 0, "fail": 0}
    failures: list[str] = []
    start = time.time()

    def work(item):
        url, dest, size, sha = item
        status = fetch_one(url, dest, size, sha)
        with _print_lock:
            done["n"] += 1
            if status == "ok":
                done["ok"] += 1
            elif status == "skip":
                done["skip"] += 1
            else:
                done["fail"] += 1
                failures.append(f"{dest.name}: {status}")
            if done["n"] % 10 == 0 or status.startswith("FAIL"):
                el = time.time() - start
                print(
                    f"[{label}] {done['n']}/{total} ok={done['ok']} "
                    f"skip={done['skip']} fail={done['fail']} {el:.0f}s",
                    flush=True,
                )

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        list(pool.map(work, rows))

    el = time.time() - start
    print(
        f"[{label}] DONE {done['n']}/{total} ok={done['ok']} skip={done['skip']} "
        f"fail={done['fail']} in {el:.0f}s",
        flush=True,
    )
    for f in failures:
        print(f"[{label}] {f}", flush=True)
    return done["fail"]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--year", choices=["2025", "2026", "both"], default="both")
    ap.add_argument("--jobs", type=int, default=6)
    args = ap.parse_args()

    rc = 0
    if args.year in ("2025", "both"):
        rc += run(targets_2025(), args.jobs, "SC2025")
    if args.year in ("2026", "both"):
        rc += run(targets_2026(), args.jobs, "SC2026")
    return 1 if rc else 0


if __name__ == "__main__":
    sys.exit(main())
