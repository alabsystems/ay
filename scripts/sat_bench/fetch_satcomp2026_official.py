#!/usr/bin/env python3
"""Provision the ACTUAL SAT-COMP 2026 Main-track instance set.

Why this exists separately from `fetch_satcomp_main.py`
-------------------------------------------------------
The in-repo manifests `benchmarks/sat/satcomp2026-main/SC2026.pinned.csv` and
`selected_benchmarks.csv` are NOT the competition set. Measured 2026-07-28
against the official per-instance results:

  * only 20 of their 400 hashes appear in the official scores.csv
  * they contain 9 duplicate hashes (400 rows, 391 distinct)

They look like a candidate/submission list. Scoring against them would compare
AY on one set of formulas to the winners on a different set.

The authoritative instance list is the `instanceid` column of the official
results export:

  https://satcompetition.github.io/2026/downloads/scores.csv

(400 distinct instanceids x 31 sequential solvers = 12,400 rows). Instances are
served by the public GBD mirror at https://benchmark-database.de/file/<id>.

Integrity
---------
Each payload is verified by recomputing the GBD hash and requiring it to equal
the official `instanceid`. The GBD hash is md5 over the CNF with comment (`c`)
and header (`p`) lines removed and all whitespace runs collapsed to single
spaces (verified by reconstruction against a known instance). This binds every
downloaded file to the exact formula the competition scored, independently of
the transport - which matters here because a local TLS-scanning AV re-signs
every HTTPS connection on this machine.

A corrected manifest is written to SC2026.official.csv for reproducibility.

Usage:
  python scripts/sat_bench/fetch_satcomp2026_official.py --jobs 6
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import lzma
import os
import re
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
MIRROR = "https://benchmark-database.de/file/"
OUT_DIR = REPO / "benchmarks/sat/satcomp2026-main/official"
MANIFEST = REPO / "benchmarks/sat/satcomp2026-main/SC2026.official.csv"

_lock = threading.Lock()
_WS = re.compile(rb"\s+")


def gbd_hash(cnf: bytes) -> str:
    """Recompute GBD's instance identity for a decompressed CNF."""
    body = b"\n".join(
        line
        for line in cnf.split(b"\n")
        if not line.startswith(b"c") and not line.startswith(b"p")
    )
    return hashlib.md5(_WS.sub(b" ", body).strip()).hexdigest()


def official_instance_ids(scores_csv: Path) -> list[str]:
    with scores_csv.open(newline="") as fh:
        ids = {row["instanceid"] for row in csv.DictReader(fh)}
    return sorted(ids)


def fetch_one(instance_id: str, retries: int = 3) -> tuple[str, dict]:
    dest = OUT_DIR / f"{instance_id}.cnf.xz"
    if dest.exists():
        return "skip", {}
    dest.parent.mkdir(parents=True, exist_ok=True)
    last = ""
    for attempt in range(1, retries + 1):
        fd, tmp_name = tempfile.mkstemp(dir=str(dest.parent), suffix=".part")
        tmp = Path(tmp_name)
        try:
            os.close(fd)
            # --ssl-no-revoke skips ONLY the revocation check, which cannot
            # succeed behind a locally installed TLS-scanning AV whose synthetic
            # CA publishes no CRL/OCSP. Chain validation against the Windows
            # trust store still applies, and content is verified below by
            # recomputing the official GBD identity hash.
            proc = subprocess.run(
                [
                    "curl", "-sS", "--fail", "--location", "--ssl-no-revoke",
                    "--max-time", "1800", "--retry", "2",
                    "-A", "ay-bench/1.0", "-o", str(tmp), MIRROR + instance_id,
                ],
                capture_output=True,
                text=True,
            )
            if proc.returncode != 0:
                last = f"curl rc={proc.returncode}: {proc.stderr.strip()[:160]}"
                tmp.unlink(missing_ok=True)
                time.sleep(2 * attempt)
                continue

            payload = tmp.read_bytes()
            try:
                cnf = lzma.decompress(payload)
            except lzma.LZMAError as exc:
                last = f"not valid xz: {exc}"
                tmp.unlink(missing_ok=True)
                continue

            got = gbd_hash(cnf)
            if got != instance_id:
                last = f"GBD identity {got} != official instanceid {instance_id}"
                tmp.unlink(missing_ok=True)
                continue

            meta = {
                "instanceid": instance_id,
                "local_path": str(dest.relative_to(REPO)).replace("\\", "/"),
                "size_bytes": len(payload),
                "sha256": hashlib.sha256(payload).hexdigest(),
                "cnf_bytes": len(cnf),
            }
            tmp.replace(dest)
            return "ok", meta
        except Exception as exc:  # noqa: BLE001
            last = f"{type(exc).__name__}: {exc}"
            tmp.unlink(missing_ok=True)
            time.sleep(2 * attempt)
    return f"FAIL: {last}", {}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--scores", required=True, help="official 2026 scores.csv")
    ap.add_argument("--jobs", type=int, default=6)
    args = ap.parse_args()

    ids = official_instance_ids(Path(args.scores))
    print(f"official 2026 main instances: {len(ids)}", flush=True)

    counters = {"n": 0, "ok": 0, "skip": 0, "fail": 0}
    metas: list[dict] = []
    failures: list[str] = []
    start = time.time()

    def work(instance_id: str) -> None:
        status, meta = fetch_one(instance_id)
        with _lock:
            counters["n"] += 1
            if status == "ok":
                counters["ok"] += 1
                metas.append(meta)
            elif status == "skip":
                counters["skip"] += 1
            else:
                counters["fail"] += 1
                failures.append(f"{instance_id}: {status}")
            if counters["n"] % 20 == 0 or status.startswith("FAIL"):
                print(
                    f"{counters['n']}/{len(ids)} ok={counters['ok']} "
                    f"skip={counters['skip']} fail={counters['fail']} "
                    f"{time.time() - start:.0f}s",
                    flush=True,
                )

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        list(pool.map(work, ids))

    print(
        f"DONE {counters['n']}/{len(ids)} ok={counters['ok']} "
        f"skip={counters['skip']} fail={counters['fail']} "
        f"in {time.time() - start:.0f}s",
        flush=True,
    )
    for line in failures:
        print(line, flush=True)

    if metas:
        existing = {}
        if MANIFEST.exists():
            with MANIFEST.open(newline="") as fh:
                existing = {r["instanceid"]: r for r in csv.DictReader(fh)}
        for meta in metas:
            existing[meta["instanceid"]] = meta
        with MANIFEST.open("w", newline="") as fh:
            writer = csv.DictWriter(
                fh,
                fieldnames=["instanceid", "local_path", "size_bytes", "sha256", "cnf_bytes"],
            )
            writer.writeheader()
            for key in sorted(existing):
                writer.writerow(existing[key])
        print(f"manifest: {MANIFEST} ({len(existing)} rows)", flush=True)

    return 1 if counters["fail"] else 0


if __name__ == "__main__":
    sys.exit(main())
