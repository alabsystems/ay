#!/usr/bin/env python3
# ay-script: milp-corpus
"""milp_corpus.py — fetch and index the MIPLIB 2017 corpus used by the W0 harness.

The corpus lives OUTSIDE the repo (default ``~/ay-bench/milp``) because it is
hundreds of megabytes of third-party instances. What lives in the repo is this
fetcher and the manifest schema, so the corpus is reproducible from scratch.

Three artifacts are produced:

``instances/*.mps.gz``
    The raw instances, left gzipped (ay-milp and HiGHS both read gz).

``meta/miplib2017-v27.solu``
    MIPLIB's reference objective values. This is the *ground truth* used by the
    regression gate: it is independent of any solver we run, so a wrong OPTIMAL
    is caught even if every solver in the portfolio agrees with each other.

``manifest.json``
    Per-instance size/composition, plus a ``tier`` assignment. The tiers exist
    because the Gurobi license available here is size-limited (2000 cols and
    2000 rows); ``gurobi`` tier instances are the ones where a head-to-head
    against Gurobi is actually measurable, and the rest are measured against
    HiGHS and against MIPLIB's reference values.

Usage:
  scripts/milp_corpus.py fetch            # download the benchmark set
  scripts/milp_corpus.py fetch --small    # also grab collection instances under the Gurobi cap
  scripts/milp_corpus.py index            # (re)build manifest.json from what is on disk
  scripts/milp_corpus.py list --tier gurobi
"""
from __future__ import annotations

import argparse
import concurrent.futures
import gzip
import json
import os
import pathlib
import sys
import urllib.error
import urllib.request

# B20: the env locator is retired; pass --corpus <dir> or symlink at the
# default path.
ROOT = (
    pathlib.Path(sys.argv[sys.argv.index("--corpus") + 1])
    if "--corpus" in sys.argv
    else pathlib.Path.home() / "ay-bench" / "milp"
)
INSTANCES = ROOT / "instances"
META = ROOT / "meta"
MANIFEST = ROOT / "manifest.json"

BASE = "https://miplib.zib.de/WebData/instances/"
LISTS = {
    "benchmark": "https://miplib.zib.de/downloads/benchmark-v2.test",
    "collection": "https://miplib.zib.de/downloads/collection-v1.test",
}
SOLU = "https://miplib.zib.de/downloads/miplib2017-v27.solu"

# The size-limited Gurobi license refuses models above this; instances at or under
# it are the ones where a direct Gurobi head-to-head is possible at all.
GUROBI_CAP_COLS = 2000
GUROBI_CAP_ROWS = 2000


def _fetch(url: str, dest: pathlib.Path, timeout: float = 120.0) -> tuple[bool, str]:
    if dest.exists() and dest.stat().st_size > 0:
        return True, "cached"
    tmp = dest.with_suffix(dest.suffix + ".part")
    try:
        with urllib.request.urlopen(url, timeout=timeout) as r:
            data = r.read()
        tmp.write_bytes(data)
        tmp.rename(dest)
        return True, f"{len(data)}B"
    except (urllib.error.URLError, OSError, TimeoutError) as e:
        tmp.unlink(missing_ok=True)
        return False, str(e)


def _head_size(name: str) -> tuple[str, int]:
    req = urllib.request.Request(BASE + name, method="HEAD")
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            return name, int(r.headers.get("Content-Length") or 0)
    except (urllib.error.URLError, OSError, ValueError, TimeoutError):
        return name, 0


def _head_sizes(names: list[str], jobs: int) -> dict[str, int]:
    out: dict[str, int] = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
        for i, (n, sz) in enumerate(ex.map(_head_size, names)):
            out[n] = sz
            if (i + 1) % 200 == 0:
                print(f"[probe] {i + 1}/{len(names)}", flush=True)
    return out


def cmd_fetch(args: argparse.Namespace) -> int:
    INSTANCES.mkdir(parents=True, exist_ok=True)
    META.mkdir(parents=True, exist_ok=True)

    for name, url in LISTS.items():
        ok, why = _fetch(url, META / f"{name}.test")
        print(f"[list] {name}: {'ok' if ok else 'FAIL'} {why}", flush=True)
    ok, why = _fetch(SOLU, META / "miplib2017-v27.solu")
    print(f"[solu] {'ok' if ok else 'FAIL'} {why}", flush=True)

    wanted: list[str] = []
    bench = (META / "benchmark.test").read_text().split()
    wanted.extend(bench)
    if args.small:
        # The collection set is 1065 instances and most of them are far too big to be
        # useful as a Gurobi-comparable tier. Downloading all of them to find out would
        # be several gigabytes, so size is probed with a HEAD first: the gzipped byte
        # count is a good enough proxy for model size to pre-filter on, and 1065 HEADs
        # cost seconds. Anything that passes is downloaded and then measured exactly by
        # `index`, which is the authority.
        coll = [n for n in (META / "collection.test").read_text().split() if n not in set(bench)]
        sizes = _head_sizes(coll, args.jobs)
        small = [n for n, sz in sizes.items() if 0 < sz <= args.max_gz_bytes]
        print(f"[fetch] collection: {len(coll)} probed, {len(small)} under "
              f"{args.max_gz_bytes}B gzipped", flush=True)
        wanted.extend(sorted(small))
    if args.only:
        keep = set(args.only)
        wanted = [n for n in wanted if n.replace(".mps.gz", "") in keep]
    if args.limit:
        wanted = wanted[: args.limit]

    todo = [n for n in wanted if not (INSTANCES / n).exists()]
    print(f"[fetch] {len(wanted)} wanted, {len(wanted) - len(todo)} cached, {len(todo)} to download",
          flush=True)

    done = fail = 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = {ex.submit(_fetch, BASE + n, INSTANCES / n): n for n in todo}
        for fut in concurrent.futures.as_completed(futs):
            n = futs[fut]
            ok, why = fut.result()
            if ok:
                done += 1
            else:
                fail += 1
                print(f"[fetch] FAIL {n}: {why}", flush=True)
            if (done + fail) % 20 == 0:
                print(f"[fetch] {done + fail}/{len(todo)} ({fail} failed)", flush=True)
    print(f"[fetch] complete: {done} downloaded, {fail} failed", flush=True)
    return 0 if fail == 0 else 1


def scan_mps(path: pathlib.Path) -> dict:
    """Size/composition of an MPS instance.

    Deliberately a lightweight section walk rather than a full parse: the harness
    only needs shape (rows/cols/nnz/integrality) for tiering and for reporting,
    and ay-milp's own reader is the authority on semantics.
    """
    opener = gzip.open if path.suffix == ".gz" else open
    rows = cols = nnz = 0
    ints = bins = 0
    section = ""
    in_int = False
    seen_cols: set[str] = set()
    int_cols: set[str] = set()
    bounds: dict[str, list] = {}
    try:
        with opener(path, "rt", errors="replace") as f:
            for line in f:
                if not line.strip() or line.startswith("*"):
                    continue
                if not line[0].isspace():
                    section = line.split()[0].upper()
                    continue
                fields = line.split()
                if section == "ROWS":
                    # N rows are objectives, not constraints.
                    if fields and fields[0].upper() != "N":
                        rows += 1
                elif section == "COLUMNS":
                    if len(fields) >= 3 and fields[1] == "'MARKER'":
                        in_int = "INTORG" in line
                        continue
                    if fields[0] not in seen_cols:
                        seen_cols.add(fields[0])
                        if in_int:
                            int_cols.add(fields[0])
                    nnz += (len(fields) - 1) // 2
                elif section == "BOUNDS":
                    if len(fields) >= 3:
                        bounds.setdefault(fields[2], []).append(
                            (fields[0].upper(), fields[3] if len(fields) > 3 else None))
    except OSError as e:
        return {"error": str(e)}

    cols = len(seen_cols)
    for c in seen_cols:
        bs = bounds.get(c, [])
        kinds = {k for k, _ in bs}
        is_bin = "BV" in kinds
        if not is_bin and c in int_cols:
            # An integer column declared with 0/1 bounds is binary in substance.
            ub = next((v for k, v in bs if k == "UP"), None)
            if ub is not None:
                try:
                    is_bin = float(ub) == 1.0
                except ValueError:
                    is_bin = False
            else:
                is_bin = not bs  # MPS default for INTORG columns is [0,1]
        if is_bin:
            bins += 1
        if c in int_cols or is_bin:
            ints += 1
    return {"rows": rows, "cols": cols, "nnz": nnz, "ints": ints, "bins": bins}


def tier_of(info: dict) -> str:
    """Tier from measured shape. THE definition — `rebuild_milp_bench.py` imports it.

    Two producers write this manifest, and a manifest whose `tier` means different
    things depending on which one built it is worse than one with no tier at all.
    """
    if "error" in info:
        return "large"
    if info["cols"] <= GUROBI_CAP_COLS and info["rows"] <= GUROBI_CAP_ROWS:
        return "gurobi"
    if info["cols"] <= 20000 and info["rows"] <= 20000:
        return "mid"
    return "large"


def load_solu() -> dict[str, dict]:
    p = META / "miplib2017-v27.solu"
    if not p.exists():
        return {}
    out: dict[str, dict] = {}
    for line in p.read_text().splitlines():
        f = line.split()
        if len(f) < 2:
            continue
        kind = f[0].strip("=")
        name = f[1]
        val = None
        if len(f) > 2:
            try:
                val = float(f[2])
            except ValueError:
                val = None
        out[name] = {"status": kind, "obj": val}
    return out


def cmd_index(args: argparse.Namespace) -> int:
    solu = load_solu()
    files = sorted(INSTANCES.glob("*.mps.gz")) + sorted(INSTANCES.glob("*.mps"))
    print(f"[index] scanning {len(files)} instances", flush=True)
    entries = {}

    def one(p: pathlib.Path):
        name = p.name.replace(".mps.gz", "").replace(".mps", "")
        return name, p, scan_mps(p)

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        for i, (name, p, info) in enumerate(ex.map(one, files)):
            ref = solu.get(name, {})
            entries[name] = {
                "file": str(p),
                "tier": tier_of(info),
                "ref_status": ref.get("status"),
                "ref_obj": ref.get("obj"),
                **info,
            }
            if (i + 1) % 25 == 0:
                print(f"[index] {i + 1}/{len(files)}", flush=True)

    MANIFEST.write_text(json.dumps({"root": str(ROOT), "instances": entries}, indent=1))
    tiers: dict[str, int] = {}
    for e in entries.values():
        tiers[e["tier"]] = tiers.get(e["tier"], 0) + 1
    print(f"[index] wrote {MANIFEST} — {len(entries)} instances, tiers={tiers}", flush=True)
    return 0


def load_manifest() -> dict:
    if not MANIFEST.exists():
        sys.exit(f"no manifest at {MANIFEST}; run: {sys.argv[0]} index")
    return json.loads(MANIFEST.read_text())


def cmd_list(args: argparse.Namespace) -> int:
    man = load_manifest()
    rows = []
    for name, e in man["instances"].items():
        if args.tier and e["tier"] != args.tier:
            continue
        if args.opt_only and e.get("ref_status") != "opt":
            continue
        rows.append((name, e))
    rows.sort(key=lambda kv: (kv[1].get("cols") or 0, kv[0]))
    if args.names_only:
        for name, _ in rows:
            print(name)
        return 0
    print(f"{'instance':28s} {'tier':8s} {'rows':>7s} {'cols':>7s} {'ints':>7s} {'ref':>8s} {'obj':>16s}")
    for name, e in rows:
        obj = "" if e.get("ref_obj") is None else f"{e['ref_obj']:.6g}"
        print(f"{name:28s} {e['tier']:8s} {e.get('rows', 0):7d} {e.get('cols', 0):7d} "
              f"{e.get('ints', 0):7d} {str(e.get('ref_status')):>8s} {obj:>16s}")
    print(f"\n{len(rows)} instances")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    f = sub.add_parser("fetch", help="download instances")
    f.add_argument("--small", action="store_true",
                   help="also fetch collection instances small enough to be Gurobi-comparable")
    f.add_argument("--max-gz-bytes", type=int, default=60_000,
                   help="with --small: gzipped-size prefilter (default 60kB)")
    f.add_argument("--only", nargs="*", help="fetch only these instance names")
    f.add_argument("--limit", type=int, default=0)
    f.add_argument("--jobs", type=int, default=8)
    f.set_defaults(fn=cmd_fetch)

    i = sub.add_parser("index", help="rebuild manifest.json")
    i.add_argument("--jobs", type=int, default=8)
    i.set_defaults(fn=cmd_index)

    l = sub.add_parser("list", help="list indexed instances")
    l.add_argument("--tier", choices=["gurobi", "mid", "large"])
    l.add_argument("--opt-only", action="store_true", help="only instances with a known optimum")
    l.add_argument("--names-only", action="store_true")
    l.set_defaults(fn=cmd_list)

    args = ap.parse_args()
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
