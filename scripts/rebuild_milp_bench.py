#!/usr/bin/env python3
# ay-script: rebuild-milp-bench
"""Rebuild ~/ay-bench/milp from MIPLIB 2017 — instances, .solu and manifest.json.

WHY THIS EXISTS. On 2026-08-06 `~/ay-bench/milp/` was found EMPTY. That directory
held the instances and the `manifest.json` for `scripts/ay_gurobi_closure.py`, the
authoritative AY-vs-Gurobi gate, so the gate had been silently inoperable — it
could not run at all, and nothing surfaced that until someone went looking for a
Gurobi number. Reports in this repo cite instance sets BY PATH, and paths rot.

The instance NAMES survived only because four committed gate reports
(the development design notes and friends) recorded them. They are embedded below so
the corpus is reconstructible from THIS REPO ALONE, which is the actual fix.

Not recoverable: the original closure corpus was 101 instances and WHICH 101 died
with the old manifest. This rebuilds the 154-name working set (151 usable), a
superset. Three names carry non-terminal .solu status and are excluded because the
driver requires OPTIMAL/INFEASIBLE/UNBOUNDED references:
milo-v13-4-3d-4-0 (=best=), pb-market-split8-70-4 and supportcase30 (=unkn=).

Usage:  scripts/rebuild_milp_bench.py [--root ~/ay-bench/milp] [--jobs 4]
"""

import argparse, gzip, hashlib, json, os, sys, urllib.request
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor

# The manifest schema is `milp_corpus.py`'s, and its consumers select and check on
# fields this script used to drop: `scripts/milp_portfolio.py --tier gurobi` (its
# DOCUMENTED default) selected nothing from an untiered manifest, and its soundness
# alarm compares against `ref_obj`, so a manifest without one made the alarm inert
# and silent. Shape and tier come from the same code that built the original.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from milp_corpus import scan_mps, tier_of  # noqa: E402

INSTANCE_URL = "https://miplib.zib.de/WebData/instances/{name}.mps.gz"
SOLU_URL = "https://miplib.zib.de/downloads/miplib2017-v27.solu"
SOLU_NAME = "miplib2017-v27.solu"
TERMINAL = {"=opt=": "opt", "=inf=": "inf", "=unbd=": "unbd"}

NAMES = [
    "22433",
    "23588",
    "aflow30a",
    "app2-2",
    "assign1-5-8",
    "b-ball",
    "beavma",
    "berlin_5_8_0",
    "bg512142",
    "bienst1",
    "bienst2",
    "blend2",
    "bppc4-08",
    "bppc8-02",
    "bppc8-09",
    "breastcancer-regularized",
    "cod105",
    "control30-3-2-3",
    "csched007",
    "csched008",
    "csched010",
    "danoint",
    "dcmulti",
    "dell",
    "dsbmip",
    "ej",
    "enlight11",
    "enlight4",
    "enlight8",
    "enlight9",
    "enlight_hard",
    "exp-1-500-5-5",
    "f2gap201600",
    "f2gap401600",
    "f2gap40400",
    "f2gap801600",
    "fhnw-binpack4-18",
    "fhnw-binpack4-4",
    "fhnw-sq2",
    "fiber",
    "flugpl",
    "flugplinf",
    "g200x740",
    "g503inf",
    "gen",
    "gen-ip002",
    "gen-ip016",
    "gen-ip021",
    "gen-ip036",
    "gen-ip054",
    "glass4",
    "gmu-35-40",
    "gmu-35-50",
    "gr4x6",
    "graphdraw-domain",
    "graphdraw-gemcutter",
    "gsvm2rl3",
    "gt2",
    "haprp",
    "ic97_potential",
    "ic97_tension",
    "k16x240b",
    "khb05250",
    "mad",
    "markshare1",
    "markshare2",
    "markshare_4_0",
    "markshare_5_0",
    "mas74",
    "mas76",
    "mik-250-20-75-1",
    "mik-250-20-75-2",
    "mik-250-20-75-3",
    "mik-250-20-75-4",
    "mik-250-20-75-5",
    "milo-v13-4-3d-3-0",
    "milo-v13-4-3d-4-0",
    "misc05inf",
    "misc07",
    "mod008inf",
    "mtest4ma",
    "neos-1396125",
    "neos-1425699",
    "neos-1430701",
    "neos-1442119",
    "neos-2624317-amur",
    "neos-2626858-aoos",
    "neos-2652786-brda",
    "neos-2656603-coxs",
    "neos-2657525-crna",
    "neos-3046601-motu",
    "neos-3046615-murg",
    "neos-3072252-nete",
    "neos-3118745-obra",
    "neos-3421095-cinca",
    "neos-3610040-iskar",
    "neos-3610051-istra",
    "neos-3610173-itata",
    "neos-3611447-jijia",
    "neos-3611689-kaihu",
    "neos-3627168-kasai",
    "neos-3754480-nidda",
    "neos-4333596-skien",
    "neos-4338804-snowy",
    "neos-4650160-yukon",
    "neos-4954672-berkel",
    "neos-5140963-mincio",
    "neos-5192052-neckar",
    "neos-631517",
    "neos-807639",
    "neos-860300",
    "neos-911970",
    "neos16",
    "neos17",
    "neos5",
    "neos859080",
    "newdano",
    "nexp-50-20-1-1",
    "nexp-50-20-4-2",
    "nh97_potential",
    "nh97_tension",
    "noswot",
    "nsa",
    "opt1217",
    "p0201",
    "p2m2p1m1p0n100",
    "pb-market-split8-70-4",
    "pigeon-08",
    "pigeon-10",
    "pigeon-13",
    "pk1",
    "ponderthis0517-inf",
    "probportfolio",
    "prod1",
    "qiu",
    "qnet1",
    "qnet1_o",
    "r50x360",
    "ran12x21",
    "ran13x13",
    "ran14x18-disj-8",
    "rlp1",
    "rout",
    "sp150x300d",
    "stein15inf",
    "stein45inf",
    "stein9inf",
    "supportcase14",
    "supportcase16",
    "supportcase26",
    "supportcase30",
    "timtab1",
    "timtab1CUTS",
    "tr12-30"
]


def fetch(url: str, dest: Path, timeout: int = 300) -> None:
    dest.parent.mkdir(parents=True, exist_ok=True)
    tmp = dest.with_suffix(dest.suffix + ".part")
    with urllib.request.urlopen(url, timeout=timeout) as r, open(tmp, "wb") as fh:
        fh.write(r.read())
    tmp.replace(dest)


def parse_solu(path: Path) -> dict:
    """name -> (status token, reference objective or None).

    The objective is the third field. Every `=opt=` entry in miplib2017-v27.solu
    carries one (774/774); `=inf=`, `=unbd=` and `=unkn=` carry none and none
    exists to carry, so a null `ref_obj` there is the truth, not a gap.
    """
    out = {}
    for raw in path.read_text(encoding="utf-8").splitlines():
        f = raw.split()
        if len(f) >= 2 and f[0].startswith("="):
            val = None
            if len(f) > 2:
                try:
                    val = float(f[2])
                except ValueError:
                    val = None
            out[f[1]] = (f[0], val)
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=str(Path.home() / "ay-bench" / "milp"))
    ap.add_argument("--jobs", type=int, default=4)
    args = ap.parse_args()
    root = Path(args.root).expanduser()
    inst_dir, meta_dir = root / "instances", root / "meta"
    inst_dir.mkdir(parents=True, exist_ok=True)
    meta_dir.mkdir(parents=True, exist_ok=True)

    solu_path = meta_dir / SOLU_NAME
    if not solu_path.exists():
        print("fetching", SOLU_URL)
        fetch(SOLU_URL, solu_path)
    solu = parse_solu(solu_path)
    print("solu entries:", len(solu))

    def one(name: str):
        dest = inst_dir / (name + ".mps.gz")
        if dest.exists() and dest.stat().st_size:
            return name, "skip"
        try:
            fetch(INSTANCE_URL.format(name=name), dest)
            return name, "ok"
        except Exception as exc:                      # noqa: BLE001
            return name, "FAIL " + type(exc).__name__

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(one, NAMES))
    failed = [n for n, s in results if s.startswith("FAIL")]
    print("fetched ok=%d skip=%d fail=%d" % (
        sum(1 for _, s in results if s == "ok"),
        sum(1 for _, s in results if s == "skip"),
        len(failed)))
    if failed:
        print("FAILED:", " ".join(failed), file=sys.stderr)

    instances, rejected = {}, []
    for name in NAMES:
        token, ref_obj = solu.get(name, (None, None))
        if token not in TERMINAL:
            rejected.append((name, "non-terminal .solu status %r" % token))
            continue
        p = inst_dir / (name + ".mps.gz")
        if not p.exists():
            rejected.append((name, "not downloaded"))
            continue
        try:
            with gzip.open(p, "rb") as fh:
                head = fh.read(4000)
            if b"ROWS" not in head:
                rejected.append((name, "no ROWS section"))
                continue
        except Exception as exc:                      # noqa: BLE001
            rejected.append((name, "gunzip: " + str(exc)[:40]))
            continue
        info = scan_mps(p)
        if "error" in info:
            rejected.append((name, "scan_mps: " + str(info["error"])[:40]))
            continue
        blob = p.read_bytes()
        instances[name] = {
            "file": str(p),
            "tier": tier_of(info),
            "ref_status": TERMINAL[token],
            "ref_obj": ref_obj,
            "sha256": hashlib.sha256(blob).hexdigest(),
            "size_bytes": len(blob),
            **info,
        }

    manifest = {
        "provenance": {
            "collection": "MIPLIB 2017",
            "source": INSTANCE_URL,
            "solu": SOLU_URL,
            "rebuilt_by": "scripts/rebuild_milp_bench.py",
            "note": (
                "Name list recovered from committed the development design notes after "
                "~/ay-bench/milp was lost. SUPERSET of the original 101-instance closure "
                "corpus, whose exact membership died with the old manifest."
            ),
        },
        "instances": instances,
    }
    (root / "manifest.json").write_text(
        json.dumps(manifest, indent=1, sort_keys=True), encoding="utf-8")
    tiers: dict = {}
    for e in instances.values():
        tiers[e["tier"]] = tiers.get(e["tier"], 0) + 1
    n_obj = sum(1 for e in instances.values() if e["ref_obj"] is not None)
    print("manifest instances: %d  tiers=%s  with ref_obj: %d/%d"
          % (len(instances), tiers, n_obj, len(instances)))
    for n, why in rejected:
        print("  excluded %-24s %s" % (n, why))
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
