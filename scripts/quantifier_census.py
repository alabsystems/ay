#!/usr/bin/env python3
# ay-script: quantifier-census
"""Per-file quantifier-bucket census for the z3-parity campaign.

`scratchpad/divscan.py` answers "how many files does AY decide that z3 does";
this answers the next question: *for the files AY loses to a quantifier reason,
which gate declined, and how much instantiation happened first.* It is the
harness behind sections 2.4/2.5 of
the development design notes, and it
is committed so that every later stage of that plan is measured against a
reproducible baseline rather than against prose.

Four subcommands:

  select     Merge divscan JSONL records and emit the quantifier rows: files
             where AY's reason-unknown mentions a quantifier. `--scope bucket`
             (default) also requires the SCAN's oracle to have decided the file,
             which reproduces the plan's 202; `--scope all` emits all 337 and
             leaves bucket membership to the `z3` subcommand, which is the only
             way a stronger oracle can ADD files to the bucket.
  run        Solve each bucket file under one posture with `--stats-full
             --debug-cert`, and record verdict, instantiation counts, the
             `:quantifier.*` counters, the reason-unknown, and which gate
             declined. One JSON object per line.
  z3         Oracle side: how z3 routes each bucket file (`-st`), recording
             `:quant-instantiations` and `:qsat-num-rounds` so that "z3 solves
             this by preprocessing, not by instantiation" is a measurement.
             Any run that printed `(error` is classified `error`, never by its
             printed verdict.
  report     Histogram a `run` output: per-flag counts, a single-blocker
             attribution, the posture-flip count, the qsu authored-root shape
             census, and the oracle routing split.

Resource discipline (AGENTS.md): AY self-terminates on `-T`, so no child is ever
SIGKILLed at the wrapper; a straggler is killed as a whole process group.
Concurrency defaults to 2 because this host runs other agents' builds. Nothing
in the output depends on a wall time: verdicts, gate identities and counters are
load-independent, wall times are recorded but are not evidence.

The oracle is a variable, not a constant. z3 4.16 answers through its own error
recovery on logics it cannot parse, so a bucket computed against it is a FLOOR.
Always run the `z3` subcommand for every oracle you intend to quote, and quote
the version and hash the rows carry.

Example (paths under $HOME; never a target or output directory in /tmp):

    scripts/quantifier_census.py select --scope all --records DIR/divscan_r1.jsonl \\
        DIR/divscan_r1b.jsonl DIR/divscan_qflia.jsonl DIR/divscan_fp_fixed.jsonl \\
        --out WORK/bucket.jsonl
    scripts/quantifier_census.py run --bucket WORK/bucket.jsonl --posture default \\
        --ay ~/ay-bench/target-z3/release/ay --out WORK/census_default.jsonl
    scripts/quantifier_census.py run --bucket WORK/bucket.jsonl --posture fast \\
        --ay ~/ay-bench/target-z3/release/ay --out WORK/census_fast.jsonl
    scripts/quantifier_census.py z3 --bucket WORK/bucket.jsonl \\
        --z3 ~/ay-bench/oracles/z3-5.1.0-arm64-osx-13.3/bin/z3 \\
        --out WORK/oracle_510.jsonl
    scripts/quantifier_census.py report WORK/census_*.jsonl WORK/oracle_*.jsonl

The frozen stage-0 result of exactly that sequence is committed at
the development design notes, and
`report` accepts it directly.
"""

import argparse
import collections
import concurrent.futures as cf
import json
import os
import re
import subprocess
import sys
import time

VERDICTS = ("sat", "unsat", "unknown")

# Gate attribution markers. Each is a substring test against the `--debug-cert`
# stderr stream; the emitting sites are named so a rename is traceable.
GATE_MARKERS = {
    # result_mapping/quantified_unsat.rs:154 (`debug_leg`), DOWNGRADE leg.
    "qsu_downgrade": "CERT/qsu leg DOWNGRADE",
    # result_mapping.rs:2637 / :2710 / :2791 / :3371.
    "degrade_277": "CERT/degrade@277",
    "degrade_298": "CERT/degrade@298",
    "degrade_343": "CERT/degrade@343",
    "degrade_802": "CERT/degrade@802",
    # mbqi.rs:550 — the finite-model / bit-vector / rest dispatch announcement.
    "fmq_dispatch": "FMQ dispatch:",
}

# `CERT/classify: result=Unsat` at result_mapping.rs:2547 — an internal UNSAT
# that the file then failed to publish. Section 2.4's supporting count.
CLASSIFY_UNSAT = re.compile(r"^CERT/classify: result=Unsat\b")

QSU_SHAPE = re.compile(
    r"^CERT/qsu shape roots=(\d+) ground=(\d+) forall=(\d+) "
    r"not_exists=(\d+) other_quant=(\d+)"
)
QSU_LEG = re.compile(r"^CERT/qsu leg (\w+)=(\w+)")
REASON = re.compile(r"\(:reason-unknown\s+([^)]*(?:\)[^)]*)*?)\)\s*$", re.MULTILINE)
STAT_ROW = re.compile(r"^\s*:([A-Za-z0-9_.\-]+)\s+(-?\d+(?:\.\d+)?)\s*$")

# Counters copied out of the `(:statistics …)` block into every census row.
TRACKED_STATS = (
    "ematching-rounds-completed",
    "ematching-instances-created",
    "quantifier.proxies_minted",
    "quantifier.guarded_instances_created",
    "quantifier.guarded_instances_asserted",
    "quantifier.mbqi.rounds",
    "quantifier.mbqi.candidates_probed",
    "quantifier.cegqi.rounds",
    "quantifier.cegqi.ce_lemmas",
)

POSTURES = {
    "default": [],
    "fast": ["--rigor", "fast"],
}


def repo_root():
    return os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


# --------------------------------------------------------------------------
# select
# --------------------------------------------------------------------------


def merge_records(paths):
    """Later files supersede earlier ones per `file` key.

    `divscan_fp_fixed.jsonl` is a corrective re-measurement of the
    floating-point divisions and must be passed last.
    """
    merged = {}
    for path in paths:
        with open(path) as handle:
            for line in handle:
                line = line.strip()
                if not line:
                    continue
                rec = json.loads(line)
                merged[rec["file"]] = rec
    return merged


def select_bucket(merged, scope):
    """Rows where AY lost to a quantifier reason.

    `scope="bucket"` additionally requires that the SCAN's oracle decided the
    file, which is how the plan's 202 was computed. That intersection is only as
    good as the oracle: z3 4.16 does not recognise several floating-point logic
    names, error-recovers past the declarations and answers anyway, so the scan
    scores those divisions as undecided and their files never enter the bucket
    at all. `scope="all"` emits every quantifier-reason row and lets the `z3`
    subcommand decide membership per oracle — which is the only way a stronger
    oracle can ever ADD files.
    """
    out = []
    for rec in merged.values():
        if "quantifier" not in rec.get("ay_reason", ""):
            continue
        if scope == "bucket" and rec["z3"] not in ("sat", "unsat"):
            continue
        out.append(rec)
    out.sort(key=lambda r: (r["division"], r["file"]))
    return out


def cmd_select(args):
    merged = merge_records(args.records)
    bucket = select_bucket(merged, args.scope)
    with open(args.out, "w") as handle:
        for rec in bucket:
            handle.write(
                json.dumps(
                    {
                        "division": rec["division"],
                        "file": rec["file"],
                        "scan_z3": rec["z3"],
                        "scan_ay_reason": rec.get("ay_reason", ""),
                    }
                )
                + "\n"
            )
    reasons = collections.Counter(r.get("ay_reason", "") for r in bucket)
    z3v = collections.Counter(r["z3"] for r in bucket)
    print(f"merged records: {len(merged)}")
    print(f"scope={args.scope} rows: {len(bucket)}  -> {args.out}")
    print(f"  scan-oracle verdict: {dict(z3v)}")
    for reason, count in reasons.most_common():
        print(f"  {reason}: {count}")
    return 0


# --------------------------------------------------------------------------
# run
# --------------------------------------------------------------------------


def parse_stats(stderr):
    """Pull the tracked counters out of the `(:statistics …)` block."""
    found = {}
    for line in stderr.splitlines():
        m = STAT_ROW.match(line)
        if not m:
            continue
        key, value = m.group(1), m.group(2)
        if key in TRACKED_STATS:
            found[key] = int(float(value))
    return found


def parse_reason(text):
    m = REASON.search(text)
    if not m:
        return ""
    return re.sub(r"\s+", " ", m.group(1)).strip()


def scan_debug_cert(stderr):
    """Gate attribution. Streams the trace; never retains it."""
    flags = {name: False for name in GATE_MARKERS}
    legs = {}
    shape = None
    classify_unsat = 0
    for line in stderr.splitlines():
        for name, marker in GATE_MARKERS.items():
            if not flags[name] and marker in line:
                flags[name] = True
        if CLASSIFY_UNSAT.match(line):
            classify_unsat += 1
        m = QSU_SHAPE.match(line)
        if m and shape is None:
            shape = {
                "roots": int(m.group(1)),
                "ground": int(m.group(2)),
                "forall": int(m.group(3)),
                "not_exists": int(m.group(4)),
                "other_quant": int(m.group(5)),
            }
        m = QSU_LEG.match(line)
        if m:
            legs[m.group(1)] = m.group(2) == "true"
    return flags, legs, shape, classify_unsat


def run_one(job):
    ay, posture, timeout, division, rel_path, abs_path, z3 = job
    cmd = [ay, "--quiet", "--stats-full", "--debug-cert", f"-T:{timeout}"]
    cmd += POSTURES[posture]
    cmd.append(abs_path)
    start = time.time()
    killed = False
    proc = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        errors="replace",
        start_new_session=True,
    )
    try:
        out, err = proc.communicate(timeout=timeout + 10)
    except subprocess.TimeoutExpired:
        # AY self-terminates on -T; reaching here means the wrapper outlived its
        # own deadline. Kill the whole group so no solver child is orphaned.
        try:
            os.killpg(proc.pid, 9)
        except ProcessLookupError:
            pass
        out, err = proc.communicate()
        killed = True
    wall = time.time() - start

    lines = [l.strip() for l in out.splitlines() if l.strip() in VERDICTS]
    if killed:
        verdict = "wrapper-timeout"
    elif "(error" in out or "(error" in err:
        verdict = "error"
    else:
        verdict = lines[-1] if lines else "none"

    flags, legs, shape, classify_unsat = scan_debug_cert(err)
    rec = {
        "division": division,
        "file": rel_path,
        "posture": posture,
        "z3": z3,
        "ay": verdict,
        "ay_wall": round(wall, 3),
        "reason": parse_reason(err + "\n" + out),
        "gates": flags,
        "classify_unsat_count": classify_unsat,
    }
    rec.update(parse_stats(err))
    if legs:
        rec["qsu_legs"] = legs
    if shape:
        rec["qsu_shape"] = shape
    return rec


def cmd_run(args):
    root = os.path.abspath(args.corpus_root)
    bucket = []
    with open(args.bucket) as handle:
        for line in handle:
            line = line.strip()
            if line:
                bucket.append(json.loads(line))

    done = set()
    if args.resume and os.path.exists(args.out):
        with open(args.out) as handle:
            for line in handle:
                try:
                    done.add(json.loads(line)["file"])
                except Exception:
                    pass

    jobs = []
    missing = 0
    for rec in bucket:
        rel = rec["file"]
        if rel in done:
            continue
        abs_path = rel if os.path.isabs(rel) else os.path.join(root, rel)
        if not os.path.exists(abs_path):
            missing += 1
            continue
        jobs.append(
            (
                args.ay,
                args.posture,
                args.timeout,
                rec["division"],
                rel,
                abs_path,
                rec.get("scan_z3", rec.get("z3", "")),
            )
        )
    print(
        f"posture={args.posture} files={len(jobs)} (skipped {len(done)} done, "
        f"{missing} missing) jobs={args.jobs} T={args.timeout}s",
        flush=True,
    )
    out = open(args.out, "a")
    n = 0
    with cf.ThreadPoolExecutor(args.jobs) as ex:
        for rec in ex.map(run_one, jobs):
            out.write(json.dumps(rec) + "\n")
            out.flush()
            n += 1
            if n % 25 == 0:
                print(f"  {n}/{len(jobs)}", flush=True)
    out.close()
    print(f"wrote {n} rows to {args.out}")
    return 0


# --------------------------------------------------------------------------
# z3 (oracle side)
# --------------------------------------------------------------------------

Z3_STAT = re.compile(r"^\s*:([a-z0-9\-]+)\s+(\d+)")


def oracle_provenance(path):
    """Path, self-reported version and content hash of an oracle binary.

    Recorded on EVERY row. A reference solver's printed verdict is only as
    trustworthy as the build that printed it, and this campaign has now been
    misled twice by numbers whose oracle was not stated.
    """
    version = ""
    try:
        version = subprocess.run(
            [path, "--version"], capture_output=True, text=True, timeout=30
        ).stdout.strip()
    except Exception:
        pass
    digest = ""
    try:
        import hashlib

        h = hashlib.sha256()
        with open(path, "rb") as handle:
            for chunk in iter(lambda: handle.read(1 << 20), b""):
                h.update(chunk)
        digest = h.hexdigest()
    except OSError:
        pass
    return {"oracle_path": path, "oracle_version": version, "oracle_sha256": digest}


def run_z3_one(job):
    z3, timeout, division, rel_path, abs_path, provenance = job
    cmd = [z3, f"-T:{timeout}", "-st", abs_path]
    start = time.time()
    proc = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        errors="replace",
        start_new_session=True,
    )
    try:
        out, err = proc.communicate(timeout=timeout + 10)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, 9)
        except ProcessLookupError:
            pass
        out, err = proc.communicate()
    wall = time.time() - start
    # A reference solver's printed verdict is not evidence that it understood the
    # input: z3 4.16 error-recovers past unknown FP sorts and answers anyway.
    # Any `(error` output disqualifies the run (2026-09-06-baseline.md).
    if "(error" in out or "(error" in err:
        verdict = "error"
    else:
        lines = [l.strip() for l in out.splitlines() if l.strip() in VERDICTS]
        verdict = lines[-1] if lines else "none"
    stats = {}
    for line in (out + "\n" + err).splitlines():
        m = Z3_STAT.match(line)
        if m:
            stats[m.group(1)] = int(m.group(2))
    rec = {
        "division": division,
        "file": rel_path,
        "posture": "z3",
        "z3_verdict": verdict,
        "z3_wall": round(wall, 3),
        "quant_instantiations": stats.get("quant-instantiations", 0),
        "qsat_num_rounds": stats.get("qsat-num-rounds", 0),
        "qsat_num_predicates": stats.get("qsat-num-predicates", 0),
    }
    rec.update(provenance)
    return rec


def cmd_z3(args):
    root = os.path.abspath(args.corpus_root)
    provenance = oracle_provenance(args.z3)
    done = set()
    if args.resume and os.path.exists(args.out):
        with open(args.out) as handle:
            for line in handle:
                try:
                    done.add(json.loads(line)["file"])
                except Exception:
                    pass
    jobs = []
    with open(args.bucket) as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            rec = json.loads(line)
            rel = rec["file"]
            if rel in done:
                continue
            abs_path = rel if os.path.isabs(rel) else os.path.join(root, rel)
            if os.path.exists(abs_path):
                jobs.append(
                    (args.z3, args.timeout, rec["division"], rel, abs_path, provenance)
                )
    print(f"oracle: {provenance}", flush=True)
    print(f"oracle: {len(jobs)} files jobs={args.jobs} T={args.timeout}s", flush=True)
    out = open(args.out, "a")
    n = 0
    with cf.ThreadPoolExecutor(args.jobs) as ex:
        for rec in ex.map(run_z3_one, jobs):
            out.write(json.dumps(rec) + "\n")
            out.flush()
            n += 1
            if n % 25 == 0:
                print(f"  {n}/{len(jobs)}", flush=True)
    out.close()
    print(f"wrote {n} rows to {args.out}")
    return 0


# --------------------------------------------------------------------------
# report
# --------------------------------------------------------------------------

# Single-blocker attribution, applied in this order. The plan's section 2.4
# table is a partition, but does not state its own priority; this order is the
# one that reproduces its row labels, and it is stated here so a disagreement
# with the prose is legible as a disagreement rather than as noise.
BLOCKER_ORDER = [
    ("cegqi-no-degrade", lambda r: r["reason_class"] == "cegqi" and not any_degrade(r)),
    ("degrade@298", lambda r: r["gates"]["degrade_298"]),
    ("qsu-DOWNGRADE", lambda r: r["gates"]["qsu_downgrade"]),
    (
        "unhandled-no-gate",
        lambda r: r["reason_class"] == "unhandled" and not any_gate(r),
    ),
    ("FMQ-dispatch", lambda r: r["gates"]["fmq_dispatch"]),
    ("degrade@343/@802", lambda r: r["gates"]["degrade_343"] or r["gates"]["degrade_802"]),
    ("degrade@277", lambda r: r["gates"]["degrade_277"]),
]


def any_degrade(rec):
    g = rec["gates"]
    return g["degrade_277"] or g["degrade_298"] or g["degrade_343"] or g["degrade_802"]


def any_gate(rec):
    return any(rec["gates"].values())


def reason_class(reason):
    if "quantifier-cegqi" in reason:
        return "cegqi"
    if "quantifier-unhandled" in reason:
        return "unhandled"
    if "quantifier-round-limit" in reason:
        return "round-limit"
    return "other"


def classify(rec):
    rec["reason_class"] = reason_class(rec.get("reason", ""))
    for name, pred in BLOCKER_ORDER:
        if pred(rec):
            return name
    return "unattributed"


def cmd_report(args):
    rows = []
    for path in args.census:
        with open(path) as handle:
            for line in handle:
                line = line.strip()
                if not line:
                    continue
                rec = json.loads(line)
                if rec.get("record") == "provenance":
                    continue
                rows.append(rec)
    oracle_rows = [r for r in rows if r.get("posture") == "z3"]
    rows = [r for r in rows if r.get("posture") != "z3"]
    by_posture = collections.defaultdict(list)
    for r in rows:
        by_posture[r["posture"]].append(r)
    by_oracle = collections.defaultdict(dict)
    for r in oracle_rows:
        by_oracle[r.get("oracle_version") or r.get("oracle_path", "?")][r["file"]] = r

    # The bucket is per-oracle. z3 4.16 scores whole floating-point divisions
    # undecided (it cannot parse their logic names), so files that a stronger
    # oracle decides never entered the plan's 202 at all. Report every oracle's
    # bucket size, and never quote one without naming which build produced it.
    for name, table in sorted(by_oracle.items()):
        decided = [r for r in table.values() if r["z3_verdict"] in ("sat", "unsat")]
        errors = [r for r in table.values() if r["z3_verdict"] == "error"]
        print(f"\n=== oracle: {name}")
        sample = next(iter(table.values()))
        print(f"    path   {sample.get('oracle_path')}")
        print(f"    sha256 {sample.get('oracle_sha256')}")
        print(f"    rows {len(table)}  decided {len(decided)}  error {len(errors)}")
        print(
            "    verdicts:",
            dict(collections.Counter(r["z3_verdict"] for r in table.values())),
        )
        print(
            "    bucket split:",
            dict(collections.Counter(r["z3_verdict"] for r in decided)),
        )
        route = collections.Counter()
        for r in decided:
            if r.get("qsat_num_rounds", 0) > 0:
                route["qsat (MBP quantifier elimination)"] += 1
            elif r.get("quant_instantiations", 0) > 0:
                route["quant-instantiations > 0"] += 1
            else:
                route["no quantifier statistics at all"] += 1
        for label, count in route.most_common():
            print(f"    {label:36} {count}")

    # Posture flips: the addressable residual is the files the pending posture
    # change does NOT already gain. A stage that "gains" one of those has gained
    # nothing (plan section 6, risk 7).
    if "default" in by_posture and "fast" in by_posture:
        dflt = {r["file"]: r for r in by_posture["default"]}
        fast = {r["file"]: r for r in by_posture["fast"]}
        flips = [
            f
            for f in dflt
            if f in fast
            and dflt[f]["ay"] not in ("sat", "unsat")
            and fast[f]["ay"] in ("sat", "unsat")
        ]
        reverse = [
            f
            for f in dflt
            if f in fast
            and dflt[f]["ay"] in ("sat", "unsat")
            and fast[f]["ay"] not in ("sat", "unsat")
        ]
        print(f"\n=== posture flips: fast decides, default does not: {len(flips)}")
        print(f"=== posture flips: default decides, fast does not: {len(reverse)}")
        for name, table in sorted(by_oracle.items()):
            unsat = {
                f for f, r in table.items() if r["z3_verdict"] == "unsat"
            }
            decided = {
                f
                for f, r in table.items()
                if r["z3_verdict"] in ("sat", "unsat")
            }
            in_bucket = [f for f in dflt if f in decided]
            residual = [f for f in in_bucket if f in unsat and f not in flips]
            print(
                f"=== [{name}] bucket {len(in_bucket)}; z3-unsat "
                f"{len([f for f in in_bucket if f in unsat])}; of those, "
                f"fast already gains {len([f for f in flips if f in unsat])}; "
                f"addressable residual {len(residual)}"
            )
            # Section 2.4 is a histogram over exactly this residual, in the
            # DEFAULT posture. Print it here so the table can be compared row
            # for row instead of against the whole quantifier-reason set.
            recs = [dflt[f] for f in residual]
            blockers = collections.Counter(classify(r) for r in recs)
            for label, _ in BLOCKER_ORDER:
                print(f"      {label:20} {blockers[label]}")
            print(f"      {'unattributed':20} {blockers['unattributed']}")
            zero_inst = sum(
                1 for r in recs if r.get("ematching-instances-created", 0) == 0
            )
            print(
                f"      zero E-matching instances {zero_inst}; reached internal "
                f"CERT/classify result=Unsat "
                f"{sum(1 for r in recs if r.get('classify_unsat_count', 0) > 0)}"
            )
            divs = collections.Counter(r["division"] for r in recs)
            print(
                "      top divisions: "
                + ", ".join(f"{d} {c}" for d, c in divs.most_common(8))
            )
            # Section 2.5, on the same residual: how the oracle actually solves
            # them. A file the oracle decides with NO quantifier statistics is
            # not evidence that more instantiation is the route.
            route = collections.Counter()
            for f in residual:
                r = table[f]
                if r.get("qsat_num_rounds", 0) > 0:
                    route["qsat (MBP; this plan does not implement it)"] += 1
                elif r.get("quant_instantiations", 0) > 0:
                    route["quant-instantiations > 0"] += 1
                else:
                    route["no quantifier statistics at all"] += 1
            for label, count in route.most_common():
                print(f"      oracle route: {label:44} {count}")

    for posture, recs in sorted(by_posture.items()):
        print(f"\n=== posture: {posture}   files: {len(recs)}")
        print("verdicts:", dict(collections.Counter(r["ay"] for r in recs)))
        print(
            "reason classes:",
            dict(collections.Counter(reason_class(r.get("reason", "")) for r in recs)),
        )
        flag_counts = collections.Counter()
        for r in recs:
            for name, fired in r["gates"].items():
                if fired:
                    flag_counts[name] += 1
        print("gate flags fired (NOT exclusive):")
        for name, _ in GATE_MARKERS.items():
            print(f"  {name:16} {flag_counts[name]}")
        blockers = collections.Counter(classify(r) for r in recs)
        print("single-blocker attribution:")
        for name, _ in BLOCKER_ORDER:
            print(f"  {name:20} {blockers[name]}")
        print(f"  {'unattributed':20} {blockers['unattributed']}")
        inst = [r.get("ematching-instances-created", 0) for r in recs]
        print(
            f"ematching-instances-created: zero on {sum(1 for i in inst if i == 0)} "
            f"of {len(inst)}, max {max(inst) if inst else 0}"
        )
        print(
            "reached internal CERT/classify result=Unsat: "
            f"{sum(1 for r in recs if r.get('classify_unsat_count', 0) > 0)}"
        )
        for key in TRACKED_STATS:
            if not key.startswith("quantifier."):
                continue
            values = [r.get(key) for r in recs]
            present = [v for v in values if v is not None]
            nonzero = sum(1 for v in present if v)
            print(
                f"  :{key:42} present on {len(present)}/{len(recs)}, "
                f"nonzero on {nonzero}, max {max(present) if present else 0}"
            )
        # The qsu authored-root shape census, under BOTH readings of "forall".
        # `CERT/qsu shape` reports four counts per file and a file usually has
        # several kinds of root at once, so "35 are forall-only" depends on
        # whether a co-occurring nested quantifier disqualifies the file. The
        # loose reading (a `forall` root present, no negated `exists`) is the one
        # the plan's prose reproduces; the strict reading (a `forall` root and
        # NOTHING else quantified) is much smaller, and the difference is the
        # measure of how much of that bucket is genuinely the plain conjunctive
        # shape the two builder legs do not cover.
        loose = collections.Counter()
        strict = collections.Counter()
        legs = collections.Counter()
        for r in recs:
            s = r.get("qsu_shape")
            if not s:
                continue
            if s["forall"] and not s["not_exists"] and not s["other_quant"]:
                strict["forall-only"] += 1
            elif s["not_exists"] and not s["forall"] and not s["other_quant"]:
                strict["not_exists-only"] += 1
            else:
                strict["other"] += 1
            if s["forall"] and not s["not_exists"]:
                loose["forall"] += 1
            elif s["not_exists"] and not s["forall"]:
                loose["not_exists"] += 1
            else:
                loose["other"] += 1
            legs[
                tuple(sorted(r.get("qsu_legs", {}).items()))
            ] += 1
        if strict:
            print("qsu authored-root shape, loose (plan's reading):", dict(loose))
            print("qsu authored-root shape, strict (no other quantified root):", dict(strict))
            for combo, count in legs.most_common(4):
                print(f"  qsu legs {dict(combo)}: {count}")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    s = sub.add_parser("select", help="emit the quantifier bucket from divscan records")
    s.add_argument("--records", nargs="+", required=True)
    s.add_argument("--out", required=True)
    s.add_argument(
        "--scope",
        choices=("bucket", "all"),
        default="bucket",
        help="bucket: quantifier rows the SCAN's oracle decided (the plan's 202). "
        "all: every quantifier-reason row, so a stronger oracle can add files.",
    )
    s.set_defaults(func=cmd_select)

    r = sub.add_parser("run", help="census one posture over a bucket")
    r.add_argument("--bucket", required=True)
    r.add_argument("--out", required=True)
    r.add_argument("--posture", choices=sorted(POSTURES), default="default")
    r.add_argument("--corpus-root", default=repo_root())
    r.add_argument("--ay", default=os.path.expanduser(os.environ.get("AY", "target/release/ay")))
    r.add_argument("--timeout", type=int, default=10)
    r.add_argument("--jobs", type=int, default=2)
    r.add_argument("--resume", action="store_true")
    r.set_defaults(func=cmd_run)

    o = sub.add_parser("z3", help="oracle side: how z3 routes each bucket file")
    o.add_argument("--bucket", required=True)
    o.add_argument("--out", required=True)
    o.add_argument("--corpus-root", default=repo_root())
    o.add_argument("--z3", default=os.environ.get("Z3", "/opt/homebrew/bin/z3"))
    o.add_argument("--timeout", type=int, default=20)
    o.add_argument("--jobs", type=int, default=2)
    o.add_argument("--resume", action="store_true")
    o.set_defaults(func=cmd_z3)

    p = sub.add_parser("report", help="histogram a census output")
    p.add_argument("census", nargs="+")
    p.set_defaults(func=cmd_report)

    args = ap.parse_args()
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
