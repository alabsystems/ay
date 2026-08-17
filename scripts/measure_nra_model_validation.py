#!/usr/bin/env python3
"""Per-instance-list model-validation measurement: run AY on the mv-prepped
benchmark, hand the FULL stdout to the pinned Dolmen as the model, and count
the Dolmen-ACCEPTED models — the only number the mv track scores.

Built for the NRA pinning classes
(the development design notes{circle,absolute}.txt`), but the list
file is any file of instance paths relative to the benchmark root, with an
optional `# comment` suffix per line.

Pipeline parity: `prep_mv`, `dolmen_status` and the Dolmen argv come from
scripts/smtcomp_harness.py, so the solver sees the same bytes and the
validator runs the same flags as the scored mv run.

INDEPENDENCE. AY runs with `AY_COMPETITION=1` so its own internal
certification lanes are shed and the ONLY judge of the model is the external
pinned Dolmen — otherwise the measurement checks AY against itself.

NEGATIVE CONTROL. Before any instance is measured, one deliberately WRONG
model (every variable forced to 0) is fed to Dolmen for the first instance in
the list; it must come back `ModelUnsat` (`E:bad-model`). If it does not, the
validator is not actually checking and the run aborts — an all-accepting
validator would report a perfect score for any garbage.

A/B. With `--ay-base` the two binaries are run INTERLEAVED on each instance
inside one task, so both sides see the same machine conditions.

Usage:
  python3 scripts/measure_nra_model_validation.py \
      --list the development design notes \
      --ay target/release/ay --jobs 4 --timeout 1200 --out /tmp/circle.jsonl
"""
import argparse
import concurrent.futures as futures
import importlib.util
import json
import os
import pathlib
import subprocess
import sys
import tempfile

def _repo_root() -> str:
    # B29: `--repo <path>` replaces the retired AY_REPO env var.
    argv = sys.argv[1:]
    if "--repo" in argv:
        return argv[argv.index("--repo") + 1]
    # Default to the checkout this script lives in (scripts/ -> repo root).
    # Deriving it beats a hardcoded absolute path: it follows the checkout, and
    # an author's home directory must not ship in the public snapshot.
    return str(pathlib.Path(__file__).resolve().parent.parent)

REPO = pathlib.Path(_repo_root())
BENCH = pathlib.Path(os.environ.get("SMTCOMP_BENCH_ROOT",
                                    REPO / "benchmarks/smtlib-2025"))
DOLMEN = pathlib.Path(os.environ.get("DOLMEN_BIN",
                                     REPO / ".competitors/dolmen/dolmen"))

spec = importlib.util.spec_from_file_location(
    "harness", REPO / "scripts/smtcomp_harness.py")
harness = importlib.util.module_from_spec(spec)
sys.modules["harness"] = harness
spec.loader.exec_module(harness)


def dolmen_argv(bench_path):
    return [str(DOLMEN), "--time=1h", "--size=40G", "--strict=false",
            "--check-model=true", "--report-style=minimal", "--warn=-all",
            bench_path]


# AY's internal certification lanes are shed, so the external Dolmen is the
# only judge of the model. Measuring without this checks AY against itself.
AY_ENV = dict(os.environ, AY_COMPETITION="1")


def prep_to_tmp(inst):
    src = BENCH / inst
    prepped = harness.prep_mv(src.read_bytes())
    with tempfile.NamedTemporaryFile("wb", suffix=".smt2", delete=False) as f:
        f.write(prepped)
        return f.name


def negative_control(inst):
    """A deliberately WRONG model must come back E:bad-model. Without this the
    whole measurement could be reporting the verdict of a validator that
    accepts anything."""
    tmp = prep_to_tmp(inst)
    try:
        decls = []
        for line in (BENCH / inst).read_text(errors="replace").splitlines():
            s = line.strip()
            if s.startswith("(declare-fun ") and s.endswith("() Real)"):
                decls.append(f" (define-fun {s.split()[1]} () Real 0.0)")
        if not decls:
            return None
        bad = ("sat\n(\n" + "\n".join(decls) + "\n)\n").encode()
        d = subprocess.run(dolmen_argv(tmp), input=bad, capture_output=True,
                           timeout=600)
        return harness.dolmen_status(d.returncode, d.stderr)
    finally:
        pathlib.Path(tmp).unlink(missing_ok=True)


def run_side(ay_bin, tmp, inst, timeout):
    try:
        proc = subprocess.run([str(ay_bin), tmp], capture_output=True,
                              timeout=timeout, env=AY_ENV)
    except subprocess.TimeoutExpired:
        return {"instance": inst, "status": "SolverTimeout"}
    out = proc.stdout
    answer = out.split(b"\n", 1)[0].decode(errors="replace").strip()
    if answer != "sat":
        return {"instance": inst, "status": "NotSat", "answer": answer,
                "stderr": proc.stderr[-300:].decode(errors="replace")}
    has_root_obj = b"root-obj" in out
    d = subprocess.run(dolmen_argv(tmp), input=out, capture_output=True,
                       timeout=600)
    # harness.dolmen_status is the 2025 exit-code/stderr parser verbatim;
    # V_OK ("Sat") is the only point-scoring outcome, V_MODEL_UNSAT
    # ("ModelUnsat", E:bad-model) is the division-voiding one.
    status = harness.dolmen_status(d.returncode, d.stderr)
    return {"instance": inst, "status": status, "answer": answer,
            "root_obj": has_root_obj, "dolmen_exit": d.returncode,
            "dolmen_stderr": d.stderr.decode(errors="replace").strip()[-200:],
            "model": out.decode(errors="replace")}


def run_one(ay_bin, inst, timeout, ay_base=None):
    """Run head (and, interleaved in the same task, base) on one instance."""
    tmp = prep_to_tmp(inst)
    try:
        row = run_side(ay_bin, tmp, inst, timeout)
        if ay_base is not None:
            base = run_side(ay_base, tmp, inst, timeout)
            row["base_status"] = base["status"]
            row["base_root_obj"] = base.get("root_obj")
        return row
    finally:
        pathlib.Path(tmp).unlink(missing_ok=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", required=True)
    ap.add_argument("--ay", required=True)
    ap.add_argument("--ay-base", help="second binary, run INTERLEAVED per "
                                      "instance for a same-day A/B")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    insts = []
    for line in pathlib.Path(args.list).read_text().splitlines():
        inst = line.partition("#")[0].strip()
        if inst:
            insts.append(inst)

    control = negative_control(insts[0])
    print(f"negative control (deliberately wrong model): {control}", flush=True)
    if control != harness.V_MODEL_UNSAT:
        sys.exit(f"ABORT: the validator did not reject a wrong model "
                 f"({control!r}); its acceptances mean nothing.")

    rows = []
    with futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        fs = {pool.submit(run_one, args.ay, i, args.timeout, args.ay_base): i
              for i in insts}
        for fut in futures.as_completed(fs):
            row = fut.result()
            rows.append(row)
            base = f"  (base: {row['base_status']})" if "base_status" in row \
                else ""
            print(f"{row['status']:>24}  {row['instance']}{base}", flush=True)

    rows.sort(key=lambda r: r["instance"])
    pathlib.Path(args.out).write_text(
        "\n".join(json.dumps(r) for r in rows) + "\n")
    counts = {}
    for r in rows:
        counts[r["status"]] = counts.get(r["status"], 0) + 1
    print("\n=== totals ===")
    for k, v in sorted(counts.items(), key=lambda kv: -kv[1]):
        print(f"{v:4d}  {k}")
    ok = counts.get(harness.V_OK, 0)
    print(f"\nDOLMEN-ACCEPTED: {ok} / {len(rows)}")
    if any("base_status" in r for r in rows):
        bcounts = {}
        for r in rows:
            b = r.get("base_status", "n/a")
            bcounts[b] = bcounts.get(b, 0) + 1
        print("\n=== base totals (interleaved) ===")
        for k, v in sorted(bcounts.items(), key=lambda kv: -kv[1]):
            print(f"{v:4d}  {k}")
        bok = bcounts.get(harness.V_OK, 0)
        print(f"\nBASE DOLMEN-ACCEPTED: {bok} / {len(rows)}")
        regressed = [r["instance"] for r in rows
                     if r.get("base_status") == harness.V_OK
                     and r["status"] != harness.V_OK]
        print(f"REGRESSED (base accepted, head did not): {len(regressed)}")
        for i in regressed:
            print(f"  {i}")
        voiding = [r["instance"] for r in rows
                   if r["status"] == harness.V_MODEL_UNSAT]
        print(f"HEAD ModelUnsat (division-voiding): {len(voiding)}")
        for i in voiding:
            print(f"  {i}")


main()
