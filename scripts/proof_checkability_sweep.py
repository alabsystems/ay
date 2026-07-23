#!/usr/bin/env python3
"""Proof-checkability sweep: for every UNSAT verdict AY reports on a corpus of
.smt2 files, determine whether the result is INDEPENDENTLY kernel-checkable —
via the complete-conflict Lean firewall (`--emit-firewall-lean`, a `theorem
no_model` grounded in `firewall_combined_unsat` over the FULL parsed
assertion set, kernel-checked by real Lean with axioms confined to
{propext, Classical.choice, Quot.sound}, no sorryAx) — and cross-checks the
verdict itself against z3 (and any `:status` metadata) to catch wrong
verdicts.

A firewall file that does NOT contain `theorem no_model` (i.e. one of the
legacy per-theory-obligation diagnostic emitters) does NOT count as a
complete certification — matches `--emit-firewall-lean --help`: "these
lemmas audit covered theory steps but do not certify the complete UNSAT
derivation."

Usage:
  scripts/proof_checkability_sweep.py --files-from LISTFILE --out OUT.json
  scripts/proof_checkability_sweep.py --dir DIR [--stride N] --out OUT.json
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
AY_BIN = ROOT / "target/release/ay"
LEAN_DIR = ROOT / "verification/lean"

AXIOM_ALLOW = {"propext", "Classical.choice", "Quot.sound"}


def run(cmd, timeout_s, cwd=None):
    try:
        p = subprocess.run(
            cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout_s
        )
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return None, "", "TIMEOUT"
    except Exception as e:  # noqa: BLE001
        return None, "", f"EXC:{e}"


def get_verdict(f, timeout_s=20):
    rc, out, err = run(
        [str(AY_BIN), "solve", str(f), "--no-proof", "-t", str(timeout_s * 1000)],
        timeout_s + 5,
    )
    if rc is None:
        return "timeout" if err == "TIMEOUT" else "error"
    lines = [l.strip() for l in out.splitlines() if l.strip() and not l.startswith("c ")]
    if not lines:
        return "error"
    last = lines[-1]
    if last in ("sat", "unsat", "unknown"):
        return last
    return "error"


def get_status_field(f):
    try:
        text = f.read_text(errors="ignore")
    except Exception:
        return None
    m = re.search(r":status\s+(sat|unsat|unknown)", text)
    return m.group(1) if m else None


def z3_verdict(f, timeout_s=15):
    if not shutil.which("z3"):
        return None
    rc, out, err = run(["z3", "-T:%d" % timeout_s, str(f)], timeout_s + 5)
    if rc is None:
        return "z3-timeout"
    # A parse/unsupported-syntax error invalidates any trailing sat/unsat line
    # z3 may still print (e.g. AY-only set-theory extensions like
    # `set.singleton` that z3 doesn't recognize) — check this FIRST, since a
    # verdict printed after an error is not a real cross-check.
    combined = out + err
    if "error" in combined.lower():
        return "z3-error"
    lines = [l.strip() for l in out.splitlines() if l.strip()]
    for l in reversed(lines):
        if l in ("sat", "unsat", "unknown"):
            return l
    return "z3-noverdict"


def check_firewall(f, timeout_s=60):
    """Returns dict: emitted(bool), complete(bool), lake_ok(bool), axioms(list),
    sorryax(bool), checked(bool), file_count(int), detail(str)."""
    with tempfile.TemporaryDirectory(prefix="fwsweep_") as td:
        # ay requires: --proof's parent dir must EXIST; --emit-firewall-lean's
        # dir must NOT pre-exist (it refuses to "replace" an existing path).
        lean_dir = os.path.join(td, "lean_out")
        proof_dir = os.path.join(td, "proof_out")
        os.makedirs(proof_dir, exist_ok=True)
        proof_path = os.path.join(proof_dir, "proof.alethe")
        rc, out, err = run(
            [str(AY_BIN), "solve", str(f), "--emit-firewall-lean", lean_dir,
             "--proof", proof_path],
            timeout_s + 5,
        )
        emitted_files = list(Path(lean_dir).glob("*.lean"))
        if not emitted_files:
            return {
                "emitted": False, "complete": False, "lake_ok": False,
                "axioms": [], "sorryax": False, "checked": False,
                "file_count": 0, "detail": "no-emission (declined)",
            }
        best = None
        for lf in emitted_files:
            src = lf.read_text(errors="ignore")
            is_complete = "theorem no_model" in src
            if not is_complete:
                rec = {
                    "emitted": True, "complete": False, "lake_ok": False,
                    "axioms": None, "sorryax": False, "checked": False,
                    "file_count": len(emitted_files),
                    "detail": f"{lf.name}: legacy/diagnostic-only (no `theorem no_model`)",
                }
                if best is None:
                    best = rec
                continue
            # Instrument our OWN `#print axioms no_model` — do not trust each
            # emitter to self-embed one (some don't, and a silent-empty axiom
            # list must never be read as "axiom-free").
            lines = src.splitlines()
            end_idx = None
            for i in range(len(lines) - 1, -1, -1):
                if re.match(r"^end\s+\S+\s*$", lines[i]):
                    end_idx = i
                    break
            if end_idx is None:
                instrumented = src + "\n#print axioms no_model\n"
            else:
                lines.insert(end_idx, "#print axioms no_model")
                instrumented = "\n".join(lines)
            inst_path = lf.with_name(lf.stem + "_instrumented.lean")
            inst_path.write_text(instrumented)
            lrc, lout, lerr = run(
                ["lake", "env", "lean", str(inst_path.resolve())], 120, cwd=str(LEAN_DIR)
            )
            lake_ok = (lrc == 0)
            combined = lout + lerr
            sorryax = "sorryAx" in combined
            axm = re.search(r"axioms:\s*\[([^\]]*)\]", combined)
            has_no_axioms_msg = "does not depend on any axioms" in combined
            if axm:
                axioms = [a.strip() for a in axm.group(1).split(",") if a.strip()]
            elif has_no_axioms_msg:
                axioms = []
            else:
                axioms = None  # could not confirm — never treat as vacuously OK
            axioms_ok = (
                lake_ok and not sorryax and axioms is not None
                and set(axioms) <= AXIOM_ALLOW
            )
            rec = {
                "emitted": True, "complete": True, "lake_ok": lake_ok,
                "axioms": axioms, "sorryax": sorryax, "checked": axioms_ok,
                "file_count": len(emitted_files), "detail": lf.name,
                "lake_raw": combined[-500:],
            }
            if best is None or (rec["checked"] and not best["checked"]):
                best = rec
        return best


def sweep(files, timeout_s=20, do_z3=True, do_firewall=True):
    results = []
    for f in files:
        f = Path(f)
        rec = {"file": str(f.relative_to(ROOT)) if f.is_absolute() else str(f)}
        rec["ay_verdict"] = get_verdict(f, timeout_s)
        rec["status_field"] = get_status_field(f)
        if do_z3:
            rec["z3_verdict"] = z3_verdict(f)
        else:
            rec["z3_verdict"] = None
        disagree = False
        # `:status unknown` means "no ground truth asserted" (common for
        # generated/practical benchmarks) — NOT a claim that conflicts with a
        # concrete AY verdict. Only sat/unsat status fields are meaningful.
        if (
            rec["status_field"] in ("sat", "unsat")
            and rec["ay_verdict"] in ("sat", "unsat")
            and rec["status_field"] != rec["ay_verdict"]
        ):
            disagree = True
        if rec["z3_verdict"] in ("sat", "unsat") and rec["ay_verdict"] in ("sat", "unsat") and rec["z3_verdict"] != rec["ay_verdict"]:
            disagree = True
        rec["disagreement"] = disagree
        if rec["ay_verdict"] == "unsat" and do_firewall:
            rec["firewall"] = check_firewall(f)
        else:
            rec["firewall"] = None
        results.append(rec)
    return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir")
    ap.add_argument("--files-from")
    ap.add_argument("--stride", type=int, default=1, help="take every Nth file (deterministic sample)")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--timeout", type=int, default=20)
    ap.add_argument("--no-z3", action="store_true")
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    if args.files_from:
        files = [l.strip() for l in Path(args.files_from).read_text().splitlines() if l.strip()]
    elif args.dir:
        files = sorted(str(p) for p in Path(args.dir).rglob("*.smt2"))
    else:
        print("need --dir or --files-from", file=sys.stderr)
        sys.exit(2)

    if args.stride > 1:
        files = files[:: args.stride]
    if args.limit:
        files = files[: args.limit]

    results = sweep(files, timeout_s=args.timeout, do_z3=not args.no_z3)

    total = len(results)
    by_verdict = {}
    for r in results:
        by_verdict[r["ay_verdict"]] = by_verdict.get(r["ay_verdict"], 0) + 1
    unsat = [r for r in results if r["ay_verdict"] == "unsat"]
    checked = [r for r in unsat if r["firewall"] and r["firewall"]["checked"]]
    unchecked = [r for r in unsat if not (r["firewall"] and r["firewall"]["checked"])]
    disagreements = [r for r in results if r["disagreement"]]

    summary = {
        "total_files": total,
        "sample_stride": args.stride,
        "by_verdict": by_verdict,
        "unsat_count": len(unsat),
        "unsat_checked": len(checked),
        "unsat_unchecked": len(unchecked),
        "disagreement_count": len(disagreements),
        "disagreements": disagreements,
        "unchecked_files": [r["file"] for r in unchecked],
    }
    out = {"summary": summary, "results": results}
    Path(args.out).write_text(json.dumps(out, indent=2))
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
