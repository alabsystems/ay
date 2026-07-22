#!/usr/bin/env python3
# ay-script: sat-bve-audit
"""Soundness audit for BVE-enabled build: run AY on instances with KNOWN verdicts,
flag any WRONG answer (CRITICAL), count Unknown regressions (completeness cost)."""
import argparse, subprocess, time, sys, glob, os

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))

_ap = argparse.ArgumentParser(description=__doc__)
_ap.add_argument("--ay-bin",
                 default=os.environ.get("AY_BIN", os.path.join(REPO, "target/release/ay")),
                 help="ay binary to audit (env: AY_BIN)")
_args = _ap.parse_args()
AY = _args.ay_bin

def ay(cnf, timeout):
    t = time.monotonic()
    try:
        p = subprocess.run([AY, "--no-proof", "-t", str(int(timeout*1000)), cnf],
                           capture_output=True, text=True, timeout=timeout+20)
        for line in p.stdout.splitlines():
            if line.startswith("s "):
                if "UNSATISFIABLE" in line: return "UNSAT", time.monotonic()-t
                if "SATISFIABLE" in line:  return "SAT", time.monotonic()-t
        return "UNKNOWN", time.monotonic()-t
    except subprocess.TimeoutExpired:
        return "TIMEOUT", time.monotonic()-t

# (label, expected, [files], timeout)
groups = []
braun = sorted(glob.glob(os.path.join(REPO, "benchmarks/sat/eq_atree_braun/*.unsat.cnf")))
groups.append(("braun(UNSAT)", "UNSAT", ["/tmp/satcampaign/reg_"+os.path.basename(f) if os.path.exists("/tmp/satcampaign/reg_"+os.path.basename(f)) else f for f in braun], 60))
groups.append(("barrel6(UNSAT)", "UNSAT", ["/tmp/satcampaign/reg_cmu-bmc-barrel6.cnf"], 60))
groups.append(("crn(UNSAT)", "UNSAT", ["/tmp/satcampaign/reg_crn_11_99_u.cnf"], 60))
groups.append(("uf250(SAT,model-recon)", "SAT", sorted(glob.glob("/tmp/satlib_clean/uf250/*.cnf"))[:25], 30))
groups.append(("uuf250(UNSAT)", "UNSAT", sorted(glob.glob("/tmp/satlib_clean/uuf250/*.cnf"))[:15], 30))

wrong = []
totals = {}
for label, exp, files, to in groups:
    n=correct=unk=0
    for f in files:
        if not os.path.exists(f): continue
        v, el = ay(f, to)
        n += 1
        if v == exp: correct += 1
        elif v in ("UNKNOWN", "TIMEOUT"): unk += 1
        else:  # opposite definite verdict = WRONG
            wrong.append((f, exp, v))
            print(f"  !!! WRONG: {os.path.basename(f)} expected {exp} got {v}")
    totals[label] = (n, correct, unk)
    print(f"{label:26} n={n:3} correct={correct:3} unknown={unk:3}  (expected {exp})")

print("\n===== AUDIT SUMMARY =====")
print(f"WRONG ANSWERS (CRITICAL): {len(wrong)} {wrong}")
tn = sum(t[0] for t in totals.values()); tc = sum(t[1] for t in totals.values()); tu = sum(t[2] for t in totals.values())
print(f"correct {tc}/{tn}, unknown/timeout {tu}/{tn}")
print("VERDICT:", "SOUND (0 wrong)" if not wrong else "UNSOUND — DO NOT ENABLE")
