#!/usr/bin/env python3
"""Sweep a corpus for WRONG ANSWERS, adjudicating every hit against real solvers.

WHY THIS EXISTS
---------------
On 2026-08-01 this campaign discovered that AY answers **unsat on satisfiable
instances** -- six confirmed cases in AUFLIA/20170829-Rodin, clean exit code 0,
contradicted unanimously by the benchmark header, z3, and cvc5's
finite-model-find. "0-wrong" is the property every claim in this campaign rests
on, and it had been false in quantified AUFLIA for an unknown period while
0-wrong results were being reported elsewhere.

It was found BY ACCIDENT, while chasing Alethe proof formatting:
`scripts/check_proofs.sh` classifies an instance as WRONG-ANSWER when AY
contradicts a declared status, so a proof-checking harness incidentally became a
soundness harness. Nothing else in the campaign was watching these paths.

The lesson is the tool: soundness must be swept deliberately and continuously,
not discovered as a side effect. That is what this script is for.

WHAT IT CHECKS
--------------
  1. AY's definite answer contradicts a definite `:status` header.
  2. AY prints a DEFINITE answer while ALSO reporting it did not decide --
     `(:reason-unknown ...)` or exit 124. A harness reads line 1, so
     `sat` + `(:reason-unknown "timeout")` scores as a wrong answer. That is a
     real, separate defect (observed on AUFLIA/misc/arr2.smt2), and it is
     budget-independent.

WHY IT CROSS-CHECKS
-------------------
A `:status` header is NOT ground truth. Older benchmark families carry wrong
ones, and this campaign was already misled once by trusting a single source. So
every flagged instance is re-adjudicated against z3 AND cvc5 --finite-model-find
(plain cvc5 returns `unknown` on these quantified problems and cannot settle
them; finite-model-find is the mode that actually finds the model). An instance
is reported CONFIRMED-WRONG only when the independent solvers agree AGAINST AY.

Runs AY exactly as the competition does: `ay --z3-mode` reading the file on
stdin. Measuring any other path measures something we do not ship.

USAGE
  scripts/soundness_sweep.py [--limit N] [--timeout S] [--jobs N] [FAMILY ...]
  scripts/soundness_sweep.py --limit 2000 AUFLIA QF_DT QF_LIA
Exit code 0 = no CONFIRMED wrong answers. Non-zero = at least one.
"""
import argparse
import concurrent.futures as cf
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# The FULL corpus: 84 divisions, 438,631 files. This previously pointed at
# `benchmarks/smtlib-2025/non-incremental`, which on this checkout contains
# exactly ONE division (QF_SLIA) — so "the soundness sweep" covered 1/84 of the
# corpus while reading as though it covered all of it. Every wrong answer this
# campaign has ever found (AUFLIA false-unsat, UFBV wrong-sat, UFNIRA wrong-sat)
# lives under `smtlib-all` and was unreachable from here.
# Override with AY_BENCH_ROOT to sweep a different tree.
BENCH = Path(os.environ.get("AY_BENCH_ROOT", ROOT / "benchmarks/smtlib-all"))

AY = os.environ.get("AY_BIN", str(ROOT / "target/release/ay"))
Z3 = os.environ.get("Z3_BIN", "z3")


def _resolve_cvc5():
    """cvc5 is the SECOND independent oracle, and it is load-bearing: a
    `:status` header is not ground truth (older families carry wrong ones), so
    a flagged instance is only called wrong once z3 and cvc5 corroborate it.

    This used to be a hardcoded `.competitors/cvc5` that does not exist on this
    checkout. `oracle()` maps the resulting OSError to "timeout", so a MISSING
    cvc5 was indistinguishable from a cvc5 that ran and gave up — the sweep
    silently degraded to a single oracle and still printed its adjudication
    banner. Resolve from the vendored path, then $CVC5_BIN, then $PATH, and
    return None rather than a path that cannot be executed.
    """
    for cand in (os.environ.get("CVC5_BIN"), str(ROOT / ".competitors/cvc5")):
        if cand and Path(cand).is_file() and os.access(cand, os.X_OK):
            return cand
    return shutil.which("cvc5")


CVC5 = _resolve_cvc5()

RED, YEL, GRN, OFF = "\033[31m", "\033[33m", "\033[32m", "\033[0m"
STATUS_RE = re.compile(r":status\s+(sat|unsat)\b")


def declared_status(path):
    try:
        head = open(path, errors="ignore").read(8192)
    except OSError:
        return None
    m = STATUS_RE.search(head)
    return m.group(1) if m else None


def run_ay(path, timeout):
    """Answer on the SUBMISSION path, plus the did-not-decide signals."""
    try:
        with open(path) as fh:
            p = subprocess.run([AY, "--z3-mode", f"-T:{timeout}"], stdin=fh,
                               capture_output=True, text=True, timeout=timeout + 25)
    except (subprocess.TimeoutExpired, OSError):
        return None, False, None
    answer, undecided = None, False
    for line in p.stdout.splitlines():
        s = line.strip()
        if s in ("sat", "unsat", "unknown") and answer is None:
            answer = s
        if "reason-unknown" in s:
            undecided = True
    # `(:reason-unknown ...)` is printed on STDERR, not stdout. Scanning only
    # stdout left the DEFINITE_BUT_UNDECIDED rule able to fire solely via
    # rc == 124 -- a latent hole found by an independent sweep (on that corpus
    # all 3 such instances happened to ALSO carry rc 124, so nothing was missed,
    # but the rule was one exit-code away from silently never firing).
    if any("reason-unknown" in line for line in p.stderr.splitlines()):
        undecided = True
    return answer, undecided, p.returncode


def oracle(cmd, timeout):
    """Run a reference solver and return its verdict, or a non-verdict marker.

    An `(error ...)` line VOIDS the verdict. Measured: z3 4.16.0 on
    `BVFPLRA/…zonotope_loose_true-unreach-call.c_39.smt2` emits

        (error "line 34 column 76: unknown sort 'FloatingPoint'")
        (error "line 35 column 41: unknown constant v_main_~y~6_…")
        sat

    — it failed to parse the FP declarations, then answered `sat` on what was
    left. Scanning stdout for the first verdict line and ignoring the errors
    took that `sat` as authoritative and reported AY's (correct, cvc5-agreed)
    `unsat` as CONFIRMED-WRONG. A soundness oracle that manufactures false
    positives is worse than none, so a solver that errored gets no vote.
    """
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 20)
    except (subprocess.TimeoutExpired, OSError):
        return "timeout"
    combined = p.stdout + p.stderr
    if "(error" in combined:
        return "error"
    for line in p.stdout.splitlines():
        s = line.strip()
        if s in ("sat", "unsat", "unknown"):
            return s
    return "none"


def adjudicate(path, timeout):
    """Independent verdicts. cvc5 needs --finite-model-find: its default strategy
    answers `unknown` on quantified problems and cannot settle a sat claim.

    When cvc5 is unavailable its verdict is reported as the distinct value
    "absent", never as "timeout" — the caller must be able to tell "the second
    oracle declined" from "there is no second oracle"."""
    z = oracle([Z3, f"-T:{timeout}", str(path)], timeout)
    if CVC5 is None:
        return z, "absent"
    c = oracle([CVC5, f"--tlimit={timeout * 1000}", "--finite-model-find", str(path)], timeout)
    return z, c


def collect(families, limit):
    """Gather `.smt2` files, applying `limit` PER FAMILY on an even stride.

    `limit` used to be a global head-slice of one globally sorted list. With a
    single family that is merely biased toward whichever benchmark sub-family
    sorts first; with several it is worse than biased — `--limit 500 UFBV
    UFNIRA UFNIA` would spend the entire budget inside UFBV and never open the
    other two, while still reporting a clean sweep of all three.

    Per family, an even stride across the sorted list samples the whole
    division instead of its alphabetical head. That matters here: the wrong
    answers this script hunts cluster by benchmark sub-family (`fmsd13
    fixpoint`, `20240414-funcprobs`), so a head-slice can miss a live class
    entirely while looking thorough.
    """
    dirs = [BENCH / f for f in families] if families else [BENCH]
    out, missing = [], []
    for d in dirs:
        if not d.is_dir():
            # Returned to the caller rather than warned-and-skipped: a typo'd
            # division silently reducing the swept set is how a soundness run
            # ends up green over nothing.
            missing.append(d.name)
            continue
        files = []
        for dp, _, fs in os.walk(d):
            files.extend(os.path.join(dp, f) for f in fs if f.endswith(".smt2"))
        files.sort()
        if limit and len(files) > limit:
            step = len(files) / limit
            files = [files[int(i * step)] for i in range(limit)]
        out.extend(files)
    return out, missing


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("families", nargs="*")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--timeout", type=int, default=10)
    ap.add_argument("--jobs", type=int, default=6)
    # The harness self-test runs this script from a SCRATCH COPY, where a
    # ROOT-relative BENCH resolves to the wrong tree (or to nothing). Making the
    # corpus explicit is what lets the self-test point it at fixtures and assert
    # the guards below actually fire.
    ap.add_argument("--bench-root", default=None,
                    help="corpus root; overrides AY_BENCH_ROOT / the repo default")
    # Escape hatch for the no-answer guard, so a deliberately hard corpus can opt
    # out rather than tempting anyone to delete the guard.
    ap.add_argument("--max-no-answer-pct", type=int, default=90)
    args = ap.parse_args()

    global BENCH
    if args.bench_root:
        BENCH = Path(args.bench_root)

    # Exit 2, not 1: a corpus that does not exist is a BROKEN INVOCATION, and it
    # shares an exit code with the other measurement guards so a caller can treat
    # "this run measured nothing" as one condition. `sys.exit(str)` would exit 1,
    # which is the same code as "found a wrong answer" -- the two must not alias.
    if not Path(AY).exists():
        print(f"{RED}no AY binary at{OFF} {AY} (build with --features cli)",
              file=sys.stderr)
        return 2
    if not BENCH.is_dir():
        print(f"{RED}no benchmark tree at{OFF} {BENCH} "
              f"(pass --bench-root, or set AY_BENCH_ROOT)", file=sys.stderr)
        return 2

    files, missing = collect(args.families, args.limit)

    # A sweep that scanned NOTHING must never look like a sweep that found
    # nothing. Previously an empty file list fell straight through to
    # "CLEAN: 0 instances scanned, 0 flagged" and exit 0 — the exact shape a
    # caller reads as "soundness verified". One fat-fingered family name, or a
    # shell that does not word-split an unquoted variable (zsh does not), was
    # enough to get a green soundness result over zero files.
    if missing:
        print(f"{RED}no such division(s){OFF}: {' '.join(missing)}", file=sys.stderr)
        print(f"available: {' '.join(sorted(p.name for p in BENCH.iterdir() if p.is_dir()))}",
              file=sys.stderr)
        return 2
    if not files:
        print(f"{RED}REFUSING{OFF}: 0 instances matched — nothing was swept, so "
              f"nothing is verified. This is an error, not a clean run.", file=sys.stderr)
        return 2

    print(f"AY      : {AY}")
    print(f"corpus  : {BENCH}")
    print(f"z3      : {shutil.which(Z3) or Z3}")
    # A degraded oracle set must be impossible to miss. Adjudication with one
    # oracle is strictly weaker, and the banner below used to claim "z3 + cvc5"
    # unconditionally while cvc5 was absent.
    if CVC5:
        print(f"cvc5    : {CVC5}")
    else:
        print(f"{RED}cvc5    : ABSENT{OFF} — adjudication DEGRADED to z3 alone.",
              file=sys.stderr)
        print(f"{RED}          A `:status` header is not ground truth, so a flag z3 "
              f"cannot settle will read as `unconfirmed` when it may be a real "
              f"wrong answer.{OFF}", file=sys.stderr)
        print(f"{RED}          Install cvc5, or set CVC5_BIN.{OFF}\n", file=sys.stderr)
    print(f"scanning: {len(files)} instances, -T:{args.timeout}, jobs={args.jobs}\n")

    # Counts instances on which AY printed no verdict line at all. "We ran N
    # files" is not "we measured N files": soundness is only testable on definite
    # answers, so this is the denominator the guard below needs.
    n_no_answer = 0

    def work(p):
        nonlocal n_no_answer
        st = declared_status(p)
        ans, undecided, rc = run_ay(p, args.timeout)
        if ans is None:
            n_no_answer += 1
        flags = []
        if ans in ("sat", "unsat") and st and ans != st:
            flags.append("CONTRADICTS_STATUS")
        if ans in ("sat", "unsat") and (undecided or rc == 124):
            flags.append("DEFINITE_BUT_UNDECIDED")
        return (p, st, ans, rc, flags) if flags else None

    flagged = []
    with cf.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        for res in ex.map(work, files):
            if res:
                flagged.append(res)
                print(f"{YEL}FLAG{OFF} {os.path.relpath(res[0], BENCH)} "
                      f"status={res[1]} ay={res[2]} rc={res[3]} {','.join(res[4])}",
                      flush=True)

    if not flagged:
        # CLEAN is a statement about what was SCANNED. Say so with the corpus and
        # the denominator attached, so it cannot be quoted as "AY is 0-wrong".
        scope = "/".join(args.families) if args.families else f"all of {BENCH.name}"
        # A run where AY produced no verdict line at all measured NOTHING on those
        # instances -- soundness is only testable on definite answers. A sweep that
        # is 100% no-answer is indistinguishable from a broken invocation, and
        # printing CLEAN there is how a dangling symlink once certified zero proofs.
        pct = (100 * n_no_answer // len(files)) if files else 0
        if pct > args.max_no_answer_pct:
            print(f"\n{RED}MEASUREMENT GUARD{OFF}: {n_no_answer}/{len(files)} "
                  f"({pct}%) instance(s) produced no verdict line at all.",
                  file=sys.stderr)
            print("Nothing meaningful was measured. Pass --max-no-answer-pct to "
                  "override deliberately.", file=sys.stderr)
            return 2
        print(f"\n{GRN}CLEAN{OFF}: {len(files)} instances scanned in {scope} "
              f"({len(files) - n_no_answer} answered), 0 flagged.")
        return 0

    # Adjudicate. A header is not ground truth -- confirm against real solvers
    # before calling anything a wrong answer.
    oracles = "z3 + cvc5 --finite-model-find" if CVC5 else f"{RED}z3 ALONE (cvc5 absent){OFF}"
    print(f"\nadjudicating {len(flagged)} flagged instance(s) against {oracles}\n")
    confirmed, contested = [], []
    for p, st, ans, rc, flags in flagged:
        z, c = adjudicate(p, max(args.timeout, 30))
        decisive = [v for v in (z, c) if v in ("sat", "unsat")]
        against = [v for v in decisive if v != ans]
        supporting = [v for v in decisive if v == ans]
        if against and supporting:
            # The oracles contradict EACH OTHER, so at least one of them is
            # itself wrong and neither can settle AY. Measured on
            # BVFPLRA/…zonotope_loose_true-unreach-call.c_39: z3 `sat`,
            # cvc5 `unsat`, AY `unsat`. Reporting that as CONFIRMED-WRONG
            # (the old behaviour, which took any dissenting oracle as proof)
            # blamed AY for being right. A split panel is an open question,
            # not a conviction.
            verdict, color = "ORACLES-DISAGREE", YEL
            contested.append((p, st, ans, z, c))
        elif against:
            verdict, color = "CONFIRMED-WRONG", RED
            confirmed.append((p, st, ans, z, c))
        else:
            verdict, color = "unconfirmed", YEL
        print(f"{color}{verdict}{OFF} {os.path.relpath(p, BENCH)}")
        print(f"        header={st}  ay={ans}  z3={z}  cvc5-fmf={c}  rc={rc}  {','.join(flags)}")

    print(f"\n{len(files)} scanned | {len(flagged)} flagged | "
          f"{RED}{len(confirmed)} CONFIRMED WRONG{OFF}"
          + (f" | {len(contested)} contested (oracles split)" if contested else ""))
    if confirmed:
        print("\nA single wrong answer voids the division it appears in.")
    if contested:
        print("Contested instances are NOT counted as wrong and NOT counted as clean — "
              "adjudicate them by hand with a longer budget.")
    return 1 if confirmed else 0


if __name__ == "__main__":
    sys.exit(main())
