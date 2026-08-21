#!/usr/bin/env python3
"""Regression test FOR THE INSTRUMENT: does the proof harness measure anything?

WHY THIS EXISTS
---------------
Proof checking is how this project knows whether it is making progress. If the
instrument lies, every number derived from it is worthless. It has lied three
times, each time in the SAME direction -- reporting success while having measured
nothing:

  1. check_proofs.sh wrote RELATIVE paths into the work-cell `ln -sf`. Every
     symlink dangled, AY read nothing, all instances came back "no-answer" in 0s,
     and the sweep printed `RESULT: PASS` having checked ZERO proofs.
  2. check_proofs.sh recorded carcara's FIRST stderr line. carcara emits
     `[WARN] … appears after …` BEFORE the real `[ERROR]`, so two instances
     were filed under an "assume-after-step" defect class THAT DOES NOT EXIST.
     Both were really `and_pos`.
  3. soundness_sweep.py scanned only stdout, but `(:reason-unknown …)` prints to
     STDERR -- so its DEFINITE_BUT_UNDECIDED rule could physically only fire via
     rc == 124.

Each was found by accident, late, after conclusions had been drawn. The fix is
not vigilance, it is fixtures: (problem, proof) pairs whose correct
classification is KNOWN IN ADVANCE, run through the REAL scripts, so a harness
that stops measuring gets caught by the harness's own test suite.

WHAT IT DOES
------------
Runs scripts/check_proofs.sh and scripts/soundness_sweep.py, unmodified, over
benchmarks/proof-fixtures/ with `ay` replaced by a deterministic stub
(benchmarks/proof-fixtures/fake_ay.py) whose behaviour each fixture spells out.
Every classification, every reason string, and both measurement guards are
asserted against the `; EXPECT-...` directives carried by the fixtures.

The stub is only the SOLVER. Work-cell symlinking, answer parsing, carcara
invocation, reason extraction, counters and exit codes are all the production
code paths.

PROVING THE TEST HAS TEETH
--------------------------
A green self-test is worth exactly as much as its ability to go red. Run

    scripts/selftest_proof_harness.py --seed-fault all

to re-introduce each historical defect into a scratch copy of the scripts and
confirm the suite catches every one. A seeded fault that the suite does not
notice is reported as a FAILURE OF THIS FILE.

USAGE
    scripts/selftest_proof_harness.py                  # the suite; 0 = healthy
    scripts/selftest_proof_harness.py --seed-fault all # prove it can go red
    scripts/selftest_proof_harness.py --list-faults
    scripts/selftest_proof_harness.py -v               # show sub-process output

EXIT CODES
    0  every fixture classified correctly / every seeded fault caught
    1  a misclassification (or, under --seed-fault, a fault that slipped through)
    2  environment problem (no carcara, no z3, missing fixtures)
"""
import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FIX = ROOT / "benchmarks/proof-fixtures"
FAKE_AY = FIX / "fake_ay.py"
CHECK_SH = ROOT / "scripts/check_proofs.sh"
SWEEP_PY = ROOT / "scripts/soundness_sweep.py"

ANSI = re.compile(r"\x1b\[[0-9;]*m")
DIRECTIVE = re.compile(r"^;\s*(EXPECT-[A-Z0-9-]+):\s*(.*?)\s*$")

RED, GRN, YEL, DIM, OFF = (
    "\033[31m", "\033[32m", "\033[33m", "\033[2m", "\033[0m",
) if sys.stdout.isatty() else ("", "", "", "", "")


# ---------------------------------------------------------------------------
# Seeded faults: each is a historical (or one-step-away) defect, expressed as an
# exact source substitution. If the suite still passes with one applied, the
# suite is not testing what it claims to.
# ---------------------------------------------------------------------------
FAULTS = {
    "warn-mask": (
        CHECK_SH,
        """CC_REASON="$(grep -m1 -E '^\\[ERROR\\]' "$err" | tr '\\t' ' ' | cut -c1-200)\"""",
        """CC_REASON="$(grep -m1 . "$err" | tr '\\t' ' ' | cut -c1-200)\"""",
        "DEFECT 2 verbatim: take carcara's first stderr line, so a [WARN] masks "
        "the real [ERROR] and the reported cause is fiction.",
    ),
    "relative-symlink": (
        CHECK_SH,
        # NB: anchored on the trailing comment. The bare `ln -sf "$src" ...`
        # also appears inside the explanatory note above it, and patching the
        # NOTE instead of the CODE made this fault look like it slipped through
        # when it had simply never been applied. Anchors must be unique --
        # apply_fault() now enforces that.
        'ln -sf "$src" "$cell/$base"            # AY writes',
        'ln -sf "$(basename "$src")" "$cell/$base"  # AY writes',
        "DEFECT 1 verbatim: a relative work-cell symlink resolves against the "
        "CELL, dangles, and every instance silently becomes a 0s no-answer.",
    ),
    "relative-corpus-path": (
        CHECK_SH,
        'case "$INPUT" in\n  /*) ;;\n  *)  INPUT="$(cd "$(dirname "$INPUT")" 2>/dev/null'
        ' && printf \'%s/%s\' "$(pwd)" "$(basename "$INPUT")")" \\\n'
        '        || die "cannot resolve corpus to an absolute path: $INPUT" ;;\nesac',
        "",
        "The half-fixed DEFECT 1 found on 2026-08-02: stop absolutizing a "
        "relative corpus DIRECTORY, so `check_proofs.sh benchmarks/...` dangles "
        "every work-cell symlink again.",
    ),
    "holey-as-valid": (
        CHECK_SH,
        '    verdict="$CC_VERDICT"',
        '    verdict="$(printf %s "$CC_VERDICT" | sed s/holey/valid/)"',
        "Report proofs containing `hole` steps as fully certified.",
    ),
    "guard-off-nothing-checked": (
        CHECK_SH,
        'if [ "$CHECKED" -eq 0 ] && [ "$ALLOW_NOTHING_CHECKED" -eq 0 ]; then',
        "if [ 1 -eq 0 ]; then",
        "Let a run that put ZERO proofs through carcara print PASS.",
    ),
    "guard-off-no-answer": (
        CHECK_SH,
        'if [ "$N_NOANSWER" -gt 0 ] && [ "$NO_ANSWER_PCT" -gt "$MAX_NO_ANSWER_PCT" ]; then',
        "if [ 1 -eq 0 ]; then",
        "Let a run in which AY never answered print PASS.",
    ),
    "provenance-stripped": (
        CHECK_SH,
        """    printf '# ay\\t%s\\n'        "$AY"\n""",
        "",
        "Drop the binary identity from the machine-readable record, so two runs "
        "of DIFFERENT `ay` builds diff as though they were the same solver -- the "
        "2026-08-02 stale-binary A/B.",
    ),
    "sweep-stdout-only": (
        SWEEP_PY,
        '    if any("reason-unknown" in line for line in p.stderr.splitlines()):\n'
        "        undecided = True\n",
        "",
        "DEFECT 3 verbatim: scan only stdout for `(:reason-unknown ...)`, which "
        "is printed on stderr, so DEFINITE_BUT_UNDECIDED can only fire via rc 124.",
    ),
    "sweep-trust-header": (
        SWEEP_PY,
        "        against = [v for v in decisive if v != ans]",
        "        against = [st] if st and st != ans else []",
        "Trust the :status header instead of adjudicating, so a benchmark with a "
        "WRONG header is reported as an AY wrong answer.",
    ),
    "sweep-guard-off-empty": (
        SWEEP_PY,
        "    if not files:",
        "    if False:",
        "Let a sweep that collected 0 instances print CLEAN.",
    ),
}


class Result:
    def __init__(self):
        self.checks = []          # (ok, label, detail)

    def expect(self, ok, label, detail=""):
        self.checks.append((bool(ok), label, detail))
        return ok

    @property
    def failed(self):
        return [c for c in self.checks if not c[0]]


def strip_ansi(s):
    return ANSI.sub("", s)


def gist(out):
    """The lines of a harness run that actually say what happened.

    Failure details used to dump whole stdout, whose first line is the banner
    (`ay : /path/...`) -- so a truncated detail showed the binary path instead of
    the verdict. Keep the verdict/guard lines only."""
    keep = [l for l in strip_ansi(out).splitlines()
            if re.match(r"^(RESULT:|MEASUREMENT GUARD|CLEAN|  This run|  \(\d)", l)
            or "no verdict line" in l or "proofs reached carcara" in l]
    return "\n".join(keep) or strip_ansi(out).strip()[-300:]


def read_tsv(path):
    """(provenance, rows) from a --report-tsv record.

    The file opens with `#`-prefixed provenance lines naming the binaries that
    produced it, then the column header, then one row per instance. Returns the
    provenance as a dict and the rows as split field lists."""
    prov, rows, seen_header = {}, [], False
    for line in Path(path).read_text().splitlines():
        if line.startswith("#"):
            f = line[1:].strip().split("\t")
            prov[f[0].strip()] = f[1] if len(f) > 1 else ""
        elif not seen_header:
            seen_header = True          # the `name\tverdict\t...` column header
        elif line:
            rows.append(line.split("\t"))
    return prov, rows


def directives(path):
    """The `; EXPECT-...` lines a fixture carries. Multi-valued: a key may repeat."""
    out = {}
    with open(path, errors="ignore") as fh:
        for line in fh:
            m = DIRECTIVE.match(line.rstrip("\n"))
            if m:
                out.setdefault(m.group(1), []).append(m.group(2))
    return out


def run(cmd, env=None, cwd=None, verbose=False):
    full = dict(os.environ)
    full.update(env or {})
    p = subprocess.run([str(c) for c in cmd], capture_output=True, text=True,
                       env=full, cwd=str(cwd or ROOT), timeout=900)
    if verbose:
        print(f"{DIM}$ {' '.join(str(c) for c in cmd)}{OFF}")
        for line in (p.stdout + p.stderr).splitlines():
            print(f"{DIM}| {line}{OFF}")
        print(f"{DIM}| rc={p.returncode}{OFF}")
    return p


# ---------------------------------------------------------------------------
# suite part 1 -- check_proofs.sh classification over benchmarks/proof-fixtures/checker
# ---------------------------------------------------------------------------
def test_relative_corpus(scripts, tmp, r, verbose):
    """A RELATIVE corpus directory must measure exactly what an absolute one does.

    Found by the measurement guard on 2026-08-02: `check_proofs.sh <relative
    dir>` fed `find`'s relative output straight into the work-cell `ln -sf`,
    every symlink dangled, and all 41 ALIA/piVC instances came back no-answer in
    0s. Absolutizing was only ever done in the .jsonl reader. This asserts both
    call shapes agree."""
    tsv = Path(tmp) / "relative.tsv"
    rel = os.path.relpath(FIX / "checker", ROOT)
    p = run([scripts["check"], "--ay", FAKE_AY, "--report-tsv", tsv,
             "--timeout", "10", rel], cwd=ROOT, verbose=verbose)
    verdicts = {}
    if tsv.exists():
        for f in read_tsv(tsv)[1]:
            verdicts[f[0]] = f[1] if len(f) > 1 else ""
    r.expect(verdicts and not any(v == "no-answer" for v in verdicts.values()),
             f"relative corpus path {rel!r}: no instance is a no-answer",
             f"verdicts={verdicts}\n{gist(p.stdout)}")
    r.expect(p.returncode == 1,
             "relative corpus path: same exit code as the absolute run (1)",
             f"got {p.returncode}\n{gist(p.stdout)}")


def test_checker(scripts, tmp, r, verbose):
    tsv = Path(tmp) / "checker.tsv"
    p = run([scripts["check"], "--ay", FAKE_AY, "--report-tsv", tsv,
             "--timeout", "10", FIX / "checker"], verbose=verbose)

    if not r.expect(tsv.exists() and tsv.stat().st_size > 0,
                    "check_proofs.sh wrote a per-instance record",
                    f"rc={p.returncode}\n{p.stdout}\n{p.stderr}"):
        return

    prov, raw = read_tsv(tsv)
    rows = {}
    for f in raw:
        f += [""] * (6 - len(f))
        rows[f[0]] = {"verdict": f[1], "answer": f[2], "reason": f[4], "warn": f[5]}

    # A verdict without the solver that produced it is not evidence. An A/B of
    # this script on 2026-08-02 unknowingly compared two different `ay` builds --
    # a copied script re-points the default $AY at its own directory -- and the
    # disagreement was nearly reported as an effect of the change under test.
    # The record must name what it measured, and must name the binary ACTUALLY
    # used (here: the stub), not whatever the repo default happens to be.
    r.expect("ay" in prov and "ay-build" in prov and "carcara" in prov,
             "record carries provenance (ay / ay-build / carcara)",
             f"got keys {sorted(prov)}")
    r.expect(prov.get("ay", "").endswith(FAKE_AY.name),
             f"provenance names the binary actually used ({FAKE_AY.name})",
             f"got ay={prov.get('ay')!r}")
    r.expect("FAKE" in prov.get("ay-build", ""),
             "provenance carries the build stamp of that binary",
             f"got ay-build={prov.get('ay-build')!r}")

    fixtures = sorted((FIX / "checker").glob("*.smt2"))
    r.expect(len(fixtures) > 0, "checker fixtures present")
    r.expect(len(rows) == len(fixtures),
             f"every fixture was classified ({len(rows)}/{len(fixtures)})",
             f"missing: {sorted(set(f.name for f in fixtures) - set(rows))}")

    for fx in fixtures:
        d = directives(fx)
        row = rows.get(fx.name)
        if not r.expect(row is not None, f"{fx.name}: appears in the record"):
            continue
        got, reason, warn = row["verdict"], row["reason"], row["warn"]

        for want in d.get("EXPECT-CHECK-VERDICT", []):
            r.expect(got == want, f"{fx.name}: verdict == {want}",
                     f"got {got!r} (reason={reason!r})")
        for sub in d.get("EXPECT-CHECK-REASON-CONTAINS", []):
            r.expect(sub in reason, f"{fx.name}: reason contains {sub!r}",
                     f"reason={reason!r}")
        for sub in d.get("EXPECT-CHECK-REASON-EXCLUDES", []):
            r.expect(sub not in reason,
                     f"{fx.name}: reason does NOT contain {sub!r}",
                     f"reason={reason!r}  <-- a warning is masking the real error")
        for _ in d.get("EXPECT-CHECK-REASON-IS-EMPTY", []):
            r.expect(reason == "", f"{fx.name}: reason is empty",
                     f"reason={reason!r}  <-- a warning was promoted to a reason")
        for sub in d.get("EXPECT-CHECK-WARN-CONTAINS", []):
            r.expect(sub in warn, f"{fx.name}: warning kept, containing {sub!r}",
                     f"warnings={warn!r}")

    # The fixture set deliberately contains invalid proofs and a wrong answer,
    # so a healthy harness must FAIL this corpus -- with rc 1 (a real defect),
    # never rc 3 (measurement broken) and never rc 0.
    r.expect(p.returncode == 1,
             "exit code 1 (real defects found, measurement sound)",
             f"got {p.returncode}\n{p.stdout}\n{p.stderr}")
    r.expect("RESULT: FAIL" in p.stdout, "reports RESULT: FAIL", p.stdout)


# ---------------------------------------------------------------------------
# suite part 2 -- soundness_sweep.py classification over .../sweep
# ---------------------------------------------------------------------------
def test_sweep(scripts, tmp, r, verbose):
    p = run([sys.executable, scripts["sweep"], "--bench-root", FIX / "sweep",
             "--timeout", "10", "--jobs", "4"],
            env={"AY_BIN": str(FAKE_AY), "CVC5_BIN": str(ROOT / ".competitors/cvc5")},
            verbose=verbose)
    out = strip_ansi(p.stdout + p.stderr)

    flags = {}       # name -> set(flag)
    adjud = {}       # name -> CONFIRMED-WRONG | unconfirmed
    for line in out.splitlines():
        m = re.match(r"^FLAG (\S+) .*?(?: |,)?([A-Z_,]+)\s*$", line)
        if m:
            flags[os.path.basename(m.group(1))] = set(m.group(2).split(","))
        m = re.match(r"^(CONFIRMED-WRONG|unconfirmed) (\S+)$", line)
        if m:
            adjud[os.path.basename(m.group(2))] = m.group(1)

    fixtures = sorted((FIX / "sweep").glob("*.smt2"))
    r.expect(len(fixtures) > 0, "sweep fixtures present")

    n_confirmed = 0
    for fx in fixtures:
        d = directives(fx)
        want = (d.get("EXPECT-SWEEP") or ["clean"])[0]
        if want == "clean":
            r.expect(fx.name not in flags, f"{fx.name}: not flagged",
                     f"flagged {flags.get(fx.name)}")
            continue
        if not r.expect(fx.name in flags, f"{fx.name}: flagged",
                          "not present in the FLAG lines of this run"):
            continue
        for wf in d.get("EXPECT-SWEEP-FLAGS", []):
            r.expect(wf in flags[fx.name], f"{fx.name}: flag {wf}",
                     f"got {sorted(flags[fx.name])}")
        want_v = "CONFIRMED-WRONG" if want == "confirmed-wrong" else "unconfirmed"
        if want_v == "CONFIRMED-WRONG":
            n_confirmed += 1
        r.expect(adjud.get(fx.name) == want_v,
                 f"{fx.name}: adjudicated {want_v}",
                 f"got {adjud.get(fx.name)!r}")

    r.expect(p.returncode == (1 if n_confirmed else 0),
             f"sweep exit code {1 if n_confirmed else 0}",
             f"got {p.returncode}")


# ---------------------------------------------------------------------------
# suite part 3 -- the "did we actually measure anything?" guards
# ---------------------------------------------------------------------------
def test_guards(scripts, tmp, r, verbose):
    # 3a. every instance answers `unknown`: each outcome legitimate, zero proofs
    #     reached carcara -> the run says nothing about proof emission.
    p = run([scripts["check"], "--ay", FAKE_AY, "--timeout", "10",
             FIX / "guard/nothing_checked"], verbose=verbose)
    r.expect(p.returncode == 3, "guard/nothing_checked: exit 3", f"got {p.returncode}")
    r.expect("0 proofs reached carcara" in p.stdout,
             "guard/nothing_checked: says 0 proofs reached carcara", gist(p.stdout))
    r.expect("RESULT: PASS" not in p.stdout,
             "guard/nothing_checked: does NOT print PASS", gist(p.stdout))

    # 3b. and the override exists, so the guard is a guard and not a wall.
    p = run([scripts["check"], "--ay", FAKE_AY, "--timeout", "10",
             "--allow-nothing-checked", FIX / "guard/nothing_checked"],
            verbose=verbose)
    r.expect(p.returncode == 0, "guard/nothing_checked: --allow-nothing-checked overrides",
             f"got {p.returncode}\n{p.stdout}")

    # 3c. AY produces no verdict line at all -- the dangling-symlink signature.
    p = run([scripts["check"], "--ay", FAKE_AY, "--timeout", "10",
             FIX / "guard/no_answer"], verbose=verbose)
    r.expect(p.returncode == 3, "guard/no_answer: exit 3", f"got {p.returncode}")
    r.expect("RESULT: PASS" not in p.stdout,
             "guard/no_answer: does NOT print PASS", gist(p.stdout))

    # 3d. the no-answer RATE guard on its own: proofs WERE checked (guard 1
    #     quiet), but 2 of 3 instances never answered.
    p = run([scripts["check"], "--ay", FAKE_AY, "--timeout", "10",
             FIX / "guard/mixed_no_answer"], verbose=verbose)
    r.expect(p.returncode == 3, "guard/mixed_no_answer: exit 3", f"got {p.returncode}")
    r.expect("produced no verdict line at all" in p.stdout,
             "guard/mixed_no_answer: names the no-answer rate", gist(p.stdout))
    r.expect("0 proofs reached carcara" not in p.stdout,
             "guard/mixed_no_answer: it is the RATE guard firing, not the empty guard",
             gist(p.stdout))

    # 3e. ... and the rate guard is a rate: raising the limit lets it through.
    p = run([scripts["check"], "--ay", FAKE_AY, "--timeout", "10",
             "--max-no-answer-pct", "90", FIX / "guard/mixed_no_answer"],
            verbose=verbose)
    r.expect(p.returncode == 0, "guard/mixed_no_answer: --max-no-answer-pct 90 passes",
             f"got {p.returncode}\n{p.stdout}")

    # 3f. a DELIBERATELY BROKEN INVOCATION: a selection file with a bad
    #     --bench-root. Nothing resolves, so nothing can be measured.
    sel = FIX / "selections/checker.jsonl"
    p = run([scripts["check"], "--ay", FAKE_AY, "--bench-root",
             "/nonexistent-bench-root", sel], verbose=verbose)
    r.expect(p.returncode == 2, "bad --bench-root: exit 2", f"got {p.returncode}")
    r.expect("RESULT: PASS" not in p.stdout,
             "bad --bench-root: does NOT print PASS", gist(p.stdout))

    # 3g. the SAME selection file with the right root must still measure, so 3f
    #     is proof of a guard and not proof of a broken fixture.
    p = run([scripts["check"], "--ay", FAKE_AY, "--bench-root", FIX, sel],
            verbose=verbose)
    r.expect(p.returncode == 0, "good --bench-root: exit 0", f"{p.stdout}\n{p.stderr}")
    r.expect(re.search(r"\(2 proofs checked\)", p.stdout) is not None,
             "good --bench-root: 2 proofs actually reached carcara", gist(p.stdout))

    # 3h. a nonexistent sweep corpus is a broken invocation. Keep this separate
    #     from the empty-corpus case below: it exits before `collect`, so it
    #     cannot discriminate the `if not files` measurement guard.
    p = run([sys.executable, scripts["sweep"], "--bench-root",
             "/nonexistent-bench-root"], env={"AY_BIN": str(FAKE_AY)},
            verbose=verbose)
    r.expect(p.returncode == 2, "sweep bad --bench-root: exit 2", f"got {p.returncode}")
    r.expect("CLEAN" not in strip_ansi(p.stdout),
             "sweep bad --bench-root: does NOT print CLEAN", gist(p.stdout))

    # 3i. the sweep's EMPTY-CORPUS guard. The root must exist so execution
    #     reaches `if not files`; otherwise the seeded guard deletion is never
    #     exercised and can slip through this self-test undetected.
    empty_bench = Path(tmp) / "empty-sweep-corpus"
    empty_bench.mkdir()
    p = run([sys.executable, scripts["sweep"], "--bench-root", empty_bench],
            env={"AY_BIN": str(FAKE_AY)}, verbose=verbose)
    r.expect(p.returncode == 2, "sweep empty corpus: exit 2", f"got {p.returncode}")
    r.expect("CLEAN" not in strip_ansi(p.stdout),
             "sweep empty corpus: does NOT print CLEAN", gist(p.stdout))

    # 3j. the sweep's no-answer guard: AY never speaks.
    p = run([sys.executable, scripts["sweep"], "--bench-root",
             FIX / "guard", "no_answer", "--timeout", "10"],
            env={"AY_BIN": str(FAKE_AY)}, verbose=verbose)
    r.expect(p.returncode == 2, "sweep all-no-answer: exit 2", f"got {p.returncode}")
    r.expect("CLEAN" not in strip_ansi(p.stdout),
             "sweep all-no-answer: does NOT print CLEAN", gist(p.stdout))


def run_suite(scripts, verbose):
    r = Result()
    with tempfile.TemporaryDirectory(prefix="ay-selftest-") as tmp:
        test_checker(scripts, tmp, r, verbose)
        test_relative_corpus(scripts, tmp, r, verbose)
        test_sweep(scripts, tmp, r, verbose)
        test_guards(scripts, tmp, r, verbose)
    return r


def report(r, quiet_ok=False):
    for ok, label, detail in r.checks:
        if ok and quiet_ok:
            continue
        mark = f"{GRN}ok  {OFF}" if ok else f"{RED}FAIL{OFF}"
        print(f"  {mark} {label}")
        if not ok and detail:
            for line in str(detail).splitlines():
                print(f"       {DIM}{line}{OFF}")
    print(f"\n  {len(r.checks) - len(r.failed)}/{len(r.checks)} assertions passed")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed-fault", metavar="NAME",
                    help="apply a seeded defect ('all' for every one) and require "
                         "the suite to CATCH it")
    ap.add_argument("--list-faults", action="store_true")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()

    if args.list_faults:
        for name, (target, _, _, why) in FAULTS.items():
            print(f"{name:26s} {target.name:22s} {why}")
        return 0

    for tool in (CHECK_SH, SWEEP_PY, FAKE_AY):
        if not tool.exists():
            print(f"missing: {tool}", file=sys.stderr)
            return 2
    carcara = os.environ.get("CARCARA_BIN") or str(Path.home() / ".cargo/bin/carcara")
    if not (Path(carcara).exists() or shutil.which("carcara")):
        print("carcara not found; the proof harness cannot be self-tested without it",
              file=sys.stderr)
        return 2
    if not shutil.which(os.environ.get("Z3_BIN", "z3")):
        print("z3 not found; soundness_sweep adjudication cannot be self-tested",
              file=sys.stderr)
        return 2

    real = {"check": CHECK_SH, "sweep": SWEEP_PY}

    if not args.seed_fault:
        print(f"harness self-test: fixtures {FIX.relative_to(ROOT)}, "
              f"stub {FAKE_AY.name}\n")
        r = run_suite(real, args.verbose)
        report(r)
        if r.failed:
            print(f"\n{RED}SELF-TEST FAILED{OFF}: the proof harness misclassified "
                  f"{len(r.failed)} known-answer case(s).")
            print("Every number this harness has produced is suspect until this is green.")
            return 1
        print(f"\n{GRN}SELF-TEST PASSED{OFF}: every known-answer fixture classified "
              f"correctly, both measurement guards fire.")
        return 0

    names = list(FAULTS) if args.seed_fault == "all" else [args.seed_fault]
    for n in names:
        if n not in FAULTS:
            print(f"unknown fault {n!r}; try --list-faults", file=sys.stderr)
            return 2

    print(f"seeded-fault mode: re-introducing {len(names)} defect(s) and requiring "
          f"the suite to catch each one\n")
    slipped = []
    for name in names:
        target, old, new, why = FAULTS[name]
        with tempfile.TemporaryDirectory(prefix="ay-selftest-fault-") as tmp:
            scripts = {}
            for key, path in real.items():
                dst = Path(tmp) / path.name
                shutil.copy2(path, dst)
                scripts[key] = dst
            dst = Path(tmp) / target.name
            src = dst.read_text()
            # An anchor must be present AND unique. An ambiguous one silently
            # patches the wrong occurrence -- the first version of the
            # relative-symlink fault matched the explanatory COMMENT that quotes
            # the same line, so the defect was never applied and the suite was
            # reported as having no teeth. A fault you cannot apply is not
            # evidence about the suite; it is a broken test.
            n = src.count(old)
            if n != 1:
                print(f"{RED}BROKEN FAULT{OFF} {name}: anchor occurs {n} times in "
                      f"{target.name} (need exactly 1); re-anchor it")
                slipped.append(name)
                continue
            dst.write_text(src.replace(old, new, 1))
            r = run_suite(scripts, args.verbose)
            caught = bool(r.failed)
            mark = f"{GRN}caught{OFF}" if caught else f"{RED}SLIPPED THROUGH{OFF}"
            print(f"  {mark:24s} {name}")
            print(f"           {DIM}{why}{OFF}")
            if caught:
                for _, label, detail in r.failed[:4]:
                    print(f"           {YEL}->{OFF} {label}")
                    if detail:
                        print(f"              {DIM}{str(detail).splitlines()[0]}{OFF}")
            else:
                slipped.append(name)

    print()
    if slipped:
        print(f"{RED}SELF-TEST HAS NO TEETH{OFF} for: {', '.join(slipped)}")
        print("These defects can be re-introduced without any fixture noticing.")
        return 1
    print(f"{GRN}ALL {len(names)} SEEDED FAULTS CAUGHT{OFF} - the suite can go red.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
