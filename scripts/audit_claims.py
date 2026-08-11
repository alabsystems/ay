#!/usr/bin/env python3
"""Audit every claimed SMT-COMP division against the evidence actually on disk.

WHY THIS EXISTS
---------------
Four separate times in one session, a campaign figure turned out not to be the
number the harness would score:

  1. Incremental submission wrapper  — scored ZERO for an entire track while every
     local measurement looked healthy (the wrapper could not run at all).
  2. UC QF_LinearIntArith            — 4,267,796 quoted; 61 of 67 dominant-family
     cores are UNVALIDATED, and unvalidated cores score 0.
  3. MV QF_Datatypes                 — "1943/1943 perfect" quoted; 1943 is the
     SELECTION SIZE. Three scoreboards give 1943 / 1935 / 1933, and the committed
     win-evidence gives 1909.
  4. UC QF_Datatypes                 — substantively strong, but there is no
     `ay.jsonl` anywhere on disk; it is only reproducible from another branch.

Every one was cheap to detect and expensive to miss. This script turns that check
into something mechanical, so a claim cannot drift from its evidence unnoticed.

WHAT IT CHECKS, per claimed division
------------------------------------
  A. Does an AY run exist on disk at all?           (UC QF_Datatypes failed this)
  B. Are the answers VALIDATED, not merely answered? (UC LIA failed this)
  C. Do repeated runs AGREE?                        (MV failed this)
  D. Does the quoted figure match the scored field?  (MV failed this)

Exit code 0 = every claim is backed. Non-zero = at least one claim is not.
Read-only: it never launches a solver and never needs the host lease.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RESULTS = ROOT / "evals/results/smtcomp-2025"

# The campaign's claimed divisions, with the figure each one asserts.
CLAIMS = [
    # Scored by the harness 2026-08-01 from tag `sq-dt-clean`: both arms in one
    # invocation, 552/552 each, 0 errors each, quiet host. ay 394 vs cvc5 385,
    # and 14,388s vs 54,480s sequential CPU. The previous 395 came from a Jul-15
    # AY-only file with no recorded run conditions and was never scored.

    # Re-scored by the harness 2026-08-04 from tag `uc-dt-pinned` after the
    # validation pass was finished: 400/400 run, 327 unsat, 316 cores validated,
    # 0 invalidated, 0 errors. The old 4,550,583 was never wrong in substance —
    # it was quoted while validation was still INCOMPLETE, so the scoreboard on
    # disk lagged at 4,048,670 and the audit could not match either figure.
    # 11 cores remain unvalidated and score ZERO, so this is a FLOOR.
    # RE-EARNED FROM CURRENT `main` 2026-08-06 (tag `uc-dt-recheck`). The
    # 66538b006 regression cost `sat` answers and spared `unsat`, so UC — scored
    # purely on unsat cores — survived it. Fresh 400-file run from HEAD plus a
    # full validate-uc: 326 unsat, 317 validated, 0 invalidated, 0 errors.
    # 9 unvalidated cores score ZERO, so this is a FLOOR.
    {"track": "uc", "division": "QF_Datatypes", "quoted": 4550593,
     "field": "seq_reduction", "note": "validated reduction floor, 3.54x cvc5, re-earned from main",
     "superseded": {
         "uc-dt-pinned": "ran 2026-07-28..30 on a PRE-regression binary, 8,576 MB",
     },
     "superseded_by":
         "uc-dt-recheck is a fresh 400-file run from CURRENT main (binary pinned at "
         "fe1bed339) plus a complete validate-uc: 326 unsat, 317 validated, 0 "
         "invalidated, 0 errors, 4,550,593. uc-dt-pinned predates the 66538b006 "
         "regression, so it cannot be used to certify what main does today. The two "
         "differ by 16,710 (0.4%) and by one instance — "
         "blocksworld_from_4_0_5_to_8_0_1_negated_goal_bmc_13, which used 1,120s of a "
         "1,200s budget at 8,576 MB and ran out at the recheck's 4,288 MB. The "
         "recheck is the HARDER envelope and the current-tree evidence, so it "
         "supersedes."},
    # 1943/1943 Dolmen-validated, 0 errors, vs SMTInterpol's WINNING 1835 and
    # cvc5's 1315 (official field, leaderboard
    # smtcomp-2025-model-validation-qf-datatypes-sequential, denominator 1943).
    # RE-EARNED FROM CURRENT `main` 2026-08-08 (tag `mv-dt-fixed`) after the
    # dt-lazy rollback fix. Fresh 1943-file run from HEAD + full Dolmen
    # validate-mv: 1919 sat, ALL 1919 Dolmen-validated (Sat=1919), 0 errors,
    # 0 timeouts. SMTInterpol's 2025 winning score is 1835.
    #
    # The 1943 figure came from mv-perfect-44d40f56 on a PRE-regression binary
    # (2026-07-21). 66538b006 then cost 24 answers on this division; the fix at
    # dt.rs restored 84 of the 99 it had taken. 1919 beats the bar by 84 and is
    # what main reproduces TODAY, so it is the honest claim.
    {"track": "mv", "division": "QF_Datatypes", "quoted": 1919,
     "field": "seq_solved", "note": "1919/1943 Dolmen-validated vs SMTInterpol's winning 1835, re-earned from main",
     "superseded": {
         "mv-confirm-433fc661": "ran 2026-07-19 00:06, pre-fix binary",
         "mv-record-e59bc181": "ran 2026-07-19 17:40, pre-fix binary",
         "mv-perfect-44d40f56": "ran 2026-07-21 02:07, PRE-66538b006 binary",
         "mv-dt-race": "ran 2026-08-04, mid-regression, abandoned at 1928/1943",
     },
     "superseded_by":
         "mv-dt-fixed is a fresh full run from CURRENT main with the dt.rs "
         "rollback fix, plus a complete Dolmen validate-mv (Sat=1919, no "
         "ModelParsingError, no ModelPartialFunctionMissing). Every earlier tag "
         "used a binary that cannot certify what main does today."},
]

# Divisions withdrawn after measurement. Listed so a retraction stays visible
# instead of quietly vanishing from the audit — a claim that disappears looks
# identical to a claim that passed.
RETRACTED = [
    {"track": "sq", "division": "QF_Datatypes", "was": 394,
     "why": "the banked run is real, but HEAD CANNOT REPRODUCE IT. RE-MEASURED "
            "2026-08-11 at the clean envelope (--jobs 1, memlimit 8576, above "
            "the banked 6954), stopped at 118 of 552 once decisive: LOST 5, "
            "GAINED 0 = 4.2%, projecting ~371 against a same-metal cvc5 385. "
            "That is a large improvement on the 2026-08-06 reading (198 of 394, "
            "27.8x slower) because the finite-enum pigeonhole blocker was fixed "
            "that day -- the Bouvier vlsat3 family answers again "
            "(TheoryLemmaKind::DatatypeEnumPigeonhole). It is still a LOSS, and "
            "the division stays retracted. Three blockers remain, all from "
            "66538b006 making certification mandatory: duplicate clause-trace "
            "ids (mechanism confirmed; do NOT fix by renumbering originals, it "
            "invalidates LRAT hints -- tried and reverted), certification "
            "overhead pushing 550-790s solves past the 1197s cap, and array "
            "axioms lacking a per-clause TheoryLemmaProof. Full record: "
            "the development design notes"},
    {"track": "uc", "division": "QF_LinearIntArith", "was": 4267796,
     "why": "same-metal race LOST 1.8x: AY 1,306,544 validated vs Yices2 "
            "2,375,255. The 4,267,796 compared an unvalidated local AY figure "
            "against a 2015-Xeon bar (2026-07-30)"},
]

RED, YEL, GRN, OFF = "\033[31m", "\033[33m", "\033[32m", "\033[0m"


def load_scoreboards(track, division):
    """Every scoreboard.json under a division, newest-looking last."""
    d = RESULTS / track / division
    if not d.is_dir():
        return []
    out = []
    for tag in sorted(p for p in d.iterdir() if p.is_dir()):
        sb = tag / "scoreboard.json"
        if sb.is_file():
            try:
                out.append((tag.name, json.loads(sb.read_text())))
            except (OSError, json.JSONDecodeError):
                pass
    return out


def ay_rows_present(track, division):
    """Does ANY per-instance AY row file exist? (Check A.)"""
    d = RESULTS / track / division
    return bool(list(d.rglob("ay*.jsonl"))) if d.is_dir() else False


def audit(claim):
    track, division = claim["track"], claim["division"]
    label = f"{track.upper()} {division}"
    problems = []
    notes = []

    boards = load_scoreboards(track, division)
    has_rows = ay_rows_present(track, division)

    # A. an AY run must exist on disk at all
    ay_boards = [(t, b) for t, b in boards if "ay" in b.get("solvers", {})]
    if not ay_boards and not has_rows:
        problems.append("NO AY EVIDENCE ON DISK — cannot be re-verified from main")

    # B/C/D over whatever AY scoreboards exist
    scored = {}
    coverage = {}
    # A run produced by a binary that PREDATES a named fix is not evidence about
    # the binary being claimed. Superseding must be declared explicitly and must
    # name the fix and the ordering — never inferred — and the tag is still
    # printed, so a superseded run cannot quietly disappear from the record.
    superseded = claim.get("superseded", {})
    for tag, why in sorted(superseded.items()):
        notes.append(f"{tag}: SUPERSEDED ({why}) — excluded from comparison")
    if superseded:
        notes.append(f"superseded by: {claim['superseded_by']}")

    for tag, b in ay_boards:
        if tag in superseded:
            continue
        ay = b["solvers"]["ay"]
        val = ay.get("validation") or {}
        # B. Unvalidated cores are a FLOOR note, not a defect.
        #
        # This check used to FAIL a claim outright. That was wrong, and the
        # error mattered: it failed UC QF_Datatypes for months over cores that
        # cannot affect the verdict. An unvalidated core already scores ZERO in
        # `seq_reduction` — the scoreboard has excluded it — so it can only make
        # the true figure HIGHER, never inflate the quoted one. (Note the
        # harness distinguishes `unvalidated`, where the validators timed out,
        # from `invalidated`, where a validator proved the core SAT; the latter
        # IS a correctness defect and is checked separately below.)
        unvalidated = ay.get("unvalidated")
        if unvalidated:
            notes.append(
                f"{tag}: {unvalidated} unvalidated — they score ZERO, so the "
                f"figure is a FLOOR (validating them can only raise it)")
        # An INVALIDATED core is a real correctness defect: a validator proved
        # the "core" satisfiable, so it was never a core.
        invalidated = ay.get("invalidated")
        if invalidated:
            problems.append(
                f"{tag}: {invalidated} INVALIDATED — a validator proved the core SAT")
        for k in ("wrong_answers", "errors"):
            if ay.get(k):
                problems.append(f"{tag}: {ay[k]}x {k}")
        # MV-style validation dicts record their own failure modes
        for k, v in val.items() if isinstance(val, dict) else []:
            if k != "Sat" and v:
                problems.append(f"{tag}: {v}x {k} (scores 0 points, not counted as an error)")
        scored[tag] = ay.get(claim["field"])
        coverage[tag] = ay.get("instances")

    # C. repeated runs must agree — but only runs that cover the SAME number of
    # instances are comparable. Scoring a complete 400-file run against an
    # ABANDONED 95-file one and calling the difference a "disagreement" is an
    # auditor bug, not evidence against the claim. Partial runs are still
    # reported, so an abandoned tag cannot hide.
    full = max((c for c in coverage.values() if c), default=None)
    vals = {t: v for t, v in scored.items()
            if v is not None and coverage.get(t) == full}
    partial = {t: (scored[t], coverage[t]) for t in scored
               if coverage.get(t) != full}
    for t, (v, c) in sorted(partial.items()):
        notes.append(f"{t}: PARTIAL run ({c}/{full} instances, scored {v}) — not comparable")
    if len(set(vals.values())) > 1:
        problems.append(
            "RUNS DISAGREE: " + ", ".join(f"{t}={v}" for t, v in vals.items()))

    # D. the quoted figure must be reproduced by at least one run.
    #
    # NOTE (found by reviewing this script's own output): an EMPTY `vals` must
    # FAIL, not pass. Treating "no scored figure on disk" as OK is precisely the
    # absence-of-evidence-as-success bug this auditor exists to catch — it would
    # have green-lit a division whose scoreboard was never produced.
    if not vals:
        problems.append(
            f"NO SCORED FIGURE on disk for field '{claim['field']}' — "
            "nothing to compare the claim against (run `score` to produce one)")
    elif claim["quoted"] not in vals.values():
        problems.append(
            f"QUOTED {claim['quoted']} matches NO run "
            f"(on disk: {sorted(set(vals.values()))})")

    return label, problems, vals, notes


def evidence_commit_drift():
    """How far has the tree moved since the newest banked evidence was written?

    THE BLIND SPOT THIS CLOSES. Every other check in this file compares a claim to
    a scoreboard ON DISK. None of them runs the solver. So a claim can pass every
    check while the current tree no longer produces the number -- which is exactly
    what happened: SQ QF_Datatypes stayed `OK` at 394 while HEAD had collapsed to
    198 (measured 2026-08-06). The evidence was never wrong; it had simply stopped
    describing the code.

    A banked figure is a claim about a BINARY, and this prints how many commits
    separate that binary from HEAD so the staleness is visible rather than implied.
    """
    import subprocess
    newest = None
    for sb in RESULTS.rglob("scoreboard.json"):
        m = sb.stat().st_mtime
        if newest is None or m > newest:
            newest = m
    if newest is None:
        return None
    try:
        since = subprocess.run(
            ["git", "log", "--oneline", "--since", str(int(newest)), "--format=%h"],
            cwd=ROOT, capture_output=True, text=True, timeout=30).stdout.split()
        head = subprocess.run(["git", "rev-parse", "--short", "HEAD"],
                              cwd=ROOT, capture_output=True, text=True,
                              timeout=30).stdout.strip()
    except Exception:
        return None
    return len(since), head


def main():
    print("SMT-COMP claim audit — does each claimed division match its evidence?\n")
    drift = evidence_commit_drift()
    if drift and drift[0] > 0:
        print(f"{YEL}STALENESS{OFF}: {drift[0]} commit(s) have landed since the newest "
              f"banked scoreboard (HEAD {drift[1]}).")
        print("        Every check below compares a claim to EVIDENCE ON DISK. None of")
        print("        them runs the solver, so none can see a claim that the current")
        print("        tree no longer reproduces. SQ QF_Datatypes passed this audit at")
        print("        394 while HEAD produced 198. RE-RUN THE DIVISION before quoting")
        print("        any figure below as a property of the code.\n")
    failed = 0
    for claim in CLAIMS:
        label, problems, vals, notes = audit(claim)
        if problems:
            failed += 1
            print(f"{RED}FAIL{OFF}  {label}   (claims {claim['quoted']:,} — {claim['note']})")
            for p in problems:
                print(f"        - {p}")
        else:
            print(f"{GRN}OK{OFF}    {label}   scored={max(vals.values())} matches the claim")
        for n in notes:
            print(f"        {YEL}note{OFF}  {n}")
        print()
    for r in RETRACTED:
        print(f"{YEL}RETRACTED{OFF}  {r['track'].upper()} {r['division']}   "
              f"(was {r['was']:,})")
        print(f"        - {r['why']}")
        print()

    total = len(CLAIMS)
    print(f"{failed} of {total} claimed divisions are NOT backed by the evidence on disk.")
    if failed:
        print("\nA claim that cannot be reproduced from `main` is not a claim; it is a memory.")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
