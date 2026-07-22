#!/usr/bin/env python3
# ay-script: word-eq-diff-fuzz
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Differential fuzzer for the string word-equation fragment (Track A3).

Generates random QF_S / QF_SLIA formulas over the word-equation fragment
(string variables, literals, str.++ equalities/disequalities, optional exact
str.len facts, QUADRATIC repeated-variable equation templates, random
`str.in_re` memberships over a small regex grammar — Stage 2 coverage —
plus Stage 3 shapes: var-var splits `x = y·z` with memberships on every
piece, and INTERVAL str.len bounds `<=`/`>=`/`<`/`>`),
solves each with both AY and z3, and reports any sat/unsat DISAGREEMENT.
When AY answers `sat`, its model is additionally z3-PINNED: the model values
are asserted back into z3 together with the original formula, and z3 must
agree the pinned formula is sat (catches wrong models even when both solvers
say sat).

Usage:
  python3 scripts/fuzz/word_eq_diff_fuzz.py --count 2000 --seed 0 \
      --ay target/debug/ay --z3 /opt/homebrew/bin/z3

Exit code 0 iff DISAGREE == 0 and PIN-FAIL == 0.
"""

import argparse
import json
import math
import random
import re
import sys
import tempfile
import os
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
REPO = SCRIPTS.parent
sys.path.insert(0, str(SCRIPTS))
from _oom_guard import (  # noqa: E402
    plan_solver_resources,
    run_captured,
    warn_concurrent_build,
)

ALPHABET = "ab"


def gen_word(rng, vars_, max_syms=4, lit_max=3):
    """A word: SMT (str.++ ...) over variables and literals."""
    n = rng.randint(1, max_syms)
    parts = []
    for _ in range(n):
        if vars_ and rng.random() < 0.55:
            parts.append(rng.choice(vars_))
        else:
            lit = "".join(rng.choice(ALPHABET) for _ in range(rng.randint(0, lit_max)))
            parts.append('"%s"' % lit)
    if len(parts) == 1:
        return parts[0]
    return "(str.++ %s)" % " ".join(parts)


def gen_lit(rng, lit_max=3):
    return "".join(rng.choice(ALPHABET) for _ in range(rng.randint(0, lit_max)))


def gen_quadratic_eq(rng, vars_):
    """A repeated-variable (quadratic-class) equation template."""
    v = rng.choice(vars_)
    l1, l2, l3 = (gen_lit(rng, 2) for _ in range(3))
    templates = [
        # v·l1·v = l2·v·l3
        '(assert (= (str.++ %s "%s" %s) (str.++ "%s" %s "%s")))' % (v, l1, v, l2, v, l3),
        # v·v = l1
        '(assert (= (str.++ %s %s) "%s"))' % (v, v, l1),
        # rotation shape: v·l1·v·l2 = l2·v·l1·v
        '(assert (= (str.++ %s "%s" %s "%s") (str.++ "%s" %s "%s" %s)))'
        % (v, l1, v, l2, l2, v, l1, v),
        # commutation: v·l1 = l1·v
        '(assert (= (str.++ %s "%s") (str.++ "%s" %s)))' % (v, l1, l1, v),
    ]
    return rng.choice(templates)


def gen_regex(rng, depth=0):
    """A random ground regex over the fuzz alphabet (Stage 2 grammar)."""
    leaf_only = depth >= 2 or rng.random() < 0.4
    if leaf_only:
        r = rng.random()
        if r < 0.5:
            return '(str.to_re "%s")' % gen_lit(rng, 2)
        if r < 0.75:
            return "(re.range \"a\" \"b\")"
        if r < 0.9:
            return "re.allchar"
        if r < 0.97:
            return "re.all"
        return "re.none"
    op = rng.random()
    if op < 0.25:
        return "(re.* %s)" % gen_regex(rng, depth + 1)
    if op < 0.45:
        return "(re.+ %s)" % gen_regex(rng, depth + 1)
    if op < 0.6:
        return "(re.opt %s)" % gen_regex(rng, depth + 1)
    if op < 0.75:
        return "(re.++ %s %s)" % (gen_regex(rng, depth + 1), gen_regex(rng, depth + 1))
    if op < 0.88:
        return "(re.union %s %s)" % (gen_regex(rng, depth + 1), gen_regex(rng, depth + 1))
    if op < 0.95:
        lo = rng.randint(0, 3)
        return "((_ re.loop %d %d) %s)" % (lo, lo + rng.randint(0, 3), gen_regex(rng, depth + 1))
    return "(re.inter %s %s)" % (gen_regex(rng, depth + 1), gen_regex(rng, depth + 1))


def gen_case(rng):
    """One random formula in the word-equation fragment."""
    nvars = rng.randint(1, 4)
    vars_ = ["v%d" % i for i in range(nvars)]
    lines = []
    has_len = rng.random() < 0.4
    logic = "QF_SLIA" if has_len else "QF_S"
    lines.append("(set-logic %s)" % logic)
    for v in vars_:
        lines.append("(declare-const %s String)" % v)
    for _ in range(rng.randint(1, 3)):
        lines.append("(assert (= %s %s))" % (gen_word(rng, vars_), gen_word(rng, vars_)))
    # Stage 2: quadratic repeated-variable templates.
    for _ in range(rng.randint(0, 2)):
        if rng.random() < 0.5:
            lines.append(gen_quadratic_eq(rng, vars_))
    for _ in range(rng.randint(0, 2)):
        if rng.random() < 0.5:
            lines.append(
                "(assert (not (= %s %s)))" % (gen_word(rng, vars_), gen_word(rng, vars_))
            )
    # M2 coverage: positive contains/prefixof/suffixof over concat words.
    for _ in range(rng.randint(0, 2)):
        pred = rng.choice(["str.contains", "str.prefixof", "str.suffixof"])
        lines.append(
            "(assert (%s %s %s))"
            % (pred, gen_word(rng, vars_, max_syms=2), gen_word(rng, vars_, max_syms=2))
        )
    # Stage 2: regex memberships (both polarities).
    for _ in range(rng.randint(0, 2)):
        if rng.random() < 0.6:
            v = rng.choice(vars_)
            membership = "(str.in_re %s %s)" % (v, gen_regex(rng))
            if rng.random() < 0.25:
                membership = "(not %s)" % membership
            lines.append("(assert %s)" % membership)
    # Stage 3a: var-var split with memberships on every piece (the regex
    # decomposition path: x = y·z propagates x's constraint onto y and z).
    if len(vars_) >= 3 and rng.random() < 0.35:
        a, b, c = rng.sample(vars_, 3)
        lines.append("(assert (= %s (str.++ %s %s)))" % (a, b, c))
        for v in (a, b, c):
            if rng.random() < 0.7:
                lines.append("(assert (str.in_re %s %s))" % (v, gen_regex(rng)))
    if has_len:
        # Stage 3b: mix exact lengths with faithful interval bounds
        # (either orientation, strict and non-strict).
        for _ in range(rng.randint(1, 3)):
            v = rng.choice(vars_)
            r = rng.random()
            if r < 0.35:
                lines.append("(assert (= (str.len %s) %d))" % (v, rng.randint(0, 3)))
            elif r < 0.6:
                op = rng.choice(["<=", "<"])
                lines.append("(assert (%s (str.len %s) %d))" % (op, v, rng.randint(0, 4)))
            elif r < 0.85:
                op = rng.choice([">=", ">"])
                lines.append("(assert (%s (str.len %s) %d))" % (op, v, rng.randint(0, 3)))
            else:
                # Reversed orientation: (op N (str.len v)).
                op = rng.choice(["<=", ">="])
                lines.append("(assert (%s %d (str.len %s)))" % (op, rng.randint(0, 4), v))
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n", vars_


def run_solver(cmd, path, timeout, plan):
    try:
        p = run_captured(
            cmd + [path],
            plan.memlimit_mb,
            timeout,
            label="fuzz/word_eq_diff_fuzz.py",
            env=dict(
                os.environ,
                MEMLIMIT=str(plan.memlimit_mb),
                NBCORE=str(plan.nbcore),
            ),
        )
    except OSError:
        return "crash"
    if p.memout:
        return "memout"
    if p.timed_out:
        return "timeout"
    if p.output_truncated:
        return "crash"
    for line in p.stdout.splitlines():
        line = line.strip()
        if line in ("sat", "unsat", "unknown"):
            return line
        if line == "timeout":  # z3's own -T wall limit fired (nonzero exit)
            return "timeout"
    # No verdict at all: distinguish a crashed solver from a sound "unknown",
    # so a broken build cannot skip every case and still exit 0.
    return "crash" if p.returncode != 0 else "unknown"


def ay_model(ay, path, timeout, plan):
    """Return {var: value} from `ay solve` with (get-model), or None."""
    with open(path) as f:
        text = f.read()
    mpath = path + ".gm.smt2"
    with open(mpath, "w") as f:
        f.write(text + "(get-model)\n")
    try:
        result = run_captured(
            [ay, "solve", "--memory", str(plan.memlimit_mb), mpath],
            plan.memlimit_mb,
            timeout,
            label="fuzz/word_eq_diff_fuzz.py[model]",
            env=dict(
                os.environ,
                MEMLIMIT=str(plan.memlimit_mb),
                NBCORE=str(plan.nbcore),
            ),
        )
        if (
            result.memout
            or result.timed_out
            or result.output_truncated
            or result.returncode != 0
        ):
            return None
        out = result.stdout
    except OSError:
        return None
    finally:
        os.unlink(mpath)
    model = {}
    for m in re.finditer(r'\(define-fun (\S+) \(\) String "((?:[^"]|"")*)"\)', out):
        model[m.group(1)] = m.group(2)
    return model if model else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--ay", default="target/debug/ay")
    ap.add_argument("--z3", default="/opt/homebrew/bin/z3")
    ap.add_argument("--timeout", type=float, default=10.0)
    ap.add_argument("--keep-failures", default=None, help="dir to save disagreeing cases")
    ap.add_argument(
        "--evidence-out",
        type=Path,
        default=REPO / "evals/results/word-eq-diff-fuzz/latest.json",
        help="JSON evidence output (includes the enforced resource envelope)",
    )
    args = ap.parse_args()
    if args.count <= 0 or not math.isfinite(args.timeout) or args.timeout <= 0:
        ap.error("--count and --timeout must be finite and positive")

    warn_concurrent_build()
    plan = plan_solver_resources(1, label="fuzz/word_eq_diff_fuzz.py")
    envelope = {
        "requested_jobs": 1,
        "jobs": plan.jobs,
        "memlimit_mb_per_child": plan.memlimit_mb,
        "nbcore_per_child": plan.nbcore,
        "headroom_mb": plan.headroom_mb,
        "enforcement": (
            "ay --memory; process-group rss_watchdog; MEMLIMIT/NBCORE environment"
        ),
    }
    print("resource plan: %s" % json.dumps(envelope, sort_keys=True))

    rng = random.Random(args.seed)
    agree = skip = disagree = pinfail = 0
    ay_crash = z3_crash = 0
    ay_memout = z3_memout = 0
    with tempfile.TemporaryDirectory() as td:
        for i in range(args.count):
            text, vars_ = gen_case(rng)
            path = os.path.join(td, "case%d.smt2" % i)
            with open(path, "w") as f:
                f.write(text)
            ay_res = run_solver(
                [args.ay, "solve", "--memory", str(plan.memlimit_mb)],
                path,
                args.timeout,
                plan,
            )
            z3_res = run_solver(
                [args.z3, "-T:%d" % max(1, int(args.timeout))],
                path,
                args.timeout,
                plan,
            )
            if ay_res == "memout":
                ay_memout += 1
            if z3_res == "memout":
                z3_memout += 1
            if ay_res == "crash" or z3_res == "crash":
                if ay_res == "crash":
                    ay_crash += 1
                    print("CRASH case %d (seed %d): ay exited nonzero with no verdict" % (i, args.seed))
                if z3_res == "crash":
                    z3_crash += 1
                    print("CRASH case %d (seed %d): z3 exited nonzero with no verdict" % (i, args.seed))
                continue
            if ay_res in ("unknown", "timeout", "memout") or z3_res in (
                "unknown",
                "timeout",
                "memout",
            ):
                skip += 1
                continue
            if ay_res != z3_res:
                disagree += 1
                print("DISAGREE case %d (seed %d): ay=%s z3=%s" % (i, args.seed, ay_res, z3_res))
                print(text)
                if args.keep_failures:
                    os.makedirs(args.keep_failures, exist_ok=True)
                    with open(
                        os.path.join(args.keep_failures, "seed%d_case%d.smt2" % (args.seed, i)),
                        "w",
                    ) as f:
                        f.write(text)
                continue
            agree += 1
            # z3-pin AY's sat model.
            if ay_res == "sat":
                model = ay_model(args.ay, path, args.timeout, plan)
                if model:
                    pin = text.replace("(check-sat)", "")
                    for v, val in model.items():
                        if v in vars_:
                            pin += '(assert (= %s "%s"))\n' % (v, val)
                    pin += "(check-sat)\n"
                    ppath = path + ".pin.smt2"
                    with open(ppath, "w") as f:
                        f.write(pin)
                    pres = run_solver(
                        [args.z3, "-T:%d" % max(1, int(args.timeout))],
                        ppath,
                        args.timeout,
                        plan,
                    )
                    if pres == "unsat":
                        pinfail += 1
                        print("PIN-FAIL case %d (seed %d): model %r rejected by z3" % (i, args.seed, model))
                        print(text)
                        if args.keep_failures:
                            os.makedirs(args.keep_failures, exist_ok=True)
                            base = os.path.join(
                                args.keep_failures, "seed%d_case%d" % (args.seed, i)
                            )
                            with open(base + ".smt2", "w") as f:
                                f.write(text)
                            with open(base + ".pin.smt2", "w") as f:
                                f.write(pin)
            if (i + 1) % 200 == 0:
                print(
                    "  ... %d/%d agree=%d skip=%d disagree=%d pinfail=%d crash=%d/%d"
                    % (i + 1, args.count, agree, skip, disagree, pinfail, ay_crash, z3_crash),
                    flush=True,
                )

    comparable = agree + disagree
    print(
        "DONE seed=%d count=%d agree=%d skip=%d DISAGREE=%d PIN-FAIL=%d AY-CRASH=%d Z3-CRASH=%d"
        % (args.seed, args.count, agree, skip, disagree, pinfail, ay_crash, z3_crash)
    )
    evidence = {
        "schema": "ay-word-eq-diff-fuzz-v1",
        "seed": args.seed,
        "count": args.count,
        "ay_binary": args.ay,
        "z3_binary": args.z3,
        "timeout_seconds": args.timeout,
        "agree": agree,
        "skip": skip,
        "disagree": disagree,
        "pin_fail": pinfail,
        "ay_crash": ay_crash,
        "z3_crash": z3_crash,
        "ay_memout": ay_memout,
        "z3_memout": z3_memout,
        "comparable": comparable,
        "resource_plan": envelope,
    }
    args.evidence_out.parent.mkdir(parents=True, exist_ok=True)
    args.evidence_out.write_text(
        json.dumps(evidence, indent=2) + "\n", encoding="utf-8"
    )
    print("evidence: %s" % args.evidence_out)
    # ay-side crashes are failures: a build that crashes on every case must not
    # report a green differential run. z3 crashes are environment noise (loud
    # in the totals above) and do not fail the run by themselves.
    if disagree or pinfail or ay_crash:
        return 1
    if comparable == 0:
        # A missing solver or a build that times out/memouts on every formula
        # must not turn the differential audit vacuously green.
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
