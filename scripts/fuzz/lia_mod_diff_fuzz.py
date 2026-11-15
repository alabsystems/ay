#!/usr/bin/env python3
# ay-script: lia-mod-diff-fuzz
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Differential fuzzer for QF_LIA with `mod`/`div` by small constants: AY vs z3.

The CHC-COMP 2026 campaign found AY answering `unknown` on trivially-unsat
parity obligations (the development design notes).
This generator produces conjunctions (and a few small disjunctions) over 2-4
integer variables, mostly UNBOUNDED, mixing

  * linear equalities with small coefficients,
  * difference / two-variable bounds (strict and non-strict),
  * optional unary box bounds,
  * `mod` / `div` atoms by k in {2..6}, negated or not,
  * CHC-style shapes: an invariant body (equalities + slab bounds), a parity
    guard and an `ite`-over-`mod` successor inequality.

Each instance is run through z3 (the oracle) and AY. A sat/unsat disagreement
is a SOUNDNESS bug: it is printed with `[DISAGREE]`, the witness is kept, and
the process exits 2. Summary counts are written as JSON.

Usage:
  python3 scripts/fuzz/lia_mod_diff_fuzz.py --ay ~/ay-bench/ay-land3c-20260925 \
      --n 3000 --seed 1 --timeout 5 --jobs 8 --out-dir /tmp/liamod
Run it under ~/ay-bench/locks/with-measure.sh on the shared Mac.
"""
import argparse
import json
import os
import random
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

VARS_ALL = ["a", "b", "c", "d"]


def lin(rng, vs, max_terms=3, max_coeff=3):
    k = rng.randint(1, min(max_terms, len(vs)))
    chosen = rng.sample(vs, k)
    parts = []
    for v in chosen:
        c = rng.choice([x for x in range(-max_coeff, max_coeff + 1) if x != 0])
        if c == 1:
            parts.append(v)
        elif c == -1:
            parts.append(f"(- {v})")
        else:
            parts.append(f"(* {c} {v})")
    if rng.random() < 0.3:
        parts.append(str(rng.randint(-3, 3)))
    return parts[0] if len(parts) == 1 else "(+ " + " ".join(parts) + ")"


def mod_atom(rng, vs):
    k = rng.randint(2, 6)
    arg = lin(rng, vs, max_terms=2, max_coeff=2) if rng.random() < 0.5 else rng.choice(vs)
    r = rng.randint(0, k - 1)
    atom = f"(= (mod {arg} {k}) {r})"
    return f"(not {atom})" if rng.random() < 0.4 else atom


def div_atom(rng, vs):
    k = rng.randint(2, 5)
    x = rng.choice(vs)
    shape = rng.random()
    if shape < 0.35 and len(vs) >= 2:
        y = rng.choice([v for v in vs if v != x])
        return f"(= {y} (div {x} {k}))"
    if shape < 0.6:
        return f"(= (* {k} (div {x} {k})) {x})"
    if shape < 0.8:
        op = rng.choice(["<=", ">=", "<", ">"])
        return f"({op} (div {lin(rng, vs, 2, 2)} {k}) {lin(rng, vs, 1, 2)})"
    y = rng.choice(vs)
    return f"(not (= (div {x} {k}) {y}))"


def pair_bound(rng, vs):
    x, y = rng.sample(vs, 2)
    op = rng.choice(["<=", "<", ">=", ">"])
    c = rng.randint(-2, 2)
    rhs = y if c == 0 else f"(+ {y} {c})"
    return f"({op} {x} {rhs})"


def lin_eq(rng, vs):
    lhs = lin(rng, vs)
    if rng.random() < 0.5:
        return f"(= {lhs} {rng.randint(-3, 3)})"
    return f"(= {lhs} {rng.choice(vs)})"


def unary_bound(rng, vs):
    v = rng.choice(vs)
    op = rng.choice(["<=", "<", ">=", ">"])
    return f"({op} {v} {rng.randint(-6, 6)})"


def random_conjunct(rng, vs, boxed):
    r = rng.random()
    if r < 0.18:
        return lin_eq(rng, vs)
    if r < 0.48:
        return pair_bound(rng, vs)
    if r < 0.70:
        return mod_atom(rng, vs)
    if r < 0.82:
        return div_atom(rng, vs)
    if r < 0.90 and boxed:
        return unary_bound(rng, vs)
    if r < 0.95:
        return f"(or {random_conjunct(rng, vs, boxed)} {random_conjunct(rng, vs, boxed)})"
    op = rng.choice(["<=", "<", ">=", ">"])
    return f"({op} {lin(rng, vs)} {rng.randint(-4, 4)})"


def chc_shape(rng, vs):
    """Invariant body + parity guard + ite-over-mod successor (s_split_12-like)."""
    x, y, z = (vs + vs)[:3] if len(vs) < 3 else rng.sample(vs, 3)
    k = rng.choice([2, 2, 2, 3, 4])
    lits = []
    # body: x = y + z (or a scaled variant), slab y - z in [lo, lo + w]
    cy, cz = rng.choice([1, 1, 2]), rng.choice([1, 1, 2])
    lits.append(f"(= {x} (+ (* {cy} {y}) (* {cz} {z})))")
    lo = rng.randint(-1, 1)
    w = rng.choice([0, 1, 1, 2])
    lits.append(f"(<= (+ {z} {lo}) {y})")
    strict = rng.random() < 0.5
    if strict:
        lits.append(f"(< {y} (+ {z} {lo + w + 1}))")
    else:
        lits.append(f"(<= {y} (+ {z} {lo + w}))")
    r = rng.randint(0, k - 1)
    guard = f"(= (mod {x} {k}) {r})"
    lits.append(f"(not {guard})" if rng.random() < 0.5 else guard)
    if rng.random() < 0.6:
        # negated successor bound through an ite over the parity guard
        a1, a0 = rng.randint(0, 1), rng.randint(0, 1)
        succ_y = f"(ite {guard} (+ {y} {a1}) (+ {y} {a0}))"
        succ_z = f"(ite {guard} {z} (+ {z} 1))"
        op = rng.choice(["<=", "<", ">=", ">"])
        lits.append(f"(not ({op} {succ_y} (+ {succ_z} {rng.randint(0, 1)})))")
    if rng.random() < 0.3:
        lits.append(pair_bound(rng, vs))
    return lits


def gen_instance(rng):
    nv = rng.randint(2, 4)
    vs = VARS_ALL[:nv]
    boxed = rng.random() < 0.25
    lits = []
    family = "chc" if rng.random() < 0.3 else "random"
    if family == "chc":
        lits.extend(chc_shape(rng, vs if nv >= 3 else VARS_ALL[:3]))
        vs = VARS_ALL[: max(nv, 3)]
    for _ in range(rng.randint(2 if family == "chc" else 3, 7) - (3 if family == "chc" else 0)):
        lits.append(random_conjunct(rng, vs, boxed))
    if boxed:
        for v in vs:
            if rng.random() < 0.8:
                lo = rng.randint(-8, 0)
                lits.append(f"(<= {lo} {v})")
                lits.append(f"(<= {v} {lo + rng.randint(0, 12)})")
    out = ["(set-logic QF_LIA)"]
    out += [f"(declare-fun {v} () Int)" for v in vs]
    out += [f"(assert {lit})" for lit in lits]
    out.append("(check-sat)")
    return family, boxed, "\n".join(out) + "\n"


def verdict(text):
    for line in text.splitlines():
        s = line.strip()
        if s in ("sat", "unsat", "unknown"):
            return s
    return "error"


def run(cmd, timeout):
    t0 = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        return verdict(p.stdout), time.time() - t0
    except subprocess.TimeoutExpired:
        return "timeout", time.time() - t0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--ay", required=True)
    ap.add_argument("--z3", default="/opt/homebrew/bin/z3")
    ap.add_argument("--n", type=int, default=1000)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--timeout", type=float, default=5.0, help="seconds per solver run")
    ap.add_argument("--memory", type=int, default=2048, help="AY --memory (MB)")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--ay-flags", default="", help="extra AY flags, e.g. --competition")
    ap.add_argument("--out-dir", required=True)
    ap.add_argument("--keep-all", action="store_true", help="keep every instance file")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    rng = random.Random(args.seed)
    insts = [(i,) + gen_instance(rng) for i in range(args.n)]
    ms = int(args.timeout * 1000)

    def one(item):
        i, family, boxed, smt = item
        path = os.path.join(args.out_dir, f"i{args.seed}_{i:05d}.smt2")
        with open(path, "w") as f:
            f.write(smt)
        z3v, z3t = run([args.z3, f"-T:{int(args.timeout)}", path], args.timeout + 2)
        ay_cmd = [args.ay, "--memory", str(args.memory), "--timeout", str(ms)]
        ay_cmd += args.ay_flags.split() + [path]
        ayv, ayt = run(ay_cmd, args.timeout + 5)
        for ext in (".alethe", ".alethe.tmp"):
            try:
                os.remove(path + ext)
            except OSError:
                pass
        keep = args.keep_all or ayv != z3v
        if not keep:
            os.remove(path)
        return dict(i=i, family=family, boxed=boxed, z3=z3v, ay=ayv, z3t=round(z3t, 3), ayt=round(ayt, 3), path=path if keep else None)

    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        rows = list(ex.map(one, insts))

    disagree = [r for r in rows if {r["z3"], r["ay"]} == {"sat", "unsat"}]
    summary = {"n": len(rows), "seed": args.seed, "ay_bin": args.ay, "ay_flags": args.ay_flags}
    for key in ("z3", "ay"):
        summary[key] = {v: sum(1 for r in rows if r[key] == v) for v in ("sat", "unsat", "unknown", "timeout", "error")}
    decided = [r for r in rows if r["z3"] in ("sat", "unsat")]
    summary["z3_decided"] = len(decided)
    summary["ay_undecided_on_z3_decided"] = sum(1 for r in decided if r["ay"] not in ("sat", "unsat"))
    summary["ay_undecided_unsat"] = sum(1 for r in decided if r["z3"] == "unsat" and r["ay"] not in ("sat", "unsat"))
    summary["ay_undecided_sat"] = sum(1 for r in decided if r["z3"] == "sat" and r["ay"] not in ("sat", "unsat"))
    summary["disagreements"] = len(disagree)
    by_family = {}
    for r in decided:
        b = by_family.setdefault(f"{r['family']}{'-boxed' if r['boxed'] else ''}", [0, 0])
        b[0] += 1
        b[1] += r["ay"] not in ("sat", "unsat")
    summary["undecided_by_family"] = by_family
    with open(os.path.join(args.out_dir, f"summary_seed{args.seed}.json"), "w") as f:
        json.dump(summary, f, indent=1)
    with open(os.path.join(args.out_dir, f"rows_seed{args.seed}.jsonl"), "w") as f:
        for r in rows:
            f.write(json.dumps(r) + "\n")
    for r in disagree:
        print(f"[DISAGREE] z3={r['z3']} ay={r['ay']} {r['path']}", flush=True)
    print(json.dumps(summary, indent=1))
    sys.exit(2 if disagree else 0)


if __name__ == "__main__":
    main()
