#!/usr/bin/env python3
# ay-script: planted-sat-fuzz
"""Differential soundness fuzz for SCC equivalent-literal substitution (decompose).

Generates PLANTED-SATISFIABLE CNFs (a fixed assignment satisfies every clause),
heavy on equivalence cycles (the structure decompose's Tarjan-SCC collapses), at
densities where the density gate still runs decompose (< 50). Because every
instance is satisfiable by construction, ANY `s UNSATISFIABLE` verdict is a
provable soundness bug in substitution.

Background: config_preprocess.rs gates decompose off on dense formulas because
of a reported false-UNSAT (#8448). The original repro was lost to a squashed
history; 200 instances here did NOT reproduce it (the bug is well-contained /
possibly historical), but this harness stays as a regression net: run it with
decompose force-enabled (`--sat-variant probe`) and fail CI on any false UNSAT.

Usage: scripts/fuzz/decompose_planted_sat_fuzz.py [count] [ay-binary]
Exit: 0 = all planted-SAT instances solved SAT/UNKNOWN; 1 = a false UNSAT (bug).
"""
import random, subprocess, os, sys, tempfile

COUNT = int(sys.argv[1]) if len(sys.argv) > 1 else 120
BIN = sys.argv[2] if len(sys.argv) > 2 else (
    "target/release/ay" if os.path.exists("target/release/ay") else "target/debug/ay")


def gen(n, classes, density, seed):
    r = random.Random(seed)
    A = {v: r.choice([True, False]) for v in range(1, n + 1)}
    vs = list(range(1, n + 1)); r.shuffle(vs)
    cls = [vs[i::classes] for i in range(classes)]
    for c in cls:                       # equal planted value within an SCC
        if c:
            val = A[c[0]]
            for v in c:
                A[v] = val
    clauses = []
    for c in cls:                       # equivalence CYCLE per class -> big SCC
        for i in range(len(c)):
            x, y = c[i], c[(i + 1) % len(c)]
            if x != y:
                clauses.append([-x, y]); clauses.append([x, -y])
    target = int(density * n)
    while len(clauses) < target:        # planted wider clauses for density
        k = r.choice([2, 3, 3, 4, 5])
        lits = set()
        while len(lits) < k:
            v = r.randint(1, n); lits.add(v if r.random() < 0.5 else -v)
        lits = list(lits)
        if not any((l > 0) == A[abs(l)] for l in lits):
            i = r.randrange(len(lits)); v = abs(lits[i]); lits[i] = v if A[v] else -v
        clauses.append(lits)
    r.shuffle(clauses)
    for c in clauses:
        r.shuffle(c)
    return n, clauses


def run(n, clauses):
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        f.write(f"p cnf {n} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")
        path = f.name
    try:
        p = subprocess.run([BIN, path, "--sat-variant", "probe", "--no-proof"],
                           capture_output=True, text=True, timeout=20)
        s = [l for l in p.stdout.splitlines() if l.startswith("s ")]
        return (s[0] if s else "s ?"), path
    except subprocess.TimeoutExpired:
        return "TIMEOUT", path


bugs = 0
for seed in range(COUNT):
    R = random.Random(seed * 7 + 1)
    n = R.choice([40, 60, 90, 120]); classes = R.choice([2, 3, 5, 8])
    density = R.choice([12, 20, 28, 38, 46])
    nn, cl = gen(n, classes, density, seed)
    verd, path = run(nn, cl)
    if "UNSATISF" in verd:
        bugs += 1
        print(f"FALSE-UNSAT (decompose soundness bug): seed={seed} n={nn} "
              f"classes={classes} density~{density} clauses={len(cl)} file={path}")
    else:
        os.unlink(path)
print(f"ran={COUNT} false_unsat={bugs} binary={BIN}")
sys.exit(1 if bugs else 0)
