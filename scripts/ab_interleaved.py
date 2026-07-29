#!/usr/bin/env python3
# ay-script: smt-ab-interleaved
"""Order-balanced A/B harness for Incremental QF_LRA lever decisions.

WHY THIS EXISTS
---------------
The campaign's previous A/B harnesses ran each file's arms in a fixed order
(arm A then arm B) and assumed per-file noise of about +-6 check-sats. Both
assumptions are wrong, and several single-digit "wins" were shipped on top of
them:

  * Replication on bmwlin_20_5_1.inter.ind_k100.smt2, SAME BINARY, same machine:
    66 vs 97 scored check-sats at 600 s, and 68 vs 78 at 300 s. That is 15-47 %,
    roughly 5x the assumed band.
  * In BOTH replications the arm that ran SECOND won. Page cache, thermal state
    and background load are order-correlated, so a fixed A-then-B schedule
    systematically credits arm B.
  * Independently corroborated 2026-07-26: in a same-binary run the identical
    arm scored 15 then 21 on rod.ind and 42 then 52 on bmwlin.ind.

So an unbalanced A/B cannot resolve anything below roughly 50 %, and its sign
is not even trustworthy.

WHAT THIS DOES
--------------
  * Runs every (file, sample) as a PAIR in BOTH orders: AB and BA. Order is
    therefore balanced within every file, and any order effect cancels in the
    mean instead of landing on one arm.
  * Reports the order effect explicitly, as its own number. If it is large
    relative to the arm effect, the comparison is not decidable at that budget
    and the tool says so rather than reporting a winner.
  * Reports a per-file breakdown and flags files whose within-arm spread across
    samples exceeds the between-arm difference (i.e. the file is too noisy to
    contribute signal).
  * Cross-checks verdict agreement on the common prefix, because a throughput
    change that alters answers is a soundness event, not a win.

USAGE
  python3 scripts/ab_interleaved.py --bin PATH --tag NAME \
      [--env-b KEY=VAL ...] [--env-a KEY=VAL ...] \
      [--timeout 90] [--samples 2] [--corpus DIR] [--glob '*.ind_k100.smt2']

Both arms use the SAME binary; they differ only in environment, so a flag's
effect is isolated (never compare binaries built from different revisions).
Results append to <tag>_ab.tsv and are resumable.
"""
import argparse
import gc
import glob
import json
import os
import statistics
import subprocess
import sys
import time

DEFAULT_CORPUS = os.environ.get(
    "AY_AB_CORPUS",
    # No absolute machine path: the publication guard rejects one, which
    # blocks the whole export. Point AY_AB_CORPUS at your SMT-LIB corpus.
    os.path.expanduser("~/smtlib-inc-2025/incremental/QF_LRA/hybrid_networks"),
)


def run_one(binary, path, extra_env, timeout):
    env = dict(os.environ)
    env.update(extra_env)
    with open(path) as fh:
        try:
            proc = subprocess.run(
                [binary, "--z3-mode"], stdin=fh, capture_output=True,
                text=True, timeout=timeout, env=env,
            )
            out = proc.stdout
        except subprocess.TimeoutExpired as exc:
            out = exc.stdout if isinstance(exc.stdout, str) else (exc.stdout or b"").decode()
    gc.collect()
    return [ln.strip() for ln in out.split("\n") if ln.strip() in ("sat", "unsat")]


def parse_env(pairs):
    env = {}
    for item in pairs or []:
        if "=" not in item:
            sys.exit(f"--env expects KEY=VAL, got {item!r}")
        k, v = item.split("=", 1)
        env[k] = v
    return env


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", required=True, help="solver binary (SAME binary for both arms)")
    ap.add_argument("--tag", required=True)
    ap.add_argument("--env-a", action="append", default=[], help="KEY=VAL for arm A (baseline)")
    ap.add_argument("--env-b", action="append", default=[], help="KEY=VAL for arm B (candidate)")
    ap.add_argument("--timeout", type=float, default=90.0)
    ap.add_argument("--samples", type=int, default=2, help="pairs per file PER ORDER")
    ap.add_argument("--corpus", default=DEFAULT_CORPUS)
    ap.add_argument("--glob", default="*.ind_k100.smt2")
    args = ap.parse_args()

    env_a, env_b = parse_env(args.env_a), parse_env(args.env_b)
    files = sorted(glob.glob(os.path.join(args.corpus, args.glob)))
    if not files:
        sys.exit(f"no files matched {args.glob} in {args.corpus}")
    res_path = f"{args.tag}_ab.tsv"

    done = set()
    if os.path.exists(res_path):
        for line in open(res_path):
            f = line.split("\t")
            if len(f) >= 4:
                done.add((f[0], f[1], f[2]))

    with open(res_path, "a") as out:
        for sample in range(args.samples):
            for path in files:
                name = os.path.basename(path)
                # Both orders, so the second-position advantage is balanced.
                for order in ("AB", "BA"):
                    key = (name, str(sample), order)
                    if key in done:
                        continue
                    first, second = (("A", env_a), ("B", env_b)) if order == "AB" \
                        else (("B", env_b), ("A", env_a))
                    r1 = run_one(args.bin, path, first[1], args.timeout)
                    r2 = run_one(args.bin, path, second[1], args.timeout)
                    got = {first[0]: r1, second[0]: r2}
                    common = min(len(got["A"]), len(got["B"]))
                    agree = all(got["A"][i] == got["B"][i] for i in range(common))
                    out.write("\t".join([
                        name, str(sample), order,
                        str(len(got["A"])), str(len(got["B"])),
                        "OK" if agree else "MISMATCH",
                        json.dumps({"A": got["A"][:250], "B": got["B"][:250]}),
                    ]) + "\n")
                    out.flush()
                    print(f"s{sample} {order} {name[:34]:34} A={len(got['A']):4} "
                          f"B={len(got['B']):4} {'OK' if agree else 'MISMATCH'}", flush=True)

    report(res_path)


def report(res_path):
    rows = []
    for line in open(res_path):
        f = line.rstrip("\n").split("\t")
        if len(f) >= 6:
            rows.append({"file": f[0], "sample": f[1], "order": f[2],
                         "a": int(f[3]), "b": int(f[4]), "agree": f[5]})
    if not rows:
        return
    print("\n=== ORDER-BALANCED A/B REPORT ===")

    mism = [r for r in rows if r["agree"] != "OK"]
    if mism:
        print(f"!!! {len(mism)} VERDICT MISMATCHES — this is a SOUNDNESS event, "
              f"not a performance result. Stop and investigate.")
        for r in mism[:10]:
            print(f"    {r['file']} sample={r['sample']} order={r['order']}")

    # Arm effect, computed within order then averaged, so order cannot leak in.
    per_order = {}
    for order in ("AB", "BA"):
        sel = [r for r in rows if r["order"] == order]
        if sel:
            per_order[order] = (sum(r["b"] - r["a"] for r in sel) / len(sel), len(sel))
    if len(per_order) == 2:
        arm = statistics.mean(v[0] for v in per_order.values())
        # Second-position advantage: in AB, B ran second; in BA, A ran second.
        order_effect = (per_order["AB"][0] - per_order["BA"][0]) / 2
        print(f"\narm effect  B-A = {arm:+.1f} counts/file "
              f"(AB pairs {per_order['AB'][0]:+.1f}, BA pairs {per_order['BA'][0]:+.1f})")
        print(f"order effect (second position) = {order_effect:+.1f} counts/file")
        if abs(order_effect) >= abs(arm):
            print("  VERDICT: NOT DECIDABLE — the order effect is at least as large as the\n"
                  "  arm effect. Do not ship on this measurement; raise the budget or the\n"
                  "  sample count, or quiesce the machine.")
        else:
            print("  (order effect is smaller than the arm effect — arm effect is meaningful)")
    else:
        print("need both AB and BA pairs for an order-balanced verdict")

    print("\nper-file (B-A per pair, and within-arm spread):")
    for name in sorted({r["file"] for r in rows}):
        sel = [r for r in rows if r["file"] == name]
        deltas = [r["b"] - r["a"] for r in sel]
        a_vals = [r["a"] for r in sel]
        spread = max(a_vals) - min(a_vals) if len(a_vals) > 1 else 0
        mean_d = statistics.mean(deltas)
        noisy = " NOISY (within-arm spread >= |delta|)" if spread >= abs(mean_d) else ""
        print(f"  {name[:38]:38} B-A={mean_d:+6.1f}  arm-A spread={spread:3d}{noisy}")


if __name__ == "__main__":
    main()
