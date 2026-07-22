#!/usr/bin/env python3
# ay-script: pb-ab-compare
"""A/B comparator for pbcomp_harness.py run outputs, scored the PB-COMP way.

The incomplete ("best answer") board ranks by answer QUALITY, not just solve
counts, so unlike the harness's built-in baseline diff this compares the
verified objective value per instance between two runs (min objective wins)
and reports best-answer wins/ties/losses alongside status transitions, wrong
answers, and crashes. Gate criteria (plan §5): net + best-answers, 0 wrong,
0 crashes, no regression.

Usage:
    scripts/pb_ab_compare.py base.jsonl candidate.jsonl
"""
from __future__ import annotations

import json
import sys
from collections import Counter, defaultdict

GOOD = ("OPTIMUM FOUND", "SATISFIABLE", "UNSATISFIABLE")


def load(path):
    rows = {}
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            r = json.loads(line)
            rows[r["instance"]] = r
    return rows


def answered(r):
    return r["status"] in GOOD and r.get("verified") is not False


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    base, cand = load(sys.argv[1]), load(sys.argv[2])
    paths = sorted(set(base) | set(cand))

    wins, losses, ties = [], [], []
    status_moves = Counter()
    wrong, crashes = [], []
    per_cat = defaultdict(Counter)

    for p in paths:
        b, c = base.get(p), cand.get(p)
        cat = (c or b).get("category", "?")
        for arm, r in (("base", b), ("cand", c)):
            if r is None:
                continue
            if r.get("wrong_answer") or "mismatch" in (r.get("note") or ""):
                wrong.append((arm, p, r.get("note")))
            if r["status"] in ("CRASH", "ERROR"):
                crashes.append((arm, p))
        if b is None or c is None:
            continue
        status_moves[f'{b["status"]} -> {c["status"]}'] += 1

        b_ok, c_ok = answered(b), answered(c)
        b_obj, c_obj = b.get("objective"), c.get("objective")
        if c_ok and not b_ok:
            wins.append((p, "answer gained"))
            per_cat[cat]["win"] += 1
        elif b_ok and not c_ok:
            losses.append((p, "answer LOST"))
            per_cat[cat]["loss"] += 1
        elif b_ok and c_ok and b_obj is not None and c_obj is not None:
            if c_obj < b_obj:
                wins.append((p, f"o {b_obj} -> {c_obj}"))
                per_cat[cat]["win"] += 1
            elif c_obj > b_obj:
                losses.append((p, f"o {b_obj} -> {c_obj} (WORSE)"))
                per_cat[cat]["loss"] += 1
            else:
                ties.append(p)
                per_cat[cat]["tie"] += 1
        else:
            ties.append(p)
            per_cat[cat]["tie"] += 1

    print(f"instances compared: {len(paths)}")
    print(f"best-answer: +{len(wins)} / ={len(ties)} / -{len(losses)}   "
          f"net {len(wins) - len(losses):+d}")
    for cat in sorted(per_cat):
        c = per_cat[cat]
        print(f"  {cat:12s} +{c['win']} ={c['tie']} -{c['loss']}")
    interesting = {k: v for k, v in status_moves.items()
                   if not k.split(" -> ")[0] == k.split(" -> ")[1]}
    if interesting:
        print("status transitions:")
        for k, v in sorted(interesting.items(), key=lambda kv: -kv[1]):
            print(f"  {v:4d}  {k}")
    print(f"wrong answers: {len(wrong)}")
    for arm, p, note in wrong:
        print(f"  [{arm}] {p}: {note}")
    print(f"crashes: {len(crashes)}")
    for arm, p in crashes:
        print(f"  [{arm}] {p}")

    if wins or losses:
        print("\ndetail (wins first):")
        for p, why in wins + losses:
            print(f"  {why:28s} {p}")

    gate = (len(wins) - len(losses) > 0) and not wrong and not crashes and not losses
    strict = "PASS" if gate else "CHECK"
    print(f"\ngate[favor-strict: net+ & 0 wrong & 0 crash & 0 losses]: {strict}")


if __name__ == "__main__":
    main()
