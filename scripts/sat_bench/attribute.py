#!/usr/bin/env python3
# ay-script: sat-attribute
"""Classify a sat_compare.py results JSON: bucket instances, attribute the gap by family."""
import json, sys, re, os, collections

d = json.load(open(sys.argv[1]))
r = d.get("results", [])
TO = d.get("timeout", 0)

def family(cnf):
    s = re.sub(r'^[0-9a-f]{6,}_', '', cnf)            # strip hash prefix
    s = re.sub(r'\.cnf$', '', s)
    s = re.sub(r'[\._-]?\d.*$', '', s)                 # strip trailing numbers/suffix
    return s or "(misc)"

def solved(v): return v in ("SAT", "UNSAT")

buckets = collections.defaultdict(list)
for x in r:
    a, k = x["ay"]["verdict"], x["kissat"]["verdict"]
    if x["disagree"]: b = "DISAGREE"
    elif solved(a) and solved(k): b = "both_solve"
    elif solved(a) and not solved(k): b = "ay_only"
    elif solved(k) and not solved(a): b = "gap_ki_only"
    else: b = "both_timeout"
    buckets[b].append(x)

n = len(r)
ay_s = sum(1 for x in r if solved(x["ay"]["verdict"]))
ki_s = sum(1 for x in r if solved(x["kissat"]["verdict"]))
def par2(key):
    return sum(x[key]["time"] if solved(x[key]["verdict"]) else 2*TO for x in r)

print(f"=== {n} instances @ {TO}s ===")
print(f"AY solved {ay_s}  PAR2={par2('ay'):.0f}")
print(f"Kissat   {ki_s}  PAR2={par2('kissat'):.0f}")
print(f"buckets: " + "  ".join(f"{k}={len(v)}" for k,v in sorted(buckets.items())))
print()

if buckets["DISAGREE"]:
    print("!!!! SOUNDNESS DISAGREEMENTS !!!!")
    for x in buckets["DISAGREE"]:
        print(f"   {x['cnf']}  AY={x['ay']['verdict']} KI={x['kissat']['verdict']}")
    print()

print("=== GAP (Kissat solves, AY does not) — by family ===")
gapfam = collections.Counter(family(x["cnf"]) for x in buckets["gap_ki_only"])
for fam, c in gapfam.most_common():
    print(f"  {c:2}  {fam}")
print()
print("=== GAP instances (Kissat time, AY verdict) ===")
for x in sorted(buckets["gap_ki_only"], key=lambda x: x["kissat"]["time"]):
    print(f"  {family(x['cnf']):20} KI={x['kissat']['verdict']:5}{x['kissat']['time']:6.1f}s  "
          f"AY={x['ay']['verdict']:8}  {x['cnf']}")
print()
if buckets["ay_only"]:
    print("=== AY-ONLY solves (AY solves, Kissat doesn't) ===")
    for x in buckets["ay_only"]:
        print(f"  {family(x['cnf']):20} AY={x['ay']['verdict']:5}{x['ay']['time']:6.1f}s  {x['cnf']}")
    print()
print("=== BOTH-SOLVE (slowdown ratio AY/KI) ===")
for x in sorted(buckets["both_solve"], key=lambda x: -(x["ay"]["time"]/max(x["kissat"]["time"],0.01))):
    ratio = x["ay"]["time"]/max(x["kissat"]["time"], 0.01)
    print(f"  {family(x['cnf']):20} AY={x['ay']['time']:6.1f}s KI={x['kissat']['time']:6.1f}s  ratio={ratio:5.1f}x  {x['cnf']}")
