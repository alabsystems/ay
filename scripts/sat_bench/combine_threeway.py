#!/usr/bin/env python3
# ay-script: sat-combine-threeway
"""Combine the 23-subset + 32-rest three_way @300s JSONs into the full-55 verdict.
Usage: combine_threeway.py threeway_300.json threeway_300_rest.json"""
import json, sys
res = []
for p in sys.argv[1:]:
    try: res += json.load(open(p))
    except Exception as e: print(f"(skip {p}: {e})")
TO = 300
def sol(v): return v in ("SAT", "UNSAT")
bs = sum(1 for r in res if sol(r['base'][0])); cs = sum(1 for r in res if sol(r['cfgB'][0])); ks = sum(1 for r in res if sol(r['ki'][0]))
def par2(k): return sum(r[k][1] if sol(r[k][0]) else 2*TO for r in res)
conv = [r['cnf'] for r in res if sol(r['cfgB'][0]) and not sol(r['base'][0])]
regr = [r['cnf'] for r in res if sol(r['base'][0]) and not sol(r['cfgB'][0])]
dis = [r['cnf'] for r in res if r.get('disagree')]
print(f"=== FULL-{len(res)} @300s (combined) ===")
print(f"baseline-AY solved {bs}  PAR2 {par2('base'):.0f}")
print(f"configB-AY  solved {cs}  PAR2 {par2('cfgB'):.0f}   (delta {cs-bs:+d} solved, PAR2 {par2('cfgB')-par2('base'):+.0f})")
print(f"Kissat      solved {ks}")
print(f"CONVERSIONS {len(conv)}: {conv}")
print(f"REGRESSIONS {len(regr)}: {regr}")
print(f"SOUNDNESS DISAGREEMENTS {len(dis)}: {dis}")
print("VERDICT:", "NET-POSITIVE + SOUND" if cs > bs and not dis and not regr else
      "NET-POSITIVE w/ regressions" if cs > bs and not dis else
      "NEUTRAL/NEGATIVE" if not dis else "UNSOUND")
