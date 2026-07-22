#!/usr/bin/env python3
# ay-script: mzn-score
"""Retroactive MiniZinc Challenge scorer — validated against the official
precomputed pairwise score tensor in results.json."""
import json, math, sys

def pair_score(kind, st1, o1, t1, st2, o2, t2):
    a1 = st1 in ('S', 'SC'); a2 = st2 in ('S', 'SC')
    c1 = st1 == 'SC';        c2 = st2 == 'SC'
    if not a1 and not a2: return 0.0, 0.0
    if a1 and not a2:     return 1.0, 0.0
    if a2 and not a1:     return 0.0, 1.0
    # both have a feasible solution
    if kind == 'SAT' or o1 is None or o2 is None or o1 == o2:
        better = 0
    elif kind == 'MIN':
        better = 1 if o1 < o2 else 2
    else:  # MAX
        better = 1 if o1 > o2 else 2
    if better == 1:      # s1 strictly better objective
        return 1.0, (0.0 if c1 else 0.5)
    if better == 2:      # s2 strictly better objective
        return (0.0 if c2 else 0.5), 1.0
    # equal objective: completeness first (opt problems only), then time split.
    # For SAT a found solution is a found solution — completeness does not
    # confer quality, so go straight to the whole-second time split.
    if kind != 'SAT':
        if c1 and not c2: return 1.0, 0.0
        if c2 and not c1: return 0.0, 1.0
    s1 = math.floor((t1 or 0) / 1000); s2 = math.floor((t2 or 0) / 1000)
    if s1 + s2 == 0:  return 0.5, 0.5
    return s2 / (s1 + s2), s1 / (s1 + s2)

def load(path):
    return json.load(open(path))['results']

def inst_kind_map(d):
    ik = {}
    for p, idxs in enumerate(d['instances']):
        for gi in idxs: ik[gi] = d['kind'][p]
    return ik

def validate(path):
    d = load(path); ik = inst_kind_map(d)
    sv=d['solvers']; R=d['results']; O=d['objectives']; T=d['times']; S=d['scores']
    ns=len(sv); ni=len(R[0]); mism=0; checked=0; ex=[]
    for s1 in range(ns):
        for s2 in range(ns):
            if s1==s2: continue
            for i in range(ni):
                got,_=pair_score(ik[i],R[s1][i],O[s1][i],T[s1][i],R[s2][i],O[s2][i],T[s2][i])
                checked+=1
                if abs(got-S[s1][s2][i])>1e-6:
                    mism+=1
                    if len(ex)<15: ex.append((sv[s1],sv[s2],i,ik[i],(R[s1][i],O[s1][i],T[s1][i]),(R[s2][i],O[s2][i],T[s2][i]),'exp',S[s1][s2][i],'got',round(got,4)))
    print(f'checked={checked} mismatches={mism} ({100*mism/checked:.3f}%)')
    for e in ex: print('  ',e)
    return mism

if __name__=='__main__':
    validate(sys.argv[1] if len(sys.argv)>1 else 'results-2025.json')
