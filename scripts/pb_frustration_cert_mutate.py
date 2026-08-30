#!/usr/bin/env python3
"""Adversarial battery for the frustrated-cycle certificates.

MUST-REJECT  = the mutated pair's truth CONTRADICTS the mutated claim.  An
accept here is a checker defect or an emitter forgery.
MAY-ACCEPT   = a different but still LEGAL proof/claim; an accept is correct and
is recorded, not counted as a failure.
"""
import subprocess, sys, os, re, json, random

def verdict(chk, opb, pbp):
    r = subprocess.run([chk, opb, pbp], capture_output=True, text=True, timeout=1800)
    line = [l for l in (r.stdout + r.stderr).splitlines() if l.startswith('s ')]
    return r.returncode, (line[-1] if line else '<no-s-line>')

def accepted(rc, v):
    return rc == 0 and re.match(r'^s VERIFIED (SATISFIABLE|UNSATISFIABLE|BOUNDS|OUTPUT)', v)

def main():
    chk, opb, pbp, out = sys.argv[1:5]
    tmp = os.path.dirname(os.path.abspath(out))
    src = open(pbp).read().splitlines()
    formula = open(opb).read().splitlines()
    res = []
    rc, v = verdict(chk, opb, pbp)
    print(f'BASELINE rc={rc} {v}')
    assert accepted(rc, v), 'baseline did not verify'
    base_v = v

    def probe(name, lines, kind, form=None, note=''):
        p = os.path.join(tmp, 'mut.pbp'); o = opb
        open(p, 'w').write('\n'.join(lines) + '\n')
        if form is not None:
            o = os.path.join(tmp, 'mut.opb'); open(o, 'w').write('\n'.join(form) + '\n')
        rc, v = verdict(chk, o, p)
        a = bool(accepted(rc, v))
        res.append({'name': name, 'kind': kind, 'rc': rc, 'verdict': v, 'accepted': a,
                    'note': note})
        flag = 'ACCEPTED' if a else 'rejected'
        bad = ' <<< MUST-REJECT ACCEPTED' if (a and kind == 'must') else ''
        print(f'  [{kind}] {name:44s} {flag:9s} rc={rc} {v}{bad}')

    ci = [i for i, l in enumerate(src) if l.startswith('conclusion')][0]
    concl = src[ci]
    lb = int(re.match(r'conclusion BOUNDS (\d+)', concl).group(1))
    ub = int(re.search(r'(\d+) : ', concl.split(':', 2)[2]).group(1)) if False else None

    # 1. bound tampering
    for delta in (1, 2, 7, 50):
        m = list(src); m[ci] = concl.replace(f'BOUNDS {lb} :', f'BOUNDS {lb+delta} :', 1)
        probe(f'lower-bound+{delta}', m, 'must')
    parts = concl.split(' : ')
    hint, ubtok = parts[1].rsplit(' ', 1)
    for delta in (1, 5):
        m = list(src)
        m[ci] = ' : '.join([parts[0], f'{hint} {int(ubtok)-delta}', parts[2]])
        probe(f'upper-bound-{delta}', m, 'must',
              note='the WITNESS costs 374, so any smaller upper bound is unsupported')

    # 2. witness tampering: flip a literal the witness sets TRUE and that pays
    lits = parts[2].rstrip(';').split()
    pos = [i for i, l in enumerate(lits) if not l.startswith('~')]
    for k in range(3):
        m = list(src); L = list(lits); i = pos[k * 37 % len(pos)]
        L[i] = '~' + L[i]
        m[ci] = ' : '.join([parts[0], parts[1], ' '.join(L) + ';'])
        probe(f'witness-flip-{lits[i]}', m, 'must')
    # drop a literal from the witness
    m = list(src); L = [l for l in lits if l != lits[pos[0]]]
    m[ci] = ' : '.join([parts[0], parts[1], ' '.join(L) + ';'])
    probe('witness-literal-dropped', m, 'must')

    # 3. derivation tampering
    pols = [i for i, l in enumerate(src) if l.startswith('pol ')]
    last = pols[-1]; second_last = pols[-2]
    m = list(src); m[last] = re.sub(r' (\d+) d ;$', lambda g: f' {int(g.group(1))+1} d ;', src[last])
    probe('final-divisor-raised', m, 'must')
    m = list(src); m[last] = re.sub(r' (\d+) d ;$', lambda g: f' {int(g.group(1))-1} d ;', src[last])
    probe('final-divisor-lowered', m, 'may', note='weaker or stronger; checker recomputes')
    # drop a saturation from a cycle derivation
    sats = [i for i in pols if src[i].rstrip().endswith('s ;')]
    for k in (0, 1, 2):
        m = list(src); m[sats[k]] = src[sats[k]].replace(' s ;', ' ;')
        probe(f'saturation-dropped-{k}', m, 'must')
    # cycle divisor 2 -> 3 (documented may-accept: rounding makes it identical)
    twod = [i for i in pols if ' 2 d ;' in src[i]]
    for k in (0, 1):
        m = list(src); m[twod[k]] = src[twod[k]].replace(' 2 d ;', ' 3 d ;')
        probe(f'cycle-divisor-2to3-{k}', m, 'may', note='VeriPB rounds up; identical row')
    # drop a summand from a cycle chain
    for k in (0, 1, 2):
        i = sats[k]
        toks = src[i].split()
        j = [t for t in range(len(toks)) if toks[t] == '+'][0]
        m = list(src); m[i] = ' '.join(toks[:j - 1] + toks[j + 1:])
        probe(f'cycle-summand-dropped-{k}', m, 'must')
    # operand pointed at an id that was never derived
    m = list(src); m[last] = re.sub(r'^pol (\d+)', 'pol 99999999', src[last])
    probe('operand-never-derived', m, 'must')
    # operand pointed at a neighbouring legal id
    m = list(src)
    m[last] = re.sub(r'^pol (\d+)', lambda g: f'pol {int(g.group(1))-1}', src[last])
    probe('operand-neighbouring-legal-id', m, 'may', note='different but legal derivation')
    # multiplier tampering in the final combination
    m = list(src)
    m[second_last] = re.sub(r' (\d+) \*', lambda g: f' {int(g.group(1))+3} *', src[second_last], count=1)
    probe('final-multiplier-raised', m, 'must', note='breaks the per-edge <= D budget')
    m = list(src)
    m[second_last] = re.sub(r' (\d+) \*', lambda g: f' {max(1,int(g.group(1))-1)} *', src[second_last], count=1)
    probe('final-multiplier-lowered-by-1', m, 'may',
          note='the packing has slack 1/3; -1/360 keeps the TRUE bound 374 derivable')
    # lower a multiplier far enough that the bound genuinely drops below 374
    m = list(src)
    ks = [int(t) for t in re.findall(r' (\d+) \*', src[second_last])]
    biggest = max(ks)
    m[second_last] = src[second_last].replace(f' {biggest} *', ' 1 *', 1)
    probe('final-multiplier-collapsed', m, 'must',
          note='drops the packing value below 374; the claim is then unsupported')
    # slack fill removed
    m = list(src)
    toks = src[second_last].split()
    k = [t for t in range(len(toks)) if toks[t].startswith('x') and toks[t] != 'x'][0]
    m[second_last] = ' '.join(toks[:k] + toks[k + 3:])
    probe('slack-axiom-dropped', m, 'must')

    # 4. structural
    mid = len(src) // 2
    probe('truncated-at-midpoint', src[:mid], 'must')
    probe('truncated-before-conclusion', src[:ci], 'must')
    m = list(src); m.insert(mid, 'pol not_a_constraint ;')
    probe('tripwire-at-midpoint', m, 'must')
    m = [l for i, l in enumerate(src) if i != last]
    probe('final-floor-line-deleted', m, 'must')
    m = list(src); m[0] = 'pseudo-Boolean proof version 2.0'
    probe('version-downgraded-to-2.0', m, 'must', note='legacy parser has no rule scope')
    m = list(src); m[1] = f'f {len(formula)} ;'.replace(str(len(formula)), '99999')
    probe('formula-count-raised', m, 'must')

    # 5. formula-side
    # tighten a row so the logged witness becomes infeasible
    fi = [i for i, l in enumerate(formula)
          if not l.startswith('*') and not l.startswith('min:') and l.strip()]
    m = list(formula)
    row = m[fi[0]]; body, rhs = row.rsplit('>=', 1)
    m[fi[0]] = f'{body}>= {int(rhs.strip().rstrip(";")) + 3} ;'
    probe('formula-row-degree-raised', src, 'must', form=m,
          note='witness becomes infeasible, upper bound unsupported')
    # delete a formula row the proof consumes
    m = [l for i, l in enumerate(formula) if i != fi[0]]
    probe('formula-row-deleted', src, 'must', form=m)
    # objective coefficient the witness sets TRUE, raised
    oi = [i for i, l in enumerate(formula) if l.startswith('min:')][0]
    true_v = lits[pos[0]]
    m = list(formula)
    m[oi] = m[oi].replace(f'+1 {true_v} ', f'+2 {true_v} ', 1)
    probe('objective-coeff-on-a-TRUE-var-raised', src, 'must', form=m,
          note='incumbent now costs 375; claimed BOUNDS 374<=obj<=374 is false')

    json.dump(res, open(out, 'w'), indent=1)
    must = [r for r in res if r['kind'] == 'must']
    may = [r for r in res if r['kind'] == 'may']
    print(f'\nMUST-REJECT {len(must)}  ACCEPTED {sum(1 for r in must if r["accepted"])}')
    print(f'MAY-ACCEPT  {len(may)}  accepted {sum(1 for r in may if r["accepted"])} (correctly)')

main()
