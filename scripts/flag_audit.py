#!/usr/bin/env python3
"""Audit AY_* environment flags: which are read, and which nothing ever sets.

A flag nothing sets is a feature that only runs if a human types it on a command
line. A competition submission types none of them, so such a flag is a dead code
path in the configuration that is actually scored. This campaign lost weeks to
exactly that: the orbitope route, the aux-free SR route and AY_SAT_SIGNED_SYMMETRY
were all unreachable in practice, and each was found by accident.

Usage:
    python3 scripts/flag_audit.py            # summary
    python3 scripts/flag_audit.py --list     # every never-set flag with a read site
    python3 scripts/flag_audit.py --check N  # exit 1 if never-set capability flags exceed N

The budget is a RATCHET: it starts at today's count (348) and only moves down.
Lowering it as flags become automatic is the mechanism that retires this class;
raising it needs a reason recorded in the development design notes
"""
import re, os, sys, collections

READ = re.compile(r'(?:env::var(?:_os)?|getenv|environ\.get|os\.environ(?:\.get)?)\s*[\(\[]\s*["\']?(AY_[A-Z0-9_]+)')
SETTERS = [re.compile(r'\b(AY_[A-Z0-9_]+)\s*='),
           re.compile(r'set_var\s*\(\s*["\'](AY_[A-Z0-9_]+)'),
           re.compile(r'\.env\s*\(\s*["\'](AY_[A-Z0-9_]+)')]
DEBUG = re.compile(r'PROBE|TRACE|DEBUG|DUMP|_LOG|STATS|VERBOSE|TELEMETRY|CENSUS|REPORT|SIDECAR_DIR')
ROOTS = ['crates', 'scripts', 'competition', 'tests', 'benches']

def scan(root_dir='.'):
    read, setat = collections.defaultdict(list), collections.defaultdict(list)
    for root in ROOTS:
        base = os.path.join(root_dir, root)
        for dp, _, fns in os.walk(base):
            if '/target/' in dp or '/.git/' in dp:
                continue
            for fn in fns:
                if not fn.endswith(('.rs', '.py', '.sh', '.toml')):
                    continue
                p = os.path.join(dp, fn)
                try:
                    txt = open(p, errors='ignore').read()
                except OSError:
                    continue
                for i, line in enumerate(txt.split('\n'), 1):
                    for m in READ.finditer(line):
                        read[m.group(1)].append(f"{p}:{i}")
                    for rx in SETTERS:
                        for m in rx.finditer(line):
                            setat[m.group(1)].append(f"{p}:{i}")
    return read, setat

def main():
    read, setat = scan(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    never = [f for f in sorted(read) if f not in setat]
    testonly = [f for f in never if all('/tests/' in s or 'tests.rs' in s for s in read[f])]
    debug = [f for f in never if f not in testonly and DEBUG.search(f)]
    capability = [f for f in never if f not in testonly and f not in debug]
    print(f"AY_* flags read        : {len(read)}")
    print(f"never set by anything  : {len(never)}")
    print(f"  capability/tuning    : {len(capability)}")
    print(f"  debug/telemetry      : {len(debug)}")
    print(f"  test-only            : {len(testonly)}")
    if '--list' in sys.argv:
        print("\nnever-set capability/tuning flags:")
        for f in capability:
            print(f"  {f}  <- {read[f][0]}")
    if '--check' in sys.argv:
        cap = int(sys.argv[sys.argv.index('--check') + 1])
        if len(capability) > cap:
            print(f"\nFAIL: {len(capability)} never-set capability flags exceeds the budget of {cap}.")
            print("Either give the flag a setter (an automatic decision in the profile/adaptive")
            print("machinery), turn it into a named constant, or delete it. Do not raise the budget")
            print("without a reason recorded in the development design notes")
            return 1
        print(f"\nOK: {len(capability)} never-set capability flags, budget {cap}.")
    return 0

if __name__ == '__main__':
    sys.exit(main())
