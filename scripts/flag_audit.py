#!/usr/bin/env python3
# ay-script: flag-audit
"""Audit AY_* environment flags: which are read, and which nothing ever sets.

A flag nothing sets is a feature that only runs if a human types it on a command
line. A competition submission types none of them, so such a flag is a dead code
path in the configuration that is actually scored. This campaign lost weeks to
exactly that: the orbitope route, the aux-free SR route and AY_SAT_SIGNED_SYMMETRY
were all unreachable in practice, and each was found by accident.

This regex scanner is a compatibility/listing aid. The canonical build ratchet
is the Rust `ay-quality-gate` exact-set audit backed by
`.code_quality_env_flag_baseline.toml`; it ignores Rust comments and non-code
strings, resolves same-file string constants, pins key/read sites, and fails
closed on unresolved environment calls.

Usage:
    python3 scripts/flag_audit.py            # summary
    python3 scripts/flag_audit.py --list     # every never-set flag with a read site
    python3 scripts/flag_audit.py --check N  # exit 1 if never-set capability flags exceed N

`--check N` preserves the historical compatibility count. B0 measured 348; B1 338, B2 331, B3 323, B4 312, B5 307, B6 246, B7 204 (setter-pattern fix re-based the count), B8 193, B9 169 (12 conversions + a doc-comment phantom + the tuple/env-dict setter patterns re-based 11 test/harness-steered flags out), B10 157 (12 ay-dpll conversions verified by an identical 112-failure names-diff), B11 145 (10 MILP kill-switch/value flags -> typed EngineEconomics carriers + CLI, 2 MODK constants), B12 128 (17 dual-simplex lane switches -> the same carriers), B13 101 (27 branch-and-bound names: cut families, LNS heuristics, prop caps, fc-mode, the seed file -> EngineEconomics/SolveOpts carriers + CLI), B14 83 (18 PB names: the ab_switches set-once bridge + hidden ay pb solve flags, probe-harness CLI dials, sweep constants), B15 73 (10 CHC names -> ay_chc::ab_switches + hidden --chc-no-* flags; the sweep-past shim folded into its existing config field), B16 68 (theories/core tail: NIA SLS + LRA warm-simplex ride TheoryDisableFlags, BVE env fallbacks deleted behind the existing CLI args, the LRA pivot-budget override deleted), B17 58 (6 dpll lanes + 2 maxsat A/B + flowcutter env arm via the CLI globals; the constant-indirection setter pattern reclassified the build-sandbox IPC marker), B18 52 (six MILP odd-verdicts exactly as their decision-table prose prescribes: BB_SHARE/LB constants, KEEP_SLACK_CUTS + DSE_PERSIST deleted-with-Dead-ledger-record, SINGLETON_DIAG folded under AY_MILP_TRACE), B19 49 (FLIP_NZ auto-decided per commit + --flip-solve, LATTICE_THREADS folded into the typed --threads budget, OBBT_OUT to a positional arg), B20 44 (the reject_instrument module deleted with its gate; ALLOCSTAT/BASIS_FILE/DIAG/CORPUS example-and-script singles to CLI flags or known-dir defaults), B21 44 (phase-2 opens: 16 ay-sat/ay-core delete-dead names retired — comment-noise setters, redundant CLI-carrier fallbacks, measured-negative levers made compiled-inert; phase-2 names never counted in this never-set ratchet, which stays 44), B22 44 (24 more MILP phase-2 names retired; NODE_CUTS + DEVEX briefly deleted then RESTORED — dict-literal setters in milp_portfolio.py, the audit now has the idiom), B23 44 (16 dpll/chc phase-2 delete-dead names retired incl. the mixed-strings soundness-gate kill-switch — the gate is now non-disableable), B24 44 (25 theories/core/chc/maxsat/frontend phase-2 names retired; 17 verdicts CORRECTED to keep — fifteen are exported by the OFFICIAL submission script, one is subprocess test IPC), B25 44 (24 phase-2 value knobs -> their named constants across chc/sat/euf/dpll/milp/lia; GMI_MAX_ROWS kept — a python closure test steers it), B26 44 (ten SAT default-on switches -> --sat-no-* via the new ay_core::SatAbSwitches carrier; the six ledger env-shim flags deferred to the capability-ledger endgame batch), B27 44 (21 CHC default-on switches -> --chc-no-* on the extended ChcAbSwitches; the condense share-cache key shrank to its one variable entry; 5 chc flags stay test-steered pending a test-seam), B28 44 (25 dpll default-on switches -> --dpll-no-*/--dpll-force-* on TheoryDisableFlags; the strings kill-switch subprocess tests migrated from env pairs to the CLI flags; mbqi's unconstructed closed-sentence `shadow` arm deleted), B29 44 (21 MILP default-on kill switches -> 19 env-less tune::Knob carriers + EngineEconomics builders + ay-milp CLI (--no-*, --dual-bypass-mode, --eager-perturb-mode); NoCertDecouple's env fallback retired, structure-route folded into SolveOpts::with_structure_routing + --no-structure-route; the rebase-time arrivals re-based 44 -> 50 and the tail re-converged: MIR_KNAP pair -> Knob::NoMirKnap, DIVE_BACKTRACKS -> its named constant, AY_REPO -> --repo, ATTRIB/_AUDIT joined the diagnostic classifier); it is not the build ratchet and must not be used
as proof that the canonical exact sets are unchanged.
"""
import re, os, sys, collections

READ = re.compile(r'(?:env::var(?:_os)?|getenv|environ\.get|os\.environ(?:\.get)?)\s*[\(\[]\s*["\']?(AY_[A-Z0-9_]+)')
SETTERS = [re.compile(r'\b(AY_[A-Z0-9_]+)\s*='),
           re.compile(r'set_var\s*\(\s*["\'](AY_[A-Z0-9_]+)'),
           re.compile(r'\.env\s*\(\s*["\'](AY_[A-Z0-9_]+)'),
           # Test-scoped setters. B6 lesson: ScopedEnvVar::set was invisible to
           # this audit, so guard-steered flags looked "never set" and their
           # deletion turned soundness guards vacuous while staying green.
           re.compile(r'ScopedEnvVar::set\s*\(\s*["\'](AY_[A-Z0-9_]+)'),
           re.compile(r'env\.set\s*\(\s*["\'](AY_[A-Z0-9_]+)'),
           # B9 lesson, same class: quoted name-value pairs passed to
           # with_serialized_env_vars were invisible too. The generic
           # paren-name-comma-value tuple shape covers those plus env-pair
           # lists in harness scripts; the lookbehind excludes Python's
           # environ.get with a default, which is a READ, not a setter
           # (verified match-by-match 2026-08-12). NOTE: no literal example
           # here — this file scans itself (the B4 self-match lesson).
           re.compile(r'(?<!get)\(\s*["\'](AY_[A-Z0-9_]+)["\']\s*,\s*["\']'),
           # …and Python env-dict assignments in harness scripts:
           # somedict[quoted-name] = value (B9, verified match-by-match).
           re.compile(r'\[["\'](AY_[A-Z0-9_]+)["\']\]\s*=[^=]'),
           # B17: an ALL-CAPS constant bound to an AY name is setter
           # INDIRECTION — continuous_benchmark.py sets its build-sandbox
           # marker through `BUILD_SANDBOX_MARKER = "AY_..."` used as a dict
           # key, which no literal pattern can see. ALL-CAPS-lvalue keeps
           # lowercase read helpers (`let name = "AY_X"`) out.
           # (Rust spelling of the same idiom: `const NAME: &str = "AY_X"`,
           # set later via command.env(NAME, ...) — dt_model_cert.rs's
           # subprocess pinning was deleted as "never-set" before this arm
           # existed and had to be restored.)
           re.compile(r'\b[A-Z][A-Z0-9_]{2,}\s*(?::\s*&str\s*)?[:=]\s*["\'](AY_[A-Z0-9_]+)["\']'),
           # B22 lesson: Python dict LITERALS set env too —
           # {"AY_X": "1"} in milp_portfolio.py armed a flag every literal
           # pattern missed and a classifier deleted. Key-position only.
           re.compile(r'[{,]\s*["\'](AY_[A-Z0-9_]+)["\']\s*:\s*["\']')]
DEBUG = re.compile(r'PROBE|TRACE|DEBUG|DUMP|_LOG|STATS|VERBOSE|TELEMETRY|CENSUS|REPORT|SIDECAR_DIR|ATTRIB|_AUDIT')
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
