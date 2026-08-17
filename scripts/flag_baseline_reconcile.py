#!/usr/bin/env python3
# ay-script: flag-baseline-reconcile
"""Reconcile .code_quality_env_flag_baseline.toml after deleting env flags.

Usage:
    cargo test -p ay-quality-gate --release --lib repository_baseline_is_exact \
        > /tmp/qg.txt 2>&1
    python3 scripts/flag_baseline_reconcile.py /tmp/qg.txt [--flags F1,F2,...]

Procedure (proven over batches B2-B8 of the env-flag migration):
 1. If --flags is given, first remove those flags' simple list entries and every
    [[table]] block whose `key = "FLAG"` matches, across all tables.
 2. Parse the failing gate's report for stale/unexpected rust_ay_key_site
    entries and rebuild the whole [[rust_ay_key_site]] section: drop stale,
    add unexpected, dedup, SORT by (path, key, context). Sorting matters — the
    gate rejects duplicate-or-unsorted sections.
 3. Re-run the gate; iterate until clean (context strings shift whenever code
    moves near a surviving read, so two passes are common).

NOT HANDLED (reconcile by hand from the report): `changed_rust_reads`
occurrence-count updates (B18 hit this when re-gating two blocks moved an
AY_MILP_TRACE read count 3 -> 5); names that legitimately REMAIN as quoted
literals (Bucket::Dead ledger records) must be re-added to the sorted
`rust_ay_key` list by hand after a --flags prune; the [[dynamic_call]] section
(generic-key `env::var_os(<expr>)` sites — B11 hit this when tune.rs's Knob
env lookup changed shape), and additions of new key strings to Rust source.
On that second point, prefer NOT adding AY_* literals to .rs files at all:
B11 moved a retired-names allowlist into tests/retired_env_names.txt because
every quoted literal in Rust counts as a key site.

Parsing notes learned the hard way:
 - The report dumps the ENTIRE expected set too; only read the sections at
   4-space indent, and bound each section by its '\n    ],' terminator — do NOT
   bracket-walk, context strings contain brackets.
 - stale+unexpected pairs with the same (path,key) are a MOVED context, not a
   deletion; the rebuild handles both uniformly.
"""
import re, sys

def entries_after(s, name, detail=False):
    out = []
    # NB: an EMPTY section prints inline as `name: [],` — matching it and
    # scanning to the next `],` would swallow the FOLLOWING section's entries
    # (found the hard way in B13: the script re-added every stale entry it had
    # just removed, oscillating forever). Require the opening bracket to end
    # its line, which only multi-entry sections do.
    for mm in re.finditer(r'^    ' + name + r': \[$', s, re.M):
        end_i = s.find('\n    ],', mm.end())
        body = s[mm.end():end_i if end_i > 0 else mm.end()]
        if detail:
            out += [dict(path=x.group(1), key=x.group(2), context=x.group(3),
                         occ=int(x.group(4)))
                    for x in re.finditer(
                        r'path: "([^"]+)",\s*(?:callee: "[^"]+",\s*)?'
                        r'key: "([^"]+)",\s*context: "([^"]*)",\s*'
                        r'occurrences: (\d+)', body)]
        else:
            out += re.findall(r'"([A-Z0-9_]+)"', body)
    return out

def main():
    report_path = sys.argv[1]
    flags = set()
    if '--flags' in sys.argv:
        flags = set(sys.argv[sys.argv.index('--flags') + 1].split(','))
    s = open(report_path).read()
    p = '.code_quality_env_flag_baseline.toml'
    t = open(p).read()

    if flags:
        removed = 0
        for f in flags:
            n = len(re.findall(r'^\s*"%s",\n' % f, t, re.M)); removed += n
            t = re.sub(r'^\s*"%s",\n' % f, '', t, flags=re.M)
        rx = re.compile(r'\[\[[a-z_]+\]\]\n(?:[a-z_]+ = [^\n]*\n)+\n?')
        out, last, blocks = [], 0, 0
        for m in rx.finditer(t):
            km = re.search(r'key = "([A-Z0-9_]+)"', m.group(0))
            if km and km.group(1) in flags:
                out.append(t[last:m.start()]); last = m.end(); blocks += 1
        out.append(t[last:]); t = ''.join(out)
        print(f"flags pass: {removed} list entries, {blocks} blocks removed")

    stale = entries_after(s, "stale_rust_ay_key_sites", True)
    unexp = entries_after(s, "unexpected_rust_ay_key_sites", True)
    if stale or unexp:
        blocks = [(x.group(1), x.group(2), x.group(3), int(x.group(4)))
                  for x in re.finditer(
                      r'\[\[rust_ay_key_site\]\]\npath = "([^"]+)"\n'
                      r'key = "([^"]+)"\ncontext = "([^"]*)"\n'
                      r'occurrences = (\d+)\n', t)]
        first = t.index('[[rust_ay_key_site]]')
        last = max(x.end() for x in re.finditer(
            r'\[\[rust_ay_key_site\]\]\npath = "[^"]+"\nkey = "[^"]+"\n'
            r'context = "[^"]*"\noccurrences = \d+\n', t))
        staleset = {(e['path'], e['key'], e['context']) for e in stale}
        entries = [b for b in blocks if (b[0], b[1], b[2]) not in staleset]
        for e in unexp:
            entries.append((e['path'], e['key'], e['context'], e['occ']))
        entries = sorted(set(entries))
        body = ''.join(
            f'[[rust_ay_key_site]]\npath = "{pth}"\nkey = "{k}"\n'
            f'context = "{c}"\noccurrences = {o}\n\n'
            for pth, k, c, o in entries)
        t = t[:first] + body + t[last:].lstrip('\n')
        print(f"key sites: -{len(stale)} stale, +{len(unexp)} unexpected")

    open(p, 'w').write(t)
    print("baseline written; re-run the gate")

if __name__ == '__main__':
    main()
