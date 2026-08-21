#!/usr/bin/env python3
# ay-script: milp-gate-corpus
"""
THE CANONICAL MILP GATE CORPUS -- the models the two MILP regression gates read,
in one durable place, with a sha256 per instance and a URL each one is
reconstructible from.

WHY THIS EXISTS. On 2026-08-20 the nineteen models `scripts/milp_node_gate.py`
pins lived in TWO SESSION-SCRATCH DIRECTORIES, i.e. per-session agent
scratchpad paths that exist only on one laptop and only for one session.
The gate was therefore only runnable by the session that happened to
have created them, and only until that scratch was reaped. Its sibling,
`scripts/corpus_guard.py`, had already lost the same bet in a louder way: its
`--corpus` default is `~/ay-corpus`, which DOES NOT EXIST on this box, so the
guard has been unrunnable-by-default for some time and nothing said so.

That is the same failure `scripts/rebuild_milp_bench.py` was written for after
`~/ay-bench/milp/` was found EMPTY in August: *reports cite instance sets by
path, and paths rot*. The fix is not a better path. The fix is a manifest in the
repository, so the corpus is reconstructible FROM THIS REPO ALONE.

WHERE, and why not somewhere that already exists:

  ~/ay-bench/            the durable bench root this repo already uses
    milp/                MIPLIB 2017 working set (154 names), rebuilt by
                         scripts/rebuild_milp_bench.py -- DO NOT ADD TO IT: that
                         script rewrites the directory and its manifest.json from
                         a fixed MIPLIB-2017 name list, so anything else parked
                         there is deleted or orphaned on the next rebuild.
    oracle_v2/           the LP oracle corpus + HiGHS references -- UNTOUCHED by
                         this script, by name, on purpose.
    milp-gate/           <-- THIS. instances/ + a README pointing back at the
                         repo, nothing else. The manifest deliberately lives in
                         the repo and is NOT copied here: two copies drift, and
                         the copy outside version control is the one that wins
                         by accident.

  Fourteen of the thirty are absent from `~/ay-bench/milp` today, and ten of
  those are MIPLIB 3.0 instances the 2017 collection does not serve at all, so
  that directory structurally cannot hold this set even if rebuild_milp_bench.py
  were taught to. A separate sibling is not a preference; it is the only
  arrangement in which ONE directory serves BOTH gates.

WHAT IS IN IT (30 instances, 33 MB uncompressed):

    19  pinned by `.milp_node_baseline.toml`            (the node ratchet)
     5  named in that file's [flaky] section            (mas74 misc07 nw04
                                                         p2756 qiu -- kept so a
                                                         later round can re-test
                                                         the exclusion instead of
                                                         re-sourcing the models)
     6  wanted only by scripts/corpus_guard.py          (air05 flugpl gen
                                                         khb05250 markshare1
                                                         markshare2)

  Stored UNCOMPRESSED (`.mps`, not `.mps.gz`) for one reason: `corpus_guard.py`
  opens `os.path.join(corpus, name + '.mps')` and cannot read a `.gz`. 33 MB is
  cheaper than a format fork between two gates that are supposed to measure the
  same files. `milp_node_gate.py` accepts either.

PROVENANCE, and how it was established. Every sha256 below is of the
UNCOMPRESSED bytes -- the bytes the solver parses, and the bytes the pinned node
counts were measured on. Each was checked against its upstream by downloading
the `.mps.gz`, decompressing it and comparing:

    20 instances  https://miplib.zib.de/WebData/instances/<name>.mps.gz
                  (the same base URL scripts/rebuild_milp_bench.py uses)
    10 instances  https://miplib2010.zib.de/miplib3/miplib3/<name>.mps.gz
                  (MIPLIB 3.0; these are not in the 2017 WebData set)

  All 30 matched. Two traps, both measured, both the reason the source is pinned
  PER INSTANCE rather than guessed from one base URL:

  * air03, air05, mod010 and nw04 are MIPLIB 3.0-era models that are ALSO served
    from the 2017 WebData path, with DIFFERENT bytes. The WebData copy is the one
    that matches what was measured here; fetching those four from the miplib3
    archive would silently change the model and therefore the pinned node counts.
  * the other ten answer HTTP 200 on the WebData path too -- but only after a
    302, and what comes back is an HTML page, not a gzip. Decompressed it is the
    EMPTY STRING (sha256 e3b0c442...). A fetcher that trusted the status code
    would write ten empty models and the gate would report a parse failure it
    could not explain. `--build` verifies the sha256 of every fetch against the
    manifest and refuses on mismatch, which is what makes the status code
    irrelevant.

USAGE
    milp_gate_corpus.py --verify [--corpus DIR]   sha256 every instance (default)
    milp_gate_corpus.py --build  [--corpus DIR]   fetch whatever is missing/wrong
    milp_gate_corpus.py --manifest --corpus DIR   rewrite the in-repo manifest

Exit codes: 0 clean, 1 content mismatch/missing, 2 harness or setup problem.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import os
import sys
import urllib.request

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MANIFEST = os.path.join(REPO, '.milp_gate_corpus.tsv')

#: The durable home. Deliberately a plain constant and not an environment
#: variable: this repository's owner has ruled that new env-var knobs are cruft,
#: and the one override anybody needs is `--corpus`, which every caller of both
#: gates already passes when it wants something else.
DEFAULT_CORPUS = os.path.expanduser('~/ay-bench/milp-gate/instances')

WEBDATA = 'https://miplib.zib.de/WebData/instances/{name}.mps.gz'
MIPLIB3 = 'https://miplib2010.zib.de/miplib3/miplib3/{name}.mps.gz'

SOURCES = {'miplib2017-webdata': WEBDATA, 'miplib3': MIPLIB3}

# WHY EACH MODEL IS HERE. Written down because "why isn't X in the corpus" and
# "why is X in the corpus" are both questions that otherwise need archaeology.
NODE_GATE_PINNED = {
    'air03', 'blend2', 'dcmulti', 'enigma', 'gt2', 'lseu', 'mas76', 'misc03',
    'mod008', 'mod010', 'p0033', 'p0201', 'p0282', 'p0548', 'pk1', 'qnet1',
    'rout', 'stein27', 'stein45',
}
NODE_GATE_FLAKY = {'mas74', 'misc07', 'nw04', 'p2756', 'qiu'}
CORPUS_GUARD = {
    'air03', 'air05', 'blend2', 'dcmulti', 'flugpl', 'gen', 'gt2', 'khb05250',
    'markshare1', 'markshare2', 'mas74', 'mas76', 'misc07', 'mod010', 'p0201',
    'pk1', 'qiu', 'qnet1', 'rout',
}


def roles(name):
    r = []
    if name in NODE_GATE_PINNED:
        r.append('node-gate')
    if name in NODE_GATE_FLAKY:
        r.append('node-gate-flaky')
    if name in CORPUS_GUARD:
        r.append('corpus-guard')
    return '+'.join(r) or 'unused'


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def read_manifest(path=MANIFEST):
    """name -> {sha256, bytes, source, roles}. Tab-separated, `#` comments."""
    rows = {}
    with open(path) as f:
        for lineno, raw in enumerate(f, 1):
            line = raw.rstrip('\n')
            if not line.strip() or line.startswith('#'):
                continue
            parts = line.split('\t')
            if len(parts) != 5:
                raise ValueError('%s:%d: want 5 tab-separated fields, got %d'
                                 % (path, lineno, len(parts)))
            name, digest, size, source, role = parts
            if source not in SOURCES:
                raise ValueError('%s:%d: unknown source %r' % (path, lineno, source))
            rows[name] = {'sha256': digest, 'bytes': int(size),
                          'source': source, 'roles': role}
    return rows


HEADER = '''\
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# THE MILP GATE CORPUS MANIFEST. Written by `scripts/milp_gate_corpus.py
# --manifest`, checked by `--verify`, and used by `--build` to reconstruct
# ~/ay-bench/milp-gate/instances from upstream.
#
# `sha256` is of the UNCOMPRESSED .mps -- the bytes the solver parses and the
# bytes `.milp_node_baseline.toml`'s node counts were measured on. Upstream
# serves .mps.gz; gzip metadata is not reproducible, so the compressed digest is
# deliberately NOT what is pinned here.
#
# source: miplib2017-webdata  https://miplib.zib.de/WebData/instances/<name>.mps.gz
#         miplib3             https://miplib2010.zib.de/miplib3/miplib3/<name>.mps.gz
#
# air03, air05, mod010 and nw04 exist in BOTH archives with DIFFERENT bytes. The
# webdata copy is the measured one; sourcing them from miplib3 would silently
# change the models and therefore every pinned node count on them.
#
# name\tsha256\tbytes\tsource\troles
'''


def write_manifest(rows, path=MANIFEST):
    with open(path, 'w') as f:
        f.write(HEADER)
        for name in sorted(rows):
            r = rows[name]
            f.write('%s\t%s\t%d\t%s\t%s\n'
                    % (name, r['sha256'], r['bytes'], r['source'], r['roles']))


def fetch(name, source, dest):
    url = SOURCES[source].format(name=name)
    with urllib.request.urlopen(url, timeout=180) as resp:
        blob = resp.read()
    text = gzip.decompress(blob)
    tmp = dest + '.part'
    with open(tmp, 'wb') as f:
        f.write(text)
    os.replace(tmp, dest)
    return url


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--corpus', default=DEFAULT_CORPUS)
    ap.add_argument('--verify', action='store_true')
    ap.add_argument('--build', action='store_true')
    ap.add_argument('--manifest', action='store_true',
                    help='rewrite the in-repo manifest from --corpus (deliberate, '
                         'like `milp_node_gate.py --ratchet`)')
    a = ap.parse_args()

    if a.manifest:
        if not os.path.isdir(a.corpus):
            print('SETUP: not a directory: %s' % a.corpus, file=sys.stderr)
            return 2
        try:
            known = {n: r['source'] for n, r in read_manifest().items()}
        except OSError:
            known = {}
        rows = {}
        for fn in sorted(os.listdir(a.corpus)):
            if not fn.endswith('.mps'):
                continue
            name = fn[:-4]
            p = os.path.join(a.corpus, fn)
            if name not in known:
                print('SETUP: %s has no recorded source; add it to SOURCES/the '
                      'manifest by hand first -- a manifest that invents its own '
                      'provenance is not provenance' % name, file=sys.stderr)
                return 2
            rows[name] = {'sha256': sha256_file(p), 'bytes': os.path.getsize(p),
                          'source': known[name], 'roles': roles(name)}
        write_manifest(rows)
        print('manifest: %d instances -> %s'
              % (len(rows), os.path.relpath(MANIFEST, REPO)))
        return 0

    try:
        want = read_manifest()
    except (OSError, ValueError) as e:
        print('SETUP: %s' % e, file=sys.stderr)
        return 2
    if not want:
        print('SETUP: manifest is empty', file=sys.stderr)
        return 2

    if a.build:
        os.makedirs(a.corpus, exist_ok=True)
        got = 0
        for name in sorted(want):
            p = os.path.join(a.corpus, name + '.mps')
            if os.path.exists(p) and sha256_file(p) == want[name]['sha256']:
                continue
            try:
                url = fetch(name, want[name]['source'], p)
            except Exception as e:  # noqa: BLE001 -- report, do not half-build
                print('SETUP: %s: %s' % (name, e), file=sys.stderr)
                return 2
            if sha256_file(p) != want[name]['sha256']:
                print('FAIL: %s from %s does not match the manifest sha256 -- '
                      'upstream changed, or the wrong archive was used'
                      % (name, url), file=sys.stderr)
                return 1
            got += 1
            print('  fetched %-11s %s' % (name, url))
        print('build: %d fetched, %d already correct, corpus %s'
              % (got, len(want) - got, a.corpus))
        return 0

    # --verify is the default: a bare invocation must MEASURE something, not
    # print help and exit 0. A verifier whose no-argument form is a no-op is the
    # same dead gate this whole file exists to retire.
    if not os.path.isdir(a.corpus):
        print('SETUP: corpus not found at %s\n'
              '       rebuild it: scripts/milp_gate_corpus.py --build'
              % a.corpus, file=sys.stderr)
        return 2
    bad, missing = [], []
    for name in sorted(want):
        p = os.path.join(a.corpus, name + '.mps')
        if not os.path.exists(p):
            missing.append(name)
            continue
        d = sha256_file(p)
        if d != want[name]['sha256']:
            bad.append('%-11s sha256 %s, manifest says %s'
                       % (name, d[:16], want[name]['sha256'][:16]))
    print('=== milp gate corpus: %d instances in %s ===' % (len(want), a.corpus))
    for m in missing:
        print('  MISSING  %-11s (%s)' % (m, SOURCES[want[m]['source']].format(name=m)))
    for b in bad:
        print('  MISMATCH %s' % b)
    if not (missing or bad):
        print('  clean: every instance matches its manifest sha256')
    print('=== %d missing, %d mismatched ===' % (len(missing), len(bad)))
    return 1 if (missing or bad) else 0


if __name__ == '__main__':
    sys.exit(main())
