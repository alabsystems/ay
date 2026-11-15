#!/usr/bin/env python3
"""Regenerate the Clean island in trust_surface.rs from the canonical .lean.

Run this after ANY edit to clean/veripb_kernel.lean, then re-run
`targo --unverified test -p veripb-core-proved --test island_sync` (which fails if the
island and the .lean have drifted) and `scripts/verify-proofs.sh`.

Mirrors strip_and_asciify() in veripb-core-proved/tests/island_sync.rs:
drop Lean comments, rewrite the two non-ASCII tokens, collapse blank runs.

The island body is EXACTLY the stripped .lean -- there is no unpinned
addendum region any more.  The seven citation-discharging theorems that
used to be spliced in here live at the end of the .lean, so `clean check`
type-checks them and `clean export-cert` exports replayable proofs of them.
"""
import sys

import os

os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))

LEAN = 'veripb-core-proved/clean/veripb_kernel.lean'
SURF = 'veripb-core-proved/src/trust_surface.rs'
ISLAND_OPEN = 'clean {\n'
# The island body contains no occurrence of "\n}\n" (a Lean declaration never
# starts a line with `}`), so this terminator is unambiguous.  island_sync.rs
# locates the island the same way.
ISLAND_CLOSE = '\n}\n'


def strip_and_asciify(src: str) -> str:
    out = []
    i, depth, n = 0, 0, len(src)
    while i < n:
        two = src[i:i + 2]
        if two == '/-':
            depth += 1
            i += 2
            continue
        if two == '-/' and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth > 0:
            i += 1
            continue
        if two == '--':
            while i < n and src[i] != '\n':
                i += 1
            continue
        out.append(src[i])
        i += 1
    s = ''.join(out).replace('→', '->').replace('∀', 'forall')
    res, blank = [], False
    for line in s.split('\n'):
        line = line.rstrip()
        if not line:
            if blank or not res:
                continue
            blank = True
        else:
            blank = False
        res.append(line)
    while res and not res[-1]:
        res.pop()
    return '\n'.join(res) + '\n'


def main():
    lean = open(LEAN).read()
    if '--print' in sys.argv[1:]:
        # The canonical island text, on stdout, without touching any file.
        sys.stdout.write(strip_and_asciify(lean))
        return
    if '--sha256' in sys.argv[1:]:
        # sha256 of that canonical text. `scripts/verify-proofs.sh` writes it
        # into the bundle manifest, where it ties the exported proof bundle to
        # the .lean it was exported from. Done here rather than by piping into
        # shasum/sha256sum so the script needs exactly one external tool.
        import hashlib
        print(hashlib.sha256(strip_and_asciify(lean).encode()).hexdigest())
        return
    surf = open(SURF).read()
    body_start = surf.index(ISLAND_OPEN) + len(ISLAND_OPEN)
    body_end = surf.index(ISLAND_CLOSE, body_start)
    if ISLAND_CLOSE in surf[body_start:body_end]:  # defensive; cannot happen
        sys.exit('ambiguous island terminator')
    new_island = strip_and_asciify(lean)
    # strip_and_asciify ends with '\n'; the body slice stops just before the
    # newline that opens the "\n}\n" terminator, so drop the trailing one.
    new_surf = surf[:body_start] + new_island[:-1] + surf[body_end:]
    # Only the ISLAND BODY must be pure ASCII (it is lexed as Rust token
    # trees); the surrounding Rust doc comments may use anything, exactly as
    # `island_body_is_pure_ascii` in tests/island_sync.rs checks.
    if not new_island.isascii():
        bad = [c for c in new_island if not c.isascii()][:5]
        sys.exit(f'non-ASCII in regenerated island body: {bad!r}')
    if '`' in new_island:
        sys.exit('backticks do not lex as Rust tokens; they must not survive '
                 'into the island body')
    open(SURF, 'w').write(new_surf)
    print('island regenerated:', len(new_island), 'bytes')
    if new_surf == surf:
        print('  (byte-identical to the committed island)')


if __name__ == '__main__':
    main()
