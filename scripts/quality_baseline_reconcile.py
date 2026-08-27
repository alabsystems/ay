#!/usr/bin/env python3
# ay-script: quality-baseline-reconcile
"""Reconcile the code-quality ratchets from the quality gate's own report.

Companion to `flag_baseline_reconcile.py`, which owns the env-flag ledger. This
one owns the four size/construct ratchets and the file_size waiver ceilings:

    .code_quality_file_size_baseline.toml       [GROWTH] / [SHRINK] / [NEW-DEBT]
    .code_quality_function_size_baseline.toml   [GROWTH] / [SHRINK] / [NEW-DEBT]
    .code_quality_construct_baseline.toml       [CHANGED] / [NEW]
    .code_quality_waivers.toml                  [OVERSIZE]

Usage:
    cargo run --release --locked -q -p ay-quality-gate > /tmp/gate.log 2>&1
    python3 scripts/quality_baseline_reconcile.py /tmp/gate.log
    # re-run the gate; repeat until it passes (two passes is normal, see below)

The ratchets are bidirectional: growth AND unratcheted shrinkage are both hard
failures, so every entry is set to the value the gate just measured. Running
this does not judge whether the growth was a good idea — it records it so the
gate enforces from the new level instead of staying red. Review the diff.

TWO PASSES, BY DESIGN: a [NEW] construct site cannot be written correctly in one
go, because the entry is bound by a scanner fingerprint that the gate never
prints for a site it has no baseline for. This script seeds such an entry with
the real site count and a deliberately wrong fingerprint; the next gate run then
reports the true value as an ordinary [CHANGED] diff, which the second pass
applies. That is why the usage above says to iterate.

NOT HANDLED (reconcile by hand): the env-flag ledger (use
flag_baseline_reconcile.py, then add the capability/key list entries, the
[[rust_read]] rows and any [[dynamic_call]] row yourself — that script documents
the same gap); [UNSORTED] baseline-identity errors, which mean two entries for
one file are out of order and want a human to look; and [INVALID-IDENTITY],
which means an entry is structurally wrong (e.g. sites = 0).

Waiver ceilings get a dated one-line re-audit note naming the commit that last
touched the file. That note is a pointer, not a justification — if the growth is
yours, replace it with a real reason before committing.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def _split_ctx(spec: str) -> tuple[str, str]:
    """`impl Foo::fn bar` -> ("impl Foo", "bar"); `fn bar` -> ("", "bar")."""
    marker = spec.rfind("::fn ")
    if marker >= 0:
        return spec[:marker], spec[marker + 5 :]
    if not spec.startswith("fn "):
        raise SystemExit(f"unrecognized function identity: {spec!r}")
    return "", spec[3:]


def _insert_after(text: str, anchor: str, block: str) -> str:
    at = text.index(anchor) + len(anchor)
    return text[:at] + block + text[at:]


def reconcile_files(log: str) -> str:
    path = ROOT / ".code_quality_file_size_baseline.toml"
    text = path.read_text()
    ratcheted = added = 0
    for name, now in re.findall(r"\[(?:GROWTH|SHRINK)\] ([^\s:]+\.rs): now (\d+) lines", log):
        pattern = re.compile(r'(\[\[file\]\]\npath = "' + re.escape(name) + r'"\nlines = )(\d+)')
        text, hits = pattern.subn(lambda m: m.group(1) + now, text)
        if hits != 1:
            raise SystemExit(f"file entry {name}: matched {hits}, expected 1")
        ratcheted += 1
    for name, lines in re.findall(
        r"\[NEW-DEBT\] unwaived oversized Rust file ([^\s:]+\.rs): (\d+) lines", log
    ):
        if f'path = "{name}"' in text:
            continue
        blocks = re.findall(r'\[\[file\]\]\npath = "([^"]+)"\nlines = (\d+)\n', text)
        prev = None
        for block in blocks:
            if block[0] < name:
                prev = block
            else:
                break
        anchor = f'[[file]]\npath = "{prev[0]}"\nlines = {prev[1]}\n'
        text = _insert_after(text, anchor, f'\n[[file]]\npath = "{name}"\nlines = {lines}\n')
        added += 1
    path.write_text(text)
    return f"files: {ratcheted} ratcheted, {added} new"


def reconcile_functions(log: str) -> str:
    path = ROOT / ".code_quality_function_size_baseline.toml"
    text = path.read_text()
    ratcheted = added = 0
    for name, spec, now in re.findall(
        r"\[(?:GROWTH|SHRINK)\] ([^\s:]+\.rs)::(.+?): now (\d+) lines", log
    ):
        ctx, fn = _split_ctx(spec)
        pattern = re.compile(
            r'(\[\[function\]\]\npath = "' + re.escape(name) + r'"\ncontext = "' + re.escape(ctx)
            + r'"\nfunction = "' + re.escape(fn) + r'"\nlines = )(\d+)'
        )
        text, hits = pattern.subn(lambda m: m.group(1) + now, text)
        if hits != 1:
            raise SystemExit(f"function {name}::{ctx}::{fn}: matched {hits}, expected 1")
        ratcheted += 1
    for name, spec, lines in re.findall(
        r"\[NEW-DEBT\] unwaived oversized Rust function ([^\s:]+\.rs)::(.+?): (\d+) lines", log
    ):
        ctx, fn = _split_ctx(spec)
        key = (name, ctx, fn)
        blocks = re.findall(
            r'\[\[function\]\]\npath = "([^"]+)"\ncontext = "([^"]*)"\nfunction = "([^"]+)"\nlines = (\d+)\n',
            text,
        )
        if key in [(b[0], b[1], b[2]) for b in blocks]:
            continue
        prev = None
        for block in blocks:
            if (block[0], block[1], block[2]) < key:
                prev = block
            else:
                break
        anchor = (
            f'[[function]]\npath = "{prev[0]}"\ncontext = "{prev[1]}"\n'
            f'function = "{prev[2]}"\nlines = {prev[3]}\n'
        )
        text = _insert_after(
            text,
            anchor,
            f'\n[[function]]\npath = "{name}"\ncontext = "{ctx}"\nfunction = "{fn}"\nlines = {lines}\n',
        )
        added += 1
    path.write_text(text)
    return f"functions: {ratcheted} ratcheted, {added} new"


def reconcile_constructs(log: str) -> str:
    path = ROOT / ".code_quality_construct_baseline.toml"
    text = path.read_text()
    updated = seeded = 0
    changed = re.findall(
        r"\[CHANGED\] construct ([^\s:]+)::(\w+) at line \d+ \([^)]*\): sites (\d+) -> (\d+), "
        r"AST (\d+) -> (\d+), macro (\d+) -> (\d+), fingerprint (sha256:[0-9a-f]+) -> (sha256:[0-9a-f]+)",
        log,
    )
    for name, cat, _so, sn, _ao, an, _mo, mn, _old, new in changed:
        pattern = re.compile(
            r'(\[\[construct\]\]\npath = "' + re.escape(name) + r'"\ncategory = "' + re.escape(cat)
            + r'"\nsites = )\d+(\nast_sites = )\d+(\nmacro_token_sites = )\d+(\nfingerprint = ")'
            r'sha256:[0-9a-f]+(")'
        )
        text, hits = pattern.subn(
            lambda m: m.group(1) + sn + m.group(2) + an + m.group(3) + mn + m.group(4) + new + m.group(5),
            text,
        )
        if hits != 1:
            raise SystemExit(f"construct {name}::{cat}: matched {hits}, expected 1")
        updated += 1
    for name, cat, count in re.findall(
        r"\[NEW\] production construct ([^\s:]+)::(\w+) has (\d+) unbaselined site", log
    ):
        key = (name, cat)
        blocks = re.findall(r'\[\[construct\]\]\npath = "([^"]+)"\ncategory = "([^"]+)"\n', text)
        if key in blocks:
            continue
        prev = None
        for block in blocks:
            if block < key:
                prev = block
            else:
                break
        anchor = f'[[construct]]\npath = "{prev[0]}"\ncategory = "{prev[1]}"\n'
        start = text.index(anchor)
        end = text.index("\n\n", start) + 2
        # Deliberately wrong fingerprint: the next gate run prints the true one.
        seed = (
            "[[construct]]\n"
            f'path = "{name}"\ncategory = "{cat}"\nsites = {count}\nast_sites = {count}\n'
            'macro_token_sites = 0\nfingerprint = "sha256:' + "a" * 64 + '"\n\n'
        )
        text = text[:end] + seed + text[end:]
        seeded += 1
    path.write_text(text)
    return f"constructs: {updated} updated, {seeded} seeded (re-run the gate)"


def reconcile_waivers(log: str, today: str) -> str:
    path = ROOT / ".code_quality_waivers.toml"
    text = path.read_text()
    ratcheted = 0
    for name, now, allowed in re.findall(
        r"\[OVERSIZE\]\s+file_size\s+(\S+)\s+\((\d+) lines > (\d+) allowed\)", log
    ):
        blame = subprocess.run(
            ["git", "log", "-1", "--format=%h %s", "--", name],
            cwd=ROOT, capture_output=True, text=True, check=False,
        ).stdout.strip()
        pattern = re.compile(r'(file = "' + re.escape(name) + r'"\nmax_lines = )' + allowed + r"\b")
        text, hits = pattern.subn(lambda m: m.group(1) + now, text)
        if hits != 1:
            raise SystemExit(f"waiver {name}: matched {hits}, expected 1")
        entry = re.search(
            r'file = "' + re.escape(name) + r'"\nmax_lines = ' + now
            + r'\nexpires = "[^"]+"\nreason = "(.*?)"\n',
            text, re.S,
        )
        note = f" Re-audited {today}: {allowed}->{now}, absorbing {blame or 'a concurrent landing'}."
        if entry and note.strip() not in entry.group(1):
            text = text[: entry.start(1)] + entry.group(1) + note + text[entry.end(1) :]
        ratcheted += 1
    path.write_text(text)
    return f"waivers: {ratcheted} ratcheted"


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    log = Path(sys.argv[1]).read_text()
    today = subprocess.run(
        ["date", "+%Y-%m-%d"], capture_output=True, text=True, check=False
    ).stdout.strip()
    report = [
        reconcile_files(log),
        reconcile_functions(log),
        reconcile_constructs(log),
        reconcile_waivers(log, today),
    ]
    print(" | ".join(report))
    for marker, meaning in (
        ("[UNSORTED]", "two entries for one file are out of order"),
        ("[INVALID-IDENTITY]", "an entry is structurally invalid"),
        ("env debt", "the env-flag ledger drifted"),
    ):
        if marker in log:
            print(f"NOT handled by this script: {marker} — {meaning}; reconcile by hand.")


if __name__ == "__main__":
    main()
