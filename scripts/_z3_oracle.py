#!/usr/bin/env python3
# ay-script: z3-oracle
"""The ONE z3 oracle resolver for AY's Python and shell tooling.

z3 is the oracle AY is measured against, and the name `z3` does not say which
program answers. A sandbox or agent terminal can put a stub first on PATH under
that name (aterm's reroute stub refuses every by-name call: exit 2, empty
stdout), and AY itself is a z3 drop-in that prints z3's banner under that name.
A harness that runs `z3` by name, or takes `shutil.which("z3")`, then either
reads a refusal as "z3 answered nothing" and goes silently blind, or compares
AY against AY. So a z3 is reached BY PATH and must PROVE it is z3 first.

This mirrors crates/ay-sys/src/z3_oracle.rs, which every Rust test and CLI path
uses; the two must keep the same rule:

1. `Z3_PATH`, when set and non-empty, is authoritative. It must name a path
   (never looked up on PATH), and a path that fails identity is an error,
   never a fallback to another z3.
2. Otherwise PATH is walked the way the aterm stub's passthrough walks it:
   empty and relative entries are skipped, and so is every directory holding a
   `.atpkg-reroute-dir` file; a candidate must be an executable non-directory,
   and a file whose second line is `# atpkg reroute stub v1` is passed over
   without being run. The first candidate that identifies as z3 wins.
3. Identity: `--version` exits 0 with a first stdout line starting
   `Z3 version `, AND `--z3-mode --version` does NOT (real z3 rejects that
   option; AY accepts it and prints the banner). Each probe is bounded.

Library use (from a script in scripts/):
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import _z3_oracle
    z3 = _z3_oracle.z3_oracle()          # raises Z3Unavailable
    subprocess.run([z3.path, "-in"], ...)
    print(z3.identity())                  # which z3 answered: banner + path

Shell use:
    z3="$(python3 scripts/_z3_oracle.py --path)" || exit 1
"""

from __future__ import annotations

import os
import subprocess
import sys
from typing import List, NamedTuple, Optional, Sequence, Tuple

REROUTE_DIR_MARKER = ".atpkg-reroute-dir"
REROUTE_STUB_SIGNATURE = "# atpkg reroute stub v1"
PROBE_TIMEOUT_S = 10.0
BANNER_PREFIX = "Z3 version "
PROGRAM = "z3.exe" if os.name == "nt" else "z3"


class PassedOver(NamedTuple):
    """A candidate the resolver did not use, and why."""

    path: str
    reason: str

    def __str__(self) -> str:
        return f"{self.path} [{self.reason}]"


class Z3Oracle(NamedTuple):
    """A z3 that proved its identity, reachable by an absolute path."""

    path: str
    banner: str
    source: str  # "Z3_PATH" | "PATH" | "explicit"
    passed_over: Tuple[PassedOver, ...] = ()

    def version(self) -> Optional[Tuple[int, int, int]]:
        return parse_banner_version(self.banner)

    def identity(self) -> str:
        """Banner, path (and where it resolves to), how it was found, and what
        was passed over: the line a report prints to say which z3 answered."""
        text = f"{self.banner} ({self.path}"
        real = os.path.realpath(self.path)
        if real != self.path:
            text += f" -> {real}"
        text += {"Z3_PATH": "; via Z3_PATH", "PATH": "; via PATH"}.get(
            self.source, "; named explicitly"
        )
        if self.passed_over:
            text += "; passed over " + ", ".join(str(p) for p in self.passed_over)
        return text + ")"


class Z3Unavailable(Exception):
    """No usable z3. `misconfigured` marks a set-but-wrong Z3_PATH, which a
    caller must never treat as plain absence."""

    def __init__(
        self,
        reason: str,
        misconfigured: bool = False,
        passed_over: Sequence[PassedOver] = (),
    ) -> None:
        super().__init__(reason)
        self.misconfigured = misconfigured
        self.passed_over = tuple(passed_over)


def z3_version_banner(returncode: int, stdout: str) -> Optional[str]:
    """The banner line of a completed `--version` run when it identifies z3."""
    lines = stdout.lstrip().splitlines()
    if returncode != 0 or not lines:
        return None
    banner = lines[0].rstrip()
    return banner if banner.startswith(BANNER_PREFIX) else None


def parse_banner_version(banner: str) -> Optional[Tuple[int, int, int]]:
    """`Z3 version 4.8.12 - 64 bit` -> (4, 8, 12); a missing patch is 0."""
    words = banner.split()
    if "version" not in words:
        return None
    index = words.index("version") + 1
    if index >= len(words):
        return None
    parts = words[index].split(".")
    try:
        numbers = [int(part) for part in parts[:3]]
    except ValueError:
        return None
    if len(numbers) < 2:
        return None
    return (numbers[0], numbers[1], numbers[2] if len(numbers) > 2 else 0)


def is_reroute_stub(path: str) -> bool:
    """True when the file's second line is the reroute-stub signature; the
    file is read, never executed."""
    try:
        with open(path, "rb") as handle:
            head = handle.read(4096)
    except OSError:
        return False
    lines = head.split(b"\n")
    return len(lines) > 1 and lines[1] == REROUTE_STUB_SIGNATURE.encode()


def _is_executable(path: str) -> bool:
    return os.path.exists(path) and not os.path.isdir(path) and os.access(path, os.X_OK)


def _names_a_path(value: str) -> bool:
    return os.path.isabs(value) or os.path.dirname(value) != ""


def path_candidates(
    program: str, path_value: Optional[str]
) -> Tuple[List[str], List[PassedOver]]:
    """Executable `program` files on `path_value` after the reroute rules, and
    the reroute directories and stub files passed over."""
    candidates: List[str] = []
    passed_over: List[PassedOver] = []
    for directory in (path_value or "").split(os.pathsep):
        if not directory or not os.path.isabs(directory):
            continue
        candidate = os.path.join(directory, program)
        if os.path.isfile(os.path.join(directory, REROUTE_DIR_MARKER)):
            if os.path.exists(candidate):
                passed_over.append(
                    PassedOver(candidate, f"aterm reroute directory ({REROUTE_DIR_MARKER})")
                )
            continue
        if not _is_executable(candidate) or candidate in candidates:
            continue
        if is_reroute_stub(candidate):
            passed_over.append(PassedOver(candidate, "aterm reroute stub"))
            continue
        candidates.append(candidate)
    return candidates, passed_over


def _probe(path: str, args: Sequence[str]) -> Tuple[int, str]:
    rendered = " ".join(args)
    try:
        completed = subprocess.run(
            [path, *args],
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            timeout=PROBE_TIMEOUT_S,
            check=False,
        )
    except subprocess.TimeoutExpired:
        raise ValueError(f"`{rendered}` did not answer within {PROBE_TIMEOUT_S:.0f} s")
    except OSError as error:
        raise ValueError(f"`{rendered}` could not run: {error}")
    return completed.returncode, completed.stdout.decode("utf-8", "replace")


def vet(candidate: str) -> str:
    """The banner, or ValueError(why the candidate is not z3)."""
    if is_reroute_stub(candidate):
        raise ValueError("aterm reroute stub")
    code, stdout = _probe(candidate, ["--version"])
    banner = z3_version_banner(code, stdout)
    if banner is None:
        first = stdout.strip().splitlines()[0] if stdout.strip() else ""
        raise ValueError(f"`--version` did not print a Z3 banner (exit={code}, stdout={first!r})")
    try:
        code, stdout = _probe(candidate, ["--z3-mode", "--version"])
    except ValueError as error:
        raise ValueError(f"negative control `--z3-mode --version`: {error}")
    if z3_version_banner(code, stdout) is not None:
        raise ValueError("answers `--z3-mode --version` with a Z3 banner: an AY drop-in, not z3")
    return banner


def identify_z3(candidate: str, source: str = "explicit") -> Z3Oracle:
    """Identity-check one explicit path; ValueError(reason) when it is not z3."""
    path = os.path.abspath(os.path.expanduser(candidate))
    if not _is_executable(path):
        raise ValueError("is not an executable file")
    return Z3Oracle(path, vet(path), source)


def _search(program: str, path_value: Optional[str]) -> Z3Oracle:
    candidates, passed_over = path_candidates(program, path_value)
    for candidate in candidates:
        try:
            return Z3Oracle(candidate, vet(candidate), "PATH", tuple(passed_over))
        except ValueError as error:
            passed_over.append(PassedOver(candidate, str(error)))
    if not passed_over:
        raise Z3Unavailable(f"no {program} on PATH")
    raise Z3Unavailable(
        f"no {program} on PATH identifies as z3; passed over "
        + ", ".join(str(p) for p in passed_over),
        passed_over=passed_over,
    )


def resolve_z3(z3_path: Optional[str] = None, path: Optional[str] = None) -> Z3Oracle:
    """The resolution rule over explicit inputs (`z3_path` plays Z3_PATH,
    `path` plays PATH). Uncached; raises Z3Unavailable."""
    if z3_path:
        if not _names_a_path(z3_path):
            raise Z3Unavailable(
                f"Z3_PATH={z3_path} is not a usable z3: it names a program, not a path; "
                "Z3_PATH is never looked up on PATH",
                misconfigured=True,
            )
        try:
            return identify_z3(z3_path, "Z3_PATH")
        except ValueError as error:
            raise Z3Unavailable(
                f"Z3_PATH={z3_path} is not a usable z3: {error}", misconfigured=True
            )
    return _search(PROGRAM, path)


def resolve_z3_program(program: str, path: Optional[str] = None) -> Z3Oracle:
    """A caller-supplied spelling: a value with a directory component is that
    file, identity-checked; a bare name is looked up with the stub-skipping walk."""
    if _names_a_path(program):
        try:
            return identify_z3(program)
        except ValueError as error:
            raise Z3Unavailable(f"{program} is not a usable z3: {error}")
    return _search(program, path)


_RESOLVED: Optional[Tuple[Optional[Z3Oracle], Optional[Z3Unavailable]]] = None


def z3_oracle() -> Z3Oracle:
    """The process's z3 oracle: Z3_PATH, else the first identified z3 on PATH.
    Resolved once per process; raises Z3Unavailable."""
    global _RESOLVED
    if _RESOLVED is None:
        try:
            _RESOLVED = (resolve_z3(os.environ.get("Z3_PATH"), os.environ.get("PATH")), None)
        except Z3Unavailable as error:
            _RESOLVED = (None, error)
    oracle, error = _RESOLVED
    if oracle is None:
        assert error is not None
        raise error
    return oracle


def resolve_z3_spelling(value: str) -> Z3Oracle:
    """A user's `--z3 VALUE`: the bare name `z3` is `z3_oracle()` (honouring
    Z3_PATH); anything else is `resolve_z3_program` over PATH."""
    if value in ("z3", PROGRAM):
        return z3_oracle()
    return resolve_z3_program(value, os.environ.get("PATH"))


def find_z3() -> Optional[Z3Oracle]:
    """`z3_oracle()`, or None when no z3 is on PATH. A set-but-wrong Z3_PATH
    still raises: an explicit choice never degrades into absence."""
    try:
        return z3_oracle()
    except Z3Unavailable as error:
        if error.misconfigured:
            raise
        return None


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    if args not in ([], ["--path"]):
        print("usage: _z3_oracle.py [--path]", file=sys.stderr)
        return 2
    try:
        oracle = z3_oracle()
    except Z3Unavailable as error:
        print(f"z3-oracle: {error}", file=sys.stderr)
        return 1
    print(oracle.path if args == ["--path"] else oracle.identity())
    return 0


if __name__ == "__main__":
    sys.exit(main())
