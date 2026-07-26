#!/usr/bin/env python3
# ay-script: no-python-test-skips
"""Reject active first-party Python test skips and expected failures."""

from __future__ import annotations

import argparse
import ast
from dataclasses import dataclass
from pathlib import Path
import subprocess
import sys
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple


REPO_ROOT = Path(__file__).resolve().parents[1]

# These trees are not first-party AY test code. Git submodules are naturally
# absent from `git ls-files '*.py'`, while these prefixes cover checked-in
# reference and externally maintained sources.
EXTERNAL_PREFIXES = (
    "external/",
    "reference/",
    "third_party/",
    "vendor/",
    "vendors/",
)

# Literal examples used to prove the gate catches every supported spelling.
# This is the only first-party Python fixture excluded from the default scan.
SELF_TEST_FIXTURE_PREFIX = "scripts/tests/fixtures/python_skip_gate/"

FORBIDDEN_CALLABLES = {
    ("pytest", "importorskip"),
    ("pytest", "skip"),
    ("pytest", "xfail"),
    ("pytest", "mark", "skip"),
    ("pytest", "mark", "skipif"),
    ("pytest", "mark", "xfail"),
    ("unittest", "expectedFailure"),
    ("unittest", "skip"),
    ("unittest", "skipIf"),
    ("unittest", "skipUnless"),
}
FORBIDDEN_RAISES = {
    ("unittest", "SkipTest"),
}


@dataclass(frozen=True, order=True)
class Finding:
    path: Path
    line: int
    column: int
    construct: str

    def render(self, root: Path = REPO_ROOT) -> str:
        try:
            display = self.path.relative_to(root)
        except ValueError:
            display = self.path
        return (
            f"{display}:{self.line}:{self.column}: "
            f"forbidden Python test skip: {self.construct}"
        )


class _ImportCollector(ast.NodeVisitor):
    def __init__(self) -> None:
        self.aliases: Dict[str, Tuple[str, ...]] = {}
        self.star_imports: Set[str] = set()

    def visit_Import(self, node: ast.Import) -> None:
        for alias in node.names:
            module = tuple(alias.name.split("."))
            if module and module[0] in {"pytest", "unittest"}:
                local = alias.asname or module[0]
                self.aliases[local] = module

    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        if node.module not in {"pytest", "unittest"}:
            return
        for alias in node.names:
            if alias.name == "*":
                self.star_imports.add(node.module)
                continue
            local = alias.asname or alias.name
            self.aliases[local] = (node.module, alias.name)


class _SkipVisitor(ast.NodeVisitor):
    def __init__(
        self,
        path: Path,
        aliases: Dict[str, Tuple[str, ...]],
        star_imports: Set[str],
    ) -> None:
        self.path = path
        self.aliases = aliases
        self.star_imports = star_imports
        self.findings: List[Finding] = []
        self._seen: Set[Tuple[int, int, str]] = set()

    def _qualified_name(self, node: ast.AST) -> Optional[Tuple[str, ...]]:
        if isinstance(node, ast.Name):
            if node.id in self.aliases:
                return self.aliases[node.id]
            if "unittest" in self.star_imports and node.id in {
                "SkipTest",
                "expectedFailure",
                "skip",
                "skipIf",
                "skipUnless",
            }:
                return ("unittest", node.id)
            if "pytest" in self.star_imports and node.id in {
                "importorskip",
                "skip",
                "xfail",
            }:
                return ("pytest", node.id)
            return (node.id,)
        if isinstance(node, ast.Attribute):
            base = self._qualified_name(node.value)
            if base is not None:
                return (*base, node.attr)
        return None

    def _record(self, node: ast.AST, construct: str) -> None:
        line = getattr(node, "lineno", 1)
        column = getattr(node, "col_offset", 0) + 1
        key = (line, column, construct)
        if key in self._seen:
            return
        self._seen.add(key)
        self.findings.append(Finding(self.path, line, column, construct))

    def _check_reference(self, node: ast.AST) -> None:
        name = self._qualified_name(node)
        if name in FORBIDDEN_CALLABLES:
            self._record(node, ".".join(name))
        elif name is not None and name[-1:] == ("skipTest",):
            self._record(node, ".".join(name))

    def _check_decorators(self, decorators: Sequence[ast.expr]) -> None:
        for decorator in decorators:
            if not isinstance(decorator, ast.Call):
                self._check_reference(decorator)

    def visit_Call(self, node: ast.Call) -> None:
        self._check_reference(node.func)
        self.generic_visit(node)

    def visit_Assign(self, node: ast.Assign) -> None:
        if not isinstance(node.value, ast.Call):
            self._check_reference(node.value)
        self.generic_visit(node)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        if node.value is not None and not isinstance(node.value, ast.Call):
            self._check_reference(node.value)
        self.generic_visit(node)

    def visit_Attribute(self, node: ast.Attribute) -> None:
        # A bare marker reference is active in places such as
        # ``pytest.param(..., marks=pytest.mark.skip)`` and
        # ``pytestmark = [pytest.mark.xfail]``.
        self._check_reference(node)
        self.generic_visit(node)

    def visit_Raise(self, node: ast.Raise) -> None:
        if node.exc is not None:
            target = node.exc.func if isinstance(node.exc, ast.Call) else node.exc
            name = self._qualified_name(target)
            if name in FORBIDDEN_RAISES:
                self._record(target, ".".join(name))
        self.generic_visit(node)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self._check_decorators(node.decorator_list)
        self.generic_visit(node)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self._check_decorators(node.decorator_list)
        self.generic_visit(node)

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self._check_decorators(node.decorator_list)
        self.generic_visit(node)


def scan_source(source: str, path: Path) -> List[Finding]:
    try:
        tree = ast.parse(source, filename=str(path))
    except SyntaxError as error:
        return [
            Finding(
                path,
                error.lineno or 1,
                error.offset or 1,
                f"syntax error while enforcing skip gate: {error.msg}",
            )
        ]

    imports = _ImportCollector()
    imports.visit(tree)
    visitor = _SkipVisitor(path, imports.aliases, imports.star_imports)
    visitor.visit(tree)
    return sorted(visitor.findings)


def scan_path(path: Path) -> List[Finding]:
    try:
        source = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        return [Finding(path, 1, 1, f"unreadable Python source: {error}")]
    return scan_source(source, path)


def _is_default_excluded(relative: Path) -> bool:
    spelling = relative.as_posix()
    return spelling.startswith(EXTERNAL_PREFIXES) or spelling.startswith(
        SELF_TEST_FIXTURE_PREFIX
    )


def discover_tracked_python_files(root: Path = REPO_ROOT) -> List[Path]:
    completed = subprocess.run(
        ["git", "ls-files", "-z", "--", "*.py"],
        cwd=root,
        check=True,
        stdout=subprocess.PIPE,
    )
    files = []
    for raw in completed.stdout.split(b"\0"):
        if not raw:
            continue
        relative = Path(raw.decode("utf-8"))
        if not _is_default_excluded(relative):
            files.append(root / relative)
    return sorted(files)


def expand_explicit_paths(paths: Iterable[Path]) -> List[Path]:
    files: Set[Path] = set()
    for path in paths:
        resolved = path.resolve()
        if resolved.is_dir():
            files.update(candidate for candidate in resolved.rglob("*.py"))
        else:
            files.add(resolved)
    return sorted(files)


def scan_files(paths: Iterable[Path]) -> List[Finding]:
    return sorted(finding for path in paths for finding in scan_path(path))


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "paths",
        nargs="*",
        type=Path,
        help="explicit Python files/directories (default: tracked first-party Python)",
    )
    args = parser.parse_args(argv)

    try:
        files = (
            expand_explicit_paths(args.paths)
            if args.paths
            else discover_tracked_python_files()
        )
    except (OSError, subprocess.CalledProcessError, UnicodeError) as error:
        print(f"failed to discover Python sources: {error}", file=sys.stderr)
        return 2

    findings = scan_files(files)
    for finding in findings:
        print(finding.render(), file=sys.stderr)
    if findings:
        print(
            f"found {len(findings)} active Python test skip construct(s)",
            file=sys.stderr,
        )
        return 1
    print(f"checked {len(files)} first-party Python files: no active test skips")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
