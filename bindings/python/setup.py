# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Build hook that bundles the AY C ABI shared library into the ayz3 wheel.
#
# Metadata lives in pyproject.toml (PEP 621). This setup.py exists ONLY to add a
# build step: before the package files are collected, it runs
#
#     cargo build -p ay-ffi --release
#
# from the Cargo workspace root and copies the produced cdylib
# (libay_ffi.{dylib,so} / ay_ffi.dll) into the `ayz3/` package directory. The
# package-data entry in pyproject.toml then folds it into the wheel, so the
# installed package finds it next to ayz3/_lib.py WITHOUT the source tree.
#
# SCOPE: this produces a wheel for the CURRENT platform only. Cross-platform
# manylinux/CI wheel building is intentionally out of scope (see README).
#
# Escape hatch: set AYZ3_SKIP_CARGO_BUILD=1 to skip the cargo invocation (e.g.
# when an already-built libay_ffi is staged in ayz3/, or for metadata-only
# operations). The build still requires the library to be present to bundle it.

import os
import shutil
import subprocess
import sys
from pathlib import Path

from setuptools import setup
from setuptools.command.build_py import build_py as _build_py
from setuptools.dist import Distribution as _Distribution

HERE = Path(__file__).resolve().parent
PKG_DIR = HERE / "ayz3"

# Platform -> (cdylib basename, cargo target/<profile> filename).
_LIB_BASENAMES = {
    "darwin": "libay_ffi.dylib",
    "linux": "libay_ffi.so",
    "win32": "ay_ffi.dll",
}


def _platform_basename() -> str:
    for key, name in _LIB_BASENAMES.items():
        if sys.platform.startswith(key):
            return name
    return "libay_ffi.so"


def _find_workspace_root() -> Path:
    """Walk up from bindings/python looking for the Cargo workspace root."""
    for parent in [HERE, *HERE.parents]:
        if (parent / "Cargo.toml").is_file() and (parent / "crates").is_dir():
            return parent
    raise RuntimeError(
        "Could not locate the AY Cargo workspace root (a dir with Cargo.toml "
        "and crates/) above bindings/python. The ayz3 wheel must be built from "
        "within the AY source tree so it can compile and bundle libay_ffi."
    )


def _build_and_stage_cdylib() -> Path:
    """Build libay_ffi (release) and copy it into the ayz3 package dir.

    Returns the staged path inside ayz3/.
    """
    basename = _platform_basename()
    dest = PKG_DIR / basename

    skip = os.environ.get("AYZ3_SKIP_CARGO_BUILD") == "1"
    workspace = None
    try:
        workspace = _find_workspace_root()
    except RuntimeError:
        # No source tree (e.g. building from an sdist). Only OK if a prebuilt
        # library is already staged in the package dir.
        if dest.is_file():
            return dest
        raise

    if not skip:
        print(f"[ayz3] building libay_ffi (release): cargo build -p ay-ffi "
              f"--release  (cwd={workspace})")
        subprocess.run(
            ["cargo", "build", "-p", "ay-ffi", "--release"],
            cwd=str(workspace),
            check=True,
        )

    src = workspace / "target" / "release" / basename
    if not src.is_file():
        # Fall back to a debug build if release is somehow absent but debug
        # exists (keeps an explicit skip-with-debug workflow usable).
        debug = workspace / "target" / "debug" / basename
        if debug.is_file():
            src = debug
        elif skip and dest.is_file():
            # AYZ3_SKIP_CARGO_BUILD with no target/ artifact: honor a library
            # already staged in ayz3/ (the documented skip workflow). Gated on
            # `skip` so a successful cargo build whose artifact is missing
            # (e.g. a redirected CARGO_TARGET_DIR) still fails loudly instead
            # of silently bundling a stale pre-staged library.
            return dest
        else:
            raise RuntimeError(
                f"[ayz3] expected built cdylib at {src} but it is missing. "
                f"Build it with `cargo build -p ay-ffi --release`."
            )

    shutil.copy2(src, dest)
    print(f"[ayz3] bundled {src} -> {dest} "
          f"({dest.stat().st_size / 1e6:.1f} MB)")
    return dest


class build_py(_build_py):
    """build_py that stages the cdylib into ayz3/ before collecting files."""

    def run(self):
        _build_and_stage_cdylib()
        super().run()


class BinaryDistribution(_Distribution):
    """Force a platform-specific wheel tag.

    The wheel bundles a compiled, platform-specific cdylib, so it is NOT a pure
    Python ("any") wheel. Marking the distribution as having binary contents
    makes the wheel tag include the platform (e.g. macosx_*/linux_*), so the
    current-platform-only wheel cannot be mistakenly installed on a foreign OS.
    """

    def has_ext_modules(self):  # noqa: D401 - setuptools hook
        return True


setup(cmdclass={"build_py": build_py}, distclass=BinaryDistribution)
