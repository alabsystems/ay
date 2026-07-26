# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Small, ownership-safe bridge to ay-search's JSON C ABI."""

from __future__ import annotations

import ctypes
import json
import os
import sys
from pathlib import Path
from typing import Any, Dict


class NativeSearchError(RuntimeError):
    """The search C ABI could not return a valid JSON response."""


_LIB_BASENAMES = {
    "darwin": "libay_ffi.dylib",
    "linux": "libay_ffi.so",
    "win32": "ay_ffi.dll",
}


def _platform_basename() -> str:
    for platform, name in _LIB_BASENAMES.items():
        if sys.platform.startswith(platform):
            return name
    return "libay_ffi.so"


def _candidate_paths():
    for variable in ("AYSEARCH_LIB", "AYZ3_LIB"):
        configured = os.environ.get(variable)
        if configured:
            yield Path(configured)

    here = Path(__file__).resolve().parent
    basename = _platform_basename()
    # A future standalone aysearch wheel may bundle next to this module. The
    # current combined wheel bundles once under sibling package ayz3.
    for name in dict.fromkeys([basename, *_LIB_BASENAMES.values()]):
        yield here / name
        yield here.parent / "ayz3" / name

    for parent in here.parents:
        target = parent / "target"
        if target.is_dir():
            for profile in ("debug", "release"):
                yield target / profile / basename
        if (parent / "Cargo.toml").is_file() and (parent / "crates").is_dir():
            break


def _load_library() -> ctypes.CDLL:
    tried = []
    for path in _candidate_paths():
        tried.append(str(path))
        if path.is_file():
            return ctypes.CDLL(str(path))
    raise OSError(
        "Could not locate libay_ffi. Build it with `cargo build -p ay-ffi`, "
        "install the bundled wheel, or set AYSEARCH_LIB to its full path.\nTried:\n  "
        + "\n  ".join(tried)
    )


lib = _load_library()


def _bind(name: str):
    function = getattr(lib, name)
    function.argtypes = [ctypes.c_char_p]
    # Keep the address. c_char_p would copy the bytes and lose the allocation
    # that must be returned to Rust with ay_string_free.
    function.restype = ctypes.c_void_p
    return function


_solve_json = _bind("ay_search_solve_json")
_compile_json = _bind("ay_search_compile_json")
_string_free = lib.ay_string_free
_string_free.argtypes = [ctypes.c_void_p]
_string_free.restype = None


def _call(function, document: Dict[str, Any]) -> Dict[str, Any]:
    encoded = json.dumps(document, separators=(",", ":")).encode("utf-8")
    pointer = function(encoded)
    if not pointer:
        raise NativeSearchError("AY search returned a null response")
    try:
        raw = ctypes.string_at(pointer).decode("utf-8")
    finally:
        _string_free(pointer)
    try:
        response = json.loads(raw)
    except (UnicodeError, json.JSONDecodeError) as error:
        raise NativeSearchError("AY search returned malformed JSON") from error
    if not isinstance(response, dict):
        raise NativeSearchError("AY search returned a non-object JSON response")
    return response


def solve(document: Dict[str, Any]) -> Dict[str, Any]:
    return _call(_solve_json, document)


def compile_smt2(document: Dict[str, Any]) -> Dict[str, Any]:
    return _call(_compile_json, document)
