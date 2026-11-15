#!/usr/bin/env python3
# ay-script: z3-reference
"""The pinned z3 reference oracle: ci/z3.pin's reader and provisioner.

ci/z3.pin is the one statement of WHICH z3 bytes AY's differential gate is
measured against: per platform row, the upstream release asset (name, size,
sha256) and the sha256 of its bin/z3. This module reads it strictly and
provisions the host's row into a content-addressed, read-only user cache:

    ${XDG_CACHE_HOME:-~/.cache}/ay-z3/<archive sha256>/<asset stem>/bin/z3

Nothing is installed machine-wide and nothing is built. The archive is
streamed to a sibling temporary file, cut at the pinned size, and must match
the pinned size and sha256; its members must be regular files under the one
top directory the asset's name promises; the unpacked bin/z3 must match its
pinned sha256. Only then is the tree made read-only and published by one
rename. An entry that exists is re-hashed on every use and never overwritten:
a tampered one is refused with the command that removes it.

    python3 scripts/_z3_reference.py --provision   # download once; print the bin/z3 path
    python3 scripts/_z3_reference.py --path        # offline; exit 2 when not provisioned
    python3 scripts/_z3_reference.py --verify      # re-hash this host's entry
    python3 scripts/_z3_reference.py --print-pin   # the pin, normalised
    python3 scripts/_z3_reference.py --measure URL # a candidate asset's identity (pin moves)

Exit codes: 0 OK, 1 integrity failure (a hash, size or member that is not the
pinned one), 2 SETUP (no row for this host, not provisioned, unreadable pin,
network). Rust tests reach the pinned bytes through the shared z3 resolver:
`export Z3_PATH="$(python3 scripts/_z3_reference.py --path)"`.

Python 3.9, standard library only.
"""

from __future__ import annotations

import argparse
import hashlib
import http.client
import os
import platform
import re
import secrets
import shlex
import shutil
import stat
import struct
import sys
import tempfile
import urllib.request
import zipfile
from typing import Callable, Dict, List, NamedTuple, Optional, Tuple

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PIN_PATH = os.path.join(REPO, "ci", "z3.pin")
CACHE_NAME = "ay-z3"
CHUNK = 1 << 20
FETCH_TIMEOUT_S = 60
MEASURE_LIMIT = 1 << 30  # --measure has no pinned size; refuse anything larger than 1 GiB

# platform.system(), platform.machine() -> the pin's row key. Exact spellings only:
# an unlisted spelling has no row, and is refused rather than guessed.
PLATFORM_ROWS = {
    ("Darwin", "arm64"): "darwin_arm64",
    ("Darwin", "x86_64"): "darwin_x86_64",
    ("Linux", "x86_64"): "linux_x86_64",
    ("Linux", "aarch64"): "linux_aarch64",
}

GLOBAL_KEYS = ("Z3_VERSION", "Z3_RELEASE_URL", "Z3_REFERENCE_ROW", "Z3_ROWS")
# Longest prefix first: Z3_ASSET_ is a prefix of the two after it.
ROW_PREFIXES = ("Z3_ASSET_SHA256_", "Z3_ASSET_SIZE_", "Z3_BIN_SHA256_", "Z3_ASSET_")
LINE = re.compile(r"^(Z3_[A-Za-z0-9_]+)=([^\s'\"$`\\]+)$")
ROW_KEY = re.compile(r"^[a-z][a-z0-9]*(_[a-z0-9]+)+$")
SHA256 = re.compile(r"^[0-9a-f]{64}$")
SIZE = re.compile(r"^[1-9][0-9]*$")
VERSION = re.compile(r"^[0-9]+\.[0-9]+\.[0-9]+$")


class Z3ReferenceError(Exception):
    """Every refusal of this module."""


class SetupError(Z3ReferenceError):
    """The host cannot run the pinned oracle yet: exit 2."""


class IntegrityError(Z3ReferenceError):
    """Bytes that are not the pinned ones: exit 1."""


class PinError(SetupError):
    """ci/z3.pin does not parse; the message names the file, the line and the rule."""


class NoRow(SetupError):
    """This platform has no row in the pin."""


class NotProvisioned(SetupError):
    """The host's row has no cache entry yet."""


class FetchError(SetupError):
    """The asset could not be downloaded."""


class Tampered(IntegrityError):
    def __init__(self, found: Optional[str], pinned: str, path: str, entry: str) -> None:
        self.found, self.pinned, self.path, self.entry = found, pinned, path, entry
        got = f"sha256 {found}" if found else "missing"
        super().__init__(
            f"{path}: bin/z3 is {got}, ci/z3.pin says sha256 {pinned}. The cache entry is read-only and is "
            f"never overwritten; remove it with `{removal_command(entry)}`, then provision again"
        )


class ArchiveMismatch(IntegrityError):
    def __init__(self, url: str, found: str, pinned: str, found_size: int, pinned_size: int) -> None:
        self.found, self.pinned = found, pinned
        super().__init__(
            f"{url}: downloaded {found_size} bytes with sha256 {found}; ci/z3.pin says {pinned_size} bytes "
            f"with sha256 {pinned}. Nothing was installed"
        )


class SizeExceeded(IntegrityError):
    """The download ran past the pinned size; it was cut there."""


class BadMember(IntegrityError):
    """An archive member that is not a regular file under the asset's one top directory."""


class BinaryMismatch(IntegrityError):
    def __init__(self, found: str, pinned: str) -> None:
        self.found, self.pinned = found, pinned
        super().__init__(
            f"the archive matches ci/z3.pin, but its bin/z3 has sha256 {found} where the pin says {pinned}. "
            "Nothing was installed"
        )


class Row(NamedTuple):
    key: str
    asset: str
    size: int
    asset_sha256: str
    bin_sha256: str

    @property
    def stem(self) -> str:
        """The archive's one top directory: the asset name without `.zip`."""
        return self.asset[: -len(".zip")]


class Pin(NamedTuple):
    version: str
    release_url: str
    reference_row: str
    rows: Tuple[Row, ...]
    source: str

    def row(self, key: str) -> Row:
        for row in self.rows:
            if row.key == key:
                return row
        raise NoRow(f"ci/z3.pin ({self.source}) has no row {key!r}; its rows are {', '.join(self.keys())}")

    def keys(self) -> Tuple[str, ...]:
        return tuple(row.key for row in self.rows)

    def url(self, row: Row) -> str:
        return self.release_url + "/" + row.asset

    def render(self) -> str:
        """The pin as normalised KEY=VALUE lines (no comments, fixed order)."""
        lines = [f"Z3_VERSION={self.version}", f"Z3_RELEASE_URL={self.release_url}",
                 f"Z3_REFERENCE_ROW={self.reference_row}", "Z3_ROWS=" + ",".join(self.keys())]
        for row in self.rows:
            lines += [f"Z3_ASSET_{row.key}={row.asset}", f"Z3_ASSET_SIZE_{row.key}={row.size}",
                      f"Z3_ASSET_SHA256_{row.key}={row.asset_sha256}", f"Z3_BIN_SHA256_{row.key}={row.bin_sha256}"]
        return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------- the pin
def parse_pin(text: str, source: str) -> Pin:
    """Strict KEY=VALUE: no spaces, quoting or expansion; every key known and stated once."""

    def refuse(rule: str, number: Optional[int] = None) -> PinError:
        where = f"{source}:{number}" if number else source
        return PinError(f"{where}: {rule}")

    values: Dict[str, str] = {}
    lines: Dict[str, int] = {}
    row_values: Dict[str, Dict[str, str]] = {}
    for number, line in enumerate(text.splitlines(), 1):
        if not line or line.startswith("#"):
            continue
        match = LINE.match(line)
        if not match:
            raise refuse("not KEY=VALUE with no spaces, quotes or expansion: " + repr(line), number)
        key, value = match.groups()
        if key in lines:
            raise refuse(f"{key} is stated twice (first at line {lines[key]})", number)
        lines[key] = number
        if key in GLOBAL_KEYS:
            values[key] = value
            continue
        prefix = next((p for p in ROW_PREFIXES if key.startswith(p)), None)
        row = key[len(prefix):] if prefix else ""
        if not prefix or not ROW_KEY.match(row):
            raise refuse(f"unknown key {key}", number)
        row_values.setdefault(row, {})[prefix] = value
    for key in GLOBAL_KEYS:
        if key not in values:
            raise refuse(f"{key} is missing")
    version = values["Z3_VERSION"]
    if not VERSION.match(version):
        raise refuse(f"Z3_VERSION={version} is not MAJOR.MINOR.PATCH")
    url = values["Z3_RELEASE_URL"]
    if not url.startswith("https://") or not url.endswith("/z3-" + version):
        raise refuse(f"Z3_RELEASE_URL={url} must be https:// and end with the tag /z3-{version}")
    keys = values["Z3_ROWS"].split(",")
    if any(not ROW_KEY.match(key) for key in keys) or len(set(keys)) != len(keys):
        raise refuse(f"Z3_ROWS={values['Z3_ROWS']} must list distinct row keys")
    if values["Z3_REFERENCE_ROW"] not in keys:
        raise refuse(f"Z3_REFERENCE_ROW={values['Z3_REFERENCE_ROW']} is not one of Z3_ROWS")
    orphans = sorted(set(row_values) - set(keys))
    if orphans:
        raise refuse(f"row keys for {', '.join(orphans)}, which Z3_ROWS does not list")
    rows: List[Row] = []
    for key in keys:
        got = row_values.get(key, {})
        missing = [prefix + key for prefix in ROW_PREFIXES if prefix not in got]
        if missing:
            raise refuse(f"row {key} is missing {', '.join(missing)}")
        asset, size = got["Z3_ASSET_"], got["Z3_ASSET_SIZE_"]
        if "/" in asset or version not in asset or not asset.endswith(".zip") or asset == ".zip":
            raise refuse(f"Z3_ASSET_{key}={asset} must be a file name carrying {version} and ending .zip")
        if not SIZE.match(size):
            raise refuse(f"Z3_ASSET_SIZE_{key}={size} is not a positive integer")
        for prefix in ("Z3_ASSET_SHA256_", "Z3_BIN_SHA256_"):
            if not SHA256.match(got[prefix]):
                raise refuse(f"{prefix}{key}={got[prefix]} is not 64 lowercase hex digits")
        rows.append(Row(key, asset, int(size), got["Z3_ASSET_SHA256_"], got["Z3_BIN_SHA256_"]))
    return Pin(version, url, values["Z3_REFERENCE_ROW"], tuple(rows), source)


def load_pin(path: Optional[str] = None) -> Pin:
    path = path or PIN_PATH
    try:
        with open(path, encoding="utf-8") as handle:
            text = handle.read()
    except OSError as error:
        raise PinError(f"{path}: {error}")
    return parse_pin(text, path)


def host_row_key(pin: Pin) -> str:
    """This host's row key; NoRow when the platform is not one the pin lists."""
    system, machine = platform.system(), platform.machine()
    key = PLATFORM_ROWS.get((system, machine))
    if key is None or key not in pin.keys():
        raise NoRow(f"ci/z3.pin has no row for {system} {machine}; its rows are {', '.join(pin.keys())}")
    return key


def match_row(pin: Pin, sha: str) -> Optional[Row]:
    """The row whose bin/z3 has these bytes, or None."""
    return next((row for row in pin.rows if row.bin_sha256 == sha), None)


# ---------------------------------------------------------------------------- the cache
def cache_root(explicit: Optional[str] = None) -> str:
    """`explicit`, else ${XDG_CACHE_HOME:-~/.cache}/ay-z3 (the ci/cakepb.pin convention)."""
    if explicit:
        return explicit
    base = os.environ.get("XDG_CACHE_HOME") or os.path.join(os.path.expanduser("~"), ".cache")
    return os.path.join(base, CACHE_NAME)


def entry_path(row: Row, root: str) -> str:
    return os.path.join(root, row.asset_sha256)


def binary_path(row: Row, root: str) -> str:
    return os.path.join(entry_path(row, root), row.stem, "bin", "z3")


def removal_command(entry: str) -> str:
    quoted = shlex.quote(entry)
    return f"chmod -R u+w {quoted} && rm -rf {quoted}"


def sha256_file(path: str) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(CHUNK), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _row(pin: Optional[Pin], key: Optional[str]) -> Tuple[Pin, Row]:
    pin = load_pin() if pin is None else pin
    return pin, pin.row(key or host_row_key(pin))


def resolve_pinned(root: Optional[str] = None, key: Optional[str] = None, pin: Optional[Pin] = None) -> str:
    """The provisioned bin/z3 of the host's row, re-hashed. Offline: never downloads."""
    pin, row = _row(pin, key)
    root = cache_root(root)
    entry = entry_path(row, root)
    path = binary_path(row, root)
    if not os.path.lexists(entry):
        raise NotProvisioned(
            f"ci/z3.pin row {row.key} is not provisioned under {root}: run "
            "`python3 scripts/_z3_reference.py --provision`"
        )
    try:
        found: Optional[str] = sha256_file(path)
    except OSError:
        found = None
    if found != row.bin_sha256:
        raise Tampered(found, row.bin_sha256, path, entry)
    return path


# ---------------------------------------------------------------------------- provisioning
Fetch = Callable[[str], object]


def _urlopen(url: str) -> object:
    return urllib.request.urlopen(url, timeout=FETCH_TIMEOUT_S)


def _download(url: str, dest: str, limit: int, fetch: Fetch) -> Tuple[int, str]:
    """Stream `url` into the new file `dest`, hashing as it goes; never read past `limit` + 1 bytes."""
    digest = hashlib.sha256()
    total = 0
    try:
        response = fetch(url)
    except (OSError, ValueError, http.client.HTTPException) as error:
        raise FetchError(f"{url}: {error}")
    try:
        with open(dest, "xb") as out:
            while True:
                try:
                    chunk = response.read(min(CHUNK, limit + 1 - total))  # type: ignore[attr-defined]
                except (OSError, http.client.HTTPException) as error:
                    raise FetchError(f"{url}: {error}")
                if not chunk:
                    break
                total += len(chunk)
                if total > limit:
                    raise SizeExceeded(f"{url}: the download ran past {limit} bytes; it was cut there")
                digest.update(chunk)
                out.write(chunk)
    finally:
        close = getattr(response, "close", None)
        if close:
            close()
    return total, digest.hexdigest()


def _open_zip(path: str, url: str) -> zipfile.ZipFile:
    try:
        return zipfile.ZipFile(path)
    except zipfile.BadZipFile as error:
        raise BadMember(f"{url}: not a zip archive ({error})")


def _checked_members(archive: zipfile.ZipFile, stem: str) -> List[zipfile.ZipInfo]:
    """Every member is a regular file under the single top directory `stem`, named once."""
    seen = set()
    members = archive.infolist()
    for info in members:
        name = info.filename
        parts = name.split("/")
        if name.endswith("/"):
            raise BadMember(f"archive member {name!r}: a directory entry, not a regular file")
        if name.startswith("/") or "\\" in name or any(part in ("", ".", "..") for part in parts):
            raise BadMember(f"archive member {name!r}: not a plain relative path")
        if parts[0] != stem or len(parts) < 2:
            raise BadMember(f"archive member {name!r}: outside the single top directory {stem}/")
        mode = info.external_attr >> 16
        if info.create_system != 3 or not stat.S_ISREG(mode):
            raise BadMember(f"archive member {name!r}: not a regular file (mode {oct(mode)})")
        if name in seen:
            raise BadMember(f"archive member {name!r}: named twice")
        seen.add(name)
    if f"{stem}/bin/z3" not in seen:
        raise BadMember(f"the archive has no {stem}/bin/z3")
    return members


def _extract(archive: zipfile.ZipFile, members: List[zipfile.ZipInfo], dest: str) -> None:
    for info in members:
        target = os.path.join(dest, *info.filename.split("/"))
        os.makedirs(os.path.dirname(target), exist_ok=True)
        with archive.open(info) as source, open(target, "xb") as out:
            shutil.copyfileobj(source, out, CHUNK)
        os.chmod(target, stat.S_IMODE(info.external_attr >> 16))


def _read_only(tree: str) -> None:
    for directory, _dirs, files in os.walk(tree, topdown=False):
        for name in files:
            path = os.path.join(directory, name)
            os.chmod(path, stat.S_IMODE(os.lstat(path).st_mode) & ~0o222)
        os.chmod(directory, 0o555)


def _discard(path: str) -> None:
    """Remove a temporary file or tree this module made, read-only or not."""
    if not os.path.lexists(path):
        return
    if os.path.isdir(path) and not os.path.islink(path):
        for directory, _dirs, _files in os.walk(path):
            os.chmod(directory, 0o700)
        shutil.rmtree(path)
    else:
        os.unlink(path)


def provision(root: Optional[str] = None, key: Optional[str] = None, fetch: Optional[Fetch] = None,
              pin: Optional[Pin] = None) -> str:
    """The host row's bin/z3, downloading and installing it first when absent. Idempotent."""
    pin, row = _row(pin, key)
    root = cache_root(root)
    entry = entry_path(row, root)
    # 1. An existing entry is verified, and a tampered one refused, never overwritten.
    if os.path.lexists(entry):
        return resolve_pinned(root, row.key, pin)
    os.makedirs(root, exist_ok=True)
    tag = f"{os.getpid()}-{secrets.token_hex(4)}"
    archive_path = os.path.join(root, f".dl-{tag}.zip")  # a sibling FILE, never inside the entry
    staging = os.path.join(root, f".tmp-{tag}")
    url = pin.url(row)
    try:
        # 2. Download, cut at the pinned size; size and sha must be the pin's.
        size, found = _download(url, archive_path, row.size, fetch or _urlopen)
        if size != row.size or found != row.asset_sha256:
            raise ArchiveMismatch(url, found, row.asset_sha256, size, row.size)
        with _open_zip(archive_path, url) as archive:
            # 3. Members, then 4. extraction with their modes.
            members = _checked_members(archive, row.stem)
            os.mkdir(staging, 0o700)
            _extract(archive, members, staging)
        # 5. The unpacked binary is the pinned one.
        found = sha256_file(os.path.join(staging, row.stem, "bin", "z3"))
        if found != row.bin_sha256:
            raise BinaryMismatch(found, row.bin_sha256)
        # 6. The archive goes before anything is made read-only.
        os.unlink(archive_path)
        # 7. Read-only, the staging directory itself included.
        _read_only(staging)
        # 8. Publish by one rename in the same directory.
        try:
            os.rename(staging, entry)
        except OSError:
            if not os.path.lexists(entry):
                raise
            # Another provisioner published first: verify its entry, discard ours.
            path = resolve_pinned(root, row.key, pin)
            _discard(staging)
            return path
    except BaseException:
        # 9. A failure anywhere leaves neither the archive nor the staging tree behind.
        _discard(archive_path)
        _discard(staging)
        raise
    return binary_path(row, root)


# ---------------------------------------------------------------------------- --measure
LC_REQ_DYLD = 0x80000000
DYLIB_COMMANDS = {0xC, 0x18 | LC_REQ_DYLD, 0x1F | LC_REQ_DYLD, 0x20, 0x23 | LC_REQ_DYLD}


def _macho_dylibs(data: bytes, base: int = 0) -> List[str]:
    """The dylibs a Mach-O (thin or universal) loads, from its load commands."""
    magic = data[base:base + 4]
    if magic in (b"\xca\xfe\xba\xbe", b"\xca\xfe\xba\xbf"):  # universal: big-endian fat header
        wide = magic[3] == 0xBF
        (count,) = struct.unpack_from(">I", data, base + 4)
        names: List[str] = []
        for index in range(count):
            if wide:
                _cpu, _sub, offset, _size, _align, _res = struct.unpack_from(">iiQQII", data, base + 8 + 32 * index)
            else:
                _cpu, _sub, offset, _size, _align = struct.unpack_from(">iiIII", data, base + 8 + 20 * index)
            names += [name for name in _macho_dylibs(data, offset) if name not in names]
        return names
    kinds = {b"\xcf\xfa\xed\xfe": ("<", 32), b"\xce\xfa\xed\xfe": ("<", 28),
             b"\xfe\xed\xfa\xcf": (">", 32), b"\xfe\xed\xfa\xce": (">", 28)}
    if magic not in kinds:
        raise ValueError("not a Mach-O file")
    order, header = kinds[magic]
    (ncmds,) = struct.unpack_from(order + "I", data, base + 16)
    offset, names = base + header, []
    for _ in range(ncmds):
        cmd, size = struct.unpack_from(order + "II", data, offset)
        if cmd in DYLIB_COMMANDS:
            (name_at,) = struct.unpack_from(order + "I", data, offset + 8)
            raw = data[offset + name_at:offset + size]
            names.append(raw.split(b"\0", 1)[0].decode("utf-8", "replace"))
        offset += size
    return names


def _elf_needed(data: bytes) -> List[str]:
    """The DT_NEEDED entries of an ELF file, from its SHT_DYNAMIC section."""
    if data[:4] != b"\x7fELF":
        raise ValueError("not an ELF file")
    wide, order = data[4] == 2, "<" if data[5] == 1 else ">"
    if wide:
        shoff, = struct.unpack_from(order + "Q", data, 0x28)
        shentsize, shnum = struct.unpack_from(order + "HH", data, 0x3A)
        section, entry = order + "IIQQQQIIQQ", order + "qQ"
    else:
        shoff, = struct.unpack_from(order + "I", data, 0x20)
        shentsize, shnum = struct.unpack_from(order + "HH", data, 0x2E)
        section, entry = order + "IIIIIIIIII", order + "iI"
    if shnum == 0:
        raise ValueError("ELF file without section headers: dynamic dependencies unreadable")
    sections = [struct.unpack_from(section, data, shoff + i * shentsize) for i in range(shnum)]
    needed: List[str] = []
    for _name, kind, _flags, _addr, offset, size, link, _info, _align, _entsize in sections:
        if kind != 6:  # SHT_DYNAMIC
            continue
        strtab = sections[link][4]
        for at in range(offset, offset + size, struct.calcsize(entry)):
            tag, value = struct.unpack_from(entry, data, at)
            if tag == 0:
                break
            if tag == 1:  # DT_NEEDED
                needed.append(data[strtab + value:data.index(b"\0", strtab + value)].decode("utf-8", "replace"))
    return needed


def dynamic_dependencies(data: bytes) -> Tuple[str, List[str]]:
    if data[:4] == b"\x7fELF":
        return "ELF", _elf_needed(data)
    return "Mach-O", _macho_dylibs(data)


def measure(url: str, fetch: Optional[Fetch] = None) -> Dict[str, object]:
    """A candidate asset's identity, for moving the pin. Installs nothing."""
    with tempfile.TemporaryDirectory(prefix="ay-z3-measure-") as scratch:
        path = os.path.join(scratch, "asset.zip")
        size, digest = _download(url, path, MEASURE_LIMIT, fetch or _urlopen)
        with _open_zip(path, url) as archive:
            names = [info.filename for info in archive.infolist()]
            tops = sorted({name.split("/", 1)[0] for name in names})
            binary = next((n for n in names if len(tops) == 1 and n == tops[0] + "/bin/z3"), None)
            data = archive.read(binary) if binary else b""
    report: Dict[str, object] = dict(url=url, bytes=size, sha256=digest, top=",".join(tops), members=len(names))
    if binary:
        report["bin_z3_sha256"] = hashlib.sha256(data).hexdigest()
        try:
            kind, needs = dynamic_dependencies(data)
        except (ValueError, struct.error, IndexError) as error:
            report["format"] = f"unreadable ({error})"
        else:
            report.update(format=kind, needs=needs, loads_libz3=any("libz3" in need for need in needs))
    return report


# ---------------------------------------------------------------------------- CLI
def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    verb = parser.add_mutually_exclusive_group(required=True)
    verb.add_argument("--provision", action="store_true", help="download and install the host's row once")
    verb.add_argument("--path", action="store_true", help="print the provisioned bin/z3 (offline)")
    verb.add_argument("--verify", action="store_true", help="re-hash the host's provisioned entry")
    verb.add_argument("--print-pin", action="store_true", help="print ci/z3.pin normalised")
    verb.add_argument("--measure", metavar="URL", help="print a candidate asset's identity; installs nothing")
    parser.add_argument("--platform", metavar="KEY", help="a pin row key instead of this host's")
    parser.add_argument("--cache", metavar="DIR", help="the cache root (default ${XDG_CACHE_HOME:-~/.cache}/ay-z3)")
    parser.add_argument("--pin", metavar="FILE", help="explicit audit pin (default ci/z3.pin; does not move the gate pin)")
    args = parser.parse_args(argv)
    try:
        if args.measure:
            report = measure(args.measure)
            for field in ("url", "bytes", "sha256", "top", "members", "bin_z3_sha256", "format"):
                print(f"{field:14s} {report.get(field, 'absent')}")
            for need in report.get("needs", []):  # type: ignore[union-attr]
                print(f"{'needs':14s} {need}")
            print(f"{'loads_libz3':14s} {report.get('loads_libz3', 'unknown')}")
            return 0
        pin = load_pin(args.pin)
        if args.print_pin:
            sys.stdout.write(pin.render())
            return 0
        if args.provision:
            print(provision(args.cache, args.platform, pin=pin))
        elif args.path:
            print(resolve_pinned(args.cache, args.platform, pin))
        else:
            path = resolve_pinned(args.cache, args.platform, pin)
            row = pin.row(args.platform or host_row_key(pin))
            print(f"{path}\nOK row {row.key} sha256 {row.bin_sha256}")
        return 0
    except IntegrityError as error:
        print(f"z3-reference: INTEGRITY: {error}", file=sys.stderr)
        return 1
    except (SetupError, OSError) as error:
        print(f"z3-reference: SETUP: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
