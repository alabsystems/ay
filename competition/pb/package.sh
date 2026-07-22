#!/bin/sh
# ay-script: pb26-package
# Trident matrix packager: builds, hardens, and VALIDATES every competition
# entry declared in competition/pb/entries.toml.
#
# Lineage: born from the 2026-07-10 failure where packaged manifests still
# declared optional git dependencies on a PRIVATE repository and the
# organizer's credential-less build host hung at a username prompt.
#
# HARD GUARANTEES — the script FAILS rather than emit any package violating:
#   G1  no git-sourced dependency in any packaged manifest or the lockfile
#   G2  the staged source builds OFFLINE from a clean extract with NO
#       credentials, NO home, an EMPTY cargo home (fully vendored); entries
#       share one byte-identical source tree (hash-verified), so the build is
#       verified once and inherited by every entry
#   G3  every entry's binary passes answer-checked smoke tests through THAT
#       ENTRY'S generated run.sh (SAT/UNSAT/OPT, WBO top-cost pair, CERT proof)
#   G4  every tarball fits the portal's upload limit
#
# Usage: competition/pb/package.sh [output-dir]   (default ~/pbcomp-work/submission)
set -eu

REPO=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
OUTDIR=${1:-"$HOME/pbcomp-work/submission"}
STAMP=$(date -u +%Y-%m-%d)
WORK=$(mktemp -d "${TMPDIR:-/tmp}/ay-trident.XXXXXX")
trap 'rm -rf "$WORK"' EXIT
mkdir -p "$OUTDIR"

# A python with tomllib (3.11+) for the manifest; probe common names.
PY=""
for candidate in python3.14 python3.13 python3.12 python3.11 python3; do
    if command -v "$candidate" >/dev/null 2>&1 \
        && "$candidate" -c 'import tomllib' >/dev/null 2>&1; then
        PY=$candidate
        break
    fi
done
[ -n "$PY" ] || { echo "ERROR: no python with tomllib (need >=3.11)" >&2; exit 2; }

STAGE="$WORK/source"
mkdir -p "$STAGE"

echo "== staging trimmed workspace (shared by all entries)"
python3 - "$REPO" "$STAGE" <<'PYEOF'
import re, sys, json, shutil, subprocess, pathlib
repo, dest = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])

meta = json.loads(subprocess.run(
    ["cargo", "metadata", "--format-version", "1", "--no-deps"],
    cwd=repo, capture_output=True, text=True, check=True).stdout)
packages = {p["name"]: p for p in meta["packages"]}
members = {p["name"]: pathlib.Path(p["manifest_path"]).parent for p in meta["packages"]}

# Closure over DECLARED path dependencies (optional ones included): cargo
# validates every path-referenced manifest at resolve time even when the dep
# is optional and its feature is off. Dev-dependencies excluded (stripped
# below; not needed to build the binary).
closure, frontier = set(), ["ay-pb"]
while frontier:
    name = frontier.pop()
    if name in closure or name not in packages:
        continue
    closure.add(name)
    for dep in packages[name]["dependencies"]:
        if dep.get("kind") == "dev" or not dep.get("path"):
            continue
        if dep["name"] in members and dep["name"] not in closure:
            frontier.append(dep["name"])
closure = sorted(closure)
print("closure members:", closure)

for name in closure:
    src = members[name]
    shutil.copytree(src, dest / src.relative_to(repo),
                    ignore=shutil.ignore_patterns("target", ".git"))

root = (repo / "Cargo.toml").read_text()
member_block = "members = [\n" + "".join(
    f'    "{members[n].relative_to(repo)}",\n' for n in closure) + "]"
root = re.sub(r"members\s*=\s*\[[^\]]*\]", member_block, root, count=1)
(dest / "Cargo.toml").write_text(root)
for extra in ("rustfmt.toml",):
    if (repo / extra).exists():
        shutil.copy2(repo / extra, dest / extra)
# Repo-root build-script includes (crates reference ../../build_support/*).
shutil.copytree(repo / "build_support", dest / "build_support")

# Strip [dev-dependencies] sections (member dev-deps resolve into the lockfile
# and drag test-only path deps + vendor weight).
DEV_SECTION = re.compile(
    r'^\[(?:target\.[^\]]+\.)?dev-dependencies\]\n(?:(?!\[).*\n?)*', re.M)
for manifest in dest.rglob("Cargo.toml"):
    text = manifest.read_text()
    stripped = DEV_SECTION.sub("", text)
    if stripped != text:
        manifest.write_text(stripped)

# Strip every OPTIONAL git-sourced dependency declaration and the default-off
# features referencing them (never in the competition binary; the declarations
# alone break credential-less hosts).
# The public workspace has no optional git-sourced dependency
# declarations; the G1a gate below still fails closed on any.
STRIP = {}
for rel, patterns in STRIP.items():
    path = dest / rel
    if not path.exists():
        continue
    text = path.read_text()
    for pat in patterns:
        text = re.sub(pat, "", text, flags=re.M)
    path.write_text(text)

# G1a: no git-sourced dependency may remain in ANY packaged manifest.
offenders = []
for manifest in dest.rglob("Cargo.toml"):
    for i, line in enumerate(manifest.read_text().splitlines(), 1):
        if re.search(r'\bgit\s*=\s*"', line):
            offenders.append(f"{manifest.relative_to(dest)}:{i}: {line.strip()}")
if offenders:
    sys.exit("G1 VIOLATION — git dependencies in packaged manifests:\n"
             + "\n".join(offenders))
print("G1a OK: no git dependencies declared in packaged manifests")
PYEOF

echo "== resolving + vendoring (network used HERE only)"
cd "$STAGE"
cargo generate-lockfile --quiet
if grep -q 'git+' Cargo.lock; then
    echo "G1 VIOLATION — git sources in packaged Cargo.lock:" >&2
    grep 'git+' Cargo.lock >&2
    exit 1
fi
echo "G1b OK: packaged lockfile is git-free"
mkdir -p .cargo
# NOTE: no --quiet — it would suppress the source-replacement config snippet
# cargo vendor prints to stdout (a smoke gate once caught exactly that).
cargo vendor --locked vendor > .cargo/config.toml 2> /dev/null
grep -q 'vendored-sources' .cargo/config.toml || {
    echo "G2 VIOLATION — vendor config missing source replacement" >&2; exit 1; }

SOURCE_HASH=$( (cd "$WORK" && find source -type f -print0 | sort -z \
    | xargs -0 shasum -a 256 | shasum -a 256 | awk '{print $1}') )
echo "staged source hash: $SOURCE_HASH"

# Emit entry metadata for the shell loop: slug|name|commandline|categories.
ENTRIES_FILE="$WORK/entries.txt"
"$PY" - "$REPO/competition/pb/entries.toml" > "$ENTRIES_FILE" <<'PYEOF'
import sys, tomllib
CATEGORY = {"DEC-LIN": 112, "OPT-LIN": 113, "DEC-LIN-CERT": 114,
            "OPT-LIN-CERT": 115, "DEC-NLC": 116, "OPT-NLC": 117,
            "SOFT-LIN": 118, "PARTIAL-LIN": 119}
manifest = tomllib.load(open(sys.argv[1], "rb"))
for entry in manifest["entry"]:
    cats = ",".join(str(CATEGORY[t]) for t in entry["tracks"])
    unchecked = "1" if entry.get("uncheckeddel") else "0"
    print("|".join([entry["slug"], entry["name"], entry["commandline"],
                    cats, unchecked]))
PYEOF

gen_run_sh() {
    slug=$1; out=$2
    "$PY" - "$REPO/competition/pb/entries.toml" \
        "$REPO/competition/pb/run.sh.in" "$slug" > "$out" <<'PYEOF'
import sys, tomllib
manifest = tomllib.load(open(sys.argv[1], "rb"))
template = open(sys.argv[2]).read()
slug = sys.argv[3]
entry = next(e for e in manifest["entry"] if e["slug"] == slug)
env_block = "\n".join(
    f'export {key}={value}' for key, value in sorted(entry.get("env", {}).items()))
out = template.replace("@TRIDENT_NAME@", entry["name"])
out = out.replace("@TRIDENT_ENV@", env_block)
sys.stdout.write(out)
PYEOF
    chmod 755 "$out"
}

# Regenerate the checked-in default run.sh from the manifest (single source of
# truth; the repo copy is the "ay" entry's).
gen_run_sh ay "$REPO/competition/pb/run.sh"

FIRST_BUILD_DONE=0
SMOKE_BIN=""
while IFS='|' read -r SLUG NAME CMDLINE CATS UNCHECKED; do
    PKGNAME="ay-pbcomp-${SLUG}-${STAMP}"
    PKG="$WORK/$PKGNAME"
    echo
    echo "== entry '$NAME' ($SLUG) -> $PKGNAME"
    mkdir -p "$PKG"
    cp -R "$STAGE" "$PKG/source"
    cp "$REPO/competition/pb/build.sh" "$PKG/"
    cp "$REPO/competition/pb/solver_description.txt" "$PKG/"
    gen_run_sh "$SLUG" "$PKG/run.sh"
    printf 'entry: %s\ncommit: %s\ndate: %s\nsource-sha256: %s\npackaged-by: competition/pb/package.sh (Trident matrix; vendored, offline, git-free)\n' \
        "$NAME" "$(cd "$REPO" && git rev-parse HEAD)" \
        "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$SOURCE_HASH" > "$PKG/COMMIT.txt"

    TARBALL="$OUTDIR/$PKGNAME.tar.gz"
    tar -czf "$TARBALL" -C "$WORK" "$PKGNAME"
    SIZE=$(stat -f%z "$TARBALL" 2>/dev/null || stat -c%s "$TARBALL")
    if [ "$SIZE" -gt 250000000 ]; then
        echo "G4 VIOLATION — $PKGNAME is $SIZE bytes (>250MB guard)" >&2
        exit 1
    fi
    echo "G4 OK: $SIZE bytes"

    SMOKE="$WORK/smoke-$SLUG"
    mkdir -p "$SMOKE"
    tar -xzf "$TARBALL" -C "$SMOKE"
    if [ "$FIRST_BUILD_DONE" -eq 0 ]; then
        SMOKEHOME="$WORK/smokehome"
        mkdir -p "$SMOKEHOME/cargo"
        CARGO_BIN_DIR=$(dirname "$(rustup which cargo 2>/dev/null || command -v cargo)")
        env -i \
            PATH="$CARGO_BIN_DIR:/usr/bin:/bin:/usr/sbin:/sbin" \
            HOME="$SMOKEHOME" \
            CARGO_HOME="$SMOKEHOME/cargo" \
            GIT_TERMINAL_PROMPT=0 \
            GIT_CONFIG_GLOBAL=/dev/null \
            GIT_CONFIG_NOSYSTEM=1 \
            CARGO_NET_OFFLINE=true \
            "$SMOKE/$PKGNAME/build.sh"
        echo "G2 OK: credential-less offline build succeeded (verified once; entries share source-sha256)"
        SMOKE_BIN="$SMOKE/$PKGNAME/ay-pb"
        FIRST_BUILD_DONE=1
    else
        # Byte-identical source tree (same staged copy, hash recorded in
        # COMMIT.txt) => the first entry's G2 build verdict applies; reuse its
        # binary for this entry's smoke.
        cp "$SMOKE_BIN" "$SMOKE/$PKGNAME/ay-pb"
        chmod 755 "$SMOKE/$PKGNAME/ay-pb"
        echo "G2 OK: inherited (source tree byte-identical to verified build)"
    fi

    RUN="$SMOKE/$PKGNAME/run.sh"
    SD="$WORK/smoke-instances"
    if [ ! -d "$SD" ]; then
        mkdir -p "$SD"
        cat > "$SD/sat.opb" <<'EOF'
* #variable= 2 #constraint= 1
+1 x1 +1 x2 >= 1 ;
EOF
        cat > "$SD/unsat.opb" <<'EOF'
* #variable= 1 #constraint= 2
+1 x1 >= 1 ;
-1 x1 >= 0 ;
EOF
        cat > "$SD/opt.opb" <<'EOF'
* #variable= 2 #constraint= 2
min: +2 x1 +3 x2 ;
+1 x1 +1 x2 >= 1 ;
-1 x1 -1 x2 >= -2 ;
EOF
        # OPT case whose lower bound is NOT a positive combination of input rows
        # (needs a divide-by-2 rounding cut): the native structural cut cannot be
        # built, so the certified path must fail closed and re-certify via the
        # OPT-LIN-CERT fallback. Exercises the deferral path that previously
        # shipped an unverifiable `rup >= 1 ;` (VeriPB reject). Optimum = 2.
        cat > "$SD/opt-hard.opb" <<'EOF'
* #variable= 3 #constraint= 3
min: +1 x1 +1 x2 +1 x3 ;
+1 x1 +1 x2 >= 1 ;
+1 x2 +1 x3 >= 1 ;
+1 x1 +1 x3 >= 1 ;
EOF
        cat > "$SD/wbo-top-unsat.wbo" <<'EOF'
* #variable= 2 #constraint= 3
soft: 2 ;
-1 x1 -1 x2 >= -1 ;
[2] +1 x1 >= 1 ;
[2] +1 x2 >= 1 ;
EOF
        cat > "$SD/wbo-top-sat.wbo" <<'EOF'
* #variable= 2 #constraint= 3
soft: 3 ;
-1 x1 -1 x2 >= -1 ;
[2] +1 x1 >= 1 ;
[2] +1 x2 >= 1 ;
EOF
    fi
    smoke_case() {
        bench=$1; expect=$2; proof=${3:-}
        if [ -n "$proof" ]; then
            got=$(TIMELIMIT=30 "$RUN" "$bench" "$proof" | grep '^s ' | head -1)
        else
            got=$(TIMELIMIT=30 "$RUN" "$bench" | grep '^s ' | head -1)
        fi
        if [ "$got" != "$expect" ]; then
            echo "G3 VIOLATION [$NAME] $(basename "$bench"): expected '$expect', got '$got'" >&2
            exit 1
        fi
        echo "  smoke[$NAME] $(basename "$bench"): $got"
    }
    smoke_case "$SD/sat.opb"           "s SATISFIABLE"
    smoke_case "$SD/unsat.opb"         "s UNSATISFIABLE"
    smoke_case "$SD/opt.opb"           "s OPTIMUM FOUND"
    smoke_case "$SD/wbo-top-unsat.wbo" "s UNSATISFIABLE"
    smoke_case "$SD/wbo-top-sat.wbo"   "s OPTIMUM FOUND"
    smoke_case "$SD/opt.opb"           "s OPTIMUM FOUND" "$SD/opt-$SLUG.veripb"
    grep -q 'conclusion BOUNDS' "$SD/opt-$SLUG.veripb" || {
        echo "G3 VIOLATION [$NAME] — certified case produced no OPT conclusion" >&2
        exit 1
    }
    smoke_case "$SD/unsat.opb"         "s UNSATISFIABLE" "$SD/unsat-$SLUG.veripb"
    grep -q 'conclusion UNSAT' "$SD/unsat-$SLUG.veripb" || {
        echo "G3 VIOLATION [$NAME] — certified UNSAT case produced no UNSAT conclusion" >&2
        exit 1
    }
    # Certified SAT: DEC-LIN-CERT passes PROOFFILE on satisfiable instances
    # too, and AY commits a solution-only `conclusion SAT` proof there — the
    # exact writer the 2026-07-15 change set rewired, so it must be
    # checker-verified like the other conclusion kinds.
    smoke_case "$SD/sat.opb"           "s SATISFIABLE" "$SD/sat-$SLUG.veripb"
    grep -q 'conclusion SAT' "$SD/sat-$SLUG.veripb" || {
        echo "G3 VIOLATION [$NAME] — certified SAT case produced no SAT conclusion" >&2
        exit 1
    }
    # The structurally-hard OPT case: certified path must produce a conclusion
    # via the fail-closed -> OPT-LIN-CERT fallback (no unverifiable native rup).
    smoke_case "$SD/opt-hard.opb"      "s OPTIMUM FOUND" "$SD/opt-hard-$SLUG.veripb"
    grep -q 'conclusion BOUNDS' "$SD/opt-hard-$SLUG.veripb" || {
        echo "G3 VIOLATION [$NAME] — hard certified case produced no OPT conclusion" >&2
        exit 1
    }
    # NOTE: a VALID cert-fallback proof legitimately ENDS with `rup >= 1 ;` — the
    # empty-clause step, made UP-derivable by the preceding lifted `rup` steps. Its
    # presence is NOT a defect; only VeriPB can tell a supported empty clause from
    # an unsupported one, so the real gate is the VeriPB run below (not a grep).
    # HARD GATE when a VeriPB checker is reachable (VERIPB/VERIPB_BIN/PATH): the
    # organizer's checker is the ultimate arbiter, so verify BOTH certified smoke
    # proofs here rather than trust that a 'conclusion BOUNDS' line means valid.
    # Skips (with a loud note) when no checker is present so credential-less build
    # hosts still package; a reachable checker makes rejection fatal.
    VERIPB_BIN=${VERIPB:-${VERIPB_BIN:-$(command -v veripb 2>/dev/null || true)}}
    if [ -n "$VERIPB_BIN" ] && [ -x "$VERIPB_BIN" ]; then
        # Verify every certified smoke proof in BOTH deletion modes. The entry
        # declares unchecked deletions (uncheckeddel), so the organizer checks
        # with `-u` — and VeriPB also switches to unchecked mode MID-PROOF when
        # a core deletion check fails. In `-u` the checker discounts soli-logged
        # solutions: an un-hinted `conclusion BOUNDS` fails there with "No
        # solution has been logged in the proof and no solution has been given
        # in the conclusion" (a known `-u`-mode reject class), so a
        # checked-mode-only gate is a false green.
        for pair in "opt.opb:opt-$SLUG.veripb" "opt-hard.opb:opt-hard-$SLUG.veripb" "unsat.opb:unsat-$SLUG.veripb" "sat.opb:sat-$SLUG.veripb"; do
            f=${pair%%:*}; p=${pair#*:}
            for mode in "" "-u"; do
                if "$VERIPB_BIN" $mode "$SD/$f" "$SD/$p" 2>&1 | grep -q 'VERIFIED'; then
                    echo "  veripb[$NAME]${mode:+ $mode} $f: VERIFIED"
                else
                    echo "G3 VIOLATION [$NAME] — VeriPB${mode:+ $mode} REJECTED certified proof for $f" >&2
                    "$VERIPB_BIN" $mode "$SD/$f" "$SD/$p" 2>&1 | tail -3 >&2
                    exit 1
                fi
            done
        done
    else
        echo "  NOTE[$NAME]: no VeriPB checker found (set VERIPB=/path); shipped the" \
             "structural CERT gate only. Verify proofs against VeriPB before submitting."
    fi
    echo "G3 OK [$NAME]: all answer-checked smoke cases passed"

    echo "VALIDATED: $TARBALL"
    echo "  sha256: $(shasum -a 256 "$TARBALL" | awk '{print $1}')"
    echo "  md5:    $(md5 -q "$TARBALL" 2>/dev/null || md5sum "$TARBALL" | awk '{print $1}')"
    CATFLAGS=$(printf ' --category %s' $(echo "$CATS" | tr ',' ' '))
    UDFLAG=""
    [ "$UNCHECKED" = "1" ] && UDFLAG=" --uncheckeddel"
    echo "  upload (submission portal): --file $TARBALL \\"
    echo "            --name $NAME --version $STAMP --commandline '$CMDLINE' \\"
    echo "            --complete Y$UDFLAG$CATFLAGS"
done < "$ENTRIES_FILE"

echo
echo "TRIDENT MATRIX COMPLETE: $(wc -l < "$ENTRIES_FILE" | tr -d ' ') entries validated"
