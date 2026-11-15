#!/bin/sh
# ay-script-lib: cargo-frontend
#
# The Cargo-family frontend for a script that also ships in the public
# snapshot. Source it, then spell a Cargo command as `ay_cargo <sub> ...`.
#
# On an ALab host Rust is the Trust toolchain, spelled `targo` (owner ruling
# 2026-09-23). A compiling subcommand must name a lane, and these scripts build
# or test the tree as a measurement, never as a proof claim, so a compiling
# subcommand runs as `targo --unverified <sub>`. A lane-free subcommand
# (`metadata`, `clean`, `fmt`, ...) runs as `targo <sub>`. The public snapshot
# pins a stock toolchain and a public host has no `targo`, so there the same
# call is plain `cargo <sub>`. The discriminator is the only one that holds:
# the real targo accepts `--unverified --version`, and stock Cargo refuses the
# flag, including a stock Cargo installed under the `targo` name.
#
#   . "$REPO_ROOT/scripts/lib/cargo_frontend.sh"
#   ay_cargo build --release -p ay --features cli
#   nice -n 5 $(ay_cargo_argv build) build --release -p ay   # under a wrapper
#
# ay_cargo_argv prints the words that go before the subcommand ("targo
# --unverified", "targo" or "cargo"), for a wrapper such as `nice` or `exec`
# that cannot run a shell function. Leave its expansion unquoted.

ay_cargo_argv() {
    if targo --unverified --version >/dev/null 2>&1; then
        case "${1:-}" in
            build | b | check | c | test | t | run | r | bench | rustc | install | doc)
                echo "targo --unverified" ;;
            *)
                echo "targo" ;;
        esac
    else
        echo "cargo"
    fi
}

ay_cargo() {
    # shellcheck disable=SC2046 # the frontend words are meant to split
    $(ay_cargo_argv "${1:-}") "$@"
}
