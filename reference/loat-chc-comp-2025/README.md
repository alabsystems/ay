# reference/loat-chc-comp-2025/README.md

Notes on LoAT's CHC-COMP 2025 entry, used as a comparison reference.

## What this is

- This directory holds only these notes. LoAT's CHC-COMP 2025 release
  (the TRL/ABMC/KIND/BMC portfolio wrapper `LoAT/loat_chc_comp.sh` plus the
  Linux `loat-static` binary) is GPL-3.0 and is not vendored here; fetch it
  from upstream as below, and git ignores the extracted binary
  (`.gitignore`: `reference/**/*-static`).
- This directory is reference-only. It is excluded from Cargo packages and should
  not be treated as part of the published AY crates.

## How to obtain the wrapper and binary

Download LoAT’s `chc-comp-2025` release and extract:

```bash
mkdir -p reference/loat-chc-comp-2025
gh release download chc-comp-2025 -R LoAT-developers/LoAT -p LoAT.zip -D /tmp
unzip -q /tmp/LoAT.zip -d reference/loat-chc-comp-2025
```

## License

LoAT is GPL-3.0. Keep the `COPYING` file that ships with the downloaded LoAT
release archive alongside the extracted binary if you vendor it locally. This
repo does not ship that license file in-tree. Use LoAT as an algorithm
reference only; do not port code into AY.
