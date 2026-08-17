#!/usr/bin/env bash
# setup.sh — Install F* toolchain for pulse-verified-gc
#
# Usage:
#   ./setup.sh              Install the pinned F* nightly build
#   ./setup.sh --release    Install latest official release instead
#   ./setup.sh --nightly    Install latest nightly instead
#   ./setup.sh --force      Reinstall even if the requested version is present
#
# Prerequisites: curl, bash
# Result: fstar/ directory with bin/fstar.exe, bin/krml, etc.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
FSTAR_DIR="$SCRIPT_DIR/fstar"

# Default: the validated nightly build.  The proofs in this repository are
# checked against this F* (and the Z3 4.15.3 that ships with it); see
# Z3_VERSION in the top-level Makefile.
SOURCE="--nightly"
# NOTE: for --nightly the upstream installer builds the release tag as
# "nightly-$VERSION", so VERSION must be the bare date.  Writing the full tag
# here yields "nightly-nightly-<date>", which 404s and then fails confusingly
# with "gzip: stdin: not in gzip format" when tar unpacks the error page.
VERSION="2026-08-15"
EXPECTED_VERSION="F* nightly-2026-08-15"
FORCE=false

red()   { printf '\033[1;31m%s\033[0m\n' "$*"; }
green() { printf '\033[1;32m%s\033[0m\n' "$*"; }
info()  { printf '\033[1;34m=> %s\033[0m\n' "$*"; }

while [[ $# -gt 0 ]]; do
  case "$1" in
    --release)
      SOURCE="--release"
      VERSION=""
      EXPECTED_VERSION=""
      shift
      ;;
    --nightly)
      SOURCE="--nightly"
      VERSION=""
      EXPECTED_VERSION=""
      shift
      ;;
    --force)
      FORCE=true
      shift
      ;;
    *)
      red "Unknown option: $1"
      exit 1
      ;;
  esac
done

# Check prerequisites
for cmd in curl bash; do
  if ! command -v "$cmd" &>/dev/null; then
    red "Missing prerequisite: $cmd"
    exit 1
  fi
done

# Skip install if already present and correct version
if [ -x "$FSTAR_DIR/bin/fstar.exe" ]; then
  INSTALLED=$("$FSTAR_DIR/bin/fstar.exe" --version 2>/dev/null | head -1 || true)
  info "F* already installed: $INSTALLED"
  if [ "$FORCE" = false ] && { [ -z "$EXPECTED_VERSION" ] || [[ "$INSTALLED" == "$EXPECTED_VERSION"* ]]; }; then
    info "Existing installation matches the requested version."
  else
    info "Reinstalling F* in $FSTAR_DIR ..."
    rm -rf "$FSTAR_DIR"
  fi
fi

if [ ! -x "$FSTAR_DIR/bin/fstar.exe" ]; then
  info "Installing F* to $FSTAR_DIR ..."
  # Defensive: tolerate a "nightly-" prefix on VERSION.  The installer prepends
  # it, so passing the full tag would resolve to "nightly-nightly-<date>".
  if [ "$SOURCE" = "--nightly" ]; then
    VERSION="${VERSION#nightly-}"
  fi
  INSTALL_ARGS=("$SOURCE" "--dest" "$FSTAR_DIR" "--no-link")
  if [ -n "$VERSION" ]; then
    INSTALL_ARGS+=("--version" "$VERSION")
  fi
  curl -fsSL https://aka.ms/install-fstar | bash -s -- "${INSTALL_ARGS[@]}"

  if [ ! -x "$FSTAR_DIR/bin/fstar.exe" ]; then
    red "Install failed — $FSTAR_DIR/bin/fstar.exe not found."
    exit 1
  fi
else
  info "Remove fstar/ or pass --force to reinstall."
fi

# Create karamel/ compatibility layout (symlinks)
# Makefiles expect KRML_HOME with: krml, include/*, krmllib/*
COMPAT="$FSTAR_DIR/karamel"
if [ ! -L "$COMPAT/krml" ]; then
  info "Setting up KaRaMeL compatibility layout..."
  rm -rf "$COMPAT"
  mkdir -p "$COMPAT"
  ln -sf ../bin/krml       "$COMPAT/krml"
  ln -sf ../include/krml   "$COMPAT/include"
  ln -sf ../lib/krml       "$COMPAT/krmllib"
fi

# Fail loudly if we ended up with a different build than the proofs were
# checked against, rather than surfacing it later as a spurious proof regression.
if [ -n "$EXPECTED_VERSION" ]; then
  INSTALLED=$("$FSTAR_DIR/bin/fstar.exe" --version 2>/dev/null | head -1 || true)
  if [[ "$INSTALLED" != "$EXPECTED_VERSION"* ]]; then
    red "Version mismatch: expected '$EXPECTED_VERSION', got '$INSTALLED'."
    exit 1
  fi
fi

green "F* toolchain ready."
"$FSTAR_DIR/bin/fstar.exe" --version
echo
green "Run 'make' to verify all modules."
