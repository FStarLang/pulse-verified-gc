#!/usr/bin/env bash
# setup.sh — Install F* toolchain for pulse-verified-gc
#
# Usage:
#   ./setup.sh              Install F* v2026.04.17 binary release
#   ./setup.sh --nightly    Install latest nightly instead
#
# Prerequisites: curl, bash
# Result: fstar/ directory with bin/fstar.exe, bin/krml, etc.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
FSTAR_DIR="$SCRIPT_DIR/fstar"

# Default: official release
SOURCE="--release"
VERSION="v2026.04.17"

if [[ "${1:-}" == "--nightly" ]]; then
  SOURCE="--nightly"
  VERSION=""
  shift
fi

red()   { printf '\033[1;31m%s\033[0m\n' "$*"; }
green() { printf '\033[1;32m%s\033[0m\n' "$*"; }
info()  { printf '\033[1;34m=> %s\033[0m\n' "$*"; }

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
  info "Remove fstar/ directory to force reinstall."
else
  info "Installing F* to $FSTAR_DIR ..."
  VERSION_FLAG=""
  if [ -n "$VERSION" ]; then
    VERSION_FLAG="--version $VERSION"
  fi
  curl -fsSL https://aka.ms/install-fstar | bash -s -- \
    $SOURCE $VERSION_FLAG \
    --dest "$FSTAR_DIR" \
    --no-link

  if [ ! -x "$FSTAR_DIR/bin/fstar.exe" ]; then
    red "Install failed — $FSTAR_DIR/bin/fstar.exe not found."
    exit 1
  fi
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

green "F* toolchain ready."
"$FSTAR_DIR/bin/fstar.exe" --version
echo
green "Run 'make' to verify all modules."
