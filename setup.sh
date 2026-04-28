#!/usr/bin/env bash
# setup.sh — Build F* toolchain from source for pulse-verified-gc
#
# Usage:
#   ./setup.sh              Clone & build F* from fstar2 branch (default)
#   ./setup.sh --update     Pull latest changes and rebuild
#   ./setup.sh --release    Install binary release instead (faster, ~2 min)
#   ./setup.sh --nightly    Install latest nightly binary instead
#
# Prerequisites (source build): git, make, opam, OCaml >= 4.14, Z3
# Prerequisites (binary):       curl, bash
#
# Result: fstar/ directory with bin/fstar.exe, karamel/krml, etc.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
FSTAR_DIR="$SCRIPT_DIR/fstar"
FSTAR_REPO="https://github.com/FStarLang/FStar.git"
FSTAR_BRANCH="master"
JOBS="${JOBS:-$(nproc 2>/dev/null || echo 4)}"

MODE="source"  # default: build from source

while [[ $# -gt 0 ]]; do
  case "$1" in
    --update)  MODE="update"; shift ;;
    --release) MODE="release"; shift ;;
    --nightly) MODE="nightly"; shift ;;
    *) echo "Unknown option: $1"; exit 1 ;;
  esac
done

red()   { printf '\033[1;31m%s\033[0m\n' "$*"; }
green() { printf '\033[1;32m%s\033[0m\n' "$*"; }
info()  { printf '\033[1;34m=> %s\033[0m\n' "$*"; }

# ── Binary install (--release / --nightly) ──────────────────────────────

install_binary() {
  local flags="$1"
  for cmd in curl bash; do
    if ! command -v "$cmd" &>/dev/null; then
      red "Missing prerequisite: $cmd"
      exit 1
    fi
  done

  if [ -x "$FSTAR_DIR/bin/fstar.exe" ]; then
    INSTALLED=$("$FSTAR_DIR/bin/fstar.exe" --version 2>/dev/null | head -1 || true)
    info "F* already installed: $INSTALLED"
    info "Remove fstar/ directory to force reinstall."
  else
    info "Installing F* binary to $FSTAR_DIR ..."
    curl -fsSL https://aka.ms/install-fstar | bash -s -- \
      $flags --dest "$FSTAR_DIR" --no-link

    if [ ! -x "$FSTAR_DIR/bin/fstar.exe" ]; then
      red "Install failed — $FSTAR_DIR/bin/fstar.exe not found."
      exit 1
    fi

    # Create karamel/ compatibility layout for binary installs
    local compat="$FSTAR_DIR/karamel"
    if [ ! -L "$compat/krml" ]; then
      info "Setting up KaRaMeL compatibility layout..."
      rm -rf "$compat"
      mkdir -p "$compat"
      ln -sf ../bin/krml       "$compat/krml"
      ln -sf ../include/krml   "$compat/include"
      ln -sf ../lib/krml       "$compat/krmllib"
    fi
  fi
}

# ── Source build (default) ──────────────────────────────────────────────

check_source_prereqs() {
  local missing=()
  for cmd in git make opam; do
    if ! command -v "$cmd" &>/dev/null; then
      missing+=("$cmd")
    fi
  done
  if [ ${#missing[@]} -gt 0 ]; then
    red "Missing prerequisites: ${missing[*]}"
    echo "Install them and re-run. For opam: https://opam.ocaml.org/doc/Install.html"
    exit 1
  fi

  # Check OCaml is available via opam
  if ! opam exec -- ocamlfind list &>/dev/null 2>&1; then
    red "OCaml toolchain not found via opam."
    echo "Run: opam init --compiler=ocaml.5.3.0 --disable-sandboxing && eval \$(opam env)"
    exit 1
  fi

  # Check Z3 is available
  if ! command -v z3 &>/dev/null && ! command -v z3-4.13.3 &>/dev/null; then
    red "Z3 SMT solver not found."
    echo "After cloning, run: bash fstar/.scripts/get_fstar_z3.sh ~/.local/bin"
    echo "Then: export PATH=~/.local/bin:\$PATH"
    exit 1
  fi
}

build_from_source() {
  check_source_prereqs

  if [ -d "$FSTAR_DIR/.git" ]; then
    info "F* source tree already exists at $FSTAR_DIR"
    if [ -x "$FSTAR_DIR/bin/fstar.exe" ]; then
      INSTALLED=$("$FSTAR_DIR/bin/fstar.exe" --version 2>/dev/null | head -1 || true)
      info "Current version: $INSTALLED"
      info "Run './setup.sh --update' to pull and rebuild."
      green "F* toolchain ready."
      "$FSTAR_DIR/bin/fstar.exe" --version
      return 0
    fi
    info "Source tree exists but not yet built. Building..."
  else
    info "Cloning F* ($FSTAR_BRANCH branch) into $FSTAR_DIR ..."
    git clone --branch "$FSTAR_BRANCH" "$FSTAR_REPO" "$FSTAR_DIR"
  fi

  cd "$FSTAR_DIR"
  git submodule update --init karamel

  info "Installing OCaml dependencies..."
  opam install --deps-only ./fstar.opam --yes

  info "Building F* + Pulse (stage 3, -j$JOBS) — this takes 15–30 min ..."
  make -j"$JOBS" 3

  info "Building KaRaMeL..."
  make karamel

  if [ ! -x "$FSTAR_DIR/bin/fstar.exe" ]; then
    red "Build failed — $FSTAR_DIR/bin/fstar.exe not found."
    exit 1
  fi
}

update_source() {
  check_source_prereqs

  if [ ! -d "$FSTAR_DIR/.git" ]; then
    red "$FSTAR_DIR is not a git repository. Run './setup.sh' first."
    exit 1
  fi

  cd "$FSTAR_DIR"
  info "Pulling latest changes..."
  git fetch origin "$FSTAR_BRANCH"
  git checkout "$FSTAR_BRANCH"
  git pull --ff-only

  git submodule update --init karamel

  info "Installing OCaml dependencies..."
  opam install --deps-only ./fstar.opam --yes

  info "Rebuilding F* + Pulse (stage 3, -j$JOBS) ..."
  make -j"$JOBS" 3

  info "Rebuilding KaRaMeL..."
  make karamel
}

# ── Main ────────────────────────────────────────────────────────────────

case "$MODE" in
  source)
    build_from_source
    ;;
  update)
    update_source
    ;;
  release)
    install_binary "--release"
    ;;
  nightly)
    install_binary "--nightly"
    ;;
esac

green "F* toolchain ready."
"$FSTAR_DIR/bin/fstar.exe" --version
echo
green "Run 'make' to verify all modules."
