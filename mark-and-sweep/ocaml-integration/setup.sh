#!/bin/bash
# setup.sh — Set up OCaml 4.14 runtimes for benchmarking.
#
# Creates two OCaml builds:
#   ocaml-4.14-unchanged/  — stock OCaml (for reference/comparison)
#   ocaml-4.14-verified-gc/ — patched to use our verified GC
#
# Prerequisites: gcc, make, git
# Usage: ./setup.sh

set -euo pipefail
cd "$(dirname "$0")"

OCAML_VERSION="4.14"
OCAML_TAG="4.14.2"
OCAML_REPO="https://github.com/ocaml/ocaml.git"

# ---- Clone OCaml if not present ----

clone_ocaml() {
    local dir=$1
    if [ ! -d "$dir" ]; then
        echo "=== Cloning OCaml $OCAML_TAG into $dir ==="
        git clone --branch "$OCAML_TAG" --depth 1 "$OCAML_REPO" "$dir"
    else
        echo "=== $dir already exists, skipping clone ==="
    fi
}

# ---- Build unchanged OCaml ----

build_unchanged() {
    local dir="ocaml-4.14-unchanged"
    clone_ocaml "$dir"
    echo "=== Building unchanged OCaml runtime ==="
    cd "$dir"
    if [ ! -f Makefile.config ]; then
        ./configure --prefix="$(pwd)/_install" --disable-naked-pointers
    fi
    make -j8
    make install
    cd ..
    echo "=== Unchanged OCaml ready ==="
}

# ---- Build verified-GC OCaml ----

build_verified_gc() {
    local dir="ocaml-4.14-verified-gc"
    clone_ocaml "$dir"

    # Copy our verified GC into the runtime
    echo "=== Copying verified GC into $dir/runtime/ ==="
    rm -rf "$dir/runtime/verified_gc"
    cp -r verified_gc "$dir/runtime/"

    # Apply runtime patch
    echo "=== Applying runtime patch ==="
    cd "$dir"
    if ! git diff --quiet; then
        echo "    (working tree already modified, resetting first)"
        git checkout -- .
    fi
    git apply ../patches/runtime.patch
    
    # Build just the runtime (we only need ocamlrun for bytecode)
    if [ ! -f Makefile.config ]; then
        ./configure --disable-naked-pointers
    fi
    echo "=== Building patched OCaml runtime ==="
    make -C runtime -j8 ocamlrun
    cd ..
    echo "=== Verified-GC OCaml runtime ready ==="
}

# ---- Main ----

echo "====================================="
echo " OCaml 4.14 Integration Setup"
echo "====================================="
echo

build_unchanged
echo
build_verified_gc

echo
echo "====================================="
echo " Setup complete!"
echo
echo " Unchanged OCaml compiler:"
echo "   ocaml-4.14-unchanged/_install/bin/ocamlc"
echo
echo " Verified-GC runtime:"
echo "   ocaml-4.14-verified-gc/runtime/ocamlrun"
echo
echo " To run benchmarks:"
echo "   cd tests && make test"
echo "====================================="
