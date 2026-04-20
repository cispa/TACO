#!/bin/bash
# Convenience script to package an artifact for TACO, designed to be run with 
# podman

# Strict mode with error reporting
set -euo pipefail
trap 's=$?; echo "$0: Error on line "$LINENO": $BASH_COMMAND"; exit $s' ERR
IFS=$'\n\t'

# Remove all unnecessary stuff first
# Remove build output
cargo clean
# Remove doc build
rm -rf docs/_build

mkdir artifact

# Artifact README
cp artifact-evaluation/artifact-evaluation.md artifact/README.md
# LICENSE
cp ./LICENSE artifact/LICENSE

# Paper pdf
#cp artifact-evaluation/paper.pdf artifact/paper.pdf
# Table 2 ods
cp artifact-evaluation/table2.ods artifact/table2.ods

# Create source directory
mkdir artifact/src

# Copy the source code
cp -R .config artifact/src
cp -R artifact-evaluation artifact/src
cp -R benchmarks artifact/src
cp -R crates artifact/src
cp -R docs artifact/src
cp -R examples artifact/src
cp -R scripts artifact/src
cp .dockerignore artifact/src
cp about.toml artifact/src
cp Cargo.toml artifact/src
cp Dockerfile artifact/src
cp LICENSE artifact/src
cp README.md artifact/src

# Build the TACO AE container
podman build -t taco -f artifact-evaluation/AE-Dockerfile .
podman save -o ./artifact/taco.tar taco

# Build the ByMC AE container
podman build -t bymc -f artifact-evaluation/ByMC-Dockerfile .
podman save -o ./artifact/bymc.tar bymc


# bundle the artifact
zip -r artifact.zip artifact/*

# remove build artifacts
rm -rf artifact
