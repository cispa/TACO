FROM rust:1.94-slim AS BUILD

RUN apt update && apt-get install -y --no-install-recommends\
        # CUDD build dependencies
        build-essential autoconf automake libtool curl

WORKDIR /taco

COPY ./ ./

# Build the release version of the binary
RUN cargo build --release --all-features --bin taco-cli
# SBOM
RUN cargo install cargo-sbom 
RUN cargo sbom > sbom.spdx.json
# LICENSES
RUN cargo install cargo-about
RUN cargo about generate --workspace ./.config/about.hbs > third-party-licenses.html


FROM quay.io/fedora/fedora-minimal:43 AS RUN

LABEL org.opencontainers.image.licenses="Apache 2.0"
LABEL org.opencontainers.image.authors="Tom Baumeister, Paul Eichler, Peter Gastauer"
LABEL org.opencontainers.image.source="https://github.com/cispa/TACO"
LABEL org.opencontainers.image.title="TACO Toolsuite"
LABEL org.opencontainers.image.description="Threshold Automata for COnsensus Model Checker"

# Install dependencies
RUN microdnf install -y \
        # SMT solvers
        z3 cvc5 \
        # Graphviz for visualization
        graphviz \
        # GNU time, awk, and python for benchmarking
        time gawk python3 \
        && microdnf clean all

# Create a non-root user
RUN useradd -M taco-user
USER taco-user

# Create working directory
WORKDIR /taco

# Copy built binary
COPY --from=BUILD /taco/target/release/taco-cli /taco/taco-cli
# Add to path
ENV PATH="/taco:${PATH}"

COPY --from=BUILD /taco/LICENSE /taco/LICENSE
COPY --from=BUILD /taco/README.md /taco/README.md
COPY --from=BUILD /taco/benchmarks /taco/benchmarks
COPY --from=BUILD /taco/examples /taco/examples
COPY --from=BUILD /taco/sbom.spdx.json /taco/sbom.spdx.json
COPY --from=BUILD /taco/third-party-licenses.html /taco/third-party-licenses.html

# Add benchmark script
RUN mkdir scripts
COPY --from=BUILD /taco/scripts/bench-taco.sh /taco/scripts/bench-taco.sh
RUN ln -s ./scripts/bench-taco.sh benchmark-taco

ENTRYPOINT [ "/bin/bash" ]
