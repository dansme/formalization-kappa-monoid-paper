FROM mcr.microsoft.com/devcontainers/base:debian-12

# Build dependencies for Lean/Lake. Nothing else: no iptables/ipset, since
# this container runs no firewall script.
RUN apt-get update && apt-get install -y --no-install-recommends \
        curl git ca-certificates build-essential \
    && rm -rf /var/lib/apt/lists/*

USER vscode
ENV ELAN_HOME=/home/vscode/.elan
ENV PATH=/home/vscode/.elan/bin:${PATH}

# Set this to match your project's lean-toolchain file so the agent never
# has to fetch a toolchain at runtime. If it doesn't match, elan will
# download the right one on first build anyway.
ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.33.0
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain "${LEAN_TOOLCHAIN}" \
    && elan --version \
    && lake --version

# Mathlib's build cache lands here.
RUN mkdir -p /home/vscode/.cache/mathlib
