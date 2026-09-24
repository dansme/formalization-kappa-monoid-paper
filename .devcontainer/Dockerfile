FROM mcr.microsoft.com/devcontainers/base:debian-12

# Build dependencies for Lean/Lake. Nothing else: no iptables/ipset, since
# this container runs no firewall script.
RUN apt-get update && apt-get install -y --no-install-recommends \
        curl git ca-certificates build-essential \
    && rm -rf /var/lib/apt/lists/*

USER vscode
ENV ELAN_HOME=/home/vscode/.elan
ENV PATH=/home/vscode/.local/bin:/home/vscode/.elan/bin:${PATH}

# Set this to match your project's lean-toolchain file so the agent never
# has to fetch a toolchain at runtime. If it doesn't match, elan will
# download the right one on first build anyway.
ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.33.0
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain "${LEAN_TOOLCHAIN}" \
    && elan --version \
    && lake --version

# uv/uvx for the lean-lsp MCP server (.mcp.json runs `uvx lean-lsp-mcp`).
# `uv tool install` bakes the server and its Python into the image, so it
# starts without a download; sudo/apt are unavailable at runtime.
RUN curl -LsSf https://astral.sh/uv/install.sh | env UV_NO_MODIFY_PATH=1 sh \
    && uv tool install lean-lsp-mcp \
    && uvx --version

# Mathlib's build cache lands here.
RUN mkdir -p /home/vscode/.cache/mathlib
