#!/usr/bin/env bash
# Launch VS Code for this dev container with a scrubbed environment, so the
# Dev Containers extension has nothing of the host's to forward into it.
#
# RUN THIS ON THE HOST, FROM A COPY OUTSIDE THE WORKSPACE:
#     install -m 755 .devcontainer/launch-vscode.sh ~/.local/bin/code-kappa
#     code-kappa /path/to/kappa_formalized
# The workspace is writable from inside the container, so a copy that lives in
# it is a script the container could have edited.  Diff the repo copy against
# yours before updating.
#
# What it does:
#  * Starts VS Code with `env -i` and an allowlist of variables: no SSH agent,
#    no GPG_AGENT_INFO, no API tokens, nothing inherited from a VS Code
#    terminal.
#  * Uses a dedicated profile (--user-data-dir/--extensions-dir).  This is
#    essential: with the default profile, `code` hands the request to an
#    already-running VS Code, which keeps the environment it started with.
#  * Points GNUPGHOME at an empty directory, so the GPG agent the extension
#    forwards (if any) holds no keys.
#  * In a Wayland session, runs VS Code as a native Wayland client with DISPLAY
#    unset, so there is no X11 display to forward.  Under X11 that is
#    impossible, and the script warns.
#  * Enforces Dev Containers settings in the dedicated profile: no copying of
#    ~/.gitconfig, no git credential helper, no Wayland socket mount.
#  * Opens the folder directly in its container.
#
# Environment knobs: CODE (the VS Code binary, default `code`), VSCODE_SANDBOX_DIR
# (profile location), KEEP_X11=1 (keep DISPLAY even under Wayland).

set -euo pipefail

folder=$(realpath "${1:-.}")
[[ -f "$folder/.devcontainer/devcontainer.json" ]] ||
  { echo "error: $folder has no .devcontainer/devcontainer.json" >&2; exit 1; }

code_bin=$(command -v "${CODE:-code}") ||
  { echo "error: VS Code binary '${CODE:-code}' not found" >&2; exit 1; }

base=${VSCODE_SANDBOX_DIR:-${XDG_DATA_HOME:-$HOME/.local/share}/vscode-sandbox}
data="$base/data"
exts="$base/extensions"
gnupg="$base/empty-gnupg"
mkdir -p "$data/User" "$exts"
mkdir -p -m 700 "$gnupg"

# --- Settings enforced in the dedicated profile ---------------------------
# Merged into the profile's settings.json on every launch; other keys you set
# in the UI are kept.  Unknown keys are ignored by VS Code.
enforced='{
  "dev.containers.dockerPath": "podman",
  "dev.containers.copyGitConfig": false,
  "dev.containers.gitCredentialHelperConfigLocation": "none",
  "dev.containers.dockerCredentialHelper": false,
  "dev.containers.mountWaylandSocket": false,
  "github.gitAuthentication": false,
  "git.terminalAuthentication": false,
  "telemetry.telemetryLevel": "off"
}'
settings="$data/User/settings.json"
if command -v python3 >/dev/null; then
  python3 - "$settings" "$enforced" <<'PY'
import json, re, sys
path, enforced = sys.argv[1], json.loads(sys.argv[2])
try:
    text = open(path).read()
    # settings.json is JSONC: drop // line comments and trailing commas.
    text = re.sub(r'^\s*//.*$', '', text, flags=re.M)
    text = re.sub(r',(\s*[}\]])', r'\1', text)
    current = json.loads(text) if text.strip() else {}
except FileNotFoundError:
    current = {}
current.update(enforced)
with open(path, 'w') as f:
    json.dump(current, f, indent=2)
    f.write('\n')
PY
else
  echo "warning: no python3; overwriting $settings with the enforced settings" >&2
  printf '%s\n' "$enforced" > "$settings"
fi

# --- Allowlisted environment ----------------------------------------------
keep=(HOME USER LOGNAME PATH SHELL LANG LANGUAGE TZ TERM
      XDG_RUNTIME_DIR XDG_DATA_DIRS XDG_CONFIG_DIRS XDG_CONFIG_HOME XDG_DATA_HOME
      XDG_CACHE_HOME XDG_STATE_HOME XDG_CURRENT_DESKTOP XDG_SESSION_TYPE
      XDG_SESSION_DESKTOP DESKTOP_SESSION DBUS_SESSION_BUS_ADDRESS
      GTK_THEME XCURSOR_THEME XCURSOR_SIZE
      DOCKER_HOST CONTAINER_HOST CONTAINERS_CONF CONTAINERS_STORAGE_CONF)
extra_args=()
if [[ -n "${WAYLAND_DISPLAY:-}" && "${KEEP_X11:-0}" != 1 ]]; then
  keep+=(WAYLAND_DISPLAY)
  extra_args+=(--ozone-platform=wayland)
elif [[ -n "${DISPLAY:-}" ]]; then
  keep+=(DISPLAY XAUTHORITY)
  echo "warning: X11 session: the container will get access to your display" \
       "(keystrokes, screenshots).  Use a Wayland session to avoid this." >&2
fi

envargs=()
for v in "${keep[@]}"; do
  [[ -n "${!v:-}" ]] && envargs+=("$v=${!v}")
done
while IFS='=' read -r v _; do               # LC_* locale variables
  [[ $v == LC_* ]] && envargs+=("$v=${!v}")
done < <(env)
envargs+=("GNUPGHOME=$gnupg" "SSH_AUTH_SOCK=" "GPG_AGENT_INFO=")

run_code() {
  env -i "${envargs[@]}" "$code_bin" --user-data-dir "$data" \
    --extensions-dir "$exts" "${extra_args[@]}" "$@"
}

# The dedicated profile starts empty: install the Dev Containers extension.
if ! compgen -G "$exts/ms-vscode-remote.remote-containers-*" >/dev/null; then
  run_code --install-extension ms-vscode-remote.remote-containers
fi

# Open the folder straight in its dev container: the authority is the host
# path, hex-encoded; the path is devcontainer.json's workspaceFolder.
hex=$(printf '%s' "$folder" | od -An -v -tx1 | tr -d ' \n')
run_code --folder-uri \
  "vscode-remote://dev-container+$hex/workspaces/$(basename "$folder")"
