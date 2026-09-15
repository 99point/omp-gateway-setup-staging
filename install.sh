#!/usr/bin/env bash
# Installs or updates the genesis CLI. Rendered from cli/install.sh.in when the
# installer is published: the release commit and both SHA-256 values are pinned
# there, so this file only ever installs the exact bytes it was published with.
# Usage: curl -fsSL https://genesis.99point.co/install | bash
# Re-running the same line updates in place; genesis --update does the same.
set +x
set -euo pipefail

RELEASE_COMMIT='e5acab8d6bde85d8bd92c73e52eed64e973b8d58'
GENESIS_SHA256='4bbfc498509347413f719e2485e435710d5c18b6931c64e8cb0941cf2e0e3491'
SETUP_SHA256='bacfe4f6e890d6cf5a5bda80d155ca33f1cfe0f695ae991a3029fe37e109f791'
# GENESIS_SOURCE overrides the download base for mirrors and local checks;
# GENESIS_INSTALL_URL is the publisher `genesis update` re-fetches this script from.
source_base="${GENESIS_SOURCE:-https://raw.githubusercontent.com/99point/omp-gateway-setup-staging/e5acab8d6bde85d8bd92c73e52eed64e973b8d58}"
install_url="${GENESIS_INSTALL_URL:-https://raw.githubusercontent.com/99point/omp-gateway-setup-staging/staging/install.sh}"
share="${HOME}/.local/share/genesis"
bin_dir="${HOME}/.local/bin"

# Read from the terminal, never curl's stdin. Discard keys entered during the
# download before offering the result's acknowledgement (Bash 3.2 / macOS).
hold_result() {
  [[ -z "${GENESIS_NO_LAUNCH:-}" && -t 1 ]] || return 1
  { exec 9<>/dev/tty; } 2>/dev/null || return 1
  local ignored
  if command -v node >/dev/null 2>&1; then
    node -e '
      const fs = require("node:fs"), tty = require("node:tty");
      const fd = fs.openSync("/dev/tty", fs.constants.O_RDWR | fs.constants.O_NONBLOCK);
      const input = new tty.ReadStream(fd);
      input.setRawMode(true);
      try {
        const bytes = Buffer.alloc(256);
        while (fs.readSync(fd, bytes, 0, bytes.length, null) > 0) {}
      } catch (error) { if (error.code !== "EAGAIN") throw error; }
      finally { input.setRawMode(false); input.destroy(); }
    '
  fi
  printf '%s\n' "$1"
  IFS= read -r ignored <&9
}
fail() {
  printf 'genesis install failed: %s\n' "$*" >&2
  hold_result 'Press Enter to exit' || true
  exit 1
}
sha256_file() {
  local output
  if command -v sha256sum >/dev/null 2>&1; then output="$(sha256sum "$1")"
  elif command -v shasum >/dev/null 2>&1; then output="$(shasum -a 256 "$1")"
  else fail 'sha256sum or shasum is required to verify the download'; fi
  printf '%s\n' "${output%% *}"
}
download() {
  printf 'Downloading %s\n' "${1##*/}"
  local proto='=https'
  [[ "${source_base}" != http://* ]] || proto='=http,https'
  curl --fail --location --silent --show-error --proto "${proto}" --proto-redir "${proto}" --tlsv1.2 \
    --connect-timeout 15 --max-time 120 --output "$2" "$1" || fail "could not download $1"
}

printf 'Checking install requirements\n'
command -v curl >/dev/null 2>&1 || fail 'curl is required'
command -v node >/dev/null 2>&1 || fail 'Node.js 18 or newer is required (https://nodejs.org); install it and rerun'
node_major="$(node -p 'process.versions.node.split(".")[0]' 2>/dev/null || printf 0)"
[[ "${node_major}" =~ ^[0-9]+$ ]] && (( node_major >= 18 )) || fail "Node.js 18 or newer is required (found $(node --version 2>/dev/null || printf 'an unusable node'))"
[[ "${HOME}" == /* ]] || fail 'HOME must be an absolute path'
for target in "${share}" "${bin_dir}"; do
  [[ ! -L "${target}" ]] || fail "${target} must not be a symlink"
done

umask 077
# Downloads land in a private scratch directory inside ~/.local/share/genesis
# and the wrapper in a private file inside ~/.local/bin: each final mv below
# stays on its destination's filesystem, so it is an atomic rename, and no
# file passes through /tmp.
mkdir -p "${share}" "${bin_dir}"
chmod 0755 "${share}" "${bin_dir}"
scratch="$(mktemp -d "${share}/.install.XXXXXXXX")"
trap 'rm -rf "${scratch}"' EXIT
download "${source_base}/genesis.mjs" "${scratch}/genesis.mjs"
download "${source_base}/agent-auth-setup.sh" "${scratch}/agent-auth-setup.sh"
printf 'Verifying downloaded files\n'
[[ "$(sha256_file "${scratch}/genesis.mjs")" == "${GENESIS_SHA256}" ]] || fail "checksum mismatch for genesis.mjs (expected ${GENESIS_SHA256})"
[[ "$(sha256_file "${scratch}/agent-auth-setup.sh")" == "${SETUP_SHA256}" ]] || fail "checksum mismatch for agent-auth-setup.sh (expected ${SETUP_SHA256})"
node --check "${scratch}/genesis.mjs" || fail 'the downloaded genesis.mjs does not parse with this Node.js'

previous=''
if [[ -f "${share}/release.json" ]]; then
  previous="$(node -e 'try { process.stdout.write(String(JSON.parse(require("fs").readFileSync(process.argv[1], "utf8")).commit ?? "")); } catch {}' "${share}/release.json" 2>/dev/null || true)"
fi
printf 'Installing Genesis\n'
chmod 0644 "${scratch}/genesis.mjs"
chmod 0755 "${scratch}/agent-auth-setup.sh"
printf '{\n  "commit": "%s",\n  "installedAt": "%s",\n  "installUrl": "%s"\n}\n' \
  "${RELEASE_COMMIT}" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "${install_url}" > "${scratch}/release.json"
chmod 0644 "${scratch}/release.json"
staged_wrapper="$(mktemp "${bin_dir}/.genesis.XXXXXXXX")"
trap 'rm -rf "${scratch}" "${staged_wrapper}"' EXIT
printf '#!/usr/bin/env bash\nexec node %s "$@"\n' "'${share//\'/\'\\\'\'}/genesis.mjs'" > "${staged_wrapper}"
chmod 0755 "${staged_wrapper}"
# Each file lands by rename: the destination never holds a half-written file.
mv -f "${scratch}/agent-auth-setup.sh" "${share}/agent-auth-setup.sh"
mv -f "${scratch}/genesis.mjs" "${share}/genesis.mjs"
mv -f "${scratch}/release.json" "${share}/release.json"
mv -f "${staged_wrapper}" "${bin_dir}/genesis"

if [[ -z "${previous}" ]]; then verb='installed'
elif [[ "${previous}" == "${RELEASE_COMMIT}" ]]; then verb='already current'
else verb='updated'; fi
printf 'genesis %s %s (%s)\n' "${RELEASE_COMMIT:0:12}" "${verb}" "${share/#${HOME}/\~}"
case ":${PATH}:" in
  *":${bin_dir}:"*) ;;
  *) printf 'Add it to PATH: export PATH="%s:$PATH"\n' "${bin_dir/#${HOME}/\$HOME}" ;;
esac

# curl | bash leaves stdin on the pipe; the setup walkthrough (prod gateway
# URL and key, then the installed clients) runs only when a terminal is
# attached and the caller (genesis update) has not asked it to stay quiet.
# exec replaces this shell without running the EXIT trap, so cleanup goes first.
if hold_result 'Press Enter to set up Genesis, or Ctrl-C to exit'; then
  exec 9>&-
  rm -rf "${scratch}" "${staged_wrapper}"
  trap - EXIT
  exec node "${share}/genesis.mjs" setup </dev/tty
fi
