#!/usr/bin/env bash
# The separate Staging CLI is retired. This installs the one Genesis CLI.
# The selected gateway and saved logins stay unchanged.
set +x
set -euo pipefail
unset GENESIS_SOURCE GENESIS_INSTALL_URL
umask 077
scratch="$(mktemp -d "${TMPDIR:-/tmp}/genesis-install.XXXXXXXX")"
trap 'rm -rf "${scratch}"' EXIT
curl --fail --location --silent --show-error --proto '=https' --proto-redir '=https' \
  --tlsv1.2 --connect-timeout 15 --max-time 120 --output "${scratch}/install.sh" \
  https://raw.githubusercontent.com/99point/omp-gateway-setup/main/install.sh
bash "${scratch}/install.sh" "$@"
