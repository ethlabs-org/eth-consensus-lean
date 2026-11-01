#!/usr/bin/env bash
# Run a CI command on a checked-out head in a bubblewrap sandbox (orb-ci.sh; owner, 2026-11-01): the box checks the
# code of PR heads and of every push to main, so that code runs without the network, the agent's credentials or the
# rest of the machine.
#   scripts/ci-sandbox.sh <worktree> -- <cmd...>   run <cmd> in <worktree>
#   scripts/ci-sandbox.sh --self-test             the isolation probes below, on throwaway directories
# Inside: no network (and no other shared namespace); an empty $HOME (tmpfs) holding only $HOME/.elan read-only; the
# worktree writable but its .lake/packages read-only (they are hard links of the watcher's packages, so a write would
# change every later check); git read-only: the main repository's .git with a minimal config (no remotes,
# credentials or URLs), the worktree's admin dir and its .git link (so the head cannot point the git that the watcher
# runs on this worktree afterwards at a config of its own); $RUN_DIR writable; /usr, /etc and the libraries read-only; a fresh
# /tmp. The toolchain is found as outside: PATH is the caller's (behind $HOME/.elan/bin), and the toolchain that
# `lake` and `lean` resolve to is bound read-only wherever it lives (the box uses /opt/tools/bin). The environment
# is cleared but for PATH, HOME, CI, RUN_DIR, TMPDIR, LANG and LAKE_*, with LAKE_ARTIFACT_CACHE=false: the shared
# artifact cache is outside the sandbox, and with it on Lake rewrites the (read-only) packages' build outputs as links
# into its cache (EROFS on the box, 7c9359c). Reverted in 6909494; this is the fix. Without bwrap, or if
# the sandbox cannot start, the command does not run (exit 1): there is no unsandboxed fallback.
# Run it from the watcher's own copy, never from the worktree under check.
set -euo pipefail

run() {
  local wt="$1"; shift
  [[ "${1:-}" == -- ]] && shift
  command -v bwrap >/dev/null || { echo "ci-sandbox: no bwrap: refusing to run unsandboxed" >&2; return 1; }
  wt="$(cd "$wt" && pwd -P)"
  local gitdir common home="${HOME:?}" run_dir="${RUN_DIR:-}" cfg args=() v
  gitdir="$(git -C "$wt" rev-parse --absolute-git-dir)"
  common="$(cd "$(git -C "$wt" rev-parse --git-common-dir)" && pwd -P)"
  cfg="$(mktemp)"
  trap 'rm -f "$cfg"' RETURN
  # The repository format only: no remotes, URLs, credentials, hooks or filters reach the sandbox.
  git config -f "$common/config" --get-regexp '^(core\.(repositoryformatversion|bare)|extensions\.)' |
    while read -r k val; do git config -f "$cfg" "$k" "$val"; done
  args=(--unshare-all --die-with-parent --new-session --clearenv
    --ro-bind /usr /usr --ro-bind /etc /etc
    --ro-bind-try /bin /bin --ro-bind-try /sbin /sbin --ro-bind-try /lib /lib --ro-bind-try /lib64 /lib64
    --ro-bind-try /lib32 /lib32 --ro-bind-try /opt /opt
    --proc /proc --dev /dev --tmpfs /tmp
    --tmpfs "$home" --ro-bind-try "$home/.elan" "$home/.elan"
    --ro-bind "$common" "$common" --ro-bind "$cfg" "$common/config")
  args+=(--bind "$wt" "$wt" --ro-bind "$gitdir" "$gitdir")
  [[ ! -e "$wt/.git" ]] || args+=(--ro-bind "$wt/.git" "$wt/.git")
  [[ ! -d "$wt/.lake/packages" ]] || args+=(--ro-bind "$wt/.lake/packages" "$wt/.lake/packages")
  for v in lake lean; do  # the toolchain root of each tool: <root>/bin/<tool> after links
    v="$(command -v "$v" 2>/dev/null)" && v="$(readlink -f "$v")" && args+=(--ro-bind-try "${v%/bin/*}" "${v%/bin/*}")
  done
  [[ -z "$run_dir" ]] || { mkdir -p "$run_dir"; run_dir="$(cd "$run_dir" && pwd -P)"; args+=(--bind "$run_dir" "$run_dir"); }
  args+=(--setenv HOME "$home" --setenv PATH "$home/.elan/bin:${PATH:-/usr/bin:/bin}"
    --setenv TMPDIR /tmp --setenv LANG C.UTF-8 --setenv CI 1 --chdir "$wt")
  [[ -z "$run_dir" ]] || args+=(--setenv RUN_DIR "$run_dir")
  for v in $(compgen -e | grep '^LAKE_' || true); do args+=(--setenv "$v" "${!v}"); done
  args+=(--setenv LAKE_ARTIFACT_CACHE false)
  bwrap "${args[@]}" -- "$@"
}

# --- self-test: isolation probes on throwaway directories ------------------------------------------------------
self_test() {
  local script tmp fails=0 out
  script="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/$(basename "${BASH_SOURCE[0]}")"
  tmp="$(mktemp -d)"
  trap 'chmod -R u+w "$tmp" 2>/dev/null; rm -rf "$tmp"' RETURN
  mkdir -p "$tmp/home/.config/gh" "$tmp/home/.elan/bin" "$tmp/ci" "$tmp/run"
  echo "oauth_token: SECRET-gh" >"$tmp/home/.config/gh/hosts.yml"
  echo "SECRET-ci" >"$tmp/ci/state"
  git init -q -b main "$tmp/repo"
  git -C "$tmp/repo" -c user.email=t@t -c user.name=t -c commit.gpgsign=false commit -q --allow-empty -m base
  git -C "$tmp/repo" config remote.origin.url "https://x-access-token:SECRET-url@github.com/o/r.git"
  git -C "$tmp/repo" config http.extraheader "AUTHORIZATION: basic SECRET-header"
  git -C "$tmp/repo" worktree add -q --detach "$tmp/ci/wt"
  mkdir -p "$tmp/ci/wt/.lake/packages/dep"; echo olean >"$tmp/ci/wt/.lake/packages/dep/A.olean"
  probe() {  # probe <label> <expected: ok|denied> <shell command run inside>
    local label="$1" want="$2" rc=0
    out="$(HOME="${PROBE_HOME:-$tmp/home}" RUN_DIR="$tmp/run" GH_TOKEN=SECRET-env LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true \
      bash "$script" "$tmp/ci/wt" -- bash -c "$3" 2>&1)" || rc=$?
    if { [[ "$want" == ok ]] && ((rc == 0)); } || { [[ "$want" == denied ]] && ((rc != 0)); }; then
      [[ "$out" != *SECRET* ]] || { echo "  WRONG: $label leaked: $out"; fails=1; return; }
      echo "  ok ($want): $label"
    else
      echo "  WRONG (expected $want, exit $rc): $label"; sed 's/^/    /' <<<"$out"; fails=1
    fi
  }
  probe "the worktree is writable" ok 'echo x >new.txt && rm new.txt'
  probe "RUN_DIR is writable" ok 'echo x >"$RUN_DIR/out"'
  probe "git works in the worktree" ok 'git rev-parse HEAD >/dev/null && git status --porcelain >/dev/null'
  probe "LAKE_* passes through, the artifact cache off" ok '[[ "$LAKE_RESTORE_ARTIFACTS" == true && "$LAKE_ARTIFACT_CACHE" == false ]]'
  probe "no GH_TOKEN in the environment" denied '[[ -n "${GH_TOKEN:-}" ]] && echo "$GH_TOKEN"'
  probe "the gh credentials are hidden" denied "cat '$tmp/home/.config/gh/hosts.yml'"
  probe "the watcher state is hidden" denied "cat '$tmp/ci/state'"
  probe "the git config has no remote URL" denied 'git remote get-url origin'
  probe "the git config has no extra header" denied 'git config --get http.extraheader'
  probe "the packages are read-only" denied 'echo bad >.lake/packages/dep/A.olean'
  probe "the main repository is read-only" denied "touch '$tmp/repo/.git/objects/x'"
  probe "the worktree's .git link is read-only" denied 'echo "gitdir: /tmp/evil" >.git'
  probe "the worktree's admin dir is read-only" denied 'echo /tmp/evil >"$(git rev-parse --absolute-git-dir)/commondir"'
  probe "no network" denied 'python3 -c "import socket; socket.create_connection((\"1.1.1.1\", 53), 3)"'
  if command -v lean >/dev/null; then  # the real toolchain, wherever the caller's PATH finds it, with the real HOME
    cp "$(dirname "$script")/../lean-toolchain" "$tmp/ci/wt/" 2>/dev/null || true  # this repository's pin, for elan
    PROBE_HOME="$HOME" probe "the caller's lean and lake run inside" ok 'lean --version >/dev/null && lake --version >/dev/null'
  else echo "  (no lean on PATH: toolchain probe not run)"; fi
  [[ "$(cat "$tmp/ci/wt/.lake/packages/dep/A.olean")" == olean ]] || { echo "  WRONG: a package changed"; fails=1; }
  local rc=0
  out="$(PATH=/nonexistent /bin/bash "$script" "$tmp/ci/wt" -- true 2>&1)" || rc=$?
  if ((rc != 0)) && [[ "$out" == *"refusing to run unsandboxed"* ]]; then echo "  ok (denied): without bwrap, nothing runs"
  else echo "  WRONG: without bwrap: exit $rc: $out"; fails=1; fi
  return "$fails"
}

if [[ "${1:-}" == --self-test ]]; then
  self_test && echo "ci-sandbox self-test: all probes as expected" || { echo "ci-sandbox self-test: FAILED"; exit 1; }
else
  [[ $# -ge 2 ]] || { echo "usage: ci-sandbox.sh <worktree> -- <cmd...> | --self-test" >&2; exit 2; }
  run "$@"
fi
