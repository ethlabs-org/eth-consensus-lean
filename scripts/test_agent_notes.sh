#!/usr/bin/env bash
# Self-test of write_agent_notes in .agents/setup (the orb-only notes block in ~/.config/amp/AGENTS.md):
# the block is refreshed, text before and after it is kept, a block written before the end
# marker existed (the legacy form) is migrated without touching what follows it, and reruns are
# byte-identical. Runs the function from .agents/setup itself, in scratch homes.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
eval "$(sed -n '/^write_agent_notes()/,/^}/p' "$here/.agents/setup")"
marker="<!-- consensus-lean orb notes -->"
end="<!-- /consensus-lean orb notes -->"
bad=0
check() { if eval "$2"; then echo "  ok: $1"; else echo "  WRONG: $1"; bad=$((bad + 1)); fi; }
count() { grep -cFx -- "$1" "$2" || true; }
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT

# 1. fresh file
h="$scratch/fresh"; mkdir -p "$h"; HOME="$h" write_agent_notes; f="$h/.config/amp/AGENTS.md"
check "fresh: one block with both markers" '[[ $(count "$marker" "$f") == 1 && $(count "$end" "$f") == 1 ]]'

# 2. user text before and after a bounded block, rerun three times
h="$scratch/bounded"; mkdir -p "$h/.config/amp"; f="$h/.config/amp/AGENTS.md"
echo "# user notes before" >"$f"; HOME="$h" write_agent_notes; echo "- user notes after" >>"$f"
HOME="$h" write_agent_notes; cp "$f" "$scratch/once"; HOME="$h" write_agent_notes; HOME="$h" write_agent_notes
check "bounded: text before kept" '[[ $(count "# user notes before" "$f") == 1 ]]'
check "bounded: text after kept" '[[ $(count "- user notes after" "$f") == 1 ]]'
check "bounded: one block" '[[ $(count "$marker" "$f") == 1 && $(count "$end" "$f") == 1 ]]'
check "bounded: reruns byte-identical" 'cmp -s "$scratch/once" "$f"'

# 3. legacy block (no end marker, as main wrote it before) followed by other text
h="$scratch/legacy"; mkdir -p "$h/.config/amp"; f="$h/.config/amp/AGENTS.md"
{
  echo "# user notes before"; echo; echo "$marker"; echo "# consensus-lean in an Amp orb"; echo
  echo "- old note"; echo "- Kernel replay is memory-heavy (about 3.3 GB per leanchecker process); keep parallel runs within the"
  echo "  orb's memory (\`free -g\`)."; echo "- another project's note after the block"
} >"$f"
HOME="$h" write_agent_notes
check "legacy: text before kept" '[[ $(count "# user notes before" "$f") == 1 ]]'
check "legacy: text after the old block kept" '[[ $(count "- another project'"'"'s note after the block" "$f") == 1 ]]'
check "legacy: old block replaced" '[[ $(count "- old note" "$f") == 0 && $(count "$marker" "$f") == 1 && $(count "$end" "$f") == 1 ]]'
cp "$f" "$scratch/once"; HOME="$h" write_agent_notes
check "legacy: rerun byte-identical" 'cmp -s "$scratch/once" "$f"'

# 4. a truncated/unknown block must not consume unrelated notes through EOF. A terminator
# before the start marker does not bound it either. Both attempts must preserve every byte.
for prefix in "" "$end" "  orb's memory (\`free -g\`)." "$marker"$'\n'"$end"; do
  h="$scratch/unterminated"; mkdir -p "$h/.config/amp"; f="$h/.config/amp/AGENTS.md"
  printf '%s\n%s\n%s\n%s\n' "$prefix" "$marker" "- edited or truncated note" "# unrelated user notes" >"$f"
  cp "$f" "$scratch/before"
  HOME="$h" write_agent_notes 2>"$scratch/warning"
  HOME="$h" write_agent_notes 2>>"$scratch/warning"
  check "unterminated: file unchanged" 'cmp -s "$scratch/before" "$f"'
  check "unterminated: warning emitted" 'grep -q "WARNING: unterminated" "$scratch/warning"'
done

echo "agent notes self-test: $([[ $bad == 0 ]] && echo passed || echo "FAILED ($bad)")"
exit $((bad > 0))
