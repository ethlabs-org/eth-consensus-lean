# Accepted inventory publication (private, report-only)

The fast watcher captures step 3c for each checked `main` / `main (re-check)` SHA.
PR and full-tier runs do not publish. CI verdicts and #63 rows are unchanged.
Reports live on the private coordination repository's isolated `ci-inventory` branch (`issues` in
`scripts/repos.toml`), not main,
Actions artifacts, a public endpoint, or expiring host run folders.

## Consumer contract, version 1

Fetch discovery server-side using authenticated `gh api`:

```
repos/ethlabs-org/consensus-lean-coordination/contents/latest.json?ref=ci-inventory
```

Decode the response's base64 `content`. Example discovery (placeholders):

```json
{
  "schema_version": 1,
  "commit": "<40-character source commit SHA>",
  "checked_at": "2026-10-31T17:31:46Z",
  "published_at": "2026-10-31T18:00:00+00:00",
  "availability": "available",
  "inventory_status": "incomplete",
  "payload_path": "commits/<source SHA>.json",
  "payload_api": "repos/ethlabs-org/consensus-lean-coordination/git/blobs/<immutable Git blob SHA>",
  "payload_sha256": "<SHA-256 of decoded payload bytes>"
}
```

Fetch `payload_api` using `gh api` and base64-decode its `content`. Blob identity
is **not** the source commit identity. Verify `payload_sha256`, envelope version,
full `commit` equality between discovery and payload, and equality to freshly
observed remote main before presenting it as current. Do not put credentials in
the generated dashboard, or fetch private GitHub data from the browser.

The payload is `{schema_version:1, commit, checked_at, ci_result, availability,
reason, inventory}`. `checked_at` is the check's start/observation UTC, not its
author time. `ci_result` is `passed` or `failed`, independent of inventory findings.
`availability:"available"` preserves the complete existing inventory schema 1,
including `status:"incomplete"` and all issues; `reason` is null. Missing, skipped,
invalid, ambiguous, or oversized output has `availability:"unavailable"`, a reason,
and **`inventory:null`**, never an empty list implying no debt. Tool errors already
represented as incomplete schema-1 findings remain available/incomplete findings.

`inventory.sorries[].ancestors` is **transitive proof-debt membership**, not direct
dependency edges. `mapped`, mapped `OPEN` rows, or absence from this inventory do
not mean proved. Missing, incomplete, unavailable, stale and pending data must not
be rendered as zero sorry or a successful proof status.

## Immutability, freshness and failures

`commits/<full SHA>.json` is first-record-wins, including an unavailable first
capture. A later successful recheck cannot silently replace it. Git blob URLs
are content-addressed; reports and latest are published in one atomic data-branch
commit. Normal main checks and rechecks may advance latest only when their exact
full source SHA equals freshly read remote main of the code repository (`code` in
`scripts/repos.toml`; the data branch is in `issues`). This includes an existing immutable
report, even if its original `checked_at` is older. Historical rechecks/retries still
publish their immutable report but never replace latest. Full runs do not publish.
Main is checked again immediately before updating the data ref; a changed head
leaves the upload pending for retry. Concurrent data-ref writes use non-force
fast-forward protection. GitHub cannot atomically compare main and update a different
ref: main can move just after the final read, so consumers must still compare SHAs.

Publication failure leaves latest unchanged. Latest alone cannot distinguish an
upload outage from a pending check: show unknown/pending/stale, retaining the last
valid snapshot only with an explicit stale label. A 404 before first publication
means unavailable discovery, not no debt. Normal polling can coalesce main heads;
only checked heads have records. A force push can revisit an earlier SHA, whose
immutable record remains the original capture.

The publisher copies JSON from **only** the exact job `RUN_DIR` obtained from its
status file (or the newly allocated non-job run directory), into
`ORB_CI_HOME/inventory-outbox`. It never searches old worktrees/jobs. Each watcher
pass retries the outbox even when `done` suppresses another check. Failures are
explicit `REPORT inventory ... pending` journal messages and never change CI's
verdict. Local `inventory.lock` serializes capture/upload; GitHub non-force
fast-forward rejects competing branch updates and retries on a later pass.

The measured initial source report is 57,890 bytes. Growth follows declarations
and transitive ancestors. A 4 MiB input/envelope cap publishes an explicit
unavailable record, never truncated debt. Git Blobs API avoids Contents API's
base64 restriction above 1 MiB. The small discovery stays in Contents API.

## Deployment

Coordinate idle refresh with the watcher owner; never stop a live CI job. Cache
the reviewed `orb-ci-refresh.sh` under `ORB_CI_HOME`, and use it as ExecStartPre
for fast and full units instead of the old single-file fetch. It resolves one
fetched SHA, stages and syntax-checks both watcher and publisher, then installs
helper first. Both old/new watchers are compatible with that helper contract;
full and tag-poll paths never invoke it. Failed staging retains the previous pair.
Back up units and cached scripts first; no host-alert/timer changes are needed.

Add a static discovery link adjacent to #63 using its existing `issue.lock`,
preserving the current issue body. No dynamic JSON goes into the comment body.
Tests: `scripts/test_publish_inventory.py` and the publication case in
`scripts/test_orb_ci.py`; both run with the normal self-tests.
