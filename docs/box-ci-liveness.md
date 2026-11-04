# Box CI liveness alerts

**Unused since 2026-11-04** (owner decision, `docs/decisions.md`): CI is GitHub Actions only and the box runs no CI. This
document describes the former box CI; it is kept as reference.

`scripts/orb-ci-liveness.py` is a project-specific check for the existing root
`ethlabs-alerts` timer (every ten minutes), not another notification system.
`scripts/install-orb-ci-liveness.py` installs a root-owned helper and a small hook
in both the deployed runner and its setup-bundle source. The setup bundle at
`/home/fradamt/ethlabs-setup` is not a Git repository; this repository owns the
helper, fixtures and integration. The hook loads the helper inside the existing
per-check exception boundary, so a broken installation cannot disable host checks.

The check reads `consensus-lean-orb-ci.service` in fradamt's user manager and
GitHub main/#63 with fradamt's credentials. Each subprocess has a 25-second
timeout and drops root privileges before execution. No credentials or command
stderr enter alerts. It does not inspect or change the watcher's worktrees,
queue, jobs or local `done` file. A local completion is not proof of publication.

## Alert contract

- An observed non-active service alerts on that timer run. A query failure is
  reported separately, never described as proof that the watcher stopped.
- A new observed main SHA starts a 30-minute grace period, including at initial
  installation. Author/committer timestamps are irrelevant. Timer sampling means
  normally 30–40 minutes from first observation, up to another ten minutes from
  the actual push. Heads never observed between polls are outside this contract.
- Only a published #63 table row for `main` or `main (re-check)` with `--fast` or
  `--changed` counts. Either PASSED or FAILED is a result; PR/full rows are not.
  The table only stores SHA8, so matching inherits that format's collision risk.
- Pending observations retain their first-seen times through rapid churn. A
  later observed head's published row covers earlier superseded observations,
  matching the watcher's polling/coalescing behavior. Churn alone cannot reset
  the deadline. A still-pending newer head keeps its own deadline.
- Once confirmed, unchanged main is healthy indefinitely, even if its row ages
  out of the 40-row table. A newly observed SHA always creates new pending work.
- GitHub/status query errors preserve pending work. Thirty minutes of impaired
  observation produces a separate unavailable alert. An overdue alert during
  that outage explicitly says a result may exist. Recovery clears the error age.
- All alert categories use the existing six-hour deduplication. Recovery does
  not bypass that host policy. `--dry` neither sends nor writes persistent state.
  Stopping the entire box/root timer still requires the existing optional external
  heartbeat; this check cannot monitor its own execution from outside the machine.

## Deployment and validation

Coordinate with the watcher/host owner first. Land through `scripts/push-main.sh`
after independent review and regression fixtures. Then run
`sudo python3 -I scripts/install-orb-ci-liveness.py` from the reviewed checkout.
It requires source/deployed parity, backs up both to `/var/backups/ethlabs-alerts`,
installs code only under root-owned non-writable ancestors, registers inventory,
and appends `/srv/NOTES.md`. It does not run the full setup installer or restart
any service/timer. Re-running it keeps exactly one hook and preserves other checks.

The two alert copies are individually atomic, not a multi-file transaction. If
installation fails between their replacements, compare both against the printed
backup directory (or newest `liveness-*` backup), restore parity while preserving
unrelated edits, then retry. Do not blindly overwrite a later host-owner change.

Validate with `sudo /usr/local/sbin/ethlabs-alerts --dry`, source/deployed hashes,
and the next normal timer execution's persisted `consensus_lean_liveness` state.
Never print `/etc/ethlabs/alerts.conf`. A delivery test must be explicitly labelled
as synthetic and use the existing transport without stopping the watcher or
editing production alert state; HTTP acceptance alone does not prove phone receipt.
`scripts/test_orb_ci_liveness.py` exercises the state machine without notification
credentials, sleeping, or live service changes, and runs in the normal self-tests.
