Archival since 2026-10-09 (user decision); the S0 freeze is retired.

# FG finality safety: S0

Date: 2026-10-06. Scope: S0, S1, S1P. Stop before S2.
All new contracts are PROVISIONAL.

The implementation starts on `fg-fin-generic` at
`88c616d10ac4c11f39333937e36998d8d05b8274`. Its tree is identical to
`2d5b47a`, the fixed step-1 comparison base. There is no source or guard delta.
The merge at 88c616d records the policy-only step-1 landing.

The step-1 API has FGCoreReads, all nine FGCoreLaws fields, FGHeadLaws,
FGSourceService, and the shared event cuts. FG-SA supplies fgsaCoreLaws.
PC-SA supplies pcsaCoreReads for `.on` and pcsa_source_mem_TF.
It does not yet supply the nine-field core-law record.
The exact original adapter edges remain unchanged.

The user accepted the Opus finding 10 scope note before S1:
`safetyScopedRoots` wraps RootInjectiveOn as the generic projection of
NamedRootCollisionFree, as in rootInjectiveOn_run. This is not an F-3
exception. The helper theorem headers must still use the scoped projection.
No allow-list line may be added.

Saved 122 frozen source and policy files as exact bytes in the session
scratch folder `/tmp/fg-fin-s0-88c616d-bytes`. Their SHA-256 hashes are in
`docs/FG-FINALITY-SAFETY-S0-hashes.json`. This includes PC-SA claims,
FG-SA frozen Statements/Claims, both frozen Claims/Proofs axiom audits,
Assembly/Root, API documents, manifest policy, pins, and guard baselines.
Check these files after each commit. Do not regenerate the hashes to accept drift.

The five step-1 API modules and two guard inputs have a separate fingerprint
in `docs/FG-FINALITY-SAFETY-S0-step1-hashes.json`. Their pinned bytes are in
the same scratch folder. This records the guard base without freezing the
reviewed safety guard extension. The five API modules stay unchanged.
