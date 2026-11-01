# S0-F / 00c — deep checker and pre-SWITCH baselines

Basis: `ee14de5f39ecd57eda0b44941646d254e534ab8a`, branch `port-s0f00c`.
This tree contains all Stage 0 packages, including the lower `FrameNext` and
upper `ComposeNext` statements. The lead must capture these baselines again
on post-P13, pre-SWITCH main after all Stage 0 landings if main differs.
After SWITCH, keep the accepted baseline and record exact exceptions.

## Files

- `scripts/V2Manifest.lean`: kernel serialization, graph capture, digest and modes.
- `scripts/fgsa-deep.py`: baseline storage and strict deep/frame checks.
- `scripts/fgsa-deep-controls.py`: isolated compiled and file-format controls.
- `scripts/check-fgsa-manifest.sh`, `scripts/gate.sh`, and
  `scripts/gate-shell-controls.py`: mandatory gate wiring and shell controls.
- `scripts/fgsa-deep-frozen.json`, `scripts/fgsa-deep-frozen.sha256`,
  and `scripts/fgsa-deep-allow.json`: deep data, checksum and empty exceptions.
- `scripts/fgsa-frame-frozen.json`, `scripts/fgsa-frame-frozen.sha256`,
  and `scripts/fgsa-frame-allow.json`: frame data, checksum and empty exceptions.
- `docs/reports/fgsa-port-s0f00c.md`: design, measurements and data attribution.

## Changes and digest format

`scripts/V2Manifest.lean` adds `deepEntryDigest` and FG-SA-only `--deep`
with `--write` and `--check`. The existing shallow functions are unchanged.
No project proof, statement, axiom, package pin, or lake configuration changes.
The current shallow manifest, original frozen manifest and its SHA stay fixed.
P13 supplier/type fingerprints stay separate and unchanged.

The digest format is `fgsa-deep-node-v1` / `fgsa-deep-entry-v1`:

- Traverse every current FG-SA manifest root. Keep public, private, generated,
  and library dependencies. Follow types, definition and opaque values,
  inductive constructors, mutual inductive types, and recursor rule data.
- For a theorem, follow its type only. Do not serialize or traverse its proof.
  Expression metadata is omitted. Definition values remain in the digest.
- Serialize kernel expressions directly. Each node has a tag, field count,
  and the UTF-8 byte length of each field. Name string/numeric components,
  expression constructors, literals, projections, levels, and binder data have
  distinct tags. Rename universe parameters to `u0`, `u1`, and so on.
  Remove macro scopes only from binder names, as the shallow binder rule does.
- Include constant name and kind, normalized type/value, universe count,
  constructor and recursor data, safety, definition reducibility hints,
  reducibility status, instance status, and dependency names.
- SHA-256 each complete serialized node. For each root, sort the closure by
  `Name.lt`, serialize the structural name and 256-bit node digest pairs with
  lengths and a root format tag, then SHA-256 those bytes. No 64-bit `ownHash`
  value contributes to this digest.
- Store a shared node table with names, SHA-256 digests, and dependency edges.
  Each root stores its digest and the full sorted list of node IDs. This is
  its dependency name/digest list without repeated names. A failure reports
  exact old/new root digests, a changed node and its old/new digest, and one
  path from the root. Removed dependencies use the baseline graph.

`scripts/fgsa-deep.py` owns file validation and exact exception checks.
It checks baseline SHA-256, schema version, basis commit format, Lean and
package pins, original frozen membership, and complete root dependency lists.
The compiled root set must equal the complete current manifest root set.
Missing baseline, SHA, or exception files fail. Duplicate JSON keys fail.
Checks never write or refresh a baseline.

The separate frame baseline contains 43 entries: canonical `RFrameExact`,
`RFrame`, `FGFoundation`, `FGFoundationClaim`, `FrameAt`, and `FrameClaim`
families, plus every entry of `FrameNext` and `ComposeNext` modules. It includes
constructors, projections and equations from the complete current manifest.
It records shallow kind, module and digest; it has its own SHA and empty
exception file. A kind or module change also fails.

`check-fgsa-manifest.sh` checks the complete shallow manifest, then the frame
and deep baselines, before the `NEG=0` exit. The existing `fgsa-manifest` gate
step therefore runs all three checks at merge and full tiers. Full tier keeps
all C1–C13 controls and also runs the new isolated compiled controls. The shell
control fixtures test frame/deep failure propagation at merge tier.

## Capture and exceptions

Capture commands, after the required root build:

```sh
lake env lean --run scripts/V2Manifest.lean --scope fgsa --deep --write
python3 scripts/fgsa-deep.py --frame-write
```

Deep mode accepts `--frozen`, `--frozen-sha`, and `--allow` overrides for its
three separate paths. `--manifest` supplies the complete current shallow
manifest. These options do not refresh the shallow manifest. The Python
frame mode accepts `--baseline`, `--sha`, `--allow`, and `--manifest`.

Both exception files start with format version 1 and an empty `exceptions`
object. Each key is an exact entry name. Its value must contain exactly these
five nonempty string fields:

```json
{
  "old_digest": "<exact baseline digest>",
  "new_digest": "<exact measured current digest>",
  "cause": "<changed dependency and reason; equality argument for class A>",
  "census_class": "A or B",
  "plan_revision": "<reviewed plan revision>"
}
```

The example is a schema guide, not an accepted exception. Deep digests have
64 lowercase hexadecimal digits; frame digests have 16. The marker `absent`
permits an explicitly recorded addition or removal. Unchanged and unknown
exceptions are stale and fail. A wrong old or new digest fails. Missing causes,
plan revisions, and invalid classes fail. C-i stays contextual evidence and
cannot replace the complete declaration's A/B class.

## Compiled census and planned SWITCH exceptions

The eight direct model seeds are `AvailableChain.FGSA.controls`, `fullTree`,
`proposalsAt`, `voterBlocks`, `headSupport`, `headVote`, `proposerSupport`, and
`fgHead`. Of 1,242 roots, 897 reach at least one seed. This is exactly all 876
source-census entries plus the 21 new entries listed below. No source-census
entry is missing. The old entries retain their 144 A / 732 B classifications.
The source recount remains 369 declarations, 876 entries, 799 originally
frozen entries, and 77 later entries.

The 154 API source reader rows in the 00b report all have a path even when
traversal stops at `Run.fgsa`. There are 364 current manifest roots with such
a path and 533 more that require the `fgsa` edge. The separate 53 Proofs
Statements rows in 00b are outside this manifest's root scope; they are not
silently added to the frozen API. Six local Next entries (`frameRNext`,
`domainRNext`, `SettledPhaseFrameNext`, and their equations) have no path to
the eight seeds. This confirms the 00b expectation for their current closure.

For each row below, the cause is the one h+i+j switch in r2 and its binding
addendum. Class A uses the same-event store transport argument in the 00b
report; class B includes the changed emitted objects or run/source premise.
Every foundation constructor/projection retains its complete carrier's B
class. The record gives the measured old digest and one current dependency
path. The post-SWITCH digest does not exist on this pre-SWITCH tree: measure it
at SWITCH before adding an exact allowance. These planning records grant no
exception. Do not invent a new digest or put a stale allowance in this baseline.

- `AvailableChain.FGSA.Run.FGFoundationClaimNext` — class B.
  Old: `3b9682f3eaa0c8ad04dd7610417912933e3f1c0815a357fdfc3b915794bfbae9`.
  Path: `AvailableChain.FGSA.Run.FGFoundationClaimNext ->
  AvailableChain.FGSA.Run.fgsa ->
  AvailableChain.FGSA.Run.act ->
  AvailableChain.FGSA.Run.actS ->
  AvailableChain.FGSA.headVote`.
- `AvailableChain.FGSA.Run.FGFoundationNext` — class B.
  Old: `8275ef51774c08b816da9a9d024ff0a6f92a8201b32816872982cc828d4d040c`.
  Path: `AvailableChain.FGSA.Run.FGFoundationNext ->
  AvailableChain.FGSA.Run.fgsa ->
  AvailableChain.FGSA.Run.act ->
  AvailableChain.FGSA.Run.actS ->
  AvailableChain.FGSA.headVote`.
- `AvailableChain.FGSA.Run.FGFoundationNext.cumul` — class B.
  Old: `9a6fff986ccc511239293f1f278d2051bf4c2dd4d9c59294a60f65fb13f6a987`.
  Path: `AvailableChain.FGSA.Run.FGFoundationNext.cumul ->
  AvailableChain.FGSA.Run.fgsa ->
  AvailableChain.FGSA.Run.act ->
  AvailableChain.FGSA.Run.actS ->
  AvailableChain.FGSA.headVote`.
- `AvailableChain.FGSA.Run.FGFoundationNext.frame` — class B.
  Old: `13fd34d93915a6eb24e8963eca4229b1a07ded02050cbad9d7ff0c4a1f32cab8`.
  Path: `AvailableChain.FGSA.Run.FGFoundationNext.frame ->
  AvailableChain.FGSA.Run.fgsa ->
  AvailableChain.FGSA.Run.act ->
  AvailableChain.FGSA.Run.actS ->
  AvailableChain.FGSA.headVote`.
- `AvailableChain.FGSA.Run.FGFoundationNext.geo` — class B.
  Old: `3ca4deede8bc473d5c9f4270ecd91161ce4ef441a4b39f5dce60b6e9fd64ac4c`.
  Path: `AvailableChain.FGSA.Run.FGFoundationNext.geo ->
  AvailableChain.FGSA.Run.fgsa ->
  AvailableChain.FGSA.Run.act ->
  AvailableChain.FGSA.Run.actS ->
  AvailableChain.FGSA.headVote`.
- `AvailableChain.FGSA.Run.FGFoundationNext.mk` — class B.
  Old: `8275ef51774c08b816da9a9d024ff0a6f92a8201b32816872982cc828d4d040c`.
  Path: `AvailableChain.FGSA.Run.FGFoundationNext.mk ->
  AvailableChain.FGSA.Run.fgsa ->
  AvailableChain.FGSA.Run.act ->
  AvailableChain.FGSA.Run.actS ->
  AvailableChain.FGSA.headVote`.
- `AvailableChain.FGSA.Run.FGFoundationNext.mono` — class B.
  Old: `6468a163d7e7ac27e6552a116762872e82370aeb84be687a49e06cf58380e6aa`.
  Path: `AvailableChain.FGSA.Run.FGFoundationNext.mono ->
  AvailableChain.FGSA.Run.fgsa ->
  AvailableChain.FGSA.Run.act ->
  AvailableChain.FGSA.Run.actS ->
  AvailableChain.FGSA.headVote`.
- `AvailableChain.FGSA.Run.FGFoundationNext.reconcile` — class B.
  Old: `fcdaa402511bf8f4fd7c947f680f428ce750fc022a2300f103ea46b10a59a592`.
  Path: `AvailableChain.FGSA.Run.FGFoundationNext.reconcile ->
  AvailableChain.FGSA.Run.fgsa ->
  AvailableChain.FGSA.Run.act ->
  AvailableChain.FGSA.Run.actS ->
  AvailableChain.FGSA.headVote`.
- `AvailableChain.FGSA.Run.FGFoundationNext.store` — class B.
  Old: `87ca023adaeeeb197bb59d23d408756033a39ce146c87ba7af4ce125d46b30ee`.
  Path: `AvailableChain.FGSA.Run.FGFoundationNext.store ->
  AvailableChain.FGSA.Run.fgsa ->
  AvailableChain.FGSA.Run.act ->
  AvailableChain.FGSA.Run.actS ->
  AvailableChain.FGSA.headVote`.
- `AvailableChain.FGSA.Run.FGFoundationNext.strat` — class B.
  Old: `0d11f7f481476a4b761e0676239f84b6dad5b0cbcdcf21c4eae703b51d936fae`.
  Path: `AvailableChain.FGSA.Run.FGFoundationNext.strat ->
  AvailableChain.FGSA.Run.fgsa ->
  AvailableChain.FGSA.Run.act ->
  AvailableChain.FGSA.Run.actS ->
  AvailableChain.FGSA.headVote`.
- `AvailableChain.FGSA.Run.FrameAtNext` — class A.
  Old: `249959a9768e8d49553c895098e7026fa2d80af275b7c8d80a400d2ff796f5a2`.
  Path: `AvailableChain.FGSA.Run.FrameAtNext ->
  AvailableChain.FGSA.Run.fgsa ->
  AvailableChain.FGSA.Run.act ->
  AvailableChain.FGSA.Run.actS ->
  AvailableChain.FGSA.headVote`.
- `AvailableChain.FGSA.Run.FrameClaimNext` — class A.
  Old: `e26f9102bbd2378773ce7465684af1879727182b8435d1030bd4bb11fd7cf1ed`.
  Path: `AvailableChain.FGSA.Run.FrameClaimNext ->
  AvailableChain.FGSA.Run.fgsa ->
  AvailableChain.FGSA.Run.act ->
  AvailableChain.FGSA.Run.actS ->
  AvailableChain.FGSA.headVote`.
- `AvailableChain.FGSA.Run.OpeningCoveredNext` — class B.
  Old: `00085ba3303d0ea8c8443036dcbbdb7c3d553f6e4b9492ed66a0122237e19135`.
  Path: `AvailableChain.FGSA.Run.OpeningCoveredNext ->
  AvailableChain.FGSA.Run.actionSourceFG ->
  AvailableChain.FGSA.fgSource ->
  AvailableChain.FGSA.fullTree`.
- `AvailableChain.FGSA.Run.RFrameExactNext` — class A.
  Old: `d7951f770bf28936b2151f9f575384b8806f41512595ea341a5899cbef6b6063`.
  Path: `AvailableChain.FGSA.Run.RFrameExactNext ->
  AvailableChain.FGSA.Run.fgsa ->
  AvailableChain.FGSA.Run.act ->
  AvailableChain.FGSA.Run.actS ->
  AvailableChain.FGSA.headVote`.
- `AvailableChain.FGSA.Run.RFrameExactNext_def` — class A.
  Old: `e59210841a170508bbb818444329501ba409443d678d34b7c9503b48646f86ca`.
  Path: `AvailableChain.FGSA.Run.RFrameExactNext_def ->
  AvailableChain.FGSA.Run.fgsa ->
  AvailableChain.FGSA.Run.act ->
  AvailableChain.FGSA.Run.actS ->
  AvailableChain.FGSA.headVote`.
- `AvailableChain.FGSA.Run.RFrameNext` — class A.
  Old: `7e7991e70df9dddbcf3b5b10306935fe46c4bcbaae4bb3bbe1a9659c0c59265d`.
  Path: `AvailableChain.FGSA.Run.RFrameNext ->
  AvailableChain.FGSA.Run.fgsa ->
  AvailableChain.FGSA.Run.act ->
  AvailableChain.FGSA.Run.actS ->
  AvailableChain.FGSA.headVote`.
- `AvailableChain.FGSA.Run.RFrameNext_def` — class A.
  Old: `beb138eae0ed794a26409b8c521f66b9b86222343344090184796ed82eb859a6`.
  Path: `AvailableChain.FGSA.Run.RFrameNext_def ->
  AvailableChain.FGSA.Run.fgsa ->
  AvailableChain.FGSA.Run.act ->
  AvailableChain.FGSA.Run.actS ->
  AvailableChain.FGSA.headVote`.
- `AvailableChain.FGSA.Run.TGeomNext` — class B.
  Old: `f376e3d350146f620ff6f61c1be613ef87b533c057cc7e76b473f35431a035a9`.
  Path: `AvailableChain.FGSA.Run.TGeomNext ->
  AvailableChain.FGSA.Run.actionSourceFG ->
  AvailableChain.FGSA.fgSource ->
  AvailableChain.FGSA.fullTree`.
- `AvailableChain.FGSA.Run.TStartNext` — class A.
  Old: `b666ca43e8d5135b61ae859fe2fb6cbecb2a72bea7125e65d0742c135f8fb271`.
  Path: `AvailableChain.FGSA.Run.TStartNext ->
  AvailableChain.FGSA.Run.fgsaAC ->
  AvailableChain.FGSA.headVote`.
- `AvailableChain.FGSA.Run.TWalkNext` — class A.
  Old: `f707e496ef466d691fcc8b3dd901abb3f1ef304adf9cb71066ed9e9d6c5fcac2`.
  Path: `AvailableChain.FGSA.Run.TWalkNext ->
  AvailableChain.FGSA.Run.fgsa ->
  AvailableChain.FGSA.Run.act ->
  AvailableChain.FGSA.Run.actS ->
  AvailableChain.FGSA.headVote`.
- `AvailableChain.FGSA.Run.WalkBatchNext` — class A.
  Old: `151c4cb9883bd895f611201b28dbe6906111566450c4c216bed98c2a501d54f4`.
  Path: `AvailableChain.FGSA.Run.WalkBatchNext ->
  AvailableChain.FGSA.Run.fgsa ->
  AvailableChain.FGSA.Run.act ->
  AvailableChain.FGSA.Run.actS ->
  AvailableChain.FGSA.headVote`.

The census can be reproduced from the baseline without a new Lean load:
read the node table, select roots whose dependency IDs contain any of the
eight seed IDs, and compare that set with the `manifest_entries` names in
`docs/FGSA-PORT-CENSUS.md`. For the 154-row check, search dependency edges
while treating `AvailableChain.FGSA.Run.fgsa` as a terminal node.

## Generated-data attribution

All following files are new in WP00c. Their old value is `absent`.
Their basis is the commit above and their plan is r2 plus the binding addendum.
The deep baseline has 1,242 entries, 3,665 nodes, and 9,742,393 bytes.
The frame baseline has 43 entries and 61,167 bytes. Both retain the 1,127
original-frozen names as separate provenance. The Lean pin is
`leanprover/lean4:v4.34.1`; the exact `lake-manifest.json` SHA-256 is
`b4be90ebe4e8057c9403a3612c98a29424cb1613499fcebffe96001490c90ffa`.

- `scripts/fgsa-deep-frozen.json`: Complete compiled kernel closure capture; every root/node value is measured.
  New file SHA-256: `25fec2f58ab2c6b4b51ecd4d0941bfc57c4a8b1cb24298ea771761fcb9df0f92`.
- `scripts/fgsa-deep-frozen.sha256`: SHA-256 of the exact deep baseline file bytes.
  New file SHA-256: `66832bc1148eb7ae8c3ed4dfdd6a5e869b565ad24c27a93adeb2830b9c34346b`.
- `scripts/fgsa-frame-frozen.json`: 43 selected entries from the unchanged complete shallow manifest.
  New file SHA-256: `32437641b9a85b5c492753de2c6f8924c82bfa74c9b8bcbd384199a2deab2bba`.
- `scripts/fgsa-frame-frozen.sha256`: SHA-256 of the exact frame baseline file bytes.
  New file SHA-256: `2951fa812c0ec37bb7dc80f83ac31724e2b74a8b85067a1c0a6beac1961d4e1d`.
- `scripts/fgsa-deep-allow.json`: Empty exact deep exception map; no semantic change is accepted here.
  New file SHA-256: `33e5449414ed33e087d9bd6c75fab9d7dd28ff5a51f2cf4cc54bd613428b9b99`.
- `scripts/fgsa-frame-allow.json`: Empty exact frame exception map; no shallow change is accepted here.
  New file SHA-256: `33e5449414ed33e087d9bd6c75fab9d7dd28ff5a51f2cf4cc54bd613428b9b99`.

No other generated repository data changes. In particular, the current FG-SA
manifest stays at SHA-256
`23453dec2be723dfead8822514b68ef6d154f2a0a1b8d229c1281cef01e62046`,
and `FGSA-API-frozen.md` stays at SHA-256
`96369fb292c500dcf37e159d530f089b6e1d1a2a3c981c9c4e219f9835717d91`.
Existing shallow allowances, expected names, audit scopes, import policy,
PC-SA data, S0 manifests/history, and P13 supplier/type fingerprints are unchanged.
Temporary control manifests and compiled fixtures are deleted by their owner.

## Validation

- Required precheck command with this worktree and base `5dbfcb3c`: PASS.
  Both the initial run and the final run print `PRECHECK PASS`.
  Log: `/tmp/s0f00c-precheck-final.log`.
- `LEAN_SLOTS=2 lake build --wfail AvailableChainFGSA AvailableChainFGSARun
  AvailableChainFGSAClaims AvailableChainPCSA AvailableChainPCSARun
  AvailableChainPCSAClaims`: PASS, 3,475 jobs. This supplies the missing
  `Claims.FrameNext.olean` before capture. Log: `/tmp/s0f00c-build.log`.
- `bash scripts/check-pcsa-manifest.sh`: PASS, 424 entries in 21 modules;
  W, N1 and N2 controls pass. Log: `/tmp/s0f00c-pcsa-manifest.log`.
- Final isolated compiled controls: PASS. Public model and private cross-module
  body changes fail deep checks while their shallow hashes stay equal. Changed
  constructor field types fail. Two distinct theorem proof values give an
  identical complete snapshot. An exact recorded exception passes; stale,
  unknown, wrong-old, wrong-new, and unexplained exceptions fail. CLI controls
  exercise actual file reads, SHA checks, exception parsing, and return codes.
  Dependency-path, closure-completeness, duplicate-JSON, missing-file,
  changed/removed-frame-entry, and wrong-SHA controls pass.
  Log: `/tmp/s0f00c-deep-controls-final.log`.
- Shell controls: PASS, including frame/deep failure at `NEG=0`, existing
  failure propagation, temporary-file cleanup, and TERM handling.
  Log: `/tmp/s0f00c-shell-controls.log`.
- Source census recount, owner check and its negative controls, Python syntax,
  and `git diff --check`: PASS. The existing scan, shallow hash functions,
  manifest parser, and frozen checker remain byte-identical.

- Required `bash scripts/check-fgsa-manifest.sh`: PASS (exit 0). The complete
  shallow manifest has 1,242 entries in 57 modules; frame has 43 entries;
  deep has 1,242 roots / 3,665 nodes. Both new exception maps are empty.
  EOF/copy/hash, C1–C13, and every deep/frame control pass, including the
  final complete-manifest moved-module control. The final frame-only check
  also passes. Log: `/tmp/s0f00c-fgsa-manifest.log`.

The additional `python3 scripts/check-fg-finality-freeze.py --check` returns
FAIL with five unlisted S0 byte differences. Four already exist at the basis
commit and are unchanged by this job: `AvailableChainFGSAClaims.lean`,
`AvailableChainFGSAClaims/Tests/Axioms.lean`, `docs/FGSA-API.md`, and
`scripts/baselines/kitfg-def-modules.txt`. WP00c adds the required mandatory
checks to the fifth file, `scripts/check-fgsa-manifest.sh`. Its exact job diff is:

- Basis SHA-256:
  `1c8622dc076d0926b08d0171d0e9fe1c383eb8c92641fc50ad9b3df58860fe9c`.
- New SHA-256:
  `3b95a9dbe9815162fc6fad985ba182bb6aa9170d9fdb94b63df5830cecc73908`.
- Cause: mandatory frame/deep checks before the merge-tier exit and additional
  full-tier controls; owner WP00c, plan r2 plus the binding addendum.

The lead/data owner must add these Stage 0 file changes to the inherited
history package. This job does not change either S0 byte manifest, rewrite
P13 fingerprints, or weaken the history check. Exact recorded/current values
for this handoff follow:


```json
[
  {
    "path": "AvailableChainFGSAClaims.lean",
    "recorded_sha256": "dfd4a9fdbc46d417f1ac84768f1670e2c8da0c08acb98f6d91768133d0d20c41",
    "basis_sha256": "f67050bc3bbd868ab6b890be316125686e196c54f1b44ea3af509a2560c68dc9",
    "current_sha256": "f67050bc3bbd868ab6b890be316125686e196c54f1b44ea3af509a2560c68dc9"
  },
  {
    "path": "AvailableChainFGSAClaims/Tests/Axioms.lean",
    "recorded_sha256": "a085f26a82c48f5554afc3263211ee872fa9cda227efa9ecd013e621b2a3a82e",
    "basis_sha256": "b93ad6459ba5afa17283a8521014bcb9fed4d2df100f299e41476ea0a2c148da",
    "current_sha256": "b93ad6459ba5afa17283a8521014bcb9fed4d2df100f299e41476ea0a2c148da"
  },
  {
    "path": "docs/FGSA-API.md",
    "recorded_sha256": "b3075a0c0979320a26ba3fca7a43327882e24685574242a0f7e979381cc0e018",
    "basis_sha256": "23453dec2be723dfead8822514b68ef6d154f2a0a1b8d229c1281cef01e62046",
    "current_sha256": "23453dec2be723dfead8822514b68ef6d154f2a0a1b8d229c1281cef01e62046"
  },
  {
    "path": "scripts/baselines/kitfg-def-modules.txt",
    "recorded_sha256": "4b548a8a8dfaed422ae177c0ca0fb823acc6fc7e6825e8f76170c7933d756f81",
    "basis_sha256": "a98b46deb10d65b1db855157240d68f8f60d7a10e51acafa606cf16b38de89c4",
    "current_sha256": "a98b46deb10d65b1db855157240d68f8f60d7a10e51acafa606cf16b38de89c4"
  },
  {
    "path": "scripts/check-fgsa-manifest.sh",
    "recorded_sha256": "1c8622dc076d0926b08d0171d0e9fe1c383eb8c92641fc50ad9b3df58860fe9c",
    "basis_sha256": "1c8622dc076d0926b08d0171d0e9fe1c383eb8c92641fc50ad9b3df58860fe9c",
    "current_sha256": "3b95a9dbe9815162fc6fad985ba182bb6aa9170d9fdb94b63df5830cecc73908"
  }
]
```

Not run: the complete FULL landing gate, SWITCH/post-SWITCH digests, and the
lead's main recapture. No review, agent, child Codex/Claude process, push,
rebase, `lake update`, or throttle-bypass environment setting was used.
