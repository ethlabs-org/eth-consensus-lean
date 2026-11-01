# r199 — G13 final audit of the FG-SA model store

**Verdict: READY WITH FIXES.** No blocking defect was found in the model or
the public theorem statements at `8e8b61e8739c53b50cd5d896a88f9af4c9ca303b`.
Two major findings concern the checks that must protect this result. Fix
M1 and M2 before the merge, then run their negative controls when Lean is
available. The local proofs do not require a root-design change. They do
not establish an unconditional protocol result across nodes.

```text
┌──────────┬───────┬───────────────────────────────────────────────────────┐
│ Severity │ Count │ Result                                                │
├──────────┼───────┼───────────────────────────────────────────────────────┤
│ BLOCKING │ 0     │ No new model or theorem defect found.                 │
│ MAJOR    │ 2     │ Lease-scan bypass; incomplete import enforcement.     │
│ MINOR    │ 3     │ Optional checks; report scope; remaining test gap.    │
└──────────┴───────┴───────────────────────────────────────────────────────┘
```

Audit date: 2026-09-29. This is an independent source audit of the whole
library. I did not run Lean, Lake, or `check-fgsa.sh`. The reported full
build of 3600 jobs, 784 scanned constants, 431 theorems, 107 lease
arguments, and successful negative control remain implementer evidence.
I checked the script bodies and ran read-only source checks, `bash -n`,
and the read-only, three-argument form of `git merge-tree`. Only this
report was written. No commit, state update, or log update was made.

Paths below are relative to this repository unless stated otherwise.
`R` is `/Users/francesco/ethereum/research/async-resilient-committees/tip-stability`.
`report:N` means `R/codex/scratch/fgsa-task13-report.md:N`.
`spec:N` means the frozen archive
`R/spec/archive/fgsa-protocol-2e884811.tex:N`.
`bp00:N` means `R/blueprint/archive/00-outline-03afa5ae.md:N`;
`bp01:N` means `R/blueprint/01-foundations.md:N`.

The spec and pinned outline hashes match the plan. The foundations hash
is `989289cce1d761adfae3bc91b0358ff858b59d1151678d8d99d547a08f8eb3ea`.
The Task 13 report hash is
`67a3c5b23e4e791f179da5df7627672a790a90c4a2bd418daa493f9062f1d401`.
The current outline has hash `bfc509e0…`; all ten named foundation items
from `bp.carrier.v1` through `bp.receiptCoverage.v1` that this plan uses
have the same statement text as the pinned archive. I also checked the
use of K1 and K8 in `R/blueprint/02-clean.md`, including its completed-event
induction and the compatibility argument at lines 471–495.

The review used the plan's Global Constraints, blocking list, task notes,
and G0–G12 dispositions, together with the existing `docs/audit/fgsa-*.md`
reports. Earlier reports refer to earlier commits. Their findings were
checked against the final source, rather than treated as current defects.

**M1 — MAJOR: an alias can pass the lease scan while its body uses the
default policy.** `scripts/CheckFGSALease.lean:94`, also `:63` and `:73`;
claim at `docs/MAP.md:684` and plan `:2291`.

The scanner skips every declaration outside `AvailableChain.FGSA` that
has a lease-policy parameter. It does not restrict this exception to the
generated `GridCO.recordGenuine.eq_1` equation lemma named in its comment.
At a call, it checks the supplied policy argument, but does not inspect
the called definition's body. Those two rules permit the following alias
pattern in a scanned module:

```lean
namespace AvailableChain.LeaseAuditAlias
def gate (_policy : GridCO.LeasePolicy) (p : GridCO.Params)
    (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  @GridCO.gate GridCO.gridLeasePolicy p 1 st r
end AvailableChain.LeaseAuditAlias

namespace AvailableChain.FGSA
def badGate (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) :
    GridCO.State 1 :=
  AvailableChain.LeaseAuditAlias.gate GridCO.slowLeasePolicy p st r
end AvailableChain.FGSA
```

The alias has a policy parameter and a different namespace, so line 94
skips its type and value. `badGate` supplies the exact accepted constant
at that parameter. The scanner therefore does not reach the default-policy
call inside the alias. Namespace conventions do not make this an adequate
check of every compiled FGSA constant. Also, `leasePositions` at line 40
recognizes only a syntactic `LeasePolicy` type; it does not reduce an alias
of that type.

This is a source-level counterexample to the scan algorithm. I did not
compile the example. No such alias was found in the current library, and
the earlier `ghostWalk_mem` defect is fixed at
`AvailableChainFGSA/Proofs/StoreInv.lean:755`. This finding does not refute
that theorem or establish a bad current lease call.

Required fix: restrict the generated-declaration exception to verified
declarations, or inspect generic bodies while allowing only their own
bound policy parameter. Still reject a concrete default-policy call in
such a body. Reduce parameter types before classifying them. Add an alias
negative control in addition to the present direct-call control. State
explicitly which imported wrapper definitions are trusted or inspected;
the scan does not follow arbitrary imported wrapper bodies.

**M2 — MAJOR: the import check does not enforce the plan's allowlist.**
`scripts/check-fgsa.sh:47`, `:53`, `:61`, and `:66`; requirement at
`docs/plans/2026-09-29-fgsa-model-store.md:222` and `:2479`.

The direct check rejects five library names. It does not reject other
imports outside the allowed set, or enforce the allowed directory for an
import. For example, a direct import of
`AvailableChainLStar.Model.Protocol` passes this blacklist and the closure
blacklist, although it is outside the plan's direct allowlist. A direct
KitFG import in `Model/` also passes, although the plan permits it only in
`Statements/` and `Proofs/`.

The closure walk uses line regexes without Lean comment handling. A valid
header such as `public import /- dependency -/ AvailableChainFramework.Profile`
does not match either regex. Thus even a forbidden closure library can
be omitted from the walk. A line break between `import` and its module
has the same problem. The existing handling of `public meta import` and
`import all` fixes the earlier G1 cases but does not close these cases.

Required fix: check parsed import headers, or tokenize them with support
for comments and whitespace. Apply the direct allowlist and its directory
restrictions, with explicit rules for internal FGSA imports and the root.
Check the full project import closure against the four forbidden library
roots. Keep the declared transitive `AvailableChainStatements` exception.
Add negative controls for an unlisted library, a wrong-layer import, and
a forbidden import with an intervening comment.

The current imports satisfy the plan. My source walk reached 78 project
modules in FGSA, GridCO, KitFG, Model, SA, SimplexFG, and Statements. It
reached none of Framework, Registry, SAPC, or Witnesses. M2 is a defect in
future enforcement, not an undeclared current dependency.

**N1 — MINOR: the final check can succeed with either audit script absent.**
`scripts/check-fgsa.sh:73` and `:77`.

Both checks are conditional on file existence. If either script is
missing, the shell skips it and can print `all FGSA checks pass`. That
condition was useful during the early tasks; it is wrong for the final
gate. Require both files, then invoke both checks without an optional
branch. Both files exist at the audited HEAD, so this did not bypass the
reported validation.

**N2 — MINOR: qualify the report's rule-equivalence claim and its use of
“no premise”.** `report:70`, `report:42`, `report:119`, and `report:166`;
`AvailableChainFGSA/Statements/Invariants.lean:11`;
`AvailableChainFGSA/Proofs/CrossNode.lean:22`.

“No model rule differs from the spec” is too broad. The report later
states DQ10 and the checked-input and duty-slot limits, but omits the
release-cutoff difference already recorded in the Reachable docstring
and r195 D2. `GridCO.releaseCount` at
`AvailableChainGridCO/Model/Protocol.lean:397` tests equivocation in all
stored label-r votes. Spec 1197–1200 tests votes stamped before `q_r`.
They agree at the scheduled release before same-time deliveries. They
can disagree after later votes and a repeated or backward clock.

Use “no new undeclared rule difference at the stated protocol boundary”.
Add the release event-order requirement to the T7 inputs; one tick per
time alone does not state that order. Change `contentAgree_self: no
premise` to “no run premise; requires CStoreInv and MetaInv”. Likewise,
the K3 table's `storeControls_eq` needs the indicated CStoreInv; only the
reconcile frame equalities are unconditional. The report already names
these local invariants elsewhere, so this is a precision fix, not a hidden
new theorem assumption. The assertion that no gate finding remains open
also needs the qualification in N3.

**N3 — MINOR: the G6 filter test still does not distinguish act(Σ) from
the full FJ-filtered tree.** `AvailableChainFGSA/Tests/Smoke.lean:555`
and `:572`; plan `:1694`; r195 N3 at
`docs/audit/fgsa-model-check-report.md:31`.

The added source and live-root tests use `B1'` with `F = B1`. That block
is stored but conflicts with F. Both the active filter and the full FJ
filter reject it. Replacing `fullTree` by just the active tree in
`liveRoot` or `fgSource` can still pass these exclusion tests. The earlier
request included a stored active target excluded only by FJ filtering.
That case remains absent.

Add that case, or record this part of r195 N3 as deferred. The existing
`stK` supplies a useful starting point: `F = genesis`, and `X` is active
but lacks a height-3 descendant witness. A hand-set live lease on X,
with a matching current fast-write entry for the source test, can
distinguish the two filters. Check the expected values from the frame
before adding the test. The present function bodies use `fullTree`
correctly; this is a regression-test gap.

**K table check.** In the statements below, erased F means
`eraseFG st.fg.F`. Membership and ancestry premises on the compared
blocks are retained. “No extra premise” means no assumption beyond the
local scope and hypotheses stated here.

- **K1 / bp.reconcile.v1** —
  `Proofs/Reconcile.lean:216`, `reconcile_harmless_origin`: given
  `FastOrigin F₀ st`, `F₀ ⪯ erased F`, and compatibility of every present
  obligation, every saved nonempty body, and S with erased F, reconcile
  changes only S to its normalized value and gives `S ⪯ S'`.
  `Proofs/StoreInv.lean:646`, `admitBlock_reconcile_harmless`: given
  CStoreInv, a stored-parent lookup and successful acceptance, with those
  three compatibility hypotheses at the post-step F, obligations, genuine
  results, and fastWrite are unchanged and S extends. No separate
  fastWrite-compatibility hypothesis is present. The result also covers an
  unchanged F. This is bp00:465 and bp01:345, with the due-lease reading
  explicitly reported at report:83 and :167. The historical-origin case
  is proved by `reconcile_fastOrigin` at `Reconcile.lean:173`. The weaker
  `reconcile_harmless` is used only as the helper for the origin theorem;
  the report and MAP correctly identify it as a helper.

- **K2 / comp.outputNesting.v1/v2** —
  `Proofs/Nesting.lean:18`, `outputNesting_v1`, proves
  `F ⪯ (if F ⪯ S then S else F)` for arbitrary F and S.
  `:115`, `outputNesting_stored`, proves that every Reachable state has
  `erased F ⪯ S`, `confirmed = S`, and `stable = confirmed`.
  `:125`, `finalized_preceq_stable`, states the accessor form on Reachable
  states. These match bp00:475 and :480 and bp01:372. No CStoreInv,
  synchrony, fault, or ContentAgree premise is added. The accessor
  equalities are definitional, as report:21–23 says. The claim applies
  after a complete event, not inside admission before reconcile.

- **K3 / bp.frame.v1 and bp.reconcile.v1** —
  `Proofs/Reconcile.lean:64`, `reconcile_frame`, preserves the entire FG
  store and every non-reconciled base/composite field listed there.
  `:81`, `storeControls_reconcile`, preserves the controls without any
  invariant premise. `Proofs/StoreInv.lean:26`, `storeControls_eq`, needs
  CStoreInv and equates the cached controls to `fjControls` on F and TF.
  Together with `fg_step_cases` at `:551`, `fg_on_block_accepts` at
  `Proofs/Admission.lean:158`, and `clock_fg` at `Proofs/Fields.lean:272`,
  they supply the projection and frame clauses of bp00:487 and bp01:232.
  Exact reconcile writes and idempotence are at `Reconcile.lean:16–99`.
  No frame input is silently replaced by an SA field.

- **K4 core / bp.store.v1** —
  `Proofs/StoreInv.lean:541`, `storeInvariant`, proves
  `Reachable p st → CStoreInv p st`. Its nine fields are at
  `Statements/Invariants.lean:54`. The imported FG invariant supplies
  parent closure, genesis, F membership, the maximum height, the selected
  lex pair, `F ⪯ J`, and an admitted finalization carrier.
  `J_mem` at `StoreInv.lean:32` supplies J membership separately.
  `fMonotone`, `process_F_mono`, and `clock_F_eq` at `:579`, `:587`, and
  `:592` give F monotonicity for every delivery and F equality for every
  clock. `process_hmax_mono` and `process_pair_mono` at `:596` and `:606`
  give height and lex-pair monotonicity; `clock_fg` supplies their clock
  cases. This covers bp00:433 and bp01:163 without a ContentAgree premise.

- **K4 metadata / bp.store.v1** —
  `Proofs/Metadata.lean:461`, `metadataInvariant`, proves
  `Reachable p st → MetaInv p st`. Its nine fields at
  `Statements/Invariants.lean:84` relate stored wires to FG blocks and
  their ordered rows, give exactly one wire per non-genesis block,
  forbid genesis wires, and give stamp keys, block/wire uniqueness, and
  the decoded row-pool cap. `process_cumulative` at `Metadata.lean:186`
  preserves TF by inclusion and blocks, both stamp lists, proposals, and
  rows by list prefix. `clock_cumulative` at `:94` preserves those fields
  by equality. First-match stamp reads therefore keep old stamps, and
  `derive` on an unchanged block keeps its state. This supplies bp01:192
  and :222 and the metadata portion of bp.frame.v1. No external metadata
  premise is added to the Reachable result.

- **K5 local / bp.carrier.v1** —
  `Proofs/StoreInv.lean:21`, `viewRootInj_TF`, obtains ViewRootInj from
  CStoreInv. `Proofs/Carrier.lean:104`, `viewRootInj_of_rootInj`, takes
  parent closure and root injectivity of a set. `:67`,
  `preceq_of_eraseFG_preceq`, reflects erased ancestry for blocks on
  ancestor paths of a ViewRootInj view; forward ancestry is at `:36`.
  `:89`, `compatible_iff_eraseFG`, gives equality of compatibility tests
  on those paths. `:112`, `rootInjectiveOn_of_viewRootInj`, gives the
  two-chain KitFG premise for stored tips in one view. Slot, root, parent,
  and genesis preservation are at `:20–34`; `eraseFG_fgBlock` at
  `Proofs/Admission.lean:49` is the flat-wire erasure equation. This is
  the local form of bp00:410 and bp01:35–82. DQ1/DQ2 and the deferred run
  lift are stated in the report. “With no hypothesis” in the
  `viewRootInj_TF` docstring should be read as no external root premise;
  its signature still requires CStoreInv.

- **K5 across nodes / bp.carrier.v1** —
  `Proofs/CrossNode.lean:61`, `fg_eq_of_eraseFG_eq_across`, takes CStoreInv
  and MetaInv at each store, ContentAgree, membership in the respective
  TF sets, and equal erasures; it concludes FG-block equality.
  `:103`, `preceq_iff_across`, gives ancestry in both directions with the
  same store premises and memberships. `:112`, `compatible_iff_across`,
  gives equality of the compatibility tests. `:125`,
  `rootInjectiveOn_across`, gives the KitFG two-chain root premise for
  the two stored tips. `:22`, `contentAgree_self`, needs both local
  invariants and no run content premise. These are the conditional
  store-pair forms of bp01:57–78. The narrowed ContentAgree asks only for
  equal erased blocks and equal ordered signed rows at equal roots.
  The proofs use exactly those components. They do not establish a
  common full proposal payload, a run adapter, or safety across nodes.

- **K8 input / bp.receiptCoverage.v1** —
  `Proofs/Admission.lean:474`, `admitBlock_sufficient`, takes CStoreInv,
  a wellFormed proposal wire, a stored parent, a nonfuture slot, a fresh
  root, and `erased F ⪯ b`. It proves base membership after process and
  membership of the reconstructed FG block in TF.
  `:532`, `admitBlock_sufficient_absent`, replaces freshness with absence
  and `∀ c ∈ base.blocks, c.root = b.root → c = b`.
  This is the local admission paragraph at bp01:591, not all transport,
  receipt, timing, or vote-cap clauses of bp00:541. DQ2 and the remaining
  run work are explicit at report:44–47, :80–82, and :170–171.

The additional **bp.activeView.v1** row is complete for the six planned
items. `Proofs/ActView.lean:54` gives membership and subset; `:59` gives
genesis/F membership; `:67` gives ancestor closure; `:76` gives antitone
restriction for fixed T and a descendant F; `:86` gives active paths;
`:97` gives persistent exclusion; `:108` and `:114` preserve other fields;
`:123` and `:132` give no veto and zero active release count for `K ⪯ F`.
`Proofs/StoreInv.lean:623` gives the FG-image equation. The invariant
premises match the table, except that `actView_blocks` itself needs none.
The genesis branch of a confirmation result uses genesis ancestry or
`actView_genesis_F`; it is not omitted from the store proof.

The **SA bridges** also have the reported scope.
`Proofs/ActView.lean:204` equates an off-gate tick to SA.clock on the
active view with cumulative blocks restored. At `:218`, the gate form
also normalizes S and appends exactly the fast set of the pre-gate view.
It requires the gate-time equations and an unsaved label; `:245` derives
the redundant arithmetic premises from the gate time. The accepted-block
bridges at `Proofs/Admission.lean:378` and `:420` take CStoreInv, hP, hacc,
and the stated same-F or moved-F condition. With moved F, they filter
the SA admission by new F and apply the three base reconcile writes.
They do not claim equality with plain SA admission after F moves.

No unreported weakening of a K statement was found. K6, K7, K9–K11 and
the full run form of K8 remain outside this library, as report:65 says.
FastOrigin is the local relation needed for K1. Its `B ⪯ F` alternative
does not itself identify a historical gate. It must not be used as a
completed proof of every clause of bp.leaseOrigins.v1 or K6.

**Model-rule check.** The following source checks found no new undeclared
divergence within the stated checked-input and scheduled-execution boundary.

- HEAD reads at `Model/Frame.lean:59–95` use receipt stamps strictly
  before the previous freeze, plus ancestors of admitted current-slot
  proposals. `storeFrame` recomputes viability inside that view but uses
  the live full-store controls. The raw merge retains unresolved votes;
  frozen support resolves against current act(Σ); carried support tests
  cumulative T. These are spec 598–614 and 1219–1302. Proposals outside
  act(Σ) remain readable through `st.proposals`.
- `proposalRows` at `Model/Frame.lean:128` uses the round window for both
  pool and block rows, removes parent-chain rows, gives the pool priority,
  and fills each decoded identity/round group to two. MetaInv supplies
  the pool bound and uniqueness. The `round?` filters already remove
  undecodable candidates, even without MetaInv. This matches spec
  544–556 and 1255–1274. The FG block keeps the full decoded ordered row
  list even when the row pool refuses a row.
- `reconcile` at `Model/Store.lean:66` deletes conflicting leases, filters
  every fast set, empties conflicting saved bodies without deleting their
  labels, and normalizes S. It keeps the cumulative trees, stamps, pools,
  proposals, and FG fields. This matches spec 874–894.
- `gateStep` and `fastSet` at `Model/Clock.lean:25` and `:14` use the active
  view, the whole-result lease veto, and the unsaved-label guard. The fast
  set contains only non-genesis prefixes passing the fast threshold. An
  empty or vetoed gate creates an empty set; slow-only renewal adds no
  member; renewal still counts if the maximum deadline does not change.
  SA.gate uses slowLeasePolicy. `leaseKeys` and
  `leaseOf_eq_deadlineOf` at `Proofs/StoreInv.lean:796` justify the one-level
  lease read. These agree with spec 754–782, subject to N2's clock boundary.
- `fgSource` at `Model/Frame.lean:178` uses only `fastWrite[rR]`, the full
  filtered tree, and a deadline strictly after now. It has no old-set,
  slow-lease, S, or root fallback. `fgInputs` at `:189` gets finality
  fields from the selected head's chain state. CStoreInv, `fgHead_stored`,
  and `fgBlockOf_spec` exclude the dummy head-field branch.
- `attest` at `Model/Frame.lean:197` calls createRow with that source and
  those head fields. The client computes finality before the height pair,
  applies the row's own lock, and returns the updated record. No source
  forces an empty height pair but does not force an empty finality pair.
  This agrees with spec 1304–1413 under DQ4's projection: T7 must sign,
  retain the record before emission, and process the own row. The omitted
  NJ component is always false in this pinned protocol; the omitted
  timeout-history set is not read by these rules.

The five declared base caches are not read by FG-SA duties or outputs.
The three auth decoders remain the only composite auth pattern matches.
Each composite API with `p : FGSA.Params` uses `p.n`; the size-polymorphic
SA/GridCO helpers do not create the old unrelated-size error.

**Non-vacuity and run premises.** Reachable has an initial constructor
and unrestricted delivery/tick constructors. CStoreInv and MetaInv have
initial proofs and separate preservation inductions. In the accepted-block
case, Inv0 comes from the pre-state CStoreInv. Metadata preservation uses
the already proved store invariant. There is no circular assumption of
the post-state invariant.

These predicates have real content. Removing genesis from the base list
violates Inv0/baseTree. A duplicate pool row violates MetaInv.poolNodup;
a stored wire with no corresponding FG block violates wireTree.
NestOK fails when F and S are conflicting branches. FastOrigin fails for
a fast member above neither a saved body nor F. ContentAgree fails for
two locally admitted proposals with the same geometry/root and different
rows. These are source deductions, not newly compiled witness lemmas.
Nontrivial reachable stores also exist: clock initial to time 12 in the
test parameters, then deliver B1, B2, B3 as in `Tests/Smoke.lean:146`.
The admission path grows T and moves F to B1; nesting is not proved only
for genesis or a stuttering model.

The four requested T7 premises are stated honestly:
ContentAgree/ContentRootInjective at report:155–165; duty-slot equality
`s = st.slot p` at :146; DQ5's unsaved-label/schedule condition at :97
and :166; and the DQ10 root limit at :163–165. Checked handler inputs,
identity binding, persistent client records, and own-row admission also
remain run obligations. Add the release ordering detail in N2.

The DQ10 example is valid: a slot-4 child of genesis has root 4, and a
slot-2 child of the formula's slot-1 child also has root 4. Different
stores can admit these different blocks. ContentAgree is false for that
pair, so the conditional cross-store conclusions do not apply. Different
row content at the same geometric block is another failure mode. The
report expressly discloses both. This does not make local K1–K4 vacuous,
and does not make every honest fork violate ContentAgree. The restriction
concerns pairs with an actual collision or content disagreement. A later
unconditional safety or liveness claim cannot remove this premise merely
because each local store is root-injective.

**Soundness and validation evidence.** The source scan, after comment and
string removal with the script's tokenizer, found no `sorry`, `admit`,
project `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`,
`opaque`, native reduction primitive, or `decide +native` in FGSA. There
are seven `decide +kernel` uses: the stP test and the six reported G6
tests. No proof-completion claim rests only on `#eval`.

All 19 library modules occur in the root imports. The 206 named theorems
in `Proofs/` have exactly 206 matching `#print axioms` lines, with no
missing or extra name. The compiled axiom scanner selects constants by
their defining module, not their namespace, and calls transitive
`collectAxioms` on every selected constant, not only on the printed list.
Its allowlist is exactly propext, Classical.choice, and Quot.sound.
Its parser and missing-name exit logic match the documented `--expect`
usage. Thus the source supports coverage of every public FGSA theorem;
the numeric compiled counts were not independently reproduced here.

The axiom check covers dependencies used by these declarations. It is
not a claim to scan every unused declaration of every imported library.
The source native scan also matters for anonymous examples. The lease
scanner checks types and values, rejects direct partial/default-policy
uses, and resets expression memoization for each owner. Its existing
negative control requires both exit 1 and the named bad call. These are
useful checks, but M1 limits their coverage. M1/M2/N1 must be kept separate
from the reported green run: that run can be true while the checks remain
incomplete.

The earlier substantive fixes are present: shared row validation; the
K1 origin form; the metadata and no-genesis-wire fields; the two-chain
cross-store export; all six active-view items; the exact block bridges;
the selector facts; and the explicit slow-policy ghostWalk_mem call.
Most G6 tests requested by both reviewers are also present. N3 identifies
the remaining part of that test request. The historical scratch mutation
results cannot be re-established from the committed source alone.

**Merge readiness.** The common ancestor with main is
`d415a7cc6b9e11906b3682efc5f36300b4adc8a5`. Main advanced during the audit;
the comparison is pinned to `3de09f008068d4db9da5e04559cac1e84f437e8d`,
which includes `a27cb92` and `00a216f`.

At that pin, only `docs/MAP.md` changed on both branches. A read-only
three-way merge reports no conflict markers. Main changed the framework
and registry part of MAP; FGSA appended its section at `docs/MAP.md:619`.
Both parts can be kept. Main's lakefile is unchanged from the common
ancestor, so `lakefile.toml:16` and `:78` are clean FGSA additions, not a
current textual conflict. Keep both the FGSA default target and its
lean_lib entry. No existing source in the 78-module project import
closure differs between the FGSA HEAD and the pinned main.

Plan 1b has not yet made its planned code changes at that pin. Its
`docs/plans/2026-09-29-phase1b-instances.md:63` and `:119` preserve the
state-function bodies, lemma statements, and module paths used here.
Its Task 0 at `:139–165` will add Kit/EngineV2 library entries and default
targets and will update MAP. Those edits can overlap future merge
locations. Retain all library entries and both documentation sections;
check the source import closure again after the engine-module moves.
The promise is an integration constraint, not proof that a future main
will build unchanged.

After the check fixes and merge, the coordinator must run the full build
and FGSA checks when the throttle permits them. This audit gives no
post-merge build result and does not authorize a merge. No other current
merge conflict or imported-API change was found.
