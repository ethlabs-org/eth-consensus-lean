**Verdict: PASS WITH MINORS. G0 may close; Task 1 may start.**

The revised plan closes the earlier blocking and major findings. Its local
invariants and proof routes are sound on paper. The cross-node results have
an explicit content premise. The plan no longer uses local root freshness
as a substitute for that premise. The six minor findings below need small
edits at the relevant task. They do not require a new design or another G0
audit.

```text
┌──────────┬───────┬───────────────────────────────────────────┐
│ Severity │ Count │ Effect                                    │
├──────────┼───────┼───────────────────────────────────────────┤
│ BLOCKING │ 0     │ None found.                               │
│ MAJOR    │ 0     │ None found.                               │
│ MINOR    │ 6     │ Small interface and document corrections. │
└──────────┴───────┴───────────────────────────────────────────┘
```

Audit: r188, 2026-09-28. This is a plan audit, not a proof certificate.
The Lean throttle blocked the one compiler attempt before elaboration.
No new signature or theorem is reported as compiled.

The only repository write is this report. No commit was made. The specific
write restriction takes priority over the general log and state rules.
There was no local `AGENTS.md` or `state.md` to read.

**Evidence and scope.** `plan:N` below means line N of
`docs/plans/2026-09-29-fgsa-model-store.md` at
`5801ce6f621313062a3bdef643bc3dd1b34657d9`, branch `fgsa-composition`.
HEAD matched this commit and the initial worktree was clean. I read the
revision-2 text and compared it with `7af69aa`, both earlier reports, and
the named Lean sources.

`R` means
`/Users/francesco/ethereum/research/async-resilient-committees/tip-stability`.
The source checks gave:

- `spec`, `R/spec/fgsa-protocol.tex`:
  `2e88481117ba3e663c559f95218ce545aba5639f201063c1942dc5599adb9787`.
- `bp01`, `R/blueprint/01-foundations.md`:
  `989289cce1d761adfae3bc91b0358ff858b59d1151678d8d99d547a08f8eb3ea`.
- `comp`, `R/codex/lean-composition-plan.md`:
  `228dbe980a2dbf6071d156725c6327925f76284445d69be030730a0671eaf309`.
- The pinned outline exists as `R/blueprint/archive/00-outline-03afa5ae.md`:
  `03afa5ae814606ac7c75525766f8b17926616a8e858b26deef1a59152fb64ad5`.
- The current `R/blueprint/00-outline.md` now has hash
  `5a89d1687ba093643cabe7e7d69e232ef7f234f1809511269a2b5e4f6925fb91`.
  Its diff from the pinned archive changes later recovery bounds and
  first-finality results. It does not change the stage-1 statements used
  here. This is source drift after revision 2, not a new foundation error.

The `eth-search` skill permits direct local reads for known authority
files. I used that route. No external research source was needed.

**Disposition of the Astra r185 findings.** “Closed” means that the change
is present in the plan body and is sufficient for implementation. It does
not mean that the proposed proof has been compiled.

```text
┌─────────┬───────────────────────────────────────────────┬────────────────────────────────────────────┐
│ Finding │ Disposition                                   │ Plan lines                                 │
├─────────┼───────────────────────────────────────────────┼────────────────────────────────────────────┤
│ B1      │ Closed; see N2 below for a rule exception.    │ 209; 1066–1156; 1293–1462                  │
│ M1      │ Closed: one body check; checked ingress.      │ 593–626; 1027–1034; 1143–1156; 1485–1498   │
│ M2      │ Closed in substance; export gap N4 below.     │ 307–313; 1818–1820; 2032–2054; 2101–2117   │
│ M3      │ Closed: local origins give K1.                │ 1511–1539; 1750–1772; 1956–1978; 2000–2004 │
│ M4      │ Closed: metadata and cumulative writes.       │ 1535–1539; 1843–1863; 2032–2044; 2069–2093 │
│ M5      │ Accepted change: direct-import boundary.      │ 204–205; 716–750                           │
│ M6      │ Closed: parser and module array corrected.    │ 836–842; 2128–2130                         │
│ N1      │ Closed: useful refusal and gate fixtures.     │ 1002–1058; 1190–1195; 1288                 │
│ N2      │ Closed: tie rule and selector obligations.    │ 1430–1435; 1979–1991; 2005                 │
│ N3      │ Closed: scheduled-input limit is explicit.    │ 1485–1494; 1630–1639                       │
│ N4      │ Old errors corrected; later drift is N1       │ 30–45; 307; 470–476                        │
│         │ below.                                        │                                            │
│ N5      │ Closed: order, ownership, sizes and G6.       │ 212–223; 430–464; 1467                     │
└─────────┴───────────────────────────────────────────────┴────────────────────────────────────────────┘
```

**Disposition of the Opus findings.**

```text
┌──────────────────┬───────────────────────────────────────────────┬───────────────────────────────────────────┐
│ Finding          │ Disposition                                   │ Plan lines                                │
├──────────────────┼───────────────────────────────────────────────┼───────────────────────────────────────────┤
│ B1; M1–M6        │ As in the Astra table.                        │ See above.                                │
│ J1               │ Closed for a v2 decode adapter; see N5.       │ 127–159; 603–685; 1127–1156               │
│ J2               │ Closed: all six active-view items stated.     │ 1568–1618                                 │
│ J3               │ Closed: accepted block, same/moved F.         │ 237–246; 1876–1905                        │
│ m1               │ Closed: exact fastSet after clockPre.         │ 1220–1243; 1555–1565; 1630–1639           │
│ m2               │ Closed: equations and acceptance sufficiency. │ 1802–1875                                 │
│ m3               │ Accepted partial change: copy the tests.      │ 319; 329; 1097–1105; 1143–1156; 1823–1828 │
│ m4               │ Closed: local and run root tests separated.   │ 308; 1831–1833; 1993–1994                 │
│ m5               │ Closed: genuine once-guard explained.         │ 315; 1214–1218                            │
│ m6               │ Closed: extra SA caches declared.             │ 216; 318; 891–900                         │
│ m7               │ Closed: collision and conditional scope       │ 320–325; 1406–1414; 2208–2210             │
│                  │ stated.                                       │                                           │
│ m8               │ Closed: greater-root tie rule; see N6.        │ 328; 1283–1285; 1430–1435; 1982–1987      │
│ LeasePolicy trap │ Correct for dependent lemmas; see N3.         │ 214; 1549–1552                            │
└──────────────────┴───────────────────────────────────────────────┴───────────────────────────────────────────┘
```

The other review notes are also addressed. Selector soundness is explicit
at `plan:1792–1800`. The inherited `σ.nj` and `Λ.timeouts` reductions are
recorded at `plan:293–299,1456–1462`. The script-header exception is at
`plan:208`. The FG version bridge is at `plan:43`. DQ4 still requires the
record/emission order and own-row processing in T7 (`plan:314`). DQ7 still
reserves the run form of T6 for T7 (`plan:98,317`).

**The two changed dispositions are acceptable.**

For Astra M5, the original report allowed either local proofs or a disclosed
change to the import boundary. Revision 2 chooses the second route. The
source graph does reach `AvailableChainStatements.Generic.Claims` through
GridCO proofs. The phase-1a plan forbids changes to that library at its
line 65. The closure check found no Framework, Registry, SAPC or Witnesses
module. Reusing these proofs adds no axiom assumption by itself. The
transitive axiom scan still checks the actual proof dependencies. This
route is sound for the stated boundary; it does not prove independence
from every future change to Statements.

For Opus m3, keeping the syntactic tests in `blockAccepted` is useful.
`Reachable` admits unchecked wires, so removing these tests would weaken
the local induction. Copying them into `wellFormed` preserves behavior on
checked inputs and gives the stated refusal classification. Under the
flat wire representation, the parent slot is already available. On a
valid full-content input, the stored parent has that same meaning. A
missing parent still prevents admission. The extra ingress tests do not
exclude a proposal that could later pass the specified acceptance tests.

**Content agreement and K5.** The statements at `plan:2101–2114` follow
from the stated hypotheses. For equal erasures of two stored nodes, their
parent erasures agree. Parent closure makes both parents available to the
induction. `stored_wire_of_block` and `ContentAgree` then give the same
ordered signed row list at the two nodes. Its projection gives the same
FG rows. Equal parents, slot, root and rows give equal FG blocks.
Genesis is the base case. For reflected ancestry, select the corresponding
ancestor in the other stored path and apply this equality result.
Compatibility follows in both directions; the content premise is symmetric
because payload equality is symmetric.

`MetaInv.wireTree` and `treeWire`, together with local root injectivity,
are enough for this argument. A second stored wire for one erased block
would violate `treeWire`; a new accepted wire cannot name an old block
because its root is fresh. No extra metadata field was found necessary.
`toRow_forall₂` preserves positions, including repeated row occurrences.
It needs only successful decoding; checked row bodies remain a separate
T7 ingress obligation. The projection intentionally removes rounds from
FG rows, while the original signed list retains them.

The run premise at `plan:309–313` has the right declared scope: genesis,
every processed or emitted proposal, honest or faulty, and all parent
paths. T7 must define this premise on full content, including the content
of ancestors. Geometric `BlockInRun` and erased `RootInjective` alone do
not supply it. The present store-pair results do not claim to prove that
run premise. Add the explicit two-chain export in N4 below to complete
the public K5 interface.

**FastOrigin, fastDom and K1.** The proof route at
`plan:1511–1539,1750–1772,1956–1978` is valid. At a fresh gate, the new
fast set consists of prefixes of the saved confirmation. `fastDom` makes
its label distinct from all existing fast-write labels. Other saved
bodies remain unchanged. A repeated gate changes neither map.

During reconciliation, take a retained B below a saved C. If C remains,
the first origin alternative remains. If C conflicts with the new F,
retention makes B compatible with F. The alternative F ⪯ B would imply
F ⪯ C, a contradiction. Thus B ⪯ F. If B was already below an older F,
local F monotonicity gives B ⪯ new F. This proves preservation even after
the original saved body was emptied.

K1 then needs compatibility of leases, nonempty saved bodies and S with
the new F. It needs no independent compatibility assumption on fastWrite.
The block-step theorem transfers the invariant to the state just before
reconcile because block admission changes neither genuine nor fastWrite.
The new result works even when F stays fixed; its stronger applicability
is harmless. No fault bound, synchrony premise or safe-finality premise
is needed for these local arguments.

**Metadata and active-view facts.** `MetaInv` supplies the admitted-wire
relation, ordered rows, unique proposal, block/stamp key correspondence,
and decoded, duplicate-free row pools with a two-row cap. The base's
initial block list and block-stamp keys are both `[genesis]`
(`AvailableChainGridCO/Model/Protocol.lean:98–118`). Accepted admission
appends one block, stamp and proposal; carried votes only append vote
stamps. Reconcile preserves these fields. `process_cumulative` preserves
old entries in order, and `clock_cumulative` preserves the lists exactly.
Together with the first-match stamp lookup, this preserves every existing
stamp. The lease and genuine key fields in `CStoreInv` are preserved by
filtering, key-preserving maps and guarded insertion.

All six `bp.activeView.v1` items are now stated at `plan:1571–1607` and
match `bp01:261–286`. In particular, an active resolved head is comparable
with any K ⪯ F. Therefore no such head contributes to release against K,
and a lease on K cannot veto an active result. These two statements do
not need a scheduled-clock premise or a store invariant. The tree
membership and closure statements correctly use `CStoreInv`.

**SA bridges, decoding and admission.** The same-F block bridge is valid:
an accepted fresh block strictly extends the old F, so its stored parent
is active. GridCO admits it on either base list. Filtering commutes with
the appended block, and carried-vote admission reads no block list.
When F moves, monotonicity gives the second filter, and reconcile gives
exactly the three base-field changes in `plan:1896–1901`. The row fold
changes only the composite row pool. These are accepted-step bridges;
they do not assert equality of the two handlers on every refused wire.

`clockPre` copies the pre-gate GridCO order. Its changes to time, expiry,
freeze, early and release do not change genuine or fastWrite. Thus the
fresh-label premise on the original state is enough. The exact fast set
must be taken after `clockPre`, as `plan:1636` now does. At d_s, the early
step for s+1 can run; freeze and release cannot run at that same time.
The arbitrary-clock bridge is an algebraic comparison with SA code.
Exact simulation of the spec's release cutoff still needs T7's scheduled
event order, as the plan states.

The decoders consistently return the label, seat and body. Standalone
and carried rows apply the same `RowBody.valid` test. `baseHead` maps a
wrong carried-vote auth to `.none`; checked proposals exclude that case.
The calls that use `p.E` now all have `Fin p.n`. I found no new dependent
committee-size mismatch on source inspection. N2 concerns an internal
rule conflict, not a failed application.

`admitBlock_sufficient` is sufficient as stated. Parent membership supplies
the FG parent. Freshness implies b is absent and b differs from stored F.
Hence erased F ⪯ b implies erased F ⪯ parent(b); local reflection gives
the FG acceptance relation. `wellFormed` supplies the remaining syntactic
tests. For later use of an *absent* block, T7 must derive the fresh-root
premise from the run root premise. Absence alone cannot do this outside
that input universe.

The `deepest` implementation uses the specified depth/root order. A
nonempty subset of a root-injective tree has one maximum, so the stated
selector theorem is valid. `fgHead_stored` also has a viable route: GHOST
returns the anchor or a tree member, and both are stored. The axiom command
uses one `--expect`; the changed top import, module array and module-prefix
test match the scanner at `scripts/CheckFGAxioms.lean:30–72`.

**DQ10 and risk R9.** Keeping the arithmetic root is sound for this T3–T6
scope, with the stated limit. The local store invariants do not assume
collision freedom of all inputs: they refuse a reused root. K1–K4 and
the stored nesting result therefore do not become vacuous because an
input collides. K5 across stores is explicitly conditional on content
agreement.

The two arithmetic examples at `plan:320–324` are correct: the fork has
roots 4 and 4; the slot-8 child of root 7 has root 64. A same-erasure
proposal with different rows or base lists can also violate full-content
injectivity without violating geometric root injectivity. The arithmetic
problem is inherited from GridCO. The full-content premise is an
additional FG-SA restriction, explicitly declared by DQ3; inheritance
does not prove that restriction.

Later safety and liveness theorems that assume either run root premise
say nothing about executions that violate it. Thus this plan cannot
support an unconditional claim about all honest executions, or all
adversarial choices within a fault bound. The plan now says so. A new root
encoding is not necessary to prove these local or conditional statements.
It would be necessary to remove this coverage restriction. No root
construction change is authorized or required by this audit.

**N1 — MINOR: update source and audit references.**

Evidence: `plan:30,45,326,470–476,2151–2152`.
The current outline path no longer has the recorded hash. Either cite the
verified `03afa5ae` archive as the fixed source, or record the new current
hash and the diff described above. Preserve Task 0's hash check. The
second-report path still says `fgsa-model-store-plan-audit-2.md`; this job's
required path is `fgsa-model-store-plan-reaudit-report.md`. Record this
report and map its `PASS WITH MINORS` verdict to G0's older `ADOPT WITH
FIXES` terminology. These are record corrections; the foundation content
has not changed.

**N2 — MINOR: reconcile M11 with the size-polymorphic fast-set helper.**

Evidence: `plan:209,1203,1563,1467,2172`.
`fastSet` and `fastSet_prefix` still have free `{n : Nat}` next to
`p : Params`. This is legal: `SA.confirmation` and `SA.prefixSupport`
permit an independent state size, and these helpers do not apply `p.E`.
It is not the earlier B1 error. It does contradict the blanket rule and
the stated checkpoint rejection. Either use `GridCO.State p.n` in these
two signatures or document this helper exception. Keep all composite
handler and FG calls indexed by p.n.

**N3 — MINOR: use the explicit lease policy only when the declaration has it.**

Evidence: `plan:214,1479,1549–1552,1917`.
Line 214 overstates the rule when it identifies declarations by the
surrounding `variable [LeasePolicy]`. Lean omits an unused section
variable from a declaration. For example, `GridCO.admitVote_blocks`
(`Proofs/Map.lean:443–447`) and `GridCO.confirmation_mem`
(`Proofs/RecordSlots.lean:150–161`) have no policy argument. Passing
`GridCO.slowLeasePolicy` as their first explicit argument would pass it
where a `GridCO.Params` value is required. In contrast, `gate_blocks`
and `gate_target_origin` do depend on the policy.

Use the precise rule already given elsewhere in the plan: inspect the
actual declaration, and supply `slowLeasePolicy` for each lease-dependent
application. The explicit `saGate_blocks` route is correct. This wording
fix prevents an implementation type error; it does not change a theorem.

**N4 — MINOR: export the cross-store two-chain root premise.**

Evidence: `plan:824–827,2018,2098–2117,2134`; `bp01:76–78`.
Task 2 exports `KitFG.RootInjectiveOn` only for two tips in one view.
Task 12 exports cross-store equality, ancestry and compatibility, but
omits the named two-chain corollary required by `KitFG.accountable`.
The hypotheses are now sufficient, so this is a small interface gap,
not the old M2 proof gap.

Add `rootInjectiveOn_across` with the same two `CStoreInv`, two `MetaInv`
and `ContentAgree` premises, and stored tips B₁ and B₂. Its conclusion is
`KitFG.RootInjectiveOn B₁ B₂`. Ancestor closure puts each compared ancestor
in its tip's store. For ancestors in one store, use local root injectivity.
For ancestors in different stores, handle genesis with local injectivity;
otherwise use their stored wires and equal roots to obtain equal payloads,
then use `fg_eq_of_eraseFG_eq_across`. Add the name to the K5 handoff table.
No stronger content premise is needed.

**N5 — MINOR: limit the v2 preservation promise to the adapter route.**

Evidence: `plan:135–144,647–649,1066–1067,1122,1402–1404,2211–2212`.
A v2-to-v1 adapter can preserve this store and these proofs. The alternative
claim that retyping the wire objects changes only Objects and its decoders
is too strong. Handlers still construct `.seat s i` and `.proposer s`
wires, and `proposalRows` compares `.auth` values. The SA base also stores
v1 wires. A native retyping can require changes at these constructors and
proofs, even though auth pattern matches are now centralized.

State that the adapter route preserves the internal API. Leave the scope
of native retyping to T7. This does not reopen the engine choice or prevent
Task 1; it corrects the future-work guarantee in the J1 disposition.

**N6 — MINOR: include the empty-set case in the deepest documentation.**

Evidence: `plan:328,1430–1435`.
`deepest ∅ = none`. For a nonempty set, `none` occurs when distinct
maximal candidates share both depth and root. A tie between non-maximal
members does not cause failure. State these cases in the docstring.
The implementation and the `X.Nonempty` premise of `deepest_spec` are
correct and need no change.

**Validation and limits.** I checked the source signatures, gate policy,
proposal and vote writes, stamp lookup, ancestry interfaces, both audits,
and the plan diff. I also ran the plan's closure loop on the cited GridCO,
SA and KitFG module roots from the worktree root. It exited 0 and reached
Statements, with no module from the four forbidden closure libraries.
The scratch script and trace are `/private/tmp/r188/closure.sh` and
`/private/tmp/r188/closure.log`. This validates the closure loop against
the current source graph; it is not a run of the future complete check
script, build or axiom scanner.

The one Lean probe is `/private/tmp/r188/Signatures.lean` (287 lines).
It extracts the proposed Objects, store, handlers, clock, FastOrigin,
CStoreInv, MetaInv and ContentAgree definitions. It includes the risky
row-position, checked-acceptance, acceptance-sufficiency, moved-F bridge
and cross-store equality signatures, plus the corrected controls call.
The theorem bodies are temporary `sorry` placeholders for elaboration
only. They are outside the repository and are not proof evidence.
The command was run from this worktree:

```text
lake env lean /private/tmp/r188/Signatures.lean
```

The throttle reported `Operation not permitted` on its shared slot locks
and history file under
`/Users/francesco/ethereum/lean/decoupled-consensus-model/collab/orch/locks`.
`pgrep -fl lean` could not read the process list. I interrupted the waiting
command; exit 130. I did not bypass the throttle or request broader access.
No elaboration result, build pass or axiom-scan pass is claimed. The
implementation checkpoints must supply those checks. The user explicitly
allowed this audit to continue on paper if the throttle blocked it.
