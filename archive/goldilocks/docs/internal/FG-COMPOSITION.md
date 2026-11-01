# FG composition registry (v2, 2026-09-28)

_Owner: the async-resilience session (research). ethereum-f1 keeps this file
consistent with FRAMEWORK-DESIGN.md §7._

## 0. Registry policy (audit W08)

- Each entry PINS its statement and its hypotheses. The pinned text is an
  exact copy of the cited source lines. It does not change when the source
  changes. Links inside pinned text are relative to `tsc/`.
- Each entry names its module variant: `nj` (`SimplexFG.nj`, DC's NJ rule),
  `fj` (`SimplexFG.fj`, the FJ root rule), or `both`. An AP-side entry names
  the variant whose frame its premises use.
- Each entry names its source file, section and line range, and the SHA-256
  of that source file at registration (§0.1).
- A change of statement or hypotheses gets a new id. The old id stays, with
  the status WITHDRAWN. Ids with an unchanged statement stay.
- The status is a dated line. A later status change adds a new dated line
  below the old one. It does not change the pinned statement.
- Status values: LEAN (a Lean certificate); PROVED (a paper proof from the
  pinned hypotheses); PROVED* (a paper proof, conditional on the listed
  unproved entries); SKETCH (a proof with an identified missing step); OPEN
  (no proof and no refutation); REFUTED (a counterexample); RULE (true by
  the honest code, not a theorem); def (a definition); WITHDRAWN (no
  composite may cite the entry); SUPERSEDED (the entry stays as a pointer;
  its pinned text does not change; a composite cites the named successor
  ids, whose conjunction states the same fact).
- Lean coverage kind (rule added 2026-09-28; text corrected the same
  day): BY HYPOTHESIS = the Lean theorem assumes, as a named premise, a
  statement equivalent to the clause (or to the clause's key step); the
  entry names the discharging ids. It differs from PARTIAL, where Lean
  derives the clause from extra premises. It is a coverage note, not a
  status value.
- Two edits of a hypotheses list keep the id, with a dated note: (a) the
  replacement of a SUPERSEDED id by its successor ids; (b) a new reference
  by id to a fact that the pinned text already uses (for example "F4" or
  "finalized crossing"). Any other change of hypotheses gets a new id.
- Pins to spec text resolve against `spec/archive/` by hash (rule added
  2026-09-28): a pin to `spec/<name>.tex` with sha256 h refers to
  `spec/archive/<name>-<first 8 hex digits of h>.tex`, whose sha256 is h.
  The spec owner archives each registered spec version there before an
  edit. The live `spec/` file can differ.
- Research sources are archived by hash (rule added 2026-09-28): at
  registration, the registry owner copies each pinned research source
  that is not in Git to `<dir>/archive/<name>-<first 8 hex digits of
  sha256>.<ext>` (for `tsc/`: `tsc/archive/`) and checks its hash. Pins
  resolve against the archive copy with the registered hash, not against
  the live file. A source in Git is recorded with its commit instead.
- "FG-SA" in a status means a proof for the FG-SA client, that is, the
  Simplex policy with honest non-equivocating signers. As a certificate
  FAMILY over every policy σ, an AP-side entry still needs a proof that uses
  only frame conditions and AP facts (FRAMEWORK-DESIGN.md §7.3, audit W02).
  [async] An entry that states FG height progress is never a family entry;
  it holds for the Simplex policy only.
- AP-side ids (`ap.*`) state only AP SERVICE facts: repair, common fresh
  sources, row service, block retention and source safety
  (FRAMEWORK-DESIGN.md §7.3, audit W02). A height rise, an FG entry law or
  a record permission is a `comp.*` or `fg.*` entry, derived after
  specialization to the Simplex policy.

### 0.1 Sources

`tsc/` = `research/async-resilient-committees/tip-stability/codex/`. [async]
`r146` = `fgsa-adj` of v1. Section numbers and line ranges replace the v1
line numbers. `r144o` is the Opus variant of r144. `r151` is `fj-theorem-h.md`.
`ldp` is `fgsa-live-dc-port.md` (ALFS proofs), `r157` is
`fgsa-live-views.md`, and `h12` is `fj-h12.md` (all registered and archived
2026-09-28). `r158` is `alfs-redteam.md`, the independent red-team of
ALFS (registered and archived 2026-09-28). `r159` is `alfs-fixes.md`, the
ALFS fixes and vote-merge proof check (the spec cites it as FIX;
registered and archived 2026-09-28). `r160` is `receipt-relay.md`, the
receipt-relay audit (the spec cites it as RR; registered and archived
2026-09-28). `r161` is `filtered-base.md`, the filtered SA base (the spec
cites it as FB), and `r163` is `spec-filtered.md`, the report of the
spec edit a3e12c57 (both registered and archived 2026-09-28). `r152` is `fj-first-finality.md`, `r153` is `fj-reach.md`, and `r153a` is
the Opus adjudication of r153, `fj-reach-adjudicate.md` (verdict VALID WITH
CORRECTIONS; registered 2026-09-28). `r153b` is a later version of the same
file, with §§A–C; §C.4 retracts the NJ claim of r153a. Line numbers cited
as r153a refer to the r153a version (sha256 `c85c0dcc…`), which is not
archived; the live file is r153b.

Archive (2026-09-28): every `tsc/` file in the table above is copied to
`tsc/archive/<name>-<hash8>.md`, with its hash verified (for example
`tsc/archive/fj-redteam-934fe292.md`). r153a cannot be archived: the
adjudicator edited the file in place, and the `c85c0dcc` version is lost.
r153b is archived as `tsc/archive/fj-reach-adjudicate-12afc81c.md`.
`dc/consensus.tex` is in the research Git repository (commit `9f5ed71`,
file unchanged at that commit); Git keeps the registered version.

```text
┌───────┬───────────────────────────┬──────────────────────────────────┬──────────────────────────────────┐
│ Key   │ File (tsc/)               │ SHA-256, first half              │ SHA-256, second half             │
├───────┼───────────────────────────┼──────────────────────────────────┼──────────────────────────────────┤
│ r143  │ fgsa-fast.md              │ 8907540c5c71fe06703bc8d2ec2d30bc │ 6cbc752a5f7577219a69196e2fd8ef37 │
│ r144  │ fgsa-no-nj.md             │ 1eaf728ffc4d56cc54fbccf581a8dffe │ 457da02b96bd59cedb012bbf5ee1e03a │
│ r144o │ fgsa-no-nj-opus.md        │ 7df2a540134deddede78ea711754bb32 │ 2911fced62271868f8b5034164db9f4e │
│ r146  │ fgsa-adjudicate.md        │ 0fe1717f6abbf0d708cada05a8a4d3e3 │ 431a530d3d5c3a65e86bf755f5642017 │
│ r147  │ fgsa-conditional.md       │ 940e481501f8c52f57bd7110faa442b5 │ 4ce4aa3bb512769a07c9b769037ea0f5 │
│ r148  │ fj-redteam.md             │ 934fe2927f047a11e37dbe52aba9d754 │ d5c461927f24b91902077f17459d47d2 │
│ r149  │ fgsa-conditional-close.md │ 1ea1ccc5c944335b7e7793afe2c6675a │ 056762e35eeaeee13ec1f6066460a902 │
│ r150  │ fgsa-theorem-h.md         │ 8211361a618814fa4d5f4b1a3c593943 │ 380c9ccb99235e8b9c413d633876adc3 │
│ r151  │ fj-theorem-h.md           │ 16b69dba55d889b9ae20dd55b228cfd8 │ 3ad22037d796c6219cdb65831718bba3 │
│ bp    │ fgsa-healing-blueprint.md │ 4d643d7a6285705ef8bcef6b408b46a4 │ 5d64641f0d92828b3539f8f938074318 │
│ sa    │ slow-arming.md            │ c1d1a4e343c6910a1072cc7e6e8816b6 │ ab6ac94b4940f204573f3a39c500db0b │
│ r152  │ fj-first-finality.md      │ d659d585ccb1a4f47ee90c6de68515cb │ fd9685f47a2764fc8ff153a0c60edb8e │
│ r153  │ fj-reach.md               │ 13843848471ae2955351c08a64cdc27a │ 0a9f34ad8d5f1b7af5f4f427de70a7b1 │
│ r153a │ fj-reach-adjudicate.md    │ c85c0dcc5c325ac0ca5ed5cc9ae5e85d │ 20d3c3aa686d6146f31adacd0d773749 │
│ r153b │ fj-reach-adjudicate.md    │ 12afc81c0e98a53366f13e2109839741 │ 84d5c1675226ec79e99ae85e83b4a47f │
│ ldp   │ fgsa-live-dc-port.md      │ 816776723e439f24612c409f2007c2a2 │ 36bb3fa2dbde605c68516333ee4c7b38 │
│ r157  │ fgsa-live-views.md        │ 5070acb6d1697fade725cb4fdb07850c │ aa91ee552b330e3bf9bbd8ace2a0d8df │
│ h12   │ fj-h12.md                 │ 26c13e92b8bfe62422e00af91f8878f1 │ 2b0b7efdc66d67d7f9b857db99b9bbd7 │
│ r158  │ alfs-redteam.md           │ f1ddd1a8863ac8f5443146bb901608a8 │ 32cb939fe2a0263de6cce5549f409c06 │
│ r159  │ alfs-fixes.md             │ 4587052c1c11165ed24e9c7c7bf2213c │ ece57be408547e639e7641023521a0fd │
│ r160  │ receipt-relay.md          │ a64d25b1623e57d68c30dbb77739e983 │ aca7fdde9f169c04c1471be9828a06dc │
│ r161  │ filtered-base.md          │ fd8e07fe667afae28dee2bc9a54d6c7f │ c46b49f9bb268865f98818decc308354 │
│ r163  │ spec-filtered.md          │ 84923d9d827cd3428f63998d09d5c8fd │ 00c04fd84604426a78c46f196dc63159 │
└───────┴───────────────────────────┴──────────────────────────────────┴──────────────────────────────────┘
```

Sources outside `tsc/` (registered 2026-09-28). `spec/` =
`research/async-resilient-committees/tip-stability/spec/`. `dc/` =
`research/healing/rewrite/`. `vc/` =
`lean/decoupled-consensus/verified-consensus/` at commit `b97b902`. `ac/` =
`lean/available-chain/` at commit `ae2a9d3` (the SA Lean model; the file is
unchanged since `588d666`). `alfs` is the ALFS spec (the DC-form rewrite),
registered 2026-09-28 from its archive copy; a pin to it names the file
`fgsa-protocol-183f2c40.tex`. "Under ALFS (spec 183f2c40)" in a status
line means the protocol of that spec. `alfs2` is the ALFS spec after r159
(the admitted-proposal HEAD vote merge, the δ_t scope, §5 row 29 on
relay, the bounds 996Δ and 1041Δ, no NJ appendix), registered
2026-09-28 from its archive copy; a pin to it names the file
`fgsa-protocol-c7c41a43.tex`. "Under ALFS (spec c7c41a43)" means that
protocol. `alfs3` is the ALFS spec after r160 (DC's receipt premise in
place of accepted-object relay; §5 row 29 class (b); the OPEN item "SA
Lean under the receipt premise"), registered 2026-09-28 from its archive
copy; a pin to it names the file `fgsa-protocol-1c6952b6.tex`. "Under
ALFS (spec 1c6952b6)" means that protocol. Re-pin rule (2026-09-28): the
live entries that pin ALFS text pin the newest registered ALFS spec.
Historical entries keep their pins: `ap.headReachesLo.v2` (`alfs`),
`ap.headReachesLo.v3` (`alfs2`), `fj.frame.v2` and
`ap.headReachesLo.v4` (`alfs3`). Pins to `spec` stay. `alfs4` is the
ALFS spec with the filtered SA base (user decision 2026-09-28; r161):
Σ.T is DC's cumulative admitted tree, `on_block` refuses `F ⋠ B` before
it unpacks the block, the SA base reads the active view act(Σ) (the
blocks compatible with F), `reconcile_with_finality` runs on each F
advance, and there is no raw tree. It is registered 2026-09-28 from its
archive copy; a pin to it names the file `fgsa-protocol-bd942ca0.tex`,
and "under ALFS (spec bd942ca0)" means that protocol. The live entries
`fj.frame.v3` and `ap.headReachesLo.v5` pin `alfs4`. The intermediate
version a3e12c57 (r163's edit, which deleted blocks from Σ.T; sha256
`a3e12c57e63f010b49b01d0935d150bbc95f884dcd456505f602f11efe55bf98`) is
archived as `spec/archive/fgsa-protocol-a3e12c57.tex` as history only.
No entry pins it.

FG-SA sources (registered 2026-09-29). `fgsa1` is the FG-SA spec (plain SA
available chain + DC finality gadget, FJ root rule only), registered from
its archive copy; a pin to it names the file `fgsa-protocol-2e884811.tex`.
The FG-SA Lean model (branch `fgsa-composition`) anchors its docstring
spec lines to this file. `fgsa2` is the adopted FG-SA spec (weak healing
and finality premises, H2′, the section "Leak identification"), registered
from its archive copy; a pin to it names the file
`fgsa-protocol-dbcb7f05.tex`. Its protocol section, preamble and Relay
paragraph are byte-identical to `fgsa1`; the change record is
`spec/archive/CHANGES-2e884811-to-dbcb7f05.md`. New recovery and leak ids
pin `fgsa2`. The live FG entries keep their pins (`alfs4`, `spec`); no
entry is re-pinned.

Re-pin (registered 2026-09-29). `fgsa3` is the adopted FG-SA spec
c1ea1db0, registered from its archive copy; a pin to it names the file
`fgsa-protocol-c1ea1db0.tex`. Against `alfs4`, the Trees paragraph
changes: no rule deletes a block of Σ.T, the SA confirmation walk starts
at Σ.F, and the inactive-block threshold is the entry height of the
accepted finalization. The protocol functions that the FJ frame pins
(`on_block`, `update_finality`, `reconcile_with_finality`, `fg_contest`
to `get_filtered_block_tree`, `live_root`, `get_head_in_tree`, the voter
trees and the HEAD duty call) are byte-identical, at new line numbers.
The intermediate spec 4e85ff34 is not registered. Its change record to
`fgsa3` is `spec/archive/CHANGES-4e85ff34-to-c1ea1db0.md` (the pre-GST
delivery clause and the healing-interface names). The blueprint cites
4e85ff34 line numbers: line L of 4e85ff34 with 200 < L ≤ 1888 is line
L+9 of `fgsa3` (diff hunks `199,200c199,209`, `1888a1898,1899`, and
later hunks after line 2029). `fj.frame.v4`, `fg.finalLock.v2`,
`fj.descent.v2`, `fj.twoChanges.core.v2` and `ap.headReachesLo.v6` pin
`fgsa3` or the adopted blueprint. `blueprint/` =
`research/async-resilient-committees/tip-stability/blueprint/`; the
keys `bp00`, `bp01` and `bp21` are its archive copies (the adopted
blueprint of 2026-09-29).

Note (2026-09-28): `spec/fgsa-protocol.tex` is not tracked in Git. It
changed after registration (sha256 then
`bc093836f57fd6decbf5d743afa0c4b14061d3e589e1cef83d58708ae35fec10`: `R ≥ 2`
as a parameter, a latency sentence and the δ_t range, which moved later
lines by +5). Every spec pin and spec line number in this registry refers
to the registered version `ae4497ab…`, archived as
`spec/archive/fgsa-protocol-ae4497ab.tex` (sha256
`ae4497abc7c5b3a6f73697f341bf730a63c7d34bd2f7546154bd022bc95af223`,
verified 2026-09-28). The spec will change again (FV, r154); the pins are
not re-pinned now. A citation of the form "spec/fgsa-protocol.tex, lines
…" in an entry means the archived file.

```text
┌───────┬──────────────────────────────────────────────────────────────────┬──────────────────────────────────┬──────────────────────────────────┐
│ Key   │ File                                                             │ SHA-256, first half              │ SHA-256, second half             │
├───────┼──────────────────────────────────────────────────────────────────┼──────────────────────────────────┼──────────────────────────────────┤
│ spec  │ spec/archive/fgsa-protocol-ae4497ab.tex                          │ ae4497abc7c5b3a6f73697f341bf730a │ 63c7d34bd2f7546154bd022bc95af223 │
│ alfs  │ spec/archive/fgsa-protocol-183f2c40.tex                          │ 183f2c409f03542dbdf3f94619240774 │ 37710b74720d09b32a42d3bdb3f04afb │
│ alfs2 │ spec/archive/fgsa-protocol-c7c41a43.tex                          │ c7c41a43727d380b74ae835032edbc97 │ 75ac98b8faa18affd5670165f841e5ca │
│ alfs3 │ spec/archive/fgsa-protocol-1c6952b6.tex                          │ 1c6952b6e6ef92bf9111121f0fb28367 │ 1af6ce936b6db3c33d056b9dda35ffcd │
│ alfs4 │ spec/archive/fgsa-protocol-bd942ca0.tex                          │ bd942ca0bce0b4251b969a503a8c8175 │ db87494ab93bf028e3a2303b7683dda7 │
│ fgsa1 │ spec/archive/fgsa-protocol-2e884811.tex                          │ 2e88481117ba3e663c559f95218ce545 │ aba5639f201063c1942dc5599adb9787 │
│ fgsa2 │ spec/archive/fgsa-protocol-dbcb7f05.tex                          │ dbcb7f05106cff51070fc767de45e3fe │ df45d0c74c8b5aeeca794a6110978864 │
│ fgsa3 │ spec/archive/fgsa-protocol-c1ea1db0.tex                          │ c1ea1db08f1da37bcde075df5d70f23a │ f7c9941bd05ae5e8aca1bb48d1b777ed │
│ bp00  │ blueprint/archive/00-outline-e6dcbcc1.md                         │ e6dcbcc1859dca4e9f30f7f947b6608a │ c4e1ab55b99cd1c562bd1f827965647d │
│ bp01  │ blueprint/archive/01-foundations-200c9c07.md                     │ 200c9c07a01bd5826750d0e89a985be8 │ 7e588f98132a68534cdd719531302a99 │
│ bp21  │ blueprint/archive/21-healing-9b7f5af8.md                         │ 9b7f5af8d013a473f9c5361f72377df6 │ 3f79728599e02d0b9414cd58789c3ac9 │
│ dc    │ dc/consensus.tex                                                 │ dc471b47a46896fe0a3df300c188fef1 │ 512f475615ce0fc0df18dbea6d2e5517 │
│ vcE   │ vc/DecoupledConsensusProofs/Protocol/ValidatorClient/Engine.lean │ 92fb0e64c1288afea98b53212cb3ad5c │ 843c9c720187367eea578d17a9d53454 │
│ vcF   │ vc/DecoupledConsensusProofs/Protocol/ChainState/                 │ aa0ed92740eb1ec8ee69e90fd2ae75f0 │ 3179a27c05accf5f631e7a254589b94c │
│       │   FinalityComparison.lean                                        │                                  │                                  │
│ vcW   │ vc/DecoupledConsensusProofs/Protocol/ValidatorClient/            │ f0d45fa7fd93a0a1c9f4dfccaf6c3f7c │ 63c43245c5deee7182a25f3963c22b5d │
│       │   WeakHeightBounds.lean                                          │                                  │                                  │
│ acG   │ ac/AvailableChainGridCO/Model/Protocol.lean                      │ f2e8afcecfe06101852ddddb2b0002a7 │ 64982d34413edcac0f958dc7934b86bc │
└───────┴──────────────────────────────────────────────────────────────────┴──────────────────────────────────┴──────────────────────────────────┘
```

### 0.2 Pinned premise sets

Entries cite these sets as hypotheses. Each set is an exact copy.

**`env.r147`** — r147 §1, lines 36–101. File `fgsa-conditional.md`, sha256
`940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.

> _fgsa-conditional.md, lines 36–101:_
>
> Use a valid, reachable FG-SA execution, starting with the specified
> initial state. An arbitrary pre-GST execution is permitted. Arbitrary
> independently assigned S records, leases, or Λ records are not permitted.
> There are n base seats per label and n unit-weight FG identities, as in
> the two rule documents. The same static faulty set has size a. Counts
> at different base labels are never added.
>
> ```text
> h = n−a;             f = (n−1) div 3;
> τ = (n+1) div 2;     q_F = (2n+2) div 3;
> a ≤ f;              h ≥ q_F ≥ τ;       h > 2a;
> 2q_F−n > a;         τ > a.
>
> Δ > 0; k ≥ 2;       L = (4k−1)Δ;
> t_s = 4sΔ;          v_s = t_s+Δ;
> e_s = t_s+2Δ;       z_s = t_s+3Δ;
> q_s = t_s+5Δ;       d_s = t_s+6Δ;
> P = 4RΔ; R ≥ 3;     T_r = rP; a_r = T_r+6Δ = d_(rR);
> δ_t = 2R slots;     ρ = 2L+G+8Δ;
> σ = (g+3)P+G+6Δ;   B_static = ρ+2σ.
> ```
>
> The following premises apply through every time used in a conclusion.
>
> 1. All honest validators participate after GST. Each has one HEAD per
>    scheduled label and one FG action per scheduled round. They process
>    clocks and receipts as specified. Honest identities do not equivocate.
> 2. Post-GST messages and accepted complete dependencies have strict Δ
>    delivery and relay. The return-relay condition covers objects already
>    accepted at GST. An emission is not a receipt, even at the sender.
> 3. Blocks and signatures are authentic. Parents have smaller slots.
>    Roots identify blocks uniquely. Views have the specified ancestor
>    closure. Original declared support subsets remain unchanged. A later
>    path receipt does not convert a raw-only declaration into support.
> 4. For (L), an awake honest proposal occurs strictly after each relevant
>    trigger and within G. Also use Rec(g): every inclusive round window
>    `[r,r+g]` contains an honest opening whose next two **slot** proposers
>    are honest. Use the rule documents' `g≥3`. The full window and every
>    gate used must fit in the horizon. Strong recurrence for first finality
>    is not used here. Neither K nor the debt parameter D enters (L).
> 5. Honest proposals include the specified current-window rows from the
>    pool and from held current-window blocks, except rows already on the
>    parent chain. Use `w_F≥1`, full-row deduplication, and distinct FG
>    identities. A faulty carrier may use old authentic rows. Stored
>    progress bits persist until that chain advances height.
> 6. The source at action r is exactly the deepest member of
>    `FastWrite_i[rR] ∩ D_action` with a live deadline. An empty latest gate
>    does not fall back to an earlier gate. Targets, repeats, and timeouts
>    all use this source. The finality pair instead uses the actual full-view
>    finality head. Its own finality pair overrides the lock at the same
>    height before the height-pair branch is evaluated. Λ persists.
> 7. R1 is used at every duty. Gates, saved raw results, resolution, and
>    release remain unfiltered. The whole-result S guard tests all live
>    leases, including excluded leases. Only a successful guarded gate
>    writes S and leases. Finality does not assign to S.
>
> For (S), a synchronous source label means that its complete SA delivery,
> return-relay, and late-test premises hold. `t_s≥GST` is a sufficient
> condition. The claim is not based on `a_r≥GST` alone. The proof needs the
> same receipt properties at each later label it uses. The SA definition
> `SynchronousLabel` explicitly includes execution, delivery, relay, honest
> majority, and horizon conditions [SA1].
>
> Full participation and `a≤f` are retained throughout this document to
> match the recovery job. The source-to-HEAD part of (S) can use weaker
> majority premises. No such weakening is needed for this interface.

**`env.r149`** — r149 §1, lines 49–79. File `fgsa-conditional-close.md`,
sha256 `1ea1ccc5c944335b7e7793afe2c6675a056762e35eeaeee13ec1f6066460a902`.
It uses `env.r147` by reference.

> _fgsa-conditional-close.md, lines 49–79:_
>
> Use [fgsa-fast §§2–4](fgsa-fast.md) and
> [fgsa-fast-opus §2](fgsa-fast-opus.md) as the FG-SA rules. Use the reachable
> execution and recovery premises of [r147 §1](fgsa-conditional.md):
> authentic objects, strict parent-slot order, full honest participation
> after GST, strict Δ delivery and accepted-object return relay, original
> declared support subsets, R1 duty views, unfiltered raw gates and release,
> the whole-result guard, persistent DC records, and the actual fresh-source
> rule at every height action. No independently assigned initial lease or S
> record is allowed.
>
> For liveness, retain the honest-proposer bound G, Rec(g), current-window
> row inclusion with `w_F ≥ 1`, and every required horizon. For safety, only
> the relevant synchronous labels and delivery horizons are needed. In
> particular, the existence of a fast write at `d_s` requires an execution
> through `d_s`, even when the safety endpoint is the earlier time `q_s`.
>
> ```text
> h = n−a;             f = (n−1) div 3;
> τ = (n+1) div 2;     q_F = (2n+2) div 3;
> a ≤ f;              h ≥ q_F ≥ τ > a;     h > 2a;
>
> t_s = 4sΔ;          v_s = t_s+Δ;          e_s = t_s+2Δ;
> z_s = t_s+3Δ;        q_s = t_s+5Δ;        d_s = t_s+6Δ;
> k ≥ 2;              L = (4k−1)Δ;
> R ≥ 3;              P = 4RΔ;             a_r = d_(rR);
> ρ = 2L+G+8Δ;        σ = (g+3)P+G+6Δ;     θ = 4Δ.
> ```
>
> Here and below, “ordinary walk” means the same duty's walk from its FG
> root Z, with the lease start removed. It retains the domain, scores,
> eligibility test, and tie order. It does not mean an unfiltered walk.

**`env.bp`** — bp §1.2, lines 118–145. File `fgsa-healing-blueprint.md`,
sha256 `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`.

> _fgsa-healing-blueprint.md, lines 118–145:_
>
> Use the equal-size C* profile: n base seats at each label and n fixed
> unit-weight FG identities, with the same static faulty set of size a.
>
> ```text
> τ = (n+1) div 2;  q_F = (2n+2) div 3;  f = (n−1) div 3;
> k ≥ 2;  L = (4k−1)Δ;  ρ = 2L+G+8Δ;  R ≥ 3;  P = 4RΔ;  θ = 4Δ;
> t_s = 4sΔ; v_s = t_s+Δ; e_s = t_s+2Δ; z_s = t_s+3Δ;
> q_s = t_s+5Δ = v_(s+1);  d_s = t_s+6Δ;
> T_r = rP;  a_r = T_r+6Δ = d_(rR);  δ_t = 2R slots;  D ≥ 2;  K ≥ g+2.
>
> a ≤ f  ⇒  h = n−a ≥ q_F ≥ τ;  τ > a;  q_F > a;  h > 2a;  2q_F−n > a.
> ```
>
> The recovery environment (E-env) is: `a≤f`; full participation from GST;
> strict Δ delivery and accepted-object relay from GST; an awake honest
> proposer strictly after each trigger and within G; DC's multi-proposer
> recurrence Rec(g); every proof window in the horizon. Readers process
> receipts while asleep. A private faulty object has no relay deadline until
> an honest reader accepts it.
>
> Let r_G be the first action round with `a_(r_G) ≥ GST`. The DC cut is the
> inclusive event prefix at `u_0 = a_(r_G+2)`. Then `GST+2P ≤ u_0 < GST+3P`.
> Let M be the honest archival frontier at u_0. As in DC,
>
> ```text
> H = the first multiple of K strictly above M+D+2;
> M+D+3 ≤ H ≤ M+D+K+2;  H+3 ≤ M+D+K+5.
> ```

**`env.r150`** — r150 §1, lines 43–112. File `fgsa-theorem-h.md`, sha256
`8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`.

> _fgsa-theorem-h.md, lines 43–112:_
>
> The exact recovery premises are:
>
> 1. The equal-size C* profile has n base seats per label and n fixed,
>    unit-weight FG identities. The same static faulty set has size
>    `a ≤ f = (n−1) div 3`. All h=`n−a` honest identities participate
>    after GST.
> 2. Objects and paths are authentic; roots are injective; parent slots
>    strictly increase. Executions start from the specified initial
>    state. S values, saved results, leases, and persistent DC records
>    have actual event origins. Completed gates do not replay.
> 3. After GST, delivery and accepted-object return relay take strictly
>    less than Δ. Honest proposal delivery and proposal-view relay
>    readiness hold. Receipts and clock events are processed also while
>    asleep. Private faulty objects acquire a relay duty only when an
>    honest reader accepts them. Every proof window fits in the horizon.
> 4. Each duty computes its frame from its own R1 view. Signed proposal
>    merges retain the original declared support subset. Raw tests,
>    saved raw results, and release are unfiltered. The S guard tests
>    all live leases, including excluded leases. Only a successful
>    guarded gate changes S or writes a lease. Finality does not assign S.
> 5. An awake honest proposer occurs strictly after every trigger and
>    within G. For the arrival bounds, retain Rec(g): an honest opening
>    and its next two slot proposers within g rounds. Honest proposals
>    include current-window rows, with `w_F ≥ 1`. Use the DC causal cap,
>    exact-entry quorum rules, finality lock, and persistent client rules.
>
> The local Theorem H needs the actual reset specified below, but does
> not need a height-progress bound. Rec(g) and row inclusion are used to
> obtain that reset within a deadline. No stronger recurrence for first
> finality is assumed or concluded.
>
> ```text
> τ = (n+1) div 2;      q_F = (2n+2) div 3;
> h ≥ q_F ≥ τ > a;     h > 2a;             2q_F−n > a;
> Δ > 0;              k ≥ 2;              L = (4k−1)Δ;
> R ≥ 3;              P = 4RΔ;            g ≥ 3;
> D ≥ 2;              K ≥ g+2;            δ_t = 2R slots;
>
> t_s = 4sΔ;          v_s = t_s+Δ;        e_s = t_s+2Δ;
> z_s = t_s+3Δ;        q_s = t_s+5Δ;       d_s = t_s+6Δ;
> T_r = rP;           a_r = d_(rR);
> ρ = 2L+G+8Δ;        σ = (g+3)P+G+6Δ;
> λ = ρ+2σ;           θ = 4Δ;             N = D+K+5.
> ```
>
> Write `ht(B)` for the DC height of a block. Prefix order is `⪯`.
> At duty d, use the blueprint's frame `(F_d,H_d,J_d,j_d,Z_d,D_d)`.
> A block B is kept when `B ⪯ Z_d` or `B ∈ D_d`. The ordinary walk is
> the same domain walk from Z_d, with the lease start removed. It retains
> the scores, eligibility rule, and tie order.
>
> Let `u_0=a_(r_G+2)`, where r_G is the first action round at or after
> GST. Let M be the honest archival frontier at that inclusive cut. Set
> H to the first multiple of K strictly above `M+D+2`. Thus
>
> ```text
> GST+2P ≤ u_0 < GST+3P;
> M+D+3 ≤ H ≤ M+D+K+2;       H+3 ≤ M+N.
> ```
>
> Use the actual DC consumer, with both outcomes. In the NJ outcome,
> `x=H` and the retained prefix has no honest target or lock at H. In
> the finalized outcome, x is its actual finalized height, `M<x≤H+1`,
> and F* is the named checkpoint at x. Every block of height greater
> than x extends F*. Do not replace this outcome by an assumed NJ bit.
>
> Let r* be the least round of an honest height-(x+1) row, let `s*=r*R`,
> and let C* be its fresh fast source body. The causal cap gives a wholly
> post-GST source label s*. Every honest row at height at least x+1 has
> label at least s*. These are the reset facts in blueprint §6.

**`env.r148`** — r148 §1, lines 76–119. File `fj-redteam.md`, sha256
`934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`.

> _fj-redteam.md, lines 76–119:_
>
> Use the equal-size C* profile: n seats at each base label and n fixed
> unit-weight FG identities; static corruption; one awake predicate;
> complete authenticated paths; injective roots; increasing parent
> slots; strict receipt cutoffs; and accepted-object relay. This does
> not prove a result for a smaller sampled committee.
>
> ```text
> τ = ceil(n/2); q = ceil(2n/3); f = floor((n−1)/3).
> L = (4k−1)Δ, k≥2; Π=min(η,L); ρ=2L+G+8Δ.
> P=4RΔ, R≥3; δ_t=2R slots; w_F≥1.
> t_s=4sΔ; v_s=t_s+Δ; e_s=t_s+2Δ; z_s=t_s+3Δ;
> q_s=t_s+5Δ; d_s=t_s+6Δ; a_r=rP+6Δ=d_(rR).
>
> Base claims: a<h≤n−a; thus a<τ and a<q.
> Recovery: a≤f; full participation; strict Δ delivery and relay;
>           honest proposal recurrence G and DC multi-proposer recurrence g.
> Then h=n−a≥q≥τ, h>2a, and 2q−n>a.
> ```
>
> First-finality bounds need the actual DC strong recurrence: three
> consecutive honest openings, with the last opening's next two slot
> proposers honest. See [Conditions.lean][conditions]. It has g≥3 in
> continuous time. Removing NJ removes the restriction K≥g+2; it does
> not remove proposer recurrence.
>
> Write h(B) for state height, not block depth or slot. Let j be the
> justified height of J, and H the maximum in the current duty view.
> An entry at one height can have many descendants at that same height.
> Two different entries at the same height conflict.
>
> Use two causal caps:
>
> ```text
> M  = maximum height of an honest height row whose source label has
>      v_s<GST, or 1 if there is no such row.
> rG = first action round at or after GST.
> u0 = a_(rG+2), with its inclusive event prefix.
> M0 = honest archival maximum at u0. Thus M≤M0.
> ```
>
> A synchronous source C at label s is retained from its transfer HEAD
> q_s=v_(s+1). It need not be in every HEAD at v_s, and need not be in
> every S at a_r=d_s. This timing correction applies to “stays canonical”
> throughout this report.

Note (2026-09-28, r160): the ALFS spec 1c6952b6 (`alfs3`) replaces
accepted-object relay by DC's receipt premise (spec lines 165–183). r160
§7 (lines 648–762) audits the ALFS uses (r158, r159, ldp, H12, FF); it
does not re-audit the R1-form proofs of this premise set. Exact vote-set
transport FAILS under the receipt premise (r160 N1, lines 428–477).

**`env.r151`** — r151 §1, lines 41–98. File `fj-theorem-h.md`, sha256
`16b69dba55d889b9ae20dd55b228cfd83ad22037d796c6219cdb65831718bba3`.
It restates the FJ frame of `fj.frame.v1` and the premises of `env.r150`.

> _fj-theorem-h.md, lines 41–98:_
>
> Use exactly [r148 §2](fj-redteam.md): plain SA, the DC exact-entry
> client, R1 duty views, fresh fast height sources, and `nj=false`.
> There is no SG or PC rule. In each duty's own view V, compute F, H,
> and the highest justified pair (j,J) compatible with F. Use:
>
> ```text
> H=j+1, all height-H blocks extend J: Z=J, lo=H−1;
> H=j+1, some height-H block conflicts with J: Z=F, lo=H;
> otherwise: Z=F, lo=H−1.
>
> D = {B∈V : F⪯B, Z⪯B, ∃W∈V, B⪯W and ht(W)≥lo};
> Kept_d(B) := B⪯Z_d or B∈D_d.
> ```
>
> The below-band eligibility test is `ht(parent)<lo`. Both viability
> and eligibility use the changed threshold in a contest. Paths add
> no support keys. Raw tests, release, saved raw results, and the S
> guard remain unfiltered. The guard tests every live lease. Finality
> does not assign S. The finality acceptance helper retains the r148
> rule; do not replace it with the new choice-band predicate.
>
> The proof uses the same recovery premises as [r150 §1](fgsa-theorem-h.md):
>
> 1. There are n base seats at each label and n fixed, unit-weight FG
>    identities, with one static faulty set of size `a≤f=(n−1) div 3`.
>    All `h=n−a` honest identities participate after GST.
> 2. Paths and signatures are authentic, roots are injective, and parent
>    slots strictly increase. Runs start from the specified initial state.
>    S, leases, saved results, and client records have actual event origins.
>    A completed gate cannot replay.
> 3. After GST, delivery and accepted-object relay take strictly less
>    than Δ. Honest proposal delivery and proposal-view relay readiness
>    hold. Receipts and clocks also run while asleep. Private faulty
>    objects acquire relay duties when an honest reader accepts them.
>    All required windows lie in the execution horizon.
> 4. Each duty uses its own R1 frame. Declared support remains the original
>    declared subset when a proposal is merged. Whole-result guards and
>    persistent exact-entry records follow the executable event order.
> 5. An honest awake proposal occurs strictly after each trigger within G.
>    For arrival, use Rec(g): an honest opening with its next two slot
>    proposers honest, within g rounds. Current-window FG rows are included,
>    `w_F≥1`, and timeout maturity is `2R` slots.
>
> The local healing theorem needs an actual reset but does not need a
> bound for reaching it. The arrival theorems additionally use item 5's
> opening recurrence and the supplied producer. No first-finality
> recurrence theorem is inferred from these premises.
>
> ```text
> τ=(n+1) div 2;          q_F=(2n+2) div 3;
> h≥q_F≥τ>a;             h>2a;             2q_F−n>a;
> Δ>0; k≥2; L=(4k−1)Δ;  R≥3; P=4RΔ;      g≥3;
> t_s=4sΔ; v_s=t_s+Δ; e_s=t_s+2Δ; z_s=t_s+3Δ;
> q_s=t_s+5Δ=v_(s+1);    d_s=t_s+6Δ;       a_r=d_(rR);
> ρ=2L+G+8Δ;             σ=(g+3)P+G+6Δ;
> λ=ρ+2σ;                θ=4Δ;             W=λ+θ;
> δ_H=2L+G−2Δ=ρ−10Δ.
> ```

Note (2026-09-28, r160): the ALFS spec 1c6952b6 (`alfs3`) replaces
accepted-object relay by DC's receipt premise (spec lines 165–183). r160
§7 (lines 648–762) audits the ALFS uses (r158, r159, ldp, H12, FF); it
does not re-audit the R1-form proofs of this premise set. Exact vote-set
transport FAILS under the receipt premise (r160 N1, lines 428–477).

### 0.3 Glossary: F-numbers (added 2026-09-28)

Two sources use the labels F1, F2, … for different facts.

- The blueprint F-table (bp §3, lines 290–311) numbers DC and SA facts:
  F1 honest row in each QC, F2 causal cap, F3 one justified entry per
  height, F4 finality lock, F5–F10 further DC facts.
- r148 (`fj-redteam.md`) numbers its own claims: F2 = a conflicting
  crossing of j proves that J cannot finalize (PROVED, lines 234–258);
  F3 = the converse, "retain J iff J can still finalize", is REFUTED (lines
  290–309); F4 = "no timeout at H−1" as a proxy for "J can finalize" is
  REFUTED and unsafe for liveness (lines 311–338); F6–F18 are its later
  claims.

In a pinned quote, an F-number belongs to the file of that quote. Every
"F3" or "F4" in the entries of v2 means the blueprint fact: F3 is
`fg.uniqueJust.v1` and F4 is `fg.finalLock.v1`. The r148 phrase
"finalized-crossing law" (line 226) and "finalized crossing" are also
`fg.finalLock.v1`. The FJ entry titles in §4 (F7, F9, F10, F12, F14, F17)
use the r148 numbers. r148 F2 is `fj.crossingNoFinal.v1`.

### 0.4 Named idealizations (added 2026-09-28)

- `ViewRootInj`: distinct blocks of a view have distinct roots. This is
  the collision-free root idealization, as in `fg.finalLock.v1`
  (`NamedRootCollisionFree`). The lex order `(h_j, J.root)` and every tie
  by root need it: DC's selector `pickUnique?` returns none on a tie of
  distinct blocks (Astra plan audit G03,
  `docs/audit/fg-plan-audit-report.md` lines 71–72).
  After I9 (2026-09-29), this idealization is not necessary.
  `viewRootInj_all` (`AvailableChainKitFG/Correspondence.lean`) proves
  `ViewRootInj` for every view, and `rootInjectiveOn_all`
  (`AvailableChainKitFG/Accountable.lean`) proves `RootInjectiveOn` for
  every two tips. The design: block roots are derived (`nodeRoot`,
  `epair`), the FG rows are packed into the block body, and `rowsOk`
  checks them. Thus the root is a function of the block content
  (`FGBlock.root_injective`). The statements keep `ViewRootInj` as a
  binder. The entries below that name it are marked "discharged by
  `viewRootInj_all` (I9, 2026-09-29)"; the history of the assumption
  stays visible.

## Index

`§` is the section of this file. New ids in v2 are listed in §7; the
ids of the f1 splits (2026-09-28) are listed in §8.

"Lean plan" is the scope of the Lean FG module (user decision
2026-09-28, §8). The module is DC-fj: DC's FG without SG and grades, with
the FJ root rule in place of NJ (FRAMEWORK-DESIGN.md §7.1). `DC-fj` = planned
in the DC-fj module (plan `docs/plans/2026-09-28-fg-module.md`);
`DC-fj (ii)` = part (ii) only; `DC-fj (item 4 partial)` = the
arithmetic of item 4 only (`comp.cut.v1`);
`none (nj)` = nj research entry, not planned for Lean now; `none` = not
needed by the DC-fj module; `—` = not an entry of the current FG-module
plan (AP-side, composite, or not scheduled). Status abbreviations
(2026-09-28, r153): "local PROVED; unif." = the local clause is PROVED and
the uniform clause is REFUTED; "impl. PRV" = the
implication is PROVED. The entry has the full dated status line. The
index shows the status under the old spec (R1 views); status lines marked
"under ALFS (spec 183f2c40)", "(spec c7c41a43)", "(spec 1c6952b6)" or
"(spec bd942ca0)" are in the entries only. Exception (2026-09-29, §9):
the index shows the WITHDRAWN status of the ids that the re-pin to
`fgsa3` withdraws, and the status of their successors.

```text
┌───────────────────────┬──────┬─────────────────────┬───┬────────────────────────┐
│ Id                    │ Var  │ Status 2026-09-28   │ § │ Lean plan              │
├───────────────────────┼──────┼─────────────────────┼───┼────────────────────────┤
│ fg.frame.v1           │ nj   │ SUPERSEDED (def)    │ 1 │ none (nj)              │
│ fg.frame.v2           │ nj   │ def                 │ 1 │ none (nj)              │
│ fg.frameCompat.v1     │ both │ PROVED              │ 1 │ DC-fj (ii)             │
│ fg.Ret.v1             │ nj   │ def                 │ 1 │ none (nj)              │
│ fg.N1.v1              │ nj   │ def                 │ 1 │ none (nj)              │
│ fg.N1eff.v1           │ nj   │ def                 │ 1 │ none (nj)              │
│ fg.N2.v1              │ nj   │ def                 │ 1 │ none (nj)              │
│ fg.N2.v2              │ nj   │ def                 │ 1 │ none (nj)              │
│ fg.HNI.v1             │ nj   │ def                 │ 1 │ none (nj)              │
│ ap.S.v1               │ nj   │ PROVED (FG-SA)      │ 2 │ —                      │
│ ap.S.v2               │ nj   │ PROVED (FG-SA)      │ 2 │ —                      │
│ ap.Sslow.v1           │ nj   │ PROVED (FG-SA)      │ 2 │ —                      │
│ ap.repair.fixedF.v1   │ nj   │ PROVED (FG-SA)      │ 2 │ —                      │
│ ap.repair.movingF.v1  │ nj   │ OPEN                │ 2 │ —                      │
│ ap.L.fixedF.v1        │ nj   │ WITHDRAWN (PROVED)  │ 2 │ —                      │
│ ap.L.movingF.v1       │ nj   │ WITHDRAWN (OPEN)    │ 2 │ —                      │
│ ap.reach.v1           │ nj   │ OPEN                │ 2 │ —                      │
│ ap.source.v1          │ nj   │ PROVED (FG-SA)      │ 2 │ —                      │
│ ap.X.v1               │ nj   │ REFUTED; WITHDRAWN  │ 2 │ —                      │
│ ap.Xplus.v1           │ nj   │ PROVED (FG-SA)      │ 2 │ —                      │
│ ap.rowService.v1      │ both │ RULE                │ 2 │ —                      │
│ ap.carrierKeep.v1     │ nj   │ WITHDRAWN (PROVED)  │ 2 │ —                      │
│ ap.carrierKeep.v2     │ nj   │ PROVED (FG-SA)      │ 2 │ —                      │
│ ap.honestSourced.v1   │ both │ WITHDRAWN (PROVED)  │ 2 │ —                      │
│ ap.honestSourced.v2   │ both │ PROVED (FG-SA)      │ 2 │ —                      │
│ ap.armedSafe.v1       │ nj   │ PROVED (FG-SA)      │ 2 │ —                      │
│ ap.outputRecovered.v1 │ nj   │ WITHDRAWN (PROVED)  │ 2 │ —                      │
│ ap.finalityHead.v1    │ nj   │ WITHDRAWN (SKETCH)  │ 2 │ —                      │
│ ap.finalityHead.v2    │ nj   │ SKETCH              │ 2 │ —                      │
│ ap.fastSupport.v1     │ both │ PROVED (RULE, τ>a)  │ 2 │ —                      │
│ ap.headReachesLo.v1   │ fj   │ PROVED (FG-SA)      │ 2 │ —                      │
│ ap.headReachesLo.v2   │ fj   │ SUPERSEDED (PROVED) │ 2 │ —                      │
│ ap.headReachesLo.v3   │ fj   │ SUPERSEDED (PROVED) │ 2 │ —                      │
│ ap.headReachesLo.v4   │ fj   │ SUPERSEDED (PROVED) │ 2 │ —                      │
│ ap.headReachesLo.v5   │ fj   │ WITHDRAWN (PROVED)  │ 2 │ —                      │
│ ap.headReachesLo.v6   │ fj   │ PROVED (paper)      │ 2 │ —                      │
│ fg.provenance.v1      │ both │ SUPERSEDED (PROVED) │ 3 │ —                      │
│ fg.provenance.v2      │ both │ PROVED              │ 3 │ DC-fj                  │
│ fg.causalCap.v1       │ both │ SUPERSEDED (PROVED) │ 3 │ —                      │
│ fg.causalCap.core.v1  │ both │ PROVED; LEAN (DC)   │ 3 │ DC-fj                  │
│ fg.uniqueJust.v1      │ both │ LEAN (DC, Lemma U)  │ 3 │ DC-fj                  │
│ fg.finalLock.v1       │ both │ WITHDRAWN (LEAN, DC)│ 3 │ DC-fj                  │
│ fg.finalLock.v2       │ both │ PROVED (paper)      │ 3 │ DC-fj                  │
│ fg.trunk.v1           │ nj   │ PROVED (a≤f)        │ 3 │ none (nj)              │
│ fg.oneBullet.v1       │ nj   │ SUPERSEDED (PROVED) │ 3 │ none (nj)              │
│ fg.oneBullet.core.v1  │ nj   │ PROVED (a≤f)        │ 3 │ none (nj)              │
│ fg.H19.v1             │ nj   │ PROVED              │ 3 │ none (nj)              │
│ fg.HNIb.v1            │ nj   │ PROVED              │ 3 │ none (nj)              │
│ fg.base.finalized.v1  │ nj   │ PROVED              │ 3 │ none (nj)              │
│ fg.base.nj.v1         │ nj   │ PROVED (FG-SA)      │ 3 │ none (nj)              │
│ fg.baseSel.nj.v1      │ nj   │ PROVED (FG-SA)      │ 3 │ none (nj)              │
│ fg.accountable.v1     │ both │ PROVED; LEAN (DC)   │ 3 │ DC-fj                  │
│ fj.frame.v1           │ fj   │ def                 │ 4 │ DC-fj                  │
│ fj.frame.v2           │ fj   │ SUPERSEDED (def)    │ 4 │ DC-fj                  │
│ fj.frame.v3           │ fj   │ WITHDRAWN (def)     │ 4 │ DC-fj                  │
│ fj.frame.v4           │ fj   │ PROVED (paper)      │ 4 │ DC-fj                  │
│ fj.frameFeasible.v1   │ fj   │ PROVED              │ 4 │ DC-fj                  │
│ fj.crossingNoFinal.v1 │ fj   │ PROVED              │ 4 │ DC-fj                  │
│ fj.descent.v1         │ fj   │ WITHDRAWN (PROVED)  │ 4 │ —                      │
│ fj.descent.v2         │ fj   │ PROVED (paper)      │ 4 │ —                      │
│ fj.canonical.v1       │ fj   │ PROVED              │ 4 │ —                      │
│ fj.inBandLock.v1      │ fj   │ PROVED              │ 4 │ DC-fj                  │
│ fj.twoChanges.v1      │ fj   │ SUPERSEDED (PROVED) │ 4 │ —                      │
│ fj.twoChanges.core.v1 │ fj   │ WITHDRAWN (PROVED)  │ 4 │ DC-fj                  │
│ fj.twoChanges.core.v2 │ fj   │ PROVED (paper)      │ 4 │ —                      │
│ fj.armedSafe.v1       │ fj   │ PROVED              │ 4 │ —                      │
│ fg.base.fj.v1         │ fj   │ REFUTED (uniform)   │ 4 │ —                      │
│ fj.firstFinality.v1   │ fj   │ local PROVED; unif. │ 4 │ —                      │
│ fj.reset.v1           │ fj   │ PROVED              │ 4 │ —                      │
│ fj.theoremN.v1        │ fj   │ PROVED              │ 4 │ —                      │
│ fj.rise.fixedF.v1     │ fj   │ PROVED              │ 4 │ —                      │
│ fj.rise.movingF.v1    │ fj   │ REFUTED (impl. PRV) │ 4 │ —                      │
│ fj.Xplus.v1           │ fj   │ PROVED              │ 4 │ —                      │
│ fj.healed.v1          │ fj   │ local PROVED; unif. │ 4 │ —                      │
│ fj.healedUnif.v1      │ fj   │ REFUTED (impl. PRV) │ 4 │ —                      │
│ fj.healedAtQ.v1       │ fj   │ REFUTED (h12, r158) │ 4 │ —                      │
│ comp.provenance.v1    │ both │ PROVED (FG-SA)      │ 5 │ —                      │
│ comp.settle.v1        │ both │ PROVED (FG-SA)      │ 5 │ —                      │
│ comp.cut.v1           │ both │ PROVED              │ 5 │ DC-fj (item 4 partial) │
│ comp.rise.fixedF.v1   │ nj   │ PROVED (FG-SA)      │ 5 │ —                      │
│ comp.rise.movingF.v1  │ nj   │ OPEN                │ 5 │ —                      │
│ comp.theoremN.v1      │ nj   │ PROVED (FG-SA)      │ 5 │ —                      │
│ comp.fgHealed.v1      │ nj   │ PROVED (FG-SA)      │ 5 │ —                      │
│ comp.healed.v1        │ nj   │ PROVED (FG-SA)      │ 5 │ —                      │
│ comp.healedLit.v1     │ nj   │ PROVED (FG-SA)      │ 5 │ —                      │
│ comp.arrivalNJ.v1     │ nj   │ PROVED (FG-SA)      │ 5 │ —                      │
│ comp.handoffBase.v1   │ nj   │ PROVED (FG-SA)      │ 5 │ —                      │
│ comp.healedUnif.v1    │ nj   │ OPEN (impl. PROVED) │ 5 │ —                      │
│ comp.healedAtQ.v1     │ nj   │ OPEN                │ 5 │ —                      │
│ comp.finality.v1      │ nj   │ SKETCH              │ 5 │ —                      │
│ comp.clean.v1         │ nj   │ PROVED (FG-SA)      │ 5 │ —                      │
│ comp.outputNesting.v1 │ both │ PROVED              │ 5 │ —                      │
│ comp.leaseVsFinal.v1  │ fj   │ REFUTED (r161 N1)   │ 5 │ —                      │
└───────────────────────┴──────┴─────────────────────┴───┴────────────────────────┘
```

## 1. Definitions (`SimplexFG.nj` frame)

These definitions use the NJ frame. FJ has its own frame (`fj.frame.v1`,
§4); these definitions do not apply to it.

### `fg.frame.v1` — duty frame

- Variant `nj`. Source r147 §2, lines 105–119. File `fgsa-conditional.md`,
  sha256 `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Statement (pinned):

> _fgsa-conditional.md, lines 105–119:_
>
> For each honest duty d, take its own R1 view V_d. Compute its controls
> together, as in the rule documents:
>
> ```text
> F_d = current accepted F, with its retained acceptance basis;
> H_d = max({1} ∪ {h(W) : W∈V_d});
> (j_d,J_d) = greatest justified pair in V_d compatible with F_d;
> Z_d = J_d if H_d=j_d+1, else F_d;
>
> D_d = {B∈V_d : F_d⪯B, Z_d⪯B,
>                   ∃W∈V_d, B⪯W and h(W)≥H_d−1}.
>
> Ret_d(B) := B⪯Z_d
>             or (Z_d⪯B and B∈D_d).
> ```

- Status: 2026-09-28 — def. This is the frame of FRAMEWORK-DESIGN.md §7.2.
  bp §1.3 (lines 153–161) has the same frame; there the F test follows from
  the Z test.
- Status: 2026-09-28 — SUPERSEDED by `fg.frame.v2`. The J line of v1 says
  "compatible with F_d"; DC and the spec select with `F_d ⪯ J`.
  `fg.frameCompat.v1` proves that the two rules select the same pair at
  every honest duty view. Thus every entry that uses this frame keeps its
  meaning.

### `fg.frame.v2` — duty frame (J selected with `F_d ⪯ J_d`)

- Variant `nj`. Source spec, section "Duties and handlers", `fg_frame`,
  lines 854–859, and appendix "NJ variant", lines 1408–1417 (the frame
  without a contest). The store rule `update_finality` has the same J
  guard: spec lines 731–752 and DC `update_finality`, dc lines 937–948.
  Files `spec/fgsa-protocol.tex` (sha256
  `ae4497abc7c5b3a6f73697f341bf730a63c7d34bd2f7546154bd022bc95af223`) and
  `dc/consensus.tex` (sha256
  `dc471b47a46896fe0a3df300c188fef1512f475615ce0fc0df18dbea6d2e5517`).
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Frame (registry form; it is `fg.frame.v1` with the J line changed):

```text
F_d = current accepted F, with its retained acceptance basis;
H_d = max({1} ∪ {h(W) : W∈V_d});
(j_d,J_d) = the lex-greatest (h_j, J.root) justified pair in V_d
            with F_d ⪯ J_d;
Z_d = J_d if H_d=j_d+1, else F_d;

D_d = {B∈V_d : F_d⪯B, Z_d⪯B,
                  ∃W∈V_d, B⪯W and h(W)≥H_d−1}.

Ret_d(B) := B⪯Z_d
            or (Z_d⪯B and B∈D_d).
```

- Statement (pinned):

> _fgsa-protocol.tex, lines 854–859:_
>
> ```latex
>   \State $F\gets\Sigma.F$
>   \Comment{the current accepted $F$}
>   \State $H\gets\max(\{1\}\cup\{\Sigma.\sigma[W].h:W\in V\})$
>   \Comment{this view's own maximum}
>   \State $(j,J)\gets$ the lex-greatest $(\Sigma.\sigma[W].h_j,
>     \Sigma.\sigma[W].J.\rootf)$ over $W\in V$ with $F\preceq\Sigma.\sigma[W].J$
> ```

> _fgsa-protocol.tex, lines 1408–1417:_
>
> ```latex
> \item \fname{fg\_frame} has no contest:
>   \[
>    (Z,\lo)\gets
>    \begin{cases}
>     (J,H-1), & H=j+1,\\
>     (F,H-1), & \text{otherwise}.
>    \end{cases}
>   \]
>   This is the frame \textsf{FRAME} of~\ADJ{2}: the root rule of~\DC{5}
>   and the band $\{H-1,H\}$, computed from the duty's own view.
> ```

> _fgsa-protocol.tex, lines 731–752:_
>
> ```latex
> \Function{update\_finality}{$\Sigma,B$}
>   \Comment{\DC{7}, extended by \ADJ{2}: F basis}
>   \State $\sigma\gets\Sigma.\sigma[B]$
>   \State $\Sigma.\hmax\gets\max(\Sigma.\hmax,\sigma.h)$
>   \Comment{archival; no duty frame reads it}
>   \If{$\Sigma.F\preceq\sigma.J$ \textbf{and}
>       $(\sigma.h_j,\sigma.J.\rootf)>(\Sigma.h_j,\Sigma.J.\rootf)$}
>     \State $(\Sigma.J,\Sigma.h_j)\gets(\sigma.J,\sigma.h_j)$;
>       $\Sigma.\jCarrier\gets B$
>     \Comment{lex order}
>   \EndIf
>   \If{$\Sigma.F\prec\sigma.F$ \textbf{and} $\sigma.F\preceq\Sigma.J$
>       \textbf{and} $\sigma.F\in\Call{viable\_tree}{\Sigma}$}
>     \State $\Sigma.F\gets\sigma.F$
>     \Comment{does not change $S$ or leases}
>     \State $W\gets$ the $W\in\Sigma.\TF$ with $\sigma.F\preceq W$ of
>       greatest $\Sigma.\sigma[W].h$
>     \Comment{ties by root}
>     \State $\Sigma.\fBasis\gets\{B,\Sigma.\jCarrier,W\}$
>     \Comment{carrier, J carrier, witness}
>   \EndIf
> \EndFunction
> ```

> _consensus.tex, lines 937–948:_
>
> ```latex
> \Function{update\_finality}{$\Sigma,\sigma$}
>   \State $\Sigma.\hmax\gets\max(\Sigma.\hmax,\sigma.h)$
>   \If{$\Sigma.F\preceq\sigma.J$ \textbf{and}
>       $(\sigma.h_j,\sigma.J.\rootf)>(\Sigma.h_j,\Sigma.J.\rootf)$}
>     \Comment{lex order}
>     \State $(\Sigma.J,\Sigma.h_j)\gets(\sigma.J,\sigma.h_j)$
>   \EndIf
>   \If{$\Sigma.F\prec\sigma.F$ \textbf{and} $\sigma.F\preceq\Sigma.J$
>       \textbf{and} $\sigma.F\in\Call{viable\_tree}{\Sigma}$}
>     \State $\Sigma.F\gets\sigma.F$
>   \EndIf
> \EndFunction
> ```

- Status: 2026-09-28 — def. It replaces `fg.frame.v1`; `fg.frameCompat.v1`
  proves that both select the same pair.
- Note: the fj counterpart is `fj.frame.v1`. It already selects J with
  `F ⪯ σ[W].J` (r148 `FJ_FRAME`, lines 151–152). `fg.frameCompat.v1`
  applies to both frames. The pinned `fg_frame` lines also
  compute the FJ frame; the NJ variant (lines 1408–1417) removes only the
  contest.
- Note: spec line 357 says "compatible", but the code of lines 736–737 and
  858–859 tests `F ⪯ J`:

> _fgsa-protocol.tex, lines 356–357:_
>
> ```latex
> $(\Sigma.F,\Sigma.J,\Sigma.h_j)$ are the accepted finalization and the
> lex-greatest justification compatible with it, as in~\DC{5}.
> ```

### `fg.frameCompat.v1` — "compatible with F" and "`F ⪯ J`" select the same pair

- Variant `both`. Source: registry, 2026-09-28. No source file states this
  lemma; the argument is below. Rule sources: dc lines 747–748, 762–767,
  820, 824 and 838 (checkpoint heights); spec lines 361–365 and 494 (F
  basis in every duty view); spec lines 736–750 (J guard and F basis).
  Hashes as in `fg.frame.v2`.
- Lean plan: DC-fj module, partial: (ii) only, F ⪯ J form (Lean
  `fBasis_lexMax`, plan `befb5d5`). Changed 2026-09-28; the earlier line
  was "none".
- Hypotheses: R1 duty views (`env.r150` item 4; spec lines 483–495); the
  F-basis rule of spec lines 742–750; the DC chain state (bp F5: one
  height per block; the entry `T_h` is the block that entered h). It does
  not use `a≤f`.
- Hypothesis added 2026-09-28 (§0 rule (b): the rule uses the lex order
  `(h_j, J.root)` and ties by root): `ViewRootInj` (§0.4); discharged by
  `viewRootInj_all` (I9, 2026-09-29).
- Lean coverage (2026-09-28): Lean covers step 1 and part (ii)
  (`fBasis_lexMax`); part (i) and step 4 stay paper.
- Note (2026-09-28, ALFS): part (ii) is now proved without the F basis
  (Lean `storeControls_eq_fjControls` and `lexMax_of_candidate`). The ALFS
  spec deletes the F basis and the J carrier (`fj.frame.v2`). The premise
  `StoreInv.Fcar` (the block that finalized F is in Σ.T_F) replaces
  them.
- Statement (registry): let d be an honest duty with view V_d and current
  accepted F = F_d. Let P1 be the greatest `(h_j, J.root)` justified pair
  in V_d whose J is compatible with F (the `fg.frame.v1` rule). Let P2 be
  the lex-greatest such pair with `F ⪯ J` (the `fg.frame.v2` rule). Then
  P1 = P2. The same holds for the FJ frame: the wording "compatible with
  F" of `env.r151` (r151 line 44) and the `F ⪯ σ[W].J` test of
  `fj.frame.v1` select the same pair.
- Proof (registry, 2026-09-28).
  1. Checkpoint heights. A justified pair is `(h, T_h)` of a chain state
     (dc line 824). `T_h` is the block that brought its chain into height
     h (dc lines 747–748, 838), so `σ[T_h].h = h`. A finalized pair is a
     former justified pair (dc line 820). The only exception is the
     initial pair `(0, genesis)`, with `σ[genesis].h = 1` (dc lines
     762–767). Thus each pair `(h,C)` has `h ≤ σ[C].h`, with equality when
     C ≠ genesis. Heights do not decrease along a chain, and a non-genesis
     entry T is the first block of its height on its chain. So every
     strict ancestor of T has state height at most `σ[T].h − 1`.
  2. Part (i): if `h_J ≥ h_F`, then "J is compatible with F" ⇔ `F ⪯ J`.
     The direction ⇐ is immediate. For ⇒, suppose `J ≺ F` strictly. Then
     F ≠ genesis, so `h_F = σ[F].h`, and step 1 gives
     `h_J ≤ σ[J].h ≤ h_F − 1`. This contradicts `h_J ≥ h_F`.
  3. Part (ii): V_d holds a pair with `F ⪯ J` and `h_J ≥ h_F`. If F is
     genesis, every pair has `F ⪯ J` and `h_J ≥ 0 = h_F`. Otherwise
     `update_finality` accepted F only with `σ.F ⪯ Σ.J` (spec line 742).
     The F basis saved the J carrier W0, with `σ[W0].J = Σ.J` (spec lines
     736–739, 749). R1 puts the F basis in every duty view (spec lines
     363–365; HEAD view item 5, line 494; a full view holds every admitted
     block). If `Σ.J = F` as blocks, then `h_J = h_F` (step 1, F ≠
     genesis). If `F ≺ Σ.J`, then `h_J = σ[Σ.J].h ≥ σ[F].h = h_F`.
  4. Each candidate of P2 is a candidate of P1, so P2 ≤ P1. Step 3 gives
     `h(P2) ≥ h_F`, so `h(P1) ≥ h_F`. Step 2 gives `F ⪯ J` for P1, so P1
     is a candidate of P2 and P1 ≤ P2. Thus P1 = P2. ∎
- Status: 2026-09-28 — PROVED (registry argument; no Lean certificate).
- Note: part (ii) needs the F basis in the view. A view without it can
  select a different pair; R1 excludes such a view at an honest duty. The
  argument reads "greatest" in `fg.frame.v1` as the lex order
  `(h_j, J.root)` of DC §5.
- Note (2026-09-28; §0 rule (a)): `fj.frame.v2` is SUPERSEDED by
  `fj.frame.v3` (spec bd942ca0: Σ.T in place of Σ.T_F, the same set;
  `update_finality` also calls `reconcile_with_finality`, which writes no
  frame input). A citation of `fj.frame.v2` here reads as `fj.frame.v3`.
- Note (2026-09-29; current use): `fj.frame.v3` is WITHDRAWN for current
  use; its successor is `fj.frame.v4` (spec `fgsa3`). The frame controls
  do not change; the Trees clauses change (no deletion from Σ.T, the SA
  walk starts at Σ.F). The note above is history. A current citation of
  `fj.frame.v2` or `fj.frame.v3` here reads as `fj.frame.v4`.

### `fg.Ret.v1` — keep predicate

- Variant `nj`. Source r147 §2, lines 117–125. File `fgsa-conditional.md`,
  sha256 `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Statement (pinned; lines 117–118 are inside the frame block above):

> _fgsa-conditional.md, lines 117–118:_
>
> ```text
> Ret_d(B) := B⪯Z_d
>             or (Z_d⪯B and B∈D_d).
> ```

> _fgsa-conditional.md, lines 121–125:_
>
> The first arm of Ret allows the root to move past B along B's chain.
> It is therefore weaker than requiring B to remain a member of D_d.
> The second arm requires a band witness in **this** view. Compatibility
> with F and Z alone is insufficient. Ancestor closure supplies the path
> from Z_d to B in this arm.

- Status: 2026-09-28 — def. It is equivalent to
  `Kept_d(B) ⇔ B ⪯ Z_d or B ∈ D_d` (bp §1.3, lines 163–167; r149 §1, line
  85), because `B ∈ D_d ⇒ Z_d ⪯ B` (bp §10, lines 1065–1067). Lemma K of bp
  §7.3 (the one-duty keep lemma) proves Kept at every honest duty after the
  reset.

### `fg.N1.v1` — literal static controls

- Variant `nj`. Source r147 §2, lines 127–138. File `fgsa-conditional.md`,
  sha256 `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Statement (pinned):

> _fgsa-conditional.md, lines 127–138:_
>
> **N1(u,v;m,F,Z): static controls.** At every honest proposal, HEAD, and
> FG choice duty in `[u,v]`, `H_d=m`, `F_d=F`, and `Z_d=Z`. R1 and the
> retained-F-basis rule continue to hold. Each duty computes D_d from its
> own view. The full archival honest frontier is m until the stopping
> event under consideration. Views, block sets, scores, leases, and raw
> results need not be equal. New blocks and band witnesses may arrive.
> The unused lower justified pair need not be fixed when Z=F.
>
> N1 concerns the selection rule, not literal equality of D_d. This matters:
> the honest proposal itself must enter later views. A static filter may
> also exclude an old lease target below the band. No claim that all old
> protected blocks remain eligible is part of N1.

- Status: 2026-09-28 — def.

### `fg.N1eff.v1` — effective static filter

- Variant `nj`. Source bp §1.3 and §2.1, lines 169–172 and 178–187. File
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`. The
  same condition is r149 §1, lines 94–97 (in `env.r149`).
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 169–172:_
>
> **Definition (effective filter).** For a duty d put
> `Ẑ_d = J_d` if `H_d = j_d+1` (J-mode), and `Ẑ_d = ◇` otherwise (F-mode).
> The effective filter is `Φ_d = (H_d, Ẑ_d)`. In F-mode, F_d is not part of
> Φ_d. Section 4 shows that this omission is harmless.

> _fgsa-healing-blueprint.md, lines 178–187:_
>
> **(N1) Static effective filter.** For times u≤v, a frontier m≥1, and
> `Ẑ ∈ {◇} ∪ Blocks`, (N1)(u,v;m,Ẑ) holds iff every honest duty d with
> t_d∈[u,v] satisfies: the honest frontier at t_d exceeds m, or
> `Φ_d = (m,Ẑ)`.
>
> (N1) permits these changes: arbitrary view growth, lease paths that enter
> or leave a HEAD view, F advances in F-mode (they are below the band, §4.1),
> lower J changes, and a finalization of J_(m−1) in J-mode. It forbids a
> change of the band threshold at a frontier that has not risen, and a
> change between the two modes.

- Status: 2026-09-28 — def.

### `fg.N2.v1` — source-closed preservation (Ret form)

- Variant `nj`. Source r147 §2, lines 140–158. File `fgsa-conditional.md`,
  sha256 `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Statement (pinned):

> _fgsa-conditional.md, lines 140–158:_
>
> **N2(C,s;a_r,t): preservation for one source.** Let `s=rR` and
> `a_r=d_s`. Require Ret_d(C) at every honest transfer HEAD at q_s, and
> at every subsequent honest choice duty through t. Equivalently this is
> preservation on `[q_s,t]`, with the first transfer HEAD included. This
> condition refers only to F_d, Z_d, H_d, V_d, and their domain predicate;
> it does not assert that any actual HEAD or S already contains C.
>
> For a family of rows, **N2(u,t)** means N2(C,s;a_r,t) for each honest
> nonempty height row with `a_r∈[u,t]` and its selected fresh source C.
> This definition includes the source boundary of each row. In particular,
> the first row's q_s can be one Δ before u.
>
> This boundary is essential to the statement being proved. A condition
> only on duties whose wall-clock times are in `[a_r,t]` does not supply a
> premise about the already completed HEAD at `q_s=a_r−Δ`. When this file
> says “N2 on `[a_r,t]`”, it means the explicit source-closed definition
> above. It does not silently infer that earlier HEAD from future controls.
> An alternative interface is Ret at q_s as a separate premise, followed
> by ordinary forward preservation on `[a_r,t]`.

- Status: 2026-09-28 — def. Used by `ap.S.v1`.

### `fg.N2.v2` — preservation of one body or a set (Kept form)

- Variant `nj`. Source r149 §1, lines 90–92; set form bp §2.1, lines
  189–192. Files `fgsa-conditional-close.md` (sha256
  `1ea1ccc5c944335b7e7793afe2c6675a056762e35eeaeee13ec1f6066460a902`) and
  `fgsa-healing-blueprint.md` (sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`).
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Statement (pinned):

> _fgsa-conditional-close.md, lines 90–92:_
>
> `N2(B;q_s,t)` requires Kept at every honest HEAD, proposal, FG source
> choice, and finality-head read in `[q_s,t]`. It includes the first HEAD
> at `q_s`. It imposes no condition on a later duty outside this interval.

> _fgsa-healing-blueprint.md, lines 189–192:_
>
> **(N2) Protected blocks are kept.** Let 𝒫 be a set of blocks, each with a
> start time q(B). (N2)(𝒫;t) holds iff every B∈𝒫 is kept at every honest
> duty d (HEAD, proposal, FG action, or finality head) with
> `q(B) ≤ t_d ≤ t`.

- Status: 2026-09-28 — def. Used by `ap.S.v2`, `ap.Sslow.v1` and
  `comp.theoremN.v1`. It differs from `fg.N2.v1`: it names every honest
  HEAD, proposal, FG source choice and finality-head read, it applies to any
  body, and its interval starts at `q_s` for every `t ≥ q_s`.

### `fg.HNI.v1` — height-m noninterference

- Variant `nj`. Source bp §7.9, lines 790–801. File
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 790–801:_
>
> **Definition (HNI).** For a height m ≥ 1, *height-m noninterference*,
> HNI(m), holds iff, over the whole run:
>
> - (h1) every justified entry at height m−1 precedes every valid block of
>   height ≥ m; and
> - (h2) every finalized checkpoint of height ≤ m−1 precedes every valid
>   block of height ≥ m.
>
> HNI(m) speaks only about FG objects **below** m. It says that they never
> separate blocks at height ≥ m. It does not say when an honest node learns
> of such an object. A justified entry at a height < m−1 needs no clause:
> it is never the root at a view with `H_d ≥ m`.

- Status: 2026-09-28 — def.

`HeightRetains(m)` (v5) is REFUTED once the frontier passes m (bp §7.9, H22,
lines 865–878) and is withdrawn.

## 2. AP-side entries

These entries use the NJ frame of §1 in their premises. The FJ analogues are
in §4. Every status below is for the FG-SA client (§0).

### `ap.S.v1` — (S) for row sources, r147 form

- Variant `nj`. Source r147 §3, lines 170–181. File `fgsa-conditional.md`,
  sha256 `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Hypotheses: `env.r147`; `fg.N2.v1` for C on `[q_s,t]`; `t ≥ a_r`.
- Statement (pinned):

> _fgsa-conditional.md, lines 170–181:_
>
> **Exact statement (S).** Under §1, let an honest nonempty height row at
> `a_r=d_s≥GST`, `s=rR`, use fresh fast source C from a synchronous label s.
> Let `t≥a_r`, and assume N2(C,s;a_r,t). Every honest HEAD emitted at a
> scheduled HEAD duty in `[q_s,t]` contains C. Every honest S that contains
> C immediately after d_s retains C through t. If `t≥d_(s+1)`, every
> honest S contains C at every time in `[d_(s+1),t]`, where
> `d_(s+1)=t_s+10Δ`. These conclusions hold for both a target row and a
> timeout row. Its named entry `T=σ[C].T_h⪯C` inherits them.
>
> “HEAD from q_s” refers to emitted HEAD duties. It does not assert that
> an arbitrary full-view recomputation between duties is an emission.
> “By +10Δ” is subject to the horizon and `t≥+10Δ` guards just stated.

- Status: 2026-09-28 — PROVED (FG-SA; r147 §3 and its claim table).
- Scope: row sources only, at FG action labels. It does not cover every fast
  body, slow bodies, or proposal parents. `comp.fgHealed.v1` does not use it
  (audit W05); it uses `ap.S.v2` and `ap.Sslow.v1`.

### `ap.S.v2` — (S) at every fast-write label

- Variant `nj`. Source r149 §2.1, lines 130–141. File
  `fgsa-conditional-close.md`, sha256
  `1ea1ccc5c944335b7e7793afe2c6675a056762e35eeaeee13ec1f6066460a902`.
- Hypotheses: `env.r149`; `fg.N2.v2` for B on `[q_s,t]`; `t_s ≥ GST`;
  `t ≥ q_s`; a fast write at `d_s` (so the execution reaches `d_s`).
- Statement (pinned):

> _fgsa-conditional-close.md, lines 130–141:_
>
> **(S) — PROVED.** Let B be a successful fast body at any label s with
> `t_s ≥ GST`: `B ∈ FastWrite_i[s]` for an honest i. Assume the recovery
> execution premises through the times used, and let `t ≥ q_s`. If
> `N2(B;q_s,t)` holds, then:
>
> 1. **S1:** every honest emitted HEAD in `[q_s,t]` contains B.
> 2. **S2:** every honest proposal P at slot u with `u ≥ s+2` and
>    `t_u ≤ t` has `B ⪯ parent(P)`.
> 3. **S3:** every honest S at each time in `[d_(s+1),t]` contains B.
>
> An interval with its lower endpoint above t contributes no conclusion.
> No requirement that s be a multiple of R occurs in this statement.

- Status: 2026-09-28 — PROVED (FG-SA; r149 §2, claim table line 28).
- Notes: the proof (r149 §2.2–§2.8) uses only the Kept premise, the release
  at τ, raw same-label compatibility and the S guard. It holds at labels
  without an FG action. It implies `ap.S.v1` for row sources (r149 lines
  152–154).

### `ap.Sslow.v1` — (S_slow) for a wholly synchronous slow window

- Variant `nj`. Source r149 §2.1, lines 143–150. File
  `fgsa-conditional-close.md`, sha256
  `1ea1ccc5c944335b7e7793afe2c6675a056762e35eeaeee13ec1f6066460a902`.
- Hypotheses: as `ap.S.v2`, with a successful slow write at s and every
  label in `[s−k+1,s]` synchronous.
- Statement (pinned):

> _fgsa-conditional-close.md, lines 143–150:_
>
> **(S_slow) — PROVED.** The same three conclusions hold when B has a
> successful slow write at label s and every label in `[s−k+1,s]` is
> synchronous. Later used labels are synchronous as well. The N2 interval
> still starts at `q_s`, not at the beginning of the slow window.
>
> For the blueprint's protected set, require `s−k+1 ≥ s*` and
> `t_(s*) ≥ GST`. Thus a window contained in `[s*,∞)` suffices. If “wholly
> after s*” is read strictly, `s−k+1 > s*` is a sufficient stronger premise.

- Status: 2026-09-28 — PROVED (FG-SA; r149 §2.4, claim table line 29).

### `ap.repair.fixedF.v1` — base repair by u+ρ under literal N1

- Variant `nj`. Source r147 §4, lines 285–287, 339–345 and 400–405. File
  `fgsa-conditional.md`, sha256
  `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Hypotheses: `env.r147`; `fg.N1.v1` from `u ≥ GST` on the interval used;
  stop at the first rise of the honest frontier.
- Service statement: the first honest proposal p strictly after T* has
  exact honest HEAD service and a fresh fast write at every honest reader
  by `p+6Δ ≤ u+ρ`; every later honest proposal whose service interval
  stays under N1 has the same service.
- Statement (pinned):

> _fgsa-conditional.md, lines 285–287:_
>
> Assume N1 from `u≥GST` on a sufficiently long interval, and stop the
> argument if the honest frontier rises. Do not require every old lease
> to be inside D_d.

> _fgsa-conditional.md, lines 339–345:_
>
> Choose the first honest proposal at time p strictly after T*, within G.
> Both proposal times lie on the 4Δ grid, so `p≥T*+4Δ>E_old`.
> Consequently
>
> ```text
> p+6Δ ≤ T*+G+6Δ ≤ u+2L+G+8Δ = u+ρ.
> ```

> _fgsa-conditional.md, lines 400–405:_
>
> Repeat the same comparison for later honest proposals while N1 lasts.
> It gives exact service, fresh fast writes, and the usual safe S suffix
> inside the domain. A later genuine result covers the last supported
> honest proposal; its guard passes because every live target has such
> support or precedes Z. This is local repair and continuation, not a
> claim about a later change of filter.

- Status: 2026-09-28 — PROVED (FG-SA; r147 §4 "Base repair under N1 —
  PROVED").
- Kind: AP service fact (audit W02). It states no height rise.

### `ap.repair.movingF.v1` — base repair by u+ρ under effective N1

- Variant `nj`. Sources: r149 §4.4, lines 444–446 (file
  `fgsa-conditional-close.md`, sha256
  `1ea1ccc5c944335b7e7793afe2c6675a056762e35eeaeee13ec1f6066460a902`); r150
  §5, lines 441–443 (file `fgsa-theorem-h.md`, sha256
  `8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`).
- Hypotheses: `env.r149`; `fg.N1eff.v1` from `u ≥ GST` until the first
  rise; the initial reachable base state at u is arbitrary.
- Service statement: as `ap.repair.fixedF.v1`, with `fg.N1eff.v1` in place
  of `fg.N1.v1` (F may advance below the band).
- Statement (pinned):

> _fgsa-conditional-close.md, lines 444–446 (excerpt; line breaks reflowed):_
>
> Once exact service under effective N1 is available, r147's height
> production proof has no further F-constancy use

> _fgsa-theorem-h.md, lines 441–443 (excerpt; line breaks reflowed):_
>
> If Reach(m) is proved with the quantifiers above, r149 §4.2 supplies the
> remaining lease and ordinary-parent facts, and (X+) supplies repair by
> `w+ρ`.

- Status: 2026-09-28 — OPEN (r149 claim table lines 32–33: effective (L)
  OPEN, the proposed M1 exact-service argument SKETCH; r150 §5).
- Notes: r149 §4.1 (source support under effective N1) and §4.2 (lease
  and ordinary-parent facts after the two-lease boundary) are PROVED. The
  missing step is x3 at the service reads, that is, `ap.reach.v1`.
  `ap.reach.v1` ⇒ this entry, by `ap.Xplus.v1` (r150 lines 441–443).
- Kind: AP service fact (audit W02).

### `ap.L.fixedF.v1` — (L) under literal N1

- Variant `nj`. Source r147 §5, lines 409–429. File `fgsa-conditional.md`,
  sha256 `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Hypotheses: `env.r147` (with premises 4 and 5); `fg.N1.v1` with F and Z
  fixed on `[u,min(t_up,u+B_static))`; `u ≥ GST`.
- Statement (pinned):

> _fgsa-conditional.md, lines 409–429:_
>
> **Exact statement (L).** Under §1, let `u≥GST` and let the honest
> archival frontier at u be m. Let t_up be the first later time at which
> that frontier exceeds m, or infinity if there is none. Suppose fixed
> F and Z make N1 hold on `[u,min(t_up,u+B_static))`, and suppose the
> execution premises and horizon are available through `u+B_static`.
> Then `t_up≤u+B_static`; that is, a rise above m occurs by
>
> ```text
> u+B_static = u+ρ+2σ,
> ρ = 2L+G+8Δ,     σ = (g+3)P+G+6Δ.
> ```
>
> If no earlier rise ends the interval, base repair completes by u+ρ.
> Every later honest proposal whose full service interval remains in
> that interval receives exact honest HEAD service and a fresh fast
> write at all honest readers at its +6Δ gate. A selected honest
> opening supplies `C_fg` and a nonempty matching target or timeout row
> at every honest validator. Its next two honest slot proposers carry
> the branch and fold the rows. At most two such production steps are
> needed to exceed m. Statements about duties after the first rise are
> not part of (L).

- Status: 2026-09-28 — PROVED (FG-SA; r147 §5). r149 §4.4 (lines 443–445)
  confirms that the literal-N1 form stays PROVED.
- Scope: this entry states FG height progress. It is not a family entry
  (§0); it holds for the Simplex policy only.
- Status: 2026-09-28 — WITHDRAWN (audit W02). The statement stays PROVED but
  is misfiled: it states a height rise. It is refiled as
  `comp.rise.fixedF.v1`; its service parts are `ap.repair.fixedF.v1`,
  `ap.source.v1`, `ap.rowService.v1` and `ap.carrierKeep.v2`.

### `ap.L.movingF.v1` — (L) under effective N1

- Variant `nj`. Source r149 §4.4, lines 436–441. File
  `fgsa-conditional-close.md`, sha256
  `1ea1ccc5c944335b7e7793afe2c6675a056762e35eeaeee13ec1f6066460a902`.
- Hypotheses: `env.r149` (all liveness premises); `fg.N1eff.v1` on
  `[u,u+λ]`; `u ≥ GST`.
- Statement (pinned):

> _fgsa-conditional-close.md, lines 436–441:_
>
> > **(L), OPEN under effective N1.** Set `u_L=GST` and
> > `λ=ρ+2σ`, where `σ=(g+3)P+G+6Δ`. For every `u≥u_L`, m, and Zhat,
> > if the honest archival frontier at u is m and
> > `N1(u,u+λ;m,Zhat)` holds, then the frontier at `u+λ` exceeds m.
> > All execution, proposer, row-inclusion, and horizon premises in §1
> > apply. The initial reachable base state at u is arbitrary.

- Status: 2026-09-28 — OPEN (r149 claim table line 32; r150 claim table line
  25). The proposed M1 argument is SKETCH (r149 line 33).
- Notes: r149 §4.1 PROVES source support under effective N1 and lower F
  advances. The missing step is transport of the viable tree between the
  proposal view and an R1 HEAD view with a new F basis (r149 §4.3, lines
  417–424). `ap.reach.v1` is a sufficient lemma. bp marks the same claim H16
  SKETCH (bp §10, lines 1086–1101); r149 §4.3 shows that the bp argument
  misses one case. Scope as `ap.L.fixedF.v1`.
- Status: 2026-09-28 — WITHDRAWN (audit W02). The statement stays OPEN but is
  misfiled: it states a height rise. It is refiled as
  `comp.rise.movingF.v1`; its missing service part is
  `ap.repair.movingF.v1`.

### `ap.reach.v1` — common supported band prefix before the reset

- Variant `nj`. Source r150 §5, lines 400–414. File `fgsa-theorem-h.md`,
  sha256 `8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`.
- Hypotheses: `env.r150`; `fg.N1eff.v1` until the first rise or the service
  deadline; frontier m at `w ≥ GST`.
- Statement (pinned):

> _fgsa-theorem-h.md, lines 400–414:_
>
> Let the frontier at `w≥GST` be m, and suppose effective N1 holds
> until the first rise or the required service deadline. Let b be the
> first proposal label strictly after w and put `ℓ=b+2k−1`. For each
> honest proposal Q at `t_j>t_ℓ` used in the local repair and production
> argument, with its service interval before the rise, the missing
> sufficient lemma is:
>
> > **Reach(m).** There exists a block T that precedes the proposal
> > parent, is present and kept at the proposal and every same-slot
> > HEAD read, has `ht(T)≥m−1`, and is contained in every honest
> > label-(j−1) HEAD.
>
> This is x3 at the service reads. It must hold for every reachable
> initial state at w, without a previous reset, without an earlier
> successful honest repair, and without literal F constancy.

- Status: 2026-09-28 — OPEN (r150 claim table line 24).
- Implication, pinned from r150 §5, lines 441–450, PROVED:

> _fgsa-theorem-h.md, lines 441–450:_
>
> If Reach(m) is proved with the quantifiers above, r149 §4.2 supplies
> the remaining lease and ordinary-parent facts, and (X+) supplies
> repair by `w+ρ`. The r147 production argument then costs at most σ
> per promotion. Two promotions exceed m. Thus the precise conditional
> claim is
>
> ```text
> Reach(m) for every required service use
>   ⇒ effective (L) with u_L=GST and λ=ρ+2σ.
> ```

### `ap.source.v1` — each honest opening is a common fresh fast source

- Variant `nj`. Source r147 §5 "Common fresh source", lines 435–449. File
  `fgsa-conditional.md`, sha256
  `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Hypotheses: `env.r147`; a completed repair (`ap.repair.fixedF.v1`; under
  effective N1, `ap.repair.movingF.v1`, OPEN); the opening's service
  interval stays under N1.
- Service statement: from the repair on, for each honest opening at
  `p = T_r`, every honest validator has a fresh fast write of the opening
  block B at `a_r = p+6Δ`, and its source choice is B: `C_fg(i,r) = B` for
  every honest i.
- Statement (pinned):

> _fgsa-conditional.md, lines 435–440 (excerpt; line breaks reflowed):_
>
> After the repair in §4, choose a Rec(g) opening at `p=T_r`.

> _fgsa-conditional.md, lines 437–440 (excerpt; line breaks reflowed):_
>
> Section 4 gives every reader the raw result B and a fresh fast write at
> `a_r=p+6Δ`. B is in the action domain. Its fresh deadline is strictly
> greater than a_r. Every fast-written block at this label is a prefix of B,
> so the deepest candidate is exactly B:

> _fgsa-conditional.md, line 443:_
>
> ```text
> For all honest i: C_fg(i,r)=B.
> ```

> _fgsa-conditional.md, lines 447–449:_
>
> This is a source at **every** honest validator, not one reader's raw
> quorum relabelled as a public certificate. No FG source is required
> at earlier actions during the repair interval.

- Status: 2026-09-28 — PROVED (FG-SA; r147 §5) under literal N1. Under
  effective N1 it holds once `ap.repair.movingF.v1` holds (r149 lines
  444–446).
- Kind: AP service fact (audit W02). The height of B and the row that
  the Simplex client emits from it are not part of this entry; they are
  used in `comp.rise.fixedF.v1`.

### `ap.X.v1` — exact service from (x1) and (x2) only

- Variant `nj`. Source r149 §5.1, lines 463–467 (the bp claim of bp §2.4,
  lines 248–256). File `fgsa-conditional-close.md`, sha256
  `1ea1ccc5c944335b7e7793afe2c6675a056762e35eeaeee13ec1f6066460a902`.
- Statement (pinned):

> _fgsa-conditional-close.md, lines 463–467:_
>
> > **(X), REFUTED.** Let P be an honest proposal at slot u after GST with
> > parent A. If (x1) every honest live lease target at `v_u` is a prefix
> > of A, and (x2) at the proposal read and every honest HEAD at `v_u`,
> > `Z_d ⪯ A` and `h(A) ≥ H_d−1`, then every honest HEAD at `v_u` names P
> > and every honest S contains P at `d_u`.

- Status: 2026-09-28 — REFUTED (r149 §5.2–§5.3, a reachable integer
  execution with `n=4, a=1, Δ=16`; rechecked in r150 §8, lines 625–633).
- Status: 2026-09-28 — WITHDRAWN (audit W03). No composite may cite it. The
  replacement is `ap.Xplus.v1`.

### `ap.Xplus.v1` — exact service with x0 and x3

- Variant `nj`. Source r149 §6, lines 632–644. File
  `fgsa-conditional-close.md`, sha256
  `1ea1ccc5c944335b7e7793afe2c6675a056762e35eeaeee13ec1f6066460a902`.
- Hypotheses: synchronous proposal delivery; proposal-view relay readiness;
  (x1) and (x2) as in `ap.X.v1`; (x0) and (x3) as pinned.
- Statement (pinned):

> _fgsa-conditional-close.md, lines 632–644:_
>
> **(X+) — PROVED.** Let P be an honest proposal at slot u, with parent A.
> Assume synchronous proposal delivery and proposal-view relay readiness,
> (x1), (x2), and these two extra conditions:
>
> - **(x0)** A is the ordinary proposal walk result, with its lease start
>   removed.
> - **(x3)** There is a prefix T of A, present in the compared views, with
>   `h(T) ≥ max_d H_d−1`, where d ranges over the proposal and same-slot
>   HEAD reads. Every honest label-(u−1) HEAD contains T. At the proposal
>   read and each HEAD root, T is kept.
>
> Then every honest HEAD at `v_u` names P, and every honest S contains P
> at `d_u`.

- Status: 2026-09-28 — PROVED (FG-SA; proof r149 lines 646–677; r150 claim
  table line 18).
- Use rule (audit W03): a composite that uses this entry must prove x0, x1,
  x2 and x3 at each call. `comp.healed.v1` does this after the reset (r150
  §3). Before the reset, x3 is `ap.reach.v1` (OPEN); r149 §6 (lines 692–695)
  does not prove it.

### `ap.rowService.v1` — honest row inclusion

- Variant `both` (a proposer rule; FJ keeps it, r148 §2). Source r147 §1,
  premise 5, lines 76–80. File `fgsa-conditional.md`, sha256
  `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Statement (pinned):

> _fgsa-conditional.md, lines 76–80:_
>
> 5. Honest proposals include the specified current-window rows from the
>    pool and from held current-window blocks, except rows already on the
>    parent chain. Use `w_F≥1`, full-row deduplication, and distinct FG
>    identities. A faulty carrier may use old authentic rows. Stored
>    progress bits persist until that chain advances height.

- Status: 2026-09-28 — RULE. [async] RULE means true by the honest
  proposer's code, not a theorem. Its timed form is a premise of
  `comp.rise.fixedF.v1`.

### `ap.carrierKeep.v1` — carriers and maturity under N1

- Variant `nj`. Source r147 §5 "Carriers and maturity", lines 485–501. File
  `fgsa-conditional.md`, sha256
  `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Hypotheses: `env.r147`; `fg.N1.v1`; exact service after the r147 §4
  repair.
- Statement (pinned):

> _fgsa-conditional.md, lines 485–501:_
>
> **Carriers and maturity.** Let B1 and B2 be the honest proposals at
> p+4Δ and p+8Δ. Exact service keeps their parent chains above B. The
> round-r rows arrive before p+7Δ. B2 includes them unless its parent
> already includes them. If the chain still has height j, its entry
> remains T, so it folds at least q_F distinct matching identities.
> If it has already left j, the desired one-height promotion has occurred
> on this selected chain. Rows at different entries are never added.
>
> A target quorum can be consumed immediately. Otherwise the stored
> progress quorum is consumed once the chain's slot reaches
> `T.slot+2R`. Since `T⪯B`, this deadline is no later than p+2P.
> Select an honest proposal Q strictly after p+2P, within G. The branch
> from B2 remains selected: B2 itself had exact service and fresh fast
> support, and N1 retains its in-band path. If that branch is still at j,
> Q consumes its stored quorum. Otherwise it is already at least j+1.
> Q's +6Δ service establishes a common fast-supported block of height
> at least j+1 for the next step.

- Status: 2026-09-28 — PROVED (FG-SA; part of the r147 §5 proof of (L)).
- Status: 2026-09-28 — WITHDRAWN (audit W02). The statement stays PROVED but
  mixes block retention with FG entries, maturity and a rise. The block
  retention part is `ap.carrierKeep.v2`; the rest is in
  `comp.rise.fixedF.v1`.

### `ap.carrierKeep.v2` — the selected chain keeps the honest carrier blocks

- Variant `nj`. Source r147 §5 "Carriers and maturity", lines 485–486 and
  496–498. File `fgsa-conditional.md`, sha256
  `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Hypotheses: `env.r147`; `fg.N1.v1`; `ap.repair.fixedF.v1`;
  `ap.source.v1` for the opening B at p.
- Service statement: let B1 and B2 be the honest proposals at `p+4Δ` and
  `p+8Δ`, and Q an honest proposal strictly after `p+2P`, within G. By
  exact service, the parent chains of B1 and B2 stay above B. At Q, the
  branch from B2 is still selected while N1 holds.
- Statement (pinned):

> _fgsa-conditional.md, lines 485–486 (excerpt; line breaks reflowed):_
>
> Let B1 and B2 be the honest proposals at p+4Δ and p+8Δ. Exact service
> keeps their parent chains above B.

> _fgsa-conditional.md, lines 496–498 (excerpt; line breaks reflowed):_
>
> Select an honest proposal Q strictly after p+2P, within G. The branch from
> B2 remains selected: B2 itself had exact service and fresh fast support,
> and N1 retains its in-band path.

- Status: 2026-09-28 — PROVED (FG-SA; r147 §5).
- Kind: AP service fact (audit W02): block retention only. Row folding
  is `ap.rowService.v1`; entries, maturity and consumption are Simplex
  transition facts, used in `comp.rise.fixedF.v1`.

### `ap.honestSourced.v1` — one fresh source per action

- Variant `both` (FJ keeps the `C_fg` rule, r148 §2). Sources: r143 §3.1,
  lines 226–244 (the rule), and r143 §10.1, lines 846–851 (compatibility).
  File `fgsa-fast.md`, sha256
  `8907540c5c71fe06703bc8d2ec2d30bc6cbc752a5f7577219a69196e2fd8ef37`.
- Statement (pinned):

> _fgsa-fast.md, lines 226–244:_
>
> At the FG action a_r, after the scheduled gate, put s=rR. This is the
> latest scheduled SA gate, including a gate that returned no result. Use:
>
> ```text
> Candidates = {B∈D_action : B∈FastWrite_i[s] and E_i(B)>a_r};
> C_fg = deepest candidate, or none if Candidates is empty.
> ```
>
> No older set may replace an empty `FastWrite_i[s]`. Sleeping does not make
> an old gate the latest gate. The candidates lie on the local raw result's
> ancestor path, so the deepest choice is unique. A deterministic root tie
> rule can be retained but is not needed on a valid local path.
>
> B need not have slot s. In particular, the source can be an old block with
> a fresh fast renewal. Its immutable entry `T=σ[B].T_h` can be older still.
> The height pair uses `(σ[B].h,T,σ[B].nj)`, not the source's slot and not
> the cache maximum. The source qualification applies before every client
> branch. A repeat still needs a current fresh source, but **the named entry
> does not need a new lease or a new slot**.

> _fgsa-fast.md, lines 846–851:_
>
> Two same-round fresh sources are prefixes of synchronous same-label
> genuine results. They are compatible. If their source heights are H+1,
> immutable entry equality on a plateau gives the same T. No G2/genuine
> comparison remains. The proof also covers a present source whose pair is
> empty; at this first new height an incompatible lock cannot precede all
> honest rows, since its QC would contain an earlier honest target.

- Status: 2026-09-28 — PROVED (FG-SA; r143 §10.1 "PROVED locally"; r146
  claim 4, freshness equivalence, PROVED).
- Status: 2026-09-28 — WITHDRAWN (audit W02). The statement stays PROVED
  but includes Simplex client and transition facts. The service part is
  `ap.honestSourced.v2`.

### `ap.honestSourced.v2` — one fresh source per action (service form)

- Variant `both` (FJ keeps the `C_fg` rule, r148 §2). Source r143 §3.1,
  lines 226–237, and §10.1, lines 846–847. File `fgsa-fast.md`, sha256
  `8907540c5c71fe06703bc8d2ec2d30bc6cbc752a5f7577219a69196e2fd8ef37`.
- Statement (pinned):

> _fgsa-fast.md, lines 226–237:_
>
> At the FG action a_r, after the scheduled gate, put s=rR. This is the
> latest scheduled SA gate, including a gate that returned no result. Use:
>
> ```text
> Candidates = {B∈D_action : B∈FastWrite_i[s] and E_i(B)>a_r};
> C_fg = deepest candidate, or none if Candidates is empty.
> ```
>
> No older set may replace an empty `FastWrite_i[s]`. Sleeping does not make
> an old gate the latest gate. The candidates lie on the local raw result's
> ancestor path, so the deepest choice is unique. A deterministic root tie
> rule can be retained but is not needed on a valid local path.

> _fgsa-fast.md, lines 846–847 (excerpt; line breaks reflowed):_
>
> Two same-round fresh sources are prefixes of synchronous same-label
> genuine results. They are compatible.

- Status: 2026-09-28 — PROVED (FG-SA; r143 §10.1 "PROVED locally"; r146
  claim 4).
- Kind: AP service fact (audit W02). v1 also pinned the height-pair fields
  and the equality of entries on a plateau; those are Simplex client and
  transition facts (`fg.provenance.v1`, bp §7.5).
- Note (2026-09-28): `fg.provenance.v1` is SUPERSEDED. The client and
  entry facts are `fg.provenance.v2` and `comp.provenance.v1`.

### `ap.armedSafe.v1` — clean safety and P1 with the FG

- Variant `nj`. Source r146 §3, claims 1a–1c, lines 26–28 (claim table),
  359–364 and 389–392. File `fgsa-adjudicate.md`, sha256
  `0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017`.
- Statement (pinned):

> _fgsa-adjudicate.md, lines 26–28:_
>
> ```text
> │ 1a │ Clean safety and monotonicity, all a<h          │ PROVED  │
> │ 1b │ Clean honest-proposal inclusion in 6Δ, all a<h  │ PROVED  │
> │ 1c │ Fast and slow P1, with their original premises  │ PROVED  │
> ```

> _fgsa-adjudicate.md, lines 359–364:_
>
> This induction uses `a<h`, not `a≤f` and not FG quorum turnout. It
> proves clean safety, monotonicity, and 6Δ service. F and S remain on
> the same chain. The accessor is their greater prefix and is monotone.
> The changed proof follows the origin/root/parent/HEAD/guard order in
> `CleanInclusion.lean`; it does not instantiate that theorem on a
> different executable `Run`.

> _fgsa-adjudicate.md, lines 389–392:_
>
> Release has at most a conflicts, below τ. Expiry is after b₁. A new
> conflicting S write fails the guard; an ancestor result keeps S. Finality
> has a compatible target origin and cannot remove B at the accessor.
> Both P1 claims follow with `Π=min(η,L)` and the original lags.

- Status: 2026-09-28 — PROVED (FG-SA; r146 1a–1c).
- Status: 2026-09-28 (ldp) — under ALFS (spec 183f2c40) (the FJ form): base P1 and the
  clean claims for all `a<h` are PROVED (paper) (ldp L8, lines 378–394;
  §10.3, lines 849–857). See `fj.armedSafe.v1`.
- Status: 2026-09-28 (r158) — under ALFS (the FJ form), independently
  checked by r158: as in `fj.armedSafe.v1` (r158 §5, lines 560–613; table
  lines 885–887).

### `ap.outputRecovered.v1` — ordinary outputs recover after the reset

- Variant `nj`. Source r150 §4.5, lines 374–387. File `fgsa-theorem-h.md`,
  sha256 `8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`.
- Hypotheses: `env.r150`; the actual reset of `fg.baseSel.nj.v1`.
- Statement (pinned):

> _fgsa-theorem-h.md, lines 374–387:_
>
> **Theorem H — PROVED.** Under §1 and the actual reset of §1, the run
> is FG-healed from q_s*. There is a repair gate `t_h=d_u` such that,
> for all times from t_h onward, all honest S values lie on one chain,
> each honest S is monotone, every accepted honest F is a prefix of
> every honest S, and every honest proposal emitted from t_h onward
> is in every honest S within 6Δ.
>
> The bound is
>
> ```text
> t_h ≤ t_(s*) + 2L+G+4Δ
>     = q_(s*) + 2L+G−Δ
>     = a_(r*) + 2L+G−2Δ.
> ```

- Status: 2026-09-28 — PROVED (FG-SA; r150 claim table line 23).
- Note: this is the local part of `comp.healed.v1`. It uses
  `comp.theoremN.v1`, so it is not a policy-uniform service fact
  (FRAMEWORK-DESIGN.md §7.3).
- Status: 2026-09-28 — WITHDRAWN (audit W02). The statement stays PROVED
  but depends on `comp.theoremN.v1`, so it is not an AP service fact.
  The local Theorem H clause of `comp.healed.v1` covers it.

### `ap.finalityHead.v1` — current-slot finality head

- Variant `nj`. Source r146 §5.4, item 1, lines 676–678. File
  `fgsa-adjudicate.md`, sha256
  `0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017`.
- Statement (pinned):

> _fgsa-adjudicate.md, lines 676–678:_
>
> 1. At the selected honest opening-plus-two-slots window, the separate
>    **current-slot finality head** is the slot-1 proposal, with the
>    required latest justification and permitted finality record.

- Status: 2026-09-28 — SKETCH (r146 claim 3g, environment-only first
  finality). It is used for finality liveness only.
- Status: 2026-09-28 — WITHDRAWN (audit W02). The statement stays SKETCH but
  includes the finality record permission, a Simplex client fact. The
  base-walk part is `ap.finalityHead.v2`; the record part is an
  obligation of `comp.finality.v1`.

### `ap.finalityHead.v2` — current-slot finality head (base walk only)

- Variant `nj`. Source r143 §11.2, interface I item 3, lines 996–999. File
  `fgsa-fast.md`, sha256
  `8907540c5c71fe06703bc8d2ec2d30bc6cbc752a5f7577219a69196e2fd8ef37`.
- Statement (pinned):

> _fgsa-fast.md, lines 996–999 (excerpt; line breaks reflowed):_
>
> In an honest opening-plus-two-slots window, the action's separate finality
> head is the slot-1 proposal. Current honest HEADs cover it; the actual R1
> root and effective leases permit that walk. Slot bounds then give
> equality.

- Status: 2026-09-28 — SKETCH (r146 claim 3g; r143 §11.2 "First-finality
  assembly: SKETCH"). It is used for finality liveness only.
- Kind: AP service fact (audit W02). The permitted finality record
  ("Its finality records are absent or aligned") is a Simplex client
  fact and is an obligation of `comp.finality.v1`.

### `ap.fastSupport.v1` — a fast write has an honest supporter

- Variant `both` (no frame premise). Sources: r143 §3.1, lines 208–218
  (file `fgsa-fast.md`, sha256
  `8907540c5c71fe06703bc8d2ec2d30bc6cbc752a5f7577219a69196e2fd8ef37`); the
  SA rule, sa lines 83–91, 157–161 and 219 (file `slow-arming.md`, sha256
  `c1d1a4e343c6910a1072cc7e6e8816b6ab6ac94b4940f204573f3a39c500db0b`); the
  SA Lean model, acG lines 352–354, 416–420 and 441–446 (file
  `AvailableChainGridCO/Model/Protocol.lean` at main `03bd912`, sha256
  `f2e8afcecfe06101852ddddb2b0002a764982d34413edcac0f958dc7934b86bc`;
  refreshed 2026-09-29: the cited text is byte-identical to the registered
  lines 381–383, 431–435 and 456–461 at `1a3f73a`, sha256 `2cb079fd…`,
  and to lines 381–383, 445–449 and 470–475 at `3e48c9f`, sha256
  `09daa0d5…`; E-3 moved the walk definitions to GridCO/Model/Walk); bp
  F-table row B3, line 314.
- Hypotheses: the static faulty set has size a with `h > a` and
  `h + a ≤ n` (so `a < τ`; under `a≤f` also `τ > a`); authentic HEADs.
- Service statement: let B ∈ `FastWrite_i[s]` at an honest reader i. Then
  B has at least τ distinct supporting seats at label s that survive the
  late equivocation test at i. Since `τ > a`, at least one of them is
  honest, and its label-s HEAD extends B.
- Statement (pinned):

> _fgsa-fast.md, lines 208–218:_
>
> Keep an immutable gate result and a local set `FastWrite_i[s]` at each
> completed gate. A block is in this set exactly when all of the following
> held at d_s:
>
> ```text
> B ≠ genesis;
> C_i[s] exists and B⪯C_i[s];
> 2*p_i(s,B) > |D_i[s]| and p_i(s,B) ≥ τ;
> the whole-result SA lease guard passed;
> the gate executed its lease write or renewal for B by the fast test.
> ```

> _slow-arming.md, lines 83–91:_
>
> Keep saved early support, the late participant pool, equivocation
> removal, full proposal-view merge, declared support subsets, block-slot
> guards, and old-block eligibility. For a raw genuine result `C_i[r]`
> and its non-genesis prefix B, write `p_i(r,B)` for B's surviving early
> support. It is an integer count from label r alone. In particular,
>
> ```text
> 2 p_i(r,B) > |D_i[r]|.
> ```

> _slow-arming.md, lines 157–161:_
>
> There is a useful absolute bound, but it comes from the regime:
>
> ```text
> h>a and h+a≤n  ⇒  a≤floor((n−1)/2)<τ=ceil(n/2).
> ```

> _slow-arming.md, line 219:_
>
> ```text
> fast_i(r,B) ⇔ B ⪯ C_i[r] and p_i(r,B)≥τ.
> ```

> _AvailableChainGridCO/Model/Protocol.lean at `1a3f73a`, lines 381–383,
> 431–435 and 456–461 (at `3e48c9f`: 381–383, 445–449 and 470–475; at
> `03bd912`: 352–354, 416–420 and 441–446; the same text):_
>
> ```lean
> def cleanSupport (p : Params) {n : Nat} (st : State n) (r : Slot) : List (Wire n) :=
>   (earlyVotes p st r).filter (fun o =>
>     !(lateVotes p st r).any (fun u => sameSeat u o && u != o))
> def prefixSupport (p : Params) {n : Nat} (st : State n) (r : Slot) (b : Block) : Nat :=
>   goldfishScore st.blocks (cleanSupport p st r) (cleanSupport p st r) b
>
> /-- The single SA release threshold is the ceiling of half the seats. -/
> def releaseThreshold (p : Params) : Nat := (p.n + 1) / 2
> def admissionLevels [LeasePolicy] (p : Params) {n : Nat} (st : State n)
>     (r : Slot) (b : Block) : List Nat :=
>   if LeasePolicy.slowArming then
>     if releaseThreshold p ≤ prefixSupport p st r b || slowEligible p st r b then
>       [releaseThreshold p] else []
>   else
> ```

- Status: 2026-09-28 — PROVED. The support count is RULE (the fast
  admission test); the honest supporter follows from `τ > a`. bp B3 states
  the same fact.
- Kind: AP service fact (audit W02): source safety. It is the SA half of
  the v1 provenance sentence "Each such C has an honest supporter since
  `τ>a`" (`fg.provenance.v1`).
- Note: the Lean model has no separate `FastWrite` record. The fast test is
  the first disjunct of `admissionLevels` (acG line 444 at `03bd912`; line 473 at `3e48c9f`; line 459 at `1a3f73a`). A Lean statement
  of this entry must name that disjunct, not the slow one.

### `ap.headReachesLo.v1` — the AP head is in D at height at least lo

- Variant `fj` (its premise is the FJ frame `fj.frame.v1`). Sources: r148
  §2, lines 188–192 and 223–230, and §7 F10, line 590 (file
  `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`); spec
  section "Duties and handlers", lines 518–526 (eligibility) and 528–535
  (walks), and the walk code, lines 902–924 and 938–955 (file
  `spec/fgsa-protocol.tex`, sha256
  `ae4497abc7c5b3a6f73697f341bf730a63c7d34bd2f7546154bd022bc95af223`).
- Lean plan: — (an AP service fact; the SA instance is later work).
- Hypotheses: `fj.frame.v1`; R1 duty views; `fg.finalLock.v1` and `a≤f`
  (so that Z ∈ D, r148 lines 223–228; clean and P1 runs with `a<h` use
  the source argument of r148 §5 instead).
- Service statement: for each duty view V and its FJ frame (Z, lo, D)
  (`fj.frame.v1`), the AP head read from V is in D and has state height
  ≥ lo. This holds in every phase (gap, uncontested and contested).
- Kind (user design correction 2026-09-28, relayed by ethereum-f1): the
  FG module exports only the frame Z, lo, D and viability. Eligibility,
  the majority test, the current-slot rule, the GHOST score and the walk
  are AP fork-choice machinery. This entry is the AP obligation that
  connects them to the frame.
- Statement (pinned):

> _fj-redteam.md, lines 188–192:_
>
> Full proposal and finality-head reads use OTHER_VIEW. HEADs use
> HEAD_VIEW. A lease outside D stays in the raw guard and release test.
> The code must change both viability and below-band eligibility in a
> contest. Changing only one does not supply the proof that the walk
> reaches H.

> _fj-redteam.md, lines 223–230:_
>
> Under a≤f, this distinction does not create an empty choice domain.
> Every frontier block has height above the height of accepted F: a
> finalization at y has a justification carrier at height at least y+1.
> The finalized-crossing law puts every such frontier block above F.
> In the J case, the carrier witnesses J's viability. In the contested
> case, a frontier witness makes F viable at lo=H. Below lo every viable
> node has a viable child, so the walk reaches lo. Clean and P1 runs with
> a<h use the source argument in §5 instead of this BFT crossing law.

> _fj-redteam.md, line 590 (excerpt; the first sentence):_
>
> In a contest, an actual head reaches H.

> _fgsa-protocol.tex, lines 518–526:_
>
> ```latex
> The domain $\Dom$ is the set of blocks $B\in V$ with $F\preceq B$,
> $Z\preceq B$, and a $W\in V$ with $B\preceq W$ and $\sigma[W].h\geq\lo$.
> A child of a block with state height below~$\lo$ is eligible without a
> majority.  Thus in a contest the band is $\{H\}$ for both viability and
> eligibility.  The code must change both: a contest that changes only
> one of them can stall the FG for ever~\FJ{7} (N12).  The contest test is
> a sufficient local certificate that $J$ cannot finalize; its negation
> does not show that $J$ can finalize~\FJ{3}.  Do not replace it by a
> test for a visible timeout~\FJ{3} (F4).
> ```

> _fgsa-protocol.tex, lines 528–535:_
>
> ```latex
> \paragraph{Walks.}  Every walk runs inside the domain of its own view.
> The walk starts at the \emph{live root}: the deepest live lease target
> in~$\Dom$, or $Z$ when there is none~\ADJ{2}.  A lease outside~$\Dom$
> has no choice authority at this duty, but it stays in the gate guard
> and in the release test.  A lease on an ancestor of~$Z$ is already
> satisfied.  There is no unfiltered fallback.  The walk uses the SA
> score (raw equivocators plus clean declared supporters above the block)
> and the eligibility of~\DC{5} with~$\lo$ in place of $\Sigma.\hmax-1$.
> ```

> _fgsa-protocol.tex, lines 902–924:_
>
> ```latex
> \Function{ghost}{$\mathit{anchor},\mathit{tree},
>   \mathit{score},\mathit{eligible}$}
>   \Comment{\DC{7}, unchanged}
>   \State $H\gets\mathit{anchor}$
>   \Loop
>     \State $\mathit{children}\gets\{B:B\text{ is a child of }H\text{ in }
>       \mathit{tree},\ \mathit{eligible}(B)\}$
>     \If{$\mathit{children}=\emptyset$} \State \Return $H$ \EndIf
>     \State $H\gets\arg\max_{B\in\mathit{children}}\mathit{score}(B)$,
>       ties by root order
>   \EndLoop
> \EndFunction
> \vspace{1pt}
> \Function{goldfish\_eligible}{$\Sigma,\lo,\mathit{votes},
>   \mathit{support\_votes},s,B$}
>   \Comment{\DC{7}, adapted: frame band floor}
>   \State $\mathit{voters\_count}\gets
>     |\{i:\mathit{votes}\text{ holds a vote by seat }i\}|$
>   \State \Return $\Sigma.\sigma[B.\parent].h<\lo$
>     or $2\,\Call{goldfish\_score}{\mathit{votes},
>       \mathit{support\_votes},s,B}>\mathit{voters\_count}$
>     or $B.\slot=\Sigma.s$
> \EndFunction
> ```

> _fgsa-protocol.tex, lines 938–955:_
>
> ```latex
> \Function{live\_root}{$\Sigma,Z,\Dom$}
>   \Comment{\SAS, redefined by \ADJ{2}: in the domain}
>   \State $\mathit{targets}\gets\{B\in\Dom:\Sigma.\lease[B]\neq\bot\}$
>   \Comment{they lie on one chain}
>   \If{$\mathit{targets}=\emptyset$} \State \Return $Z$ \EndIf
>   \State \Return the deepest $B\in\mathit{targets}$
> \EndFunction
> \vspace{1pt}
> \Function{get\_head\_in\_tree}{$\Sigma,V,
>   \mathit{votes},\mathit{support\_votes},k$}
>   \Comment{\DC{7}, redefined by \ADJ{2} and \FJ{2}}
>   \State $(Z,\lo,\Dom)\gets\Call{fg\_frame}{\Sigma,V}$
>   \Comment{R1: the frame of this view}
>   \State $A\gets\Call{live\_root}{\Sigma,Z,\Dom}$
>   \Comment{root priority; lease start}
>   \State \Return $\Call{goldfish\_fork\_choice}{\Sigma,A,\Dom,\lo,
>     \mathit{votes},\mathit{support\_votes},k}$
> \EndFunction
> ```

- SA discharge (registry, 2026-09-28). The SA walk is
  `get_head_in_tree` (spec lines 946–955).
  1. Start in D. The walk starts at the live root A: the deepest live
     lease target in D, else Z (spec lines 529–530, 938–944). If A is a
     lease target, A ∈ D by definition. If A = Z, then Z ∈ D: in the J
     case the J carrier (height H ≥ lo) witnesses J; in the F cases a
     frontier block at height H > h(F) extends F by `fg.finalLock.v1`
     and witnesses F at lo ≤ H (r148 lines 223–228).
  2. Stay in D. `ghost` moves only to children in its tree argument, and
     the tree is D (spec lines 907–908, 953).
  3. No stop below lo. Let X ∈ D with `σ[X].h < lo`. X has a witness
     W ∈ V with `X ⪯ W` and `σ[W].h ≥ lo`, so X ≠ W. Let Y be the child of
     X on the path to W. Then `F ⪯ X ⪯ Y`, `Z ⪯ X ⪯ Y` and `Y ⪯ W`, and V is
     ancestor-closed, so Y ∈ D. The parent X of Y has state height below
     lo, so Y is eligible without a majority (spec line 920). Thus X has an
     eligible child, and `ghost` does not return X.
  4. Stop. The tree is finite and each step goes to a child, so `ghost`
     returns a block. By steps 2 and 3 it is in D with state height ≥ lo.
  This uses the eligibility threshold lo in both viability and
  eligibility, in every phase. The start at the live root and the in-band
  choice by score stay AP data; this entry says nothing about which block
  at or above lo the walk returns.
- Status: 2026-09-28 — PROVED (FG-SA; paper, r148 lines 223–230 and 590;
  SA discharge above).
- Note (2026-09-28): the frame side of its feasibility is
  `fj.frameFeasible.v1` (D ≠ ∅ and D reaches lo). Step 1 of the SA
  discharge uses its part (2).
- Note (2026-09-28, ALFS): the service statement and its SA discharge are
  for the view form `fj.frame.v1`. Under ALFS (`fj.frame.v2`) the walk
  starts at `live_root`, taken in the full filtered tree, and walks the
  frozen voter tree; the start can lie outside that tree. When the frozen
  domain is empty (a late contest), the HEAD returns its anchor (ldp L6,
  lines 354–356; O3, lines 544–546). This entry is not re-proved for
  ALFS.
- Note (2026-09-28): the ALFS form is `ap.headReachesLo.v2`. This entry
  stays as the view form; it is not superseded.
- Note: the weaker form "the AP does not block leaving H−1" is NOT enough.
  An AP that lets the head leave H−1 but keeps it at H−1 for another
  reason gives the N12 stall. r148 F11 tests the old band `{H−1,H}` in
  viability and eligibility with the FJ root test: the frontier stays at
  3 for ever, while FJ with `lo = H` reaches height 4:

> _fj-redteam.md, lines 599–601:_
>
> F11 — REFUTED. Here is N12 with exact receipts, starting from genesis.
> The tested variant has FJ's frontier root test, but always uses the
> old band {H−1,H}, in both viability and eligibility.

> _fj-redteam.md, lines 728–733:_
>
> Within rules with root F in a contest and one uniform witness
> threshold lo, lo=H is the least threshold that excludes every
> unsupported H−1 branch. H−1 fails by this execution; lo>H has no
> witness at all. A different branch-dependent filter could work, but
> it needs its own proof. This does not prove that every possible
> alternative band design fails.

- Note (2026-09-28; §0 rule (a)): `fj.frame.v2` is SUPERSEDED by
  `fj.frame.v3` (spec bd942ca0: Σ.T in place of Σ.T_F, the same set;
  `update_finality` also calls `reconcile_with_finality`, which writes no
  frame input). A citation of `fj.frame.v2` here reads as `fj.frame.v3`.
- Note (2026-09-29; current use): `fj.frame.v3` is WITHDRAWN for current
  use; its successor is `fj.frame.v4` (spec `fgsa3`). The frame controls
  do not change; the Trees clauses change (no deletion from Σ.T, the SA
  walk starts at Σ.F). The note above is history. A current citation of
  `fj.frame.v2` or `fj.frame.v3` here reads as `fj.frame.v4`.
- Note (2026-09-29; current use): `fg.finalLock.v1` is WITHDRAWN for current
  use. The citations above are history. A current use of this entry
  reads them as §9, "Current reading of withdrawn ids".


### `ap.headReachesLo.v2` — the AP head under ALFS (frozen tree, live anchor)

- Variant `fj` (its premise is the ALFS frame `fj.frame.v2`). Sources:
  ldp §4.5–§4.6 (L5, L6), lines 316–360, and §9.4 (C5), lines 695–706 and
  737–747 (file `fgsa-live-dc-port.md`, archived as
  `tsc/archive/fgsa-live-dc-port-81677672.md`, sha256
  `816776723e439f24612c409f2007c2a236bb3fa2dbde605c68516333ee4c7b38`); the
  ALFS spec `ghost` and `goldfish_eligible`, lines 978–1000, `live_root`,
  lines 1014–1026, and `get_head_in_tree`, lines 1028–1035 (file
  `spec/archive/fgsa-protocol-183f2c40.tex`, sha256
  `183f2c409f03542dbdf3f9461924077437710b74720d09b32a42d3bdb3f04afb`).
- Lean plan: — (an AP service fact; the SA instance is later work).
- Hypotheses: `fj.frame.v2`; `fj.frameFeasible.v1` part (4) on the frozen
  voter tree (ancestor-closed); for clause 4, the ALFS recovery premises
  of ldp §2 and the premises of L5 (an honest proposal after GST and
  after the two-lease boundary of a phase).
- Service statement (registry, 2026-09-28). For a HEAD duty, let V be its
  frozen voter tree, (Z, lo) the store controls (`fj.frame.v2`), D_V the
  filtered domain of V, and A = `live_root` (the deepest live lease in the
  full filtered tree, else Z).
  1. If A ∈ D_V, or A has an eligible child in D_V, the AP head is in D_V
     and has state height ≥ lo.
  2. Otherwise the AP head is A (the anchor fallback). A can lie outside
     the walked tree (DC's rule, ldp lines 594–597).
  3. If A = Z and D_V ≠ ∅, then Z ∈ D_V, so clause 1 applies.
  4. After the two-lease boundary, with the HEAD's live frame equal to the
     proposer's, a fallback needs D_V = ∅, and an empty D_V needs a
     contest event in `(t_s−Δ, v_s)`: at most 2 such slots per frontier,
     at most 4 before the reset, and none after it (C5, ldp lines
     697–706). Before the boundary, a fallback is part of the initial
     repair ρ (ldp lines 737–738). The FJ producer charges these slots.
- Note on the requested form (2026-09-28): the form "if D_V ≠ ∅, the head
  is in D_V" holds under clause 4's premises, not in general. `ghost`
  returns its anchor when the anchor has no eligible child in the walked
  tree (spec lines 983–985). A live lease A outside D_V, with D_V ≠ ∅, can
  therefore be the head before the boundary.
- SA discharge (registry, 2026-09-28), as in `ap.headReachesLo.v1`, with
  the start at `live_root` and DC's rule that the walk may start outside
  the walked tree (spec lines 1028–1035).
  1. Clause 1. If A ∈ D_V, the v1 steps 2–4 apply with tree D_V: the walk
     stays in D_V, and below lo every block of D_V has an eligible child
     in D_V (`fj.frameFeasible.v1` part (4); the frozen voter tree is
     ancestor-closed; eligibility uses `band_floor`, spec line 996). If
     A ∉ D_V and A has an eligible child Y ∈ D_V, the walk moves into D_V
     at its first step, and the same steps apply from there.
  2. Clause 2. `ghost` returns its anchor when the anchor has no eligible
     child in the tree (spec lines 983–985).
  3. Clause 3. Let B ∈ D_V with witness W ∈ V, `h(W) ≥ lo`. Then
     `Z ⪯ B ⪯ W`, Z ∈ V by ancestor closure, `F ⪯ Z`, and W witnesses Z,
     so Z ∈ D_V.
  4. Clause 4 is ldp C5 (lines 697–706), with L5 step 3 (a nonempty
     domain when the frames are equal) and L6 (the three event cases).
  The start at `live_root` and the in-band choice by score stay AP data.
- Statement (pinned):

> _fgsa-live-dc-port.md, lines 316–360:_
>
> ### 4.5 L5 — HEAD agreement after repair (PROVED)
>
> Premises: honest proposal P at `t_s` after GST and after the two-lease
> boundary of a phase, and no event in `(t_s−Δ,v_s)`.
>
> 1. **Nonempty domain.** The frontier H exceeds `ht(F)` (a finalization at
>    y has a carrier at y+1). Every height-H block extends F (crossing), and
>    extends J in an uncontested top frame. So the proposer's full domain
>    is nonempty. A viable block below lo has a viable child, which is
>    eligible, so the proposer's walk stops at A with `ht(A)≥lo`.
> 2. **Same frame.** No event in the window, and L3 for F.
> 3. **Candidates.** By L1 each child candidate at x is a proposer candidate
>    or lies on `anc(P)`. A competitor off P's path has its witness in the
>    proposer's store. Scores and eligibility are equal (same votes, same
>    lo). The path to A is viable at x through A itself, which is in `anc(P)`.
> 4. **Walk.** From x's anchor (⪯A, L4), each step picks the proposer's
>    choice: a subset of candidates that contains the maximum keeps it. At
>    A the proposer found no eligible old child, so x finds none. P is the
>    one valid current-slot child. P has no stored child. **HEAD = P.**
>
> This is SA's `honest_proposal_heads_of_ordinary_parent` with the FG frame
> added. DC's analog is `fixedHeightJustificationRoot_namedOpeningVoteStoresExtend`,
> whose SG-root premise `get_sg_root ⪯ A` becomes L4. Then r156 §5.1 gives:
> release of conflicts at `q_s`, raw result exactly P with support at least
> h at `d_s`, fast write, guard passes.
>
> ### 4.6 L6 — frame ahead of view (PROVED)
>
> When an event reaches x after `z_(s−1)` and before `v_s`, x's caches have
> it and x's block view does not. Three cases:
>
> - **Frontier rise to H without contest.** `lo=H−1`. The new carrier X
>   crossed `H−1` with a quorum that has an honest row for the entry E at
>   `H−1`. That row's source contained E and was held before its action,
>   hence before `z_(s−1)` (r156 §1.2 timing). E is in the view. So every
>   block that X witnesses keeps a view witness (E). No loss.
> - **Top J.** Root J; J has honest target rows, so J is in the view, and
>   `ht(J)=H−1=lo`. The domain is J's subtree. No empty domain.
> - **Contest, or a rise into a contest.** `lo=H`. The view can lack every
>   height-H block. Then the view domain is empty and the HEAD returns the
>   anchor. DC does the same: an empty filtered view returns the SG root.
>
> In each case the slot is the one charged by L2. The anchor case cannot
> break L8: in a P1 run the anchor is a live lease that extends the armed
> block B (§4.8).

> _fgsa-live-dc-port.md, lines 695–706:_
>
> ### 9.4 The root (anchor) fallback on the SA side (C5, PROVED)
>
> **When it occurs.** A HEAD falls back to its anchor X (the FG root if no
> live lease is in the full domain) only when its frozen domain is empty.
> If the HEAD's live frame equals the proposer's, P's path carries A with
> `ht(A)≥lo`, so the domain is not empty (L5 step 3). F moves never empty it
> (C1). A top J is in the view at height lo, and in a band rise the crossed
> entry E is in the view (L6). So a fallback needs an event in `(t_s−Δ,v_s)`
> that puts the node in a contest frame (first contest witness, or a rise
> into a contest). By L2 this is at most two slots per frontier, and before
> the reset only frontiers M and M+1 count: at most four slots in all.
> After the reset no contest exists above M+1, so no fallback occurs.

> _fgsa-live-dc-port.md, lines 737–747:_
>
> Before the boundary X need not precede A; then its effect is part of the
> initial repair ρ, which the bound already pays.
>
> **FJ does not make it a lever.** The contest root F and the band `lo=H`
> produce an empty frozen domain only while the height-H blocks are newer
> than the freeze. A known contest stays on at fixed (H, J); old height-H
> blocks are in every later frozen view; new old-stock W blocks at H do
> not change the frame and cannot empty a domain that already holds
> height-H blocks. So the adversary gets one fallback slot per contest
> event and per rise, not one per slot. DC has the same one-slot effect
> with its SG root; FJ adds at most the contest event per frontier.

> _fgsa-protocol-183f2c40.tex, lines 978–1000:_
>
> ```latex
> \Function{ghost}{$\mathit{anchor},\mathit{tree},
>   \mathit{score},\mathit{eligible}$}
>   \Comment{\DC{7}, unchanged}
>   \State $H\gets\mathit{anchor}$
>   \Loop
>     \State $\mathit{children}\gets\{B:B\text{ is a child of }H\text{ in }
>       \mathit{tree},\ \mathit{eligible}(B)\}$
>     \If{$\mathit{children}=\emptyset$} \State \Return $H$ \EndIf
>     \State $H\gets\arg\max_{B\in\mathit{children}}\mathit{score}(B)$,
>       ties by root order
>   \EndLoop
> \EndFunction
> \vspace{1pt}
> \Function{goldfish\_eligible}{$\Sigma,\mathit{votes},
>   \mathit{support\_votes},s,B$}
>   \Comment{\DC{7}, redefined (a): band floor}
>   \State $\mathit{voters\_count}\gets
>     |\{i:\mathit{votes}\text{ holds a vote by seat }i\}|$
>   \State \Return $\Sigma.\sigma[B.\parent].h<\Call{band\_floor}{\Sigma}$
>     or $2\,\Call{goldfish\_score}{\mathit{votes},
>       \mathit{support\_votes},s,B}>\mathit{voters\_count}$
>     or $B.\slot=\Sigma.s$
> \EndFunction
> ```

> _fgsa-protocol-183f2c40.tex, lines 1014–1026:_
>
> ```latex
> \Function{live\_root}{$\Sigma$}
>   \Comment{\DC{7} \fname{get\_sg\_root}, redefined (b); \SAS{} \fname{live\_root}}
>   \State $\mathit{tree}\gets\Call{get\_filtered\_block\_tree}{\Sigma}$
>   \Comment{the full filtered tree, not a view}
>   \State $\mathit{targets}\gets\{B\in\mathit{tree}:\Sigma.\lease[B]\neq\bot\}$
>   \Comment{they lie on one chain}
>   \If{$\mathit{targets}=\emptyset$}
>     \State \Return $\Call{get\_fg\_root}{\Sigma}$
>     \Comment{no live lease in the tree}
>   \EndIf
>   \State \Return the deepest $B\in\mathit{targets}$
>   \Comment{the deepest live lease in place of grade~1}
> \EndFunction
> ```

> _fgsa-protocol-183f2c40.tex, lines 1028–1035:_
>
> ```latex
> \Function{get\_head\_in\_tree}{$\Sigma,\mathit{tree},
>   \mathit{votes},\mathit{support\_votes},k$}
>   \Comment{\DC{7}, adapted (b): live root}
>   \State $A\gets\Call{live\_root}{\Sigma}$
>   \Comment{in place of \fname{get\_sg\_root}}
>   \State \Return $\Call{goldfish\_fork\_choice}{\Sigma,A,
>     \mathit{tree},\mathit{votes},\mathit{support\_votes},k}$
> \EndFunction
> ```

- Status: 2026-09-28 — PROVED (paper; SA under ALFS; ldp L5, L6, C5 and
  the registry discharge above). ldp imports r156 §§4–7 (ldp lines 68–71).
- Status: 2026-09-28 (r158) — checked by r158 (M1, lines 79–95; §3.1,
  lines 242–301; §4, lines 429–515). Clauses 1–3: consistent with M1.
  r158 §3.1 is an exact read of clause 2 with D_V ≠ ∅: the anchor X is
  outside D_V, `ht(X)=2 < lo=3`, and HEAD = X (lines 280–289). That read
  is in the outage, just after a frame rise (lines 291–293). Clause 4:
  the ldp sentence that a HEAD falls back "only when its frozen domain is
  empty" (ldp lines 697–698) is REFUTED as a general rule (r158 lines
  84–86 and 643–645). The conclusion of clause 4 at an honest proposal
  after phase settlement and the two-lease repair stays PROVED, by a
  different step: the full-store witness W and the common pivot give
  HEAD = P at every honest HEAD (r158 lines 434–457 and 477–504). This
  step does not use `ht(HEAD) ≥ lo` of ldp L4/C2 (r158 lines 629–630).
  r158 charges each effective event with θ = 4Δ (lines 532–537), not each
  fallback slot, and makes no no-reorg claim for a damaged event slot
  (lines 643–645 and 649–655). Thus the slot count of clause 4 (2 per
  frontier, 4 before the reset) is not a premise of the r158 bounds.
- Status: 2026-09-28 — SUPERSEDED by `ap.headReachesLo.v3` (the r158
  form, spec c7c41a43). Clauses 1–3 are unchanged in v3; clause 4 is
  replaced by v3 clauses 4–6. This entry keeps its spec 183f2c40 pins.
- Status: 2026-09-28 (r160) — under the receipt premise: ldp L5 HOLDS
  with the exact HEAD from r160 §4.3; its justification "same votes"
  (pinned ldp line 329) is to be read as equal scores (r160 row "LDP
  L5", lines 697–698). ldp C5 HOLDS only as the corrected bounded-event
  and P1 claim (r160 lines 707–708).
- Note (2026-09-28, r158 M1): M1 agrees with the note on the requested
  form above. A nonempty frozen domain does not force the HEAD into it.

> _alfs-redteam.md, lines 79–86:_
>
> **M1.** LDP L4/C2 and the imported r156 §5.1 use the statement that an
> honest supporting HEAD has height at least the band floor. For ALFS, the
> start is selected in the full tree. It need not be in the frozen filtered
> tree. The argument “a viable block below the band has an eligible child”
> cannot be applied to that start in the frozen tree. LDP §9.4 also says
> that returning this start requires an empty frozen domain. That statement
> is false as a general rule fact: §3.1 gives an exact ALFS read with a
> nonempty domain and a start outside it.

> _alfs-redteam.md, lines 438–444:_
>
> At an honest HEAD read, the full filtered domain is nonempty. A height-H
> carrier extends every lower accepted F by DC finalized crossing. In
> the uncontested top-J case it also extends J. The full-tree anchor
> belongs to this full domain. Every subsequent walked child belongs to
> the frozen domain, which is a subset of the full domain at that read.
> Consequently the resulting HEAD K belongs to the **full** domain.
> It need not belong to the frozen domain and need not have height lo.

- Note: `ap.headReachesLo.v1` is the view form and is not superseded.

### `ap.headReachesLo.v3` — the AP head under ALFS, r158 form (witness W, settled proposal)

- Variant `fj` (its premise is the ALFS frame `fj.frame.v2`, spec
  c7c41a43). Sources: r158 M1, lines 79–95; §3.1, lines 242–293; §4,
  lines 429–537; table lines 629–630 and 643–645; lines 649–655 (file
  `alfs-redteam.md`, archived as `tsc/archive/alfs-redteam-f1ddd1a8.md`,
  sha256 `f1ddd1a8863ac8f5443146bb901608a832cb939fe2a0263de6cce5549f409c06`);
  r159 §1, lines 23–65 and 70–98 (file `alfs-fixes.md`, archived as
  `tsc/archive/alfs-fixes-4587052c.md`, sha256
  `4587052c1c11165ed24e9c7c7bf2213cece57be408547e639e7641023521a0fd`);
  the ALFS spec `alfs2` (`spec/archive/fgsa-protocol-c7c41a43.tex`,
  sha256 `c7c41a43727d380b74ae835032edbc9775ac98b8faa18affd5670165f841e5ca`):
  `ghost` and `goldfish_eligible` lines 987–1009, `live_root` 1023–1035,
  `get_head_in_tree` 1037–1044, the HEAD vote merge of `goldfish_vote`
  1217–1231, the vote-merge prose 555–565, §5 row 29 (relay) 1614–1618,
  and the δ_t scope 1356–1361.
- Lean plan: — (an AP service fact; the SA instance is later work).
- Hypotheses: `fj.frame.v2`; `fj.frameFeasible.v1` part (4) on the frozen
  voter tree (ancestor-closed); the admitted-proposal HEAD vote merge
  (spec lines 1222–1223 and 555–562), with r159 §1 as its proof check
  (M-A exact transport, M-B source transfer, M-C outage retention; the
  table for P1, L1–L8 and C1–C5, lines 70–98); accepted-object relay as
  an SA run premise (spec §5 row 29, lines 1614–1618, and lines 174–176;
  r158 L1); for clauses 4–6, the Recovery premises with `R ≥ 3` and
  `δ_t = 2R` (spec lines 1356–1361).
- Service statement (registry, 2026-09-28). For a HEAD duty, let V be its
  frozen voter tree, (Z, lo) the store controls (`fj.frame.v2`), D_V the
  filtered domain of V, D the filtered domain of the full store, and
  A = `live_root` (the deepest live lease in the full filtered tree,
  else Z).
  1. (v2 clause 1) If A ∈ D_V, or A has an eligible child in D_V, the AP
     head is in D_V and has state height ≥ lo.
  2. (v2 clause 2) Otherwise the AP head is A. This can occur with
     D_V ≠ ∅: r158 §3.1 is an exact ALFS read with D_V ≠ ∅, head
     A = X ∉ D_V and `ht(X) = 2 < lo = 3` (r158 lines 280–293).
  3. (v2 clause 3) If A = Z and D_V ≠ ∅, then Z ∈ D_V.
  4. (full-store witness W) Fix a settled phase: H, the active top-J
     restriction and lo are fixed; lower F moves are allowed. At a
     synchronous label r whose duties are in this phase, every honest
     HEAD K is in D, and some full-store block W has `K ⪯ W` and
     `ht(W) ≥ lo`. Accepted-object relay puts W and its path at all
     honest readers before `v_r+Δ = e_r < z_r`. K need not be in D_V and
     need not have height lo.
  5. (settled proposal) Let b be the first proposal label strictly after
     phase settlement, and `ℓ = b+2k−1`. At an honest proposal P strictly
     after `t_ℓ`, while the phase persists, every honest HEAD is P (W and
     the common pivot).
  6. (event cost) At a fixed frontier the phases are gap, uncontested
     top J and contested top J. Each effective event costs one
     settlement θ = 4Δ, and the two-lease repair of clause 5 starts after
     it. No count per fallback slot is used, and no no-reorg claim is made
     for a damaged event slot.
- Change against v2: clauses 4–6 replace v2 clause 4 (a fallback needs
  D_V = ∅ and a contest event; at most 2 slots per frontier, 4 before
  the reset, none after). The step "fallback only when the frozen domain
  is empty" of ldp C5 is REFUTED as a general rule (r158 lines 84–86 and
  643–645). The v2 note on the requested form stays true: "D_V ≠ ∅ ⇒
  head in D_V" is false in general (clause 2).
- SA discharge (registry, 2026-09-28).
  1. Clauses 1–3: as in v2, with the c7c41a43 lines (`ghost` returns its
     anchor at lines 992–994; eligibility uses `band_floor`, line 1005;
     the start at `live_root`, lines 1037–1044).
  2. Clause 4: r158 §4, W (lines 434–449). With the admitted merge, r159
     M-B gives the source scores (lines 39–54; table rows L4 and C2).
  3. Clause 5: r158 lines 477–509 (two-lease repair, common pivot, exact
     service). r159 M-A gives the exact votes with the admitted merge
     (lines 28–37; table row L5).
  4. Clause 6: r158 lines 532–537, 643–645 and 649–655; r159 table row
     C5 (lines 95–97).
  The start at `live_root` and the in-band choice by score stay AP data.
- Statement (pinned):

> _alfs-redteam.md, lines 434–449:_
>
> **W: full-store witness transfer.** Fix a settled phase: H, the active
> top-J restriction, and lo are fixed. Lower F moves are allowed. Consider
> a synchronous label r whose relevant duties are inside this phase.
>
> At an honest HEAD read, the full filtered domain is nonempty. A height-H
> carrier extends every lower accepted F by DC finalized crossing. In
> the uncontested top-J case it also extends J. The full-tree anchor
> belongs to this full domain. Every subsequent walked child belongs to
> the frozen domain, which is a subset of the full domain at that read.
> Consequently the resulting HEAD K belongs to the **full** domain.
> It need not belong to the frozen domain and need not have height lo.
>
> There is therefore a full-store block W with `K⪯W` and `ht(W)≥lo`.
> The honest reader held W no later than v_r. Accepted-object relay puts
> W and its path at all honest readers before `v_r+Δ=e_r<z_r`.
> If a raw source body B has this honest HEAD as a supporter, `B⪯K⪯W`.

> _alfs-redteam.md, lines 477–509:_
>
> **Two-lease repair and the common pivot.** Let b be the first proposal
> label strictly after phase settlement and let `ℓ=b+2k−1`. A lease
> whose last write label is at most `b+k−2` expires by
> `E_old=d_(b+k−2)+L=t_ℓ+Δ`. Every later origin is a synchronous fast
> source or has a wholly synchronous slow window. Choose an honest
> proposal strictly after t_ℓ, within G. The slot grid puts it at least
> 4Δ after t_ℓ, so all remaining live leases have the phase support
> just proved.
>
> The preceding honest batch covers all of those leases. At each branch
> before such a target the score toward it is at least h and a competing
> score is at most a, including equivocation scores. The ordinary full
> proposal walk reaches every such target. Its actual lease anchor is
> on that same path. Every same-slot HEAD anchor is also on it: there
> is no intervening gate, and release/expiry can only remove leases.
> This is the common pivot that DC gets from SG.
>
> **Exact service.** The honest proposer has every block accepted at a
> reader before the freeze, by strict relay. Its current proposal adds
> only its own ancestor path to that HEAD. A competing old viable child
> and its witness in the HEAD view were therefore available to the
> proposer. The original declared support subset gives the same scores
> on the comparison. The common pivot gives the same starting suffix.
> The full proposal walk cannot stop below lo, since it starts inside
> its own nonempty domain. Its parent A supplies a band witness on the
> current proposal's path. Thus the selected path persists in the HEAD
> view, and no new competing child can defeat it. Every honest HEAD is
> exactly P.
>
> At q_s the h≥τ votes for P release any conflict from the pending gate.
> At d_s, `2h>n` gives raw result P, the guard passes, and P has a fresh
> fast write. This proves the phase repair within `ρ=2L+G+8Δ` and
> service at every later honest proposal while the phase persists.

> _alfs-redteam.md, lines 532–537:_
>
> **Events and the bound.** At a fixed frontier the phase order remains
> gap, uncontested top J, contested top J. Same-height justification
> uniqueness prevents a new top J at that height. A contest remains
> known. Each effective event is common after strict relay and a freeze;
> θ=4Δ suffices. Start the two-lease repair after that settlement. Do not
> infer phase support across an interrupting event.

> _alfs-redteam.md, lines 280–293:_
>
> `H=4,j=2,F=g,Z_fg=g,lo=3`. At V:
>
> ```text
> full filtered tree contains X, witnessed by Y or Q;
> frozen processed view contains g,A,E,B,X,C,P;
> frozen filtered tree is {g,A,E,C,P};
> live full-tree anchor is X;
> X has no child in the frozen filtered tree;
> HEAD = X, although that tree is nonempty and ht(X)=2<lo=3.
> ```
>
> This directly refutes the unrestricted fallback/nonemptiness sentence.
> It does **not** refute the settled-phase result proved in §4 or a recovery
> bound: this read is in the outage, and its frame has just risen.

> _alfs-fixes.md, lines 28–37:_
>
> **M-A: exact transport at an honest proposal.** In each clean, settled
> phase, or healed comparison, the proof puts the honest proposal P on
> the retained path. Thus P passes FG admission at the reader. A lower
> F move cannot exclude it: the proposal parent is in band, and finalized
> crossing puts it above F. P is the only authentic proposal for that
> slot. Each frozen vote at the reader reaches the proposer before its
> read. P carries the complete proposer vote set and its original support
> subset. The two merges therefore agree at this comparison. This is the
> DC vote transport used for exact service. It does not assume that all
> faulty proposals are admitted.

> _alfs-fixes.md, lines 80–83 and 95–97:_
>
> ```text
> │ L4     │ Holds  │ W relays a full-store witness; M-B gives phase support. Do not     │
> │        │        │ infer ht(HEAD)≥lo from a nonempty frozen domain.                   │
> │ L5     │ Holds  │ W and L4 give the common pivot; M-A gives exact votes. Candidate   │
> │        │        │ reflection and path persistence are unchanged.                     │
> │ C5     │ Holds  │ Bounded event cost and P1 retention only. Returning an outside     │
> │        │        │ anchor does not imply an empty domain. A damaged event slot can    │
> │        │        │ reorganize S; r158 §§3.1,6 correct the text.                       │
> ```

> _fgsa-protocol-c7c41a43.tex, lines 987–1009:_
>
> ```latex
> \Function{ghost}{$\mathit{anchor},\mathit{tree},
>   \mathit{score},\mathit{eligible}$}
>   \Comment{\DC{7}, unchanged}
>   \State $H\gets\mathit{anchor}$
>   \Loop
>     \State $\mathit{children}\gets\{B:B\text{ is a child of }H\text{ in }
>       \mathit{tree},\ \mathit{eligible}(B)\}$
>     \If{$\mathit{children}=\emptyset$} \State \Return $H$ \EndIf
>     \State $H\gets\arg\max_{B\in\mathit{children}}\mathit{score}(B)$,
>       ties by root order
>   \EndLoop
> \EndFunction
> \vspace{1pt}
> \Function{goldfish\_eligible}{$\Sigma,\mathit{votes},
>   \mathit{support\_votes},s,B$}
>   \Comment{\DC{7}, redefined (a): band floor}
>   \State $\mathit{voters\_count}\gets
>     |\{i:\mathit{votes}\text{ holds a vote by seat }i\}|$
>   \State \Return $\Sigma.\sigma[B.\parent].h<\Call{band\_floor}{\Sigma}$
>     or $2\,\Call{goldfish\_score}{\mathit{votes},
>       \mathit{support\_votes},s,B}>\mathit{voters\_count}$
>     or $B.\slot=\Sigma.s$
> \EndFunction
> ```

> _fgsa-protocol-c7c41a43.tex, lines 1023–1035:_
>
> ```latex
> \Function{live\_root}{$\Sigma$}
>   \Comment{\DC{7} \fname{get\_sg\_root}, redefined (b); \SAS{} \fname{live\_root}}
>   \State $\mathit{tree}\gets\Call{get\_filtered\_block\_tree}{\Sigma}$
>   \Comment{the full filtered tree, not a view}
>   \State $\mathit{targets}\gets\{B\in\mathit{tree}:\Sigma.\lease[B]\neq\bot\}$
>   \Comment{they lie on one chain}
>   \If{$\mathit{targets}=\emptyset$}
>     \State \Return $\Call{get\_fg\_root}{\Sigma}$
>     \Comment{no live lease in the tree}
>   \EndIf
>   \State \Return the deepest $B\in\mathit{targets}$
>   \Comment{the deepest live lease in place of grade~1}
> \EndFunction
> ```

> _fgsa-protocol-c7c41a43.tex, lines 1037–1044:_
>
> ```latex
> \Function{get\_head\_in\_tree}{$\Sigma,\mathit{tree},
>   \mathit{votes},\mathit{support\_votes},k$}
>   \Comment{\DC{7}, adapted (b): live root}
>   \State $A\gets\Call{live\_root}{\Sigma}$
>   \Comment{in place of \fname{get\_sg\_root}}
>   \State \Return $\Call{goldfish\_fork\_choice}{\Sigma,A,
>     \mathit{tree},\mathit{votes},\mathit{support\_votes},k}$
> \EndFunction
> ```

> _fgsa-protocol-c7c41a43.tex, lines 1217–1231:_
>
> ```latex
>     \State $\mathit{votes}\gets\{\mathit{vote}\in\Sigma.\gfPool[s-1]:
>       \Sigma.\timestamp(\mathit{vote})<t_{s-1}+3\Delta\}$
>     \Comment{received before the freeze}
>     \State $\mathit{support\_votes}\gets\{\mathit{vote}\in\mathit{votes}:
>       \Sigma.\resolutionTime(\mathit{vote})<t_{s-1}+3\Delta\}$
>     \ForAll{$B\in\Sigma.\TF$ with $B.\slot=s$}
>       \Comment{admitted proposals, as in \DC{7}}
>       \State $\mathit{votes}\gets\mathit{votes}\cup
>         \{\mathit{vote}\in B.\votesf:\mathit{vote}.\slot=s-1\}$
>       \State $\mathit{support\_votes}\gets\mathit{support\_votes}\cup
>         \{(i,s-1,H')\in B.\supportf:H'\in\Sigma.\T,\ H'.\slot\leq s-1\}$
>     \EndFor
>     \State $\mathit{tree}\gets\Call{voter\_filtered\_block\_tree}{\Sigma,s}$
>     \State $H\gets\Call{get\_head\_in\_tree}{\Sigma,\mathit{tree},
>       \mathit{votes},\mathit{support\_votes},s-1}$
> ```

- Status: 2026-09-28 — PROVED (paper; SA under ALFS, spec c7c41a43;
  r158 §4, r159 §1). It is not a mixed FG-SA Lean theorem (r158 line 905;
  r159 lines 211–213).
- Status: 2026-09-28 (r160) — SUPERSEDED by `ap.headReachesLo.v4` (the
  receipt premise, spec 1c6952b6). Under the receipt premise the
  conclusions of clauses 1–6 HOLD (r160 §7, lines 663–674 and 697–708).
  Two steps of this entry NEED-CHANGE: the hypothesis "accepted-object
  relay" (spec 1c6952b6 uses DC's receipt premise) and the proof step
  "M-A gives exact votes" (pinned r159 row L5; r160 row "alfs-fixes §1
  M-A", lines 658–659). Exact vote-set equality is REFUTED (r160 N1,
  lines 428–477); the scores are equal (r160 §4.3). This entry keeps its
  spec c7c41a43 pins.
- Note: `ap.headReachesLo.v1` is the view form and is not superseded.
  `ap.headReachesLo.v2` is SUPERSEDED by this entry.

### `ap.headReachesLo.v4` — the AP head under ALFS, receipt premise (witness W, settled proposal)

- Variant `fj` (its premise is the ALFS frame `fj.frame.v2`, spec
  1c6952b6). Sources: r158 M1, lines 79–95; §3.1, lines 242–293; §4,
  lines 429–537; table lines 629–630 and 643–645; lines 649–655 (file
  `alfs-redteam.md`, archived as `tsc/archive/alfs-redteam-f1ddd1a8.md`,
  sha256 `f1ddd1a8863ac8f5443146bb901608a832cb939fe2a0263de6cce5549f409c06`);
  r159 §1, lines 39–65 (M-B, M-C) (file `alfs-fixes.md`, archived as
  `tsc/archive/alfs-fixes-4587052c.md`, sha256
  `4587052c1c11165ed24e9c7c7bf2213cece57be408547e639e7641023521a0fd`);
  r160 §3.1–§3.3, lines 172–265; §4.3, lines 383–409; N1, lines 428–477;
  §7, lines 648–762 (file `receipt-relay.md`, archived as
  `tsc/archive/receipt-relay-a64d25b1.md`, sha256
  `a64d25b1623e57d68c30dbb77739e983aca7fdde9f169c04c1471be9828a06dc`);
  the ALFS spec `alfs3` (`spec/archive/fgsa-protocol-1c6952b6.tex`,
  sha256 `1c6952b6e6ef92bf9111121f0fb283671af6ce936b6db3c33d056b9dda35ffcd`):
  the Relay paragraph, lines 165–183; `ghost` and `goldfish_eligible`
  994–1016; `live_root` 1030–1042; `get_head_in_tree` 1044–1051; the HEAD
  vote merge of `goldfish_vote` 1224–1238; the vote-merge prose 562–572;
  §5 row 29, lines 1621–1625; the δ_t scope 1363–1368.
- Lean plan: — (an AP service fact; the SA instance is later work).
- Hypotheses: `fj.frame.v2`; `fj.frameFeasible.v1` part (4) on the frozen
  voter tree (ancestor-closed); the admitted-proposal HEAD vote merge
  (spec lines 1229–1230 and 562–569); DC's receipt premise (spec lines
  165–183; §5 row 29, lines 1621–1625: the raw tree has no receiver
  exclusion), with the transport that r160 §3 derives from the handlers
  (exact block paths, §3.3; in-window vote-or-equivocation, §3.2; exact
  timely honest rows, §3.4); for clauses 4–6, the Recovery premises with
  `R ≥ 3` and `δ_t = 2R` (spec lines 1363–1368).
- Service statement (registry, 2026-09-28). For a HEAD duty, let V be its
  frozen voter tree, (Z, lo) the store controls (`fj.frame.v2`), D_V the
  filtered domain of V, D the filtered domain of the full store, and
  A = `live_root` (the deepest live lease in the full filtered tree,
  else Z).
  1. (v3 clause 1) If A ∈ D_V, or A has an eligible child in D_V, the AP
     head is in D_V and has state height ≥ lo.
  2. (v3 clause 2) Otherwise the AP head is A. This can occur with
     D_V ≠ ∅ (r158 §3.1, lines 280–293).
  3. (v3 clause 3) If A = Z and D_V ≠ ∅, then Z ∈ D_V.
  4. (full-store witness W) Fix a settled phase: H, the active top-J
     restriction and lo are fixed; lower F moves are allowed. At a
     synchronous label r whose duties are in this phase, every honest
     HEAD K is in D, and some full-store block W has `K ⪯ W` and
     `ht(W) ≥ lo`. Every honest reader has W and its path in its raw tree
     before `v_r+Δ = e_r < z_r` (r160 §3.3), and FG-admits them by
     finalized crossing in the fixed phase (r160 §7, row "redteam §4 W").
     K need not be in D_V and need not have height lo.
  5. (settled proposal) Let b be the first proposal label strictly after
     phase settlement, and `ℓ = b+2k−1`. At an honest proposal P strictly
     after `t_ℓ`, while the phase persists, every honest HEAD is P (W and
     the common pivot). At each honest reader, the participating seats,
     the equivocating seats, the scores and the eligibility of the
     freeze-plus-P merge equal those of P's vote set; the two vote sets
     can differ in votes of equivocating seats (r160 §4.3).
  6. (event cost) At a fixed frontier the phases are gap, uncontested
     top J and contested top J. Each effective event costs one
     settlement θ = 4Δ, and the two-lease repair of clause 5 starts after
     it. No count per fallback slot is used, and no no-reorg claim is made
     for a damaged event slot.
- Change against v3: the relay hypothesis is DC's receipt premise, not
  accepted-object relay (a weaker hypothesis, so a new id by §0). v3's
  proof step "M-A gives exact votes" (r159 M-A) is replaced by the equal
  counts and scores of r160 §4.3. Exact vote-set equality at an honest
  proposal is REFUTED under the receipt premise (r160 N1). The
  conclusions of clauses 1–6 are those of v3.
- SA discharge (registry, 2026-09-28).
  1. Clauses 1–3: as in v3, with the 1c6952b6 lines (`ghost` returns its
     anchor at lines 999–1001; eligibility uses `band_floor`, line 1012;
     the start at `live_root`, lines 1044–1051).
  2. Clause 4: r158 §4, W (lines 434–449); r160 §7 row "redteam §4 W"
     (HOLDS: raw witness and path transport, then FG crossing and
     fixed-phase admission); source scores by r159 M-B, which HOLDS
     under the receipt premise (r160 §4.2 and §7).
  3. Clause 5: r158 lines 477–509 (two-lease repair, common pivot, exact
     service); r160 §7 rows "redteam §4 two-lease repair" (HOLDS) and
     "redteam §4 exact service" (NEEDS-CHANGE: use equal counts and
     scores, not equal signatures; exact P and ρ stay), with r160 §4.3.
  4. Clause 6: r158 lines 532–537, 643–645 and 649–655; r160 §7 rows
     "redteam §4 event settlement" and "LDP C5" (HOLDS).
  The start at `live_root` and the in-band choice by score stay AP data.
- Statement (pinned):

> _alfs-redteam.md, lines 434–449:_
>
> **W: full-store witness transfer.** Fix a settled phase: H, the active
> top-J restriction, and lo are fixed. Lower F moves are allowed. Consider
> a synchronous label r whose relevant duties are inside this phase.
>
> At an honest HEAD read, the full filtered domain is nonempty. A height-H
> carrier extends every lower accepted F by DC finalized crossing. In
> the uncontested top-J case it also extends J. The full-tree anchor
> belongs to this full domain. Every subsequent walked child belongs to
> the frozen domain, which is a subset of the full domain at that read.
> Consequently the resulting HEAD K belongs to the **full** domain.
> It need not belong to the frozen domain and need not have height lo.
>
> There is therefore a full-store block W with `K⪯W` and `ht(W)≥lo`.
> The honest reader held W no later than v_r. Accepted-object relay puts
> W and its path at all honest readers before `v_r+Δ=e_r<z_r`.
> If a raw source body B has this honest HEAD as a supporter, `B⪯K⪯W`.

> _alfs-redteam.md, lines 477–509:_
>
> **Two-lease repair and the common pivot.** Let b be the first proposal
> label strictly after phase settlement and let `ℓ=b+2k−1`. A lease
> whose last write label is at most `b+k−2` expires by
> `E_old=d_(b+k−2)+L=t_ℓ+Δ`. Every later origin is a synchronous fast
> source or has a wholly synchronous slow window. Choose an honest
> proposal strictly after t_ℓ, within G. The slot grid puts it at least
> 4Δ after t_ℓ, so all remaining live leases have the phase support
> just proved.
>
> The preceding honest batch covers all of those leases. At each branch
> before such a target the score toward it is at least h and a competing
> score is at most a, including equivocation scores. The ordinary full
> proposal walk reaches every such target. Its actual lease anchor is
> on that same path. Every same-slot HEAD anchor is also on it: there
> is no intervening gate, and release/expiry can only remove leases.
> This is the common pivot that DC gets from SG.
>
> **Exact service.** The honest proposer has every block accepted at a
> reader before the freeze, by strict relay. Its current proposal adds
> only its own ancestor path to that HEAD. A competing old viable child
> and its witness in the HEAD view were therefore available to the
> proposer. The original declared support subset gives the same scores
> on the comparison. The common pivot gives the same starting suffix.
> The full proposal walk cannot stop below lo, since it starts inside
> its own nonempty domain. Its parent A supplies a band witness on the
> current proposal's path. Thus the selected path persists in the HEAD
> view, and no new competing child can defeat it. Every honest HEAD is
> exactly P.
>
> At q_s the h≥τ votes for P release any conflict from the pending gate.
> At d_s, `2h>n` gives raw result P, the guard passes, and P has a fresh
> fast write. This proves the phase repair within `ρ=2L+G+8Δ` and
> service at every later honest proposal while the phase persists.

> _alfs-redteam.md, lines 532–537:_
>
> **Events and the bound.** At a fixed frontier the phase order remains
> gap, uncontested top J, contested top J. Same-height justification
> uniqueness prevents a new top J at that height. A contest remains
> known. Each effective event is common after strict relay and a freeze;
> θ=4Δ suffices. Start the two-lease repair after that settlement. Do not
> infer phase support across an interrupting event.

> _receipt-relay.md, lines 385–409:_
>
> Let P be the unique authenticated honest proposal of slot s, admitted
> at the reader. Write `(A,S)` for its raw and original declared-support
> sets. Write `(A',S')` for the reader's freeze-plus-P merge.
>
> P supplies `A⊆A'` and `S⊆S'`, as *carried metadata*, even when local
> vote handlers refuse a copy. Each extra frozen raw vote reaches the
> proposer before `t_s=z_(s−1)+Δ`, or that proposer has two distinct
> votes of its seat. If the vote is extra, the latter case holds.
> For an extra frozen support vote, relay its resolved head block too:
> if the proposer kept that vote, it was resolved there and would be
> in S. Otherwise its seat already equivocates in A.
>
> Thus every extra raw or support vote belongs to an equivocator in A.
> The participating seats and equivocating seats in A and A' are equal.
> For a nonequivocating seat the support choice is unchanged; for an
> equivocator its score is already one on every branch. Scores and
> eligibility on the compared candidates are equal. Block transport
> and the existing domain/anchor comparison then give exact HEAD P.
>
> **Replace “equal vote sets” with this statement.** N1 refutes exact
> membership and raw/support set equality. At an honest slot the raw-
> proposal and admitted-proposal merges themselves still agree when P
> is admitted: P is the only authenticated current-slot proposal.
> What fails is the additional assertion that the merged set equals
> the proposer's set. The desired HEAD service remains exact.

> _receipt-relay.md, lines 663–664, 667–670, 673–674, 697–698 and 707–708:_
>
> ```text
> │ redteam §4 W                 │ HOLDS        │ Raw witness/path transport, then FG        │
> │                              │              │ crossing and fixed-phase admission.        │
> │ redteam §4 two-lease repair  │ HOLDS        │ Lease classification and h versus a        │
> │                              │              │ counts unchanged.                          │
> │ redteam §4 exact service     │ NEEDS-CHANGE │ Use equal counts/scores, not equal         │
> │                              │              │ signatures. Exact P and ρ stay.            │
> │ redteam §4 event settlement  │ HOLDS        │ Relay admitted certificate carriers;       │
> │ and stopped-phase budgets    │              │ saturation of row pools is irrelevant.     │
> │ LDP L5                       │ HOLDS        │ Exact HEAD after repair via §4.3; update   │
> │                              │              │ the “same votes” justification.            │
> │ LDP C5 / §9.4                │ HOLDS        │ Corrected bounded event/P1 claim only.     │
> │                              │              │ Old outside-anchor claim stays refuted.    │
> ```

> _fgsa-protocol-1c6952b6.tex, lines 165–183:_
>
> ```latex
> \paragraph{Relay.}  The run premise is the receipt premise of~\cite{DC}.
> An honest node forwards every block that it accepts and every vote and
> row that it accepts, also when it accepts the object from a block
> (\cite{DC}, lines 203 and 530).  When an honest node accepts an object
> at time~$t$, every honest node that does not hold it calls the handler
> of that object before $\max\{t,t_{\rm GST}\}+\Delta$, with its
> dependencies present.  This is DC's \textsf{PartialSynchrony.relay}
> (\textsf{handlesAt}).  The handler can refuse the object; for example,
> the vote pool refuses a third distinct vote of one seat.  The premise
> does not require acceptance.  One difference from~\cite{DC} is in the
> receiver exclusion: DC's receiver can skip a block that conflicts
> with~$F$; the raw SA tree of this document has no such exclusion,
> because the SA base processes every branch~(b).  The proofs derive the
> transport that they need from the handlers~\cite[\S3]{RR}: exact
> transport of block paths, in-window transport of a vote or of the
> equivocation of its seat, and exact transport of timely honest rows.
> At an honest proposal the reader's merge can differ from the proposer's
> vote set only in the votes of equivocating seats; the scores are
> equal~\cite[\S4.3]{RR}, as in DC's \textsf{ScorePreservingViewExtension}.
> ```

> _fgsa-protocol-1c6952b6.tex, lines 994–1016:_
>
> ```latex
> \Function{ghost}{$\mathit{anchor},\mathit{tree},
>   \mathit{score},\mathit{eligible}$}
>   \Comment{\DC{7}, unchanged}
>   \State $H\gets\mathit{anchor}$
>   \Loop
>     \State $\mathit{children}\gets\{B:B\text{ is a child of }H\text{ in }
>       \mathit{tree},\ \mathit{eligible}(B)\}$
>     \If{$\mathit{children}=\emptyset$} \State \Return $H$ \EndIf
>     \State $H\gets\arg\max_{B\in\mathit{children}}\mathit{score}(B)$,
>       ties by root order
>   \EndLoop
> \EndFunction
> \vspace{1pt}
> \Function{goldfish\_eligible}{$\Sigma,\mathit{votes},
>   \mathit{support\_votes},s,B$}
>   \Comment{\DC{7}, redefined (a): band floor}
>   \State $\mathit{voters\_count}\gets
>     |\{i:\mathit{votes}\text{ holds a vote by seat }i\}|$
>   \State \Return $\Sigma.\sigma[B.\parent].h<\Call{band\_floor}{\Sigma}$
>     or $2\,\Call{goldfish\_score}{\mathit{votes},
>       \mathit{support\_votes},s,B}>\mathit{voters\_count}$
>     or $B.\slot=\Sigma.s$
> \EndFunction
> ```

> _fgsa-protocol-1c6952b6.tex, lines 1030–1042:_
>
> ```latex
> \Function{live\_root}{$\Sigma$}
>   \Comment{\DC{7} \fname{get\_sg\_root}, redefined (b); \SAS{} \fname{live\_root}}
>   \State $\mathit{tree}\gets\Call{get\_filtered\_block\_tree}{\Sigma}$
>   \Comment{the full filtered tree, not a view}
>   \State $\mathit{targets}\gets\{B\in\mathit{tree}:\Sigma.\lease[B]\neq\bot\}$
>   \Comment{they lie on one chain}
>   \If{$\mathit{targets}=\emptyset$}
>     \State \Return $\Call{get\_fg\_root}{\Sigma}$
>     \Comment{no live lease in the tree}
>   \EndIf
>   \State \Return the deepest $B\in\mathit{targets}$
>   \Comment{the deepest live lease in place of grade~1}
> \EndFunction
> ```

> _fgsa-protocol-1c6952b6.tex, lines 1044–1051:_
>
> ```latex
> \Function{get\_head\_in\_tree}{$\Sigma,\mathit{tree},
>   \mathit{votes},\mathit{support\_votes},k$}
>   \Comment{\DC{7}, adapted (b): live root}
>   \State $A\gets\Call{live\_root}{\Sigma}$
>   \Comment{in place of \fname{get\_sg\_root}}
>   \State \Return $\Call{goldfish\_fork\_choice}{\Sigma,A,
>     \mathit{tree},\mathit{votes},\mathit{support\_votes},k}$
> \EndFunction
> ```

> _fgsa-protocol-1c6952b6.tex, lines 1224–1238:_
>
> ```latex
>     \State $\mathit{votes}\gets\{\mathit{vote}\in\Sigma.\gfPool[s-1]:
>       \Sigma.\timestamp(\mathit{vote})<t_{s-1}+3\Delta\}$
>     \Comment{received before the freeze}
>     \State $\mathit{support\_votes}\gets\{\mathit{vote}\in\mathit{votes}:
>       \Sigma.\resolutionTime(\mathit{vote})<t_{s-1}+3\Delta\}$
>     \ForAll{$B\in\Sigma.\TF$ with $B.\slot=s$}
>       \Comment{admitted proposals, as in \DC{7}}
>       \State $\mathit{votes}\gets\mathit{votes}\cup
>         \{\mathit{vote}\in B.\votesf:\mathit{vote}.\slot=s-1\}$
>       \State $\mathit{support\_votes}\gets\mathit{support\_votes}\cup
>         \{(i,s-1,H')\in B.\supportf:H'\in\Sigma.\T,\ H'.\slot\leq s-1\}$
>     \EndFor
>     \State $\mathit{tree}\gets\Call{voter\_filtered\_block\_tree}{\Sigma,s}$
>     \State $H\gets\Call{get\_head\_in\_tree}{\Sigma,\mathit{tree},
>       \mathit{votes},\mathit{support\_votes},s-1}$
> ```

- Status: 2026-09-28 — PROVED (paper; SA under ALFS, spec 1c6952b6;
  r158 §4, r159 M-B and M-C, r160 §§3–4 and §7). It is not a Lean
  theorem: the SA Lean theorems assume the stronger AcceptedObjectRelay
  (spec OPEN item, lines 1697–1701; r160 §9).
- Status: 2026-09-28 (r161) — SUPERSEDED by `ap.headReachesLo.v5` (the
  filtered base, spec bd942ca0). The spec has no raw tree, and the
  receipt premise has DC's receiver exclusion. The conclusions of
  clauses 1–6 HOLD (r161 §6.3, lines 587–613). Steps that NEED-CHANGE:
  the raw-tree transport of W (r161 row W: admission by crossing first)
  and transport and reflection on the retained suffix only (rows L1,
  L3, C1). This entry keeps its spec 1c6952b6 pins.
- Status: 2026-09-28 (r162) — the reason in the status line above, "the
  SA Lean theorems assume the stronger AcceptedObjectRelay", no longer
  holds. The plain SA Lean base is on the receipt premise (merge
  `1a3f73a` in `lean/available-chain`, branch `receipt-relay`: `059669d`,
  `5d03d92`, `eec0f94`): the regimes (`Generic/Regimes.lean`,
  `Strong/Regimes.lean`) have no accepted-relay field; the public
  theorems `gridContract_from_engine`, `saContract_from_engine`,
  `fastP1_from_engine`, `sapcContract_from_engine` and
  `sapcStrong_from_engine` keep their statements and use only the
  standard axioms (`#print axioms`, team-lead); SA-PC derives acceptance
  from receipt (`AvailableChainSAPC/Proofs/ReceiptRelay.lean`,
  `receipt_acceptedRelay`). The full build of main at `1a3f73a` passes
  (3,558 jobs; team-lead, 2026-09-28). `CatalogLock --check` fails at
  `1a3f73a`: eight Catalog L3 hashes changed (`Catalog.sleepy` and its
  dependents), because `SleepyRegime` lost its accepted-relay field; the
  lock is not rewritten yet (user decision pending). The status of this
  entry does
  not change (SUPERSEDED; paper): there is no FG-SA Lean instance.
- Note: `ap.headReachesLo.v1` is the view form and is not superseded.
  `ap.headReachesLo.v2` and `ap.headReachesLo.v3` are SUPERSEDED; v4 is
  the current form.

### `ap.headReachesLo.v5` — the AP head under ALFS, filtered base (witness W, settled proposal)

- Variant `fj` (its premise is the ALFS frame `fj.frame.v3`, spec
  bd942ca0). Sources: r158 M1, lines 79–95; §3.1, lines 242–293; §4,
  lines 429–537; table lines 629–630 and 643–645; lines 649–655 (file
  `alfs-redteam.md`, archived as `tsc/archive/alfs-redteam-f1ddd1a8.md`,
  sha256 `f1ddd1a8863ac8f5443146bb901608a832cb939fe2a0263de6cce5549f409c06`);
  r160 §3.2, §3.4 and §4.3, lines 206–240, 267–293 and 383–409 (file
  `receipt-relay.md`, archived as `tsc/archive/receipt-relay-a64d25b1.md`,
  sha256 `a64d25b1623e57d68c30dbb77739e983aca7fdde9f169c04c1471be9828a06dc`);
  r161 §3, lines 194–225; §6.2, lines 550–585; §6.3, lines 587–627; §6.4,
  lines 629–668 (file `filtered-base.md`, archived as
  `tsc/archive/filtered-base-fd8e07fe.md`, sha256
  `fd8e07fe667afae28dee2bc9a54d6c7fc46b49f9bb268865f98818decc308354`);
  the ALFS spec `alfs4` (`spec/archive/fgsa-protocol-bd942ca0.tex`,
  sha256 `bd942ca0bce0b4251b969a503a8c8175db87494ab93bf028e3a2303b7683dda7`):
  the Relay paragraph, lines 169–190; the Trees paragraph 352–371;
  `ghost` and `goldfish_eligible` 1038–1060; `live_root` 1074–1086;
  `get_head_in_tree` 1088–1095; the HEAD vote merge of `goldfish_vote`
  1271–1285; the vote-merge prose 595–602; the recovery proof
  1530–1545; the δ_t scope 1410–1415.
- Lean plan: — (an AP service fact; the SA instance is later work).
- Hypotheses: `fj.frame.v3`; `fj.frameFeasible.v1` part (4) on the frozen
  voter tree (ancestor-closed); the admitted-proposal HEAD vote merge
  over Σ.T (spec lines 1276–1277 and 595–602); DC's receipt premise with
  DC's receiver exclusion of a block incompatible with F (spec lines
  169–183), and the admission-or-coverage lemma (r161 §3; spec lines
  184–190), with r160's vote-or-equivocation and honest-row transport
  (r160 §3.2, §3.4); for clauses 4–6, the Recovery premises, with `a ≤ f`,
  `R ≥ 3` and `δ_t = 2R` (spec lines 1410–1415).
- Service statement (registry, 2026-09-28). For a HEAD duty, let V be its
  frozen voter tree, (Z, lo) the store controls (`fj.frame.v3`), D_V the
  filtered domain of V, D the filtered domain of Σ.T, and A = `live_root`
  (the deepest live lease in the full filtered tree, else Z).
  1. (v4 clause 1) If A ∈ D_V, or A has an eligible child in D_V, the AP
     head is in D_V and has state height ≥ lo.
  2. (v4 clause 2) Otherwise the AP head is A. This can occur with
     D_V ≠ ∅ (the exact instance r158 §3.1, lines 280–293, is an ALFS read
     of spec 183f2c40 in which every block extends F; r161 does not
     re-run it).
  3. (v4 clause 3) If A = Z and D_V ≠ ∅, then Z ∈ D_V.
  4. (full-store witness W, admitted) Fix a settled phase: H, the active
     top-J restriction and lo are fixed; lower F moves are allowed. At a
     synchronous label r whose duties are in this phase, every honest
     HEAD K is in D, and some block W ∈ Σ.T has `K ⪯ W` and `ht(W) ≥ lo`.
     No honest receiver excludes W: a lower accepted F has finalized
     height below lo, and finalized crossing at `a ≤ f` puts W above it;
     in a top-J phase `F ⪯ J ⪯ W`. Every honest reader admits W and its
     path before `v_r+Δ = e_r < z_r`. For a source B with `B ⪯ K`, either
     the receiving F stays below B and the path is admitted, or F covers
     B. K need not be in D_V and need not have height lo.
  5. (settled proposal) Let b be the first proposal label strictly after
     phase settlement, and `ℓ = b+2k−1`. At an honest proposal P strictly
     after `t_ℓ`, while the phase persists, every honest HEAD is P (W and
     the common pivot). On the retained suffix (the candidates at or
     above the current F), the participating seats, the equivocating
     seats, the scores and the eligibility of each reader's merge equal
     those of P's vote set (r160 §4.3, r161 §6.2).
  6. (event cost) At a fixed frontier the phases are gap, uncontested
     top J and contested top J. Each effective event costs one
     settlement θ = 4Δ, and the two-lease repair of clause 5 starts after
     it. No count per fallback slot is used, and no no-reorg claim is made
     for a damaged event slot.
- Change against v4: the spec has no raw tree. The receipt premise now
  has DC's receiver exclusion, so the raw-tree transport of v4 clause 4
  (r160 §3.3) is replaced by admission of W by finalized crossing and by
  admission-or-coverage for sources (r161 §3 and §6.2; r161 §6.3 row W:
  NEEDS-CHANGE, "Prove receiver admission of W by crossing first"). Score
  equality in clause 5 is restricted to the retained suffix. The
  hypotheses change (a new id by §0). The conclusions of clauses 1–6
  are those of v4.
- SA discharge (registry, 2026-09-28).
  1. Clauses 1–3: as in v4, with the bd942ca0 lines (`ghost` and
     eligibility, lines 1038–1060; the start at `live_root`,
     lines 1088–1095).
  2. Clause 4: r158 §4, W (lines 434–449); r161 §6.2, lines 552–565
     (admission of W by crossing, then admission-or-coverage); r161 §6.3
     rows L4 and W.
  3. Clause 5: r158 lines 477–509 (two-lease repair, common pivot, exact
     service); r161 §6.2, lines 567–585 (source histories, the retained
     suffix, exact HEAD P); r160 §4.3; r161 §6.3 rows L1, L3, L5, C1, C2.
  4. Clause 6: r158 lines 532–537, 643–645 and 649–655; r161 §6.3 rows L6
     and C5; spec lines 1543–1545 (the empty-frozen-domain case stays in
     the event-settlement allowance).
  The start at `live_root` and the in-band choice by score stay AP data.
- Statement (pinned):

> _alfs-redteam.md, lines 434–449:_
>
> **W: full-store witness transfer.** Fix a settled phase: H, the active
> top-J restriction, and lo are fixed. Lower F moves are allowed. Consider
> a synchronous label r whose relevant duties are inside this phase.
>
> At an honest HEAD read, the full filtered domain is nonempty. A height-H
> carrier extends every lower accepted F by DC finalized crossing. In
> the uncontested top-J case it also extends J. The full-tree anchor
> belongs to this full domain. Every subsequent walked child belongs to
> the frozen domain, which is a subset of the full domain at that read.
> Consequently the resulting HEAD K belongs to the **full** domain.
> It need not belong to the frozen domain and need not have height lo.
>
> There is therefore a full-store block W with `K⪯W` and `ht(W)≥lo`.
> The honest reader held W no later than v_r. Accepted-object relay puts
> W and its path at all honest readers before `v_r+Δ=e_r<z_r`.
> If a raw source body B has this honest HEAD as a supporter, `B⪯K⪯W`.

> _alfs-redteam.md, lines 477–509:_
>
> **Two-lease repair and the common pivot.** Let b be the first proposal
> label strictly after phase settlement and let `ℓ=b+2k−1`. A lease
> whose last write label is at most `b+k−2` expires by
> `E_old=d_(b+k−2)+L=t_ℓ+Δ`. Every later origin is a synchronous fast
> source or has a wholly synchronous slow window. Choose an honest
> proposal strictly after t_ℓ, within G. The slot grid puts it at least
> 4Δ after t_ℓ, so all remaining live leases have the phase support
> just proved.
>
> The preceding honest batch covers all of those leases. At each branch
> before such a target the score toward it is at least h and a competing
> score is at most a, including equivocation scores. The ordinary full
> proposal walk reaches every such target. Its actual lease anchor is
> on that same path. Every same-slot HEAD anchor is also on it: there
> is no intervening gate, and release/expiry can only remove leases.
> This is the common pivot that DC gets from SG.
>
> **Exact service.** The honest proposer has every block accepted at a
> reader before the freeze, by strict relay. Its current proposal adds
> only its own ancestor path to that HEAD. A competing old viable child
> and its witness in the HEAD view were therefore available to the
> proposer. The original declared support subset gives the same scores
> on the comparison. The common pivot gives the same starting suffix.
> The full proposal walk cannot stop below lo, since it starts inside
> its own nonempty domain. Its parent A supplies a band witness on the
> current proposal's path. Thus the selected path persists in the HEAD
> view, and no new competing child can defeat it. Every honest HEAD is
> exactly P.
>
> At q_s the h≥τ votes for P release any conflict from the pending gate.
> At d_s, `2h>n` gives raw result P, the guard passes, and P has a fresh
> fast write. This proves the phase repair within `ρ=2L+G+8Δ` and
> service at every later honest proposal while the phase persists.

> _alfs-redteam.md, lines 532–537:_
>
> **Events and the bound.** At a fixed frontier the phase order remains
> gap, uncontested top J, contested top J. Same-height justification
> uniqueness prevents a new top J at that height. A contest remains
> known. Each effective event is common after strict relay and a freeze;
> θ=4Δ suffices. Start the two-lease repair after that settlement. Do not
> infer phase support across an interrupting event.

> _receipt-relay.md, lines 385–409:_
>
> Let P be the unique authenticated honest proposal of slot s, admitted
> at the reader. Write `(A,S)` for its raw and original declared-support
> sets. Write `(A',S')` for the reader's freeze-plus-P merge.
>
> P supplies `A⊆A'` and `S⊆S'`, as *carried metadata*, even when local
> vote handlers refuse a copy. Each extra frozen raw vote reaches the
> proposer before `t_s=z_(s−1)+Δ`, or that proposer has two distinct
> votes of its seat. If the vote is extra, the latter case holds.
> For an extra frozen support vote, relay its resolved head block too:
> if the proposer kept that vote, it was resolved there and would be
> in S. Otherwise its seat already equivocates in A.
>
> Thus every extra raw or support vote belongs to an equivocator in A.
> The participating seats and equivocating seats in A and A' are equal.
> For a nonequivocating seat the support choice is unchanged; for an
> equivocator its score is already one on every branch. Scores and
> eligibility on the compared candidates are equal. Block transport
> and the existing domain/anchor comparison then give exact HEAD P.
>
> **Replace “equal vote sets” with this statement.** N1 refutes exact
> membership and raw/support set equality. At an honest slot the raw-
> proposal and admitted-proposal merges themselves still agree when P
> is admitted: P is the only authenticated current-slot proposal.
> What fails is the additional assertion that the merged set equals
> the proposer's set. The desired HEAD service remains exact.

> _filtered-base.md, lines 196–219:_
>
> Write `B ~ F` for compatibility. Suppose a proof protects B and has
> established `B ~ F_y` at the receiving node y.
>
> * If `F_y⪯B`, every support head above B extends F_y. Its complete path
>   can be admitted. With the existing receipt deadline, the r160
>   vote-or-equivocation argument gives exactly the surviving support
>   needed at the cutoff. A second vote still acts as evidence even if
>   its head cannot resolve.
> * If `B⪯F_y`, the receiver's output and every FG-domain HEAD cover B
>   through finality. No support-path receipt for B is needed at that
>   receiver. Every lease that conflicts with B also conflicts with F_y
>   and has been deleted.
>
> Equality can use either case. An ancestor on an already admitted path
> does not need a new acceptance event. If F changes while transport is
> pending, apply the cases at the receiving read. A crossing from the first
> case into the second discharges the requirement by coverage. It does not
> extend the transport deadline.
>
> This proves the useful replacement for “all source paths arrive.” It
> does **not** prove compatibility by itself. Clean/P1 obtain compatibility
> from the joint source-history induction in §4. Recovery obtains it from
> the high witness and finalized-crossing argument in §6. Use neither proof
> outside its premise set.

> _filtered-base.md, lines 552–585:_
>
> W is the full-store witness of [r158 §4](alfs-redteam.md), not necessarily
> the HEAD itself. In a settled phase, each honest HEAD K belongs to the
> full domain and has an admitted descendant W of height at least lo.
> In an F-root phase, a lower accepted finalization has finalized height
> strictly below lo. [DC's finalized-crossing result][dc-crossing] at `a≤f` puts W above
> that finalization. In a top-J phase, W is above J, and F is below J.
> Thus the receiver cannot exclude the high witness needed in this proof.
> The same applies if F advances during relay.
>
> Relay W with its path by `e_r<z_r`. For a source B supported by K,
> `B⪯K⪯W`. Either the receiving F remains below B and the witness/path
> is retained, or F covers B. This proves W for the filtered base without
> the raw-layer premise of r160. A low branch such as X in N2 is not a
> counterexample: it is not the high phase witness.
>
> All synchronous genuine sources have an honest supporter by §4.1.
> Consequently all relevant phase source bodies are compatible with lower
> F moves. Their needed slow histories do not disappear on a conflicting
> prune; if F passes their target, the target is already covered.
> Arbitrary earlier leases and histories still age out in the original
> two-lease interval. Deleted leases only reduce this old set.
>
> After that interval, the ordinary honest proposal parent covers all
> remaining leases or their finality replacement. W gives candidate
> persistence; admitted-path reflection and r160's score-preserving
> extension give exact HEAD P. No extra slot or network delay is needed.
> The local repair bound remains `ρ=2L+G+8Δ`.
>
> Pruning also removes some old vote support and proposal containers. On
> any retained candidate at or above the new F, an excluded head contributes
> zero clean support both before and after pruning. Retained raw signatures
> give the same participation and equivocation scores. On the removed
> ancestor trunk the result is obtained from F instead. This is the needed
> score argument; literal equality of the full merges is not required.

> _filtered-base.md, lines 593–611:_
>
> ```text
> │ L1   │ NEEDS-CHANGE │ Restrict transport/reflection to admitted candidates │
> │      │              │ and their witnesses; otherwise F covers the prefix.  │
> │ L2   │ HOLDS        │ Keep archival H and live cache rules. In recovery,   │
> │      │              │ high contest witnesses survive lower F by crossing.  │
> │ L3   │ NEEDS-CHANGE │ Same lower-F domain result and settled-walk scope;   │
> │      │              │ use retained-suffix score equality after pruning.    │
> │ L4   │ HOLDS        │ Full-store anchor; W plus scoped source transfer.    │
> │ L5   │ HOLDS        │ Repaired common pivot and exact honest HEAD P.       │
> │ L6   │ HOLDS        │ Same event settlement and freeze allowance.          │
> │ L7   │ HOLDS        │ Certificate descent; retained high source bodies     │
> │      │              │ or a finality prefix discharge the path obligation.  │
> │ L8   │ HOLDS        │ Clean/P1 at all a<h, with §4's joint induction.      │
> │ C1   │ NEEDS-CHANGE │ Fixed-view domain identity stays; physical pruning   │
> │      │              │ also needs the retained-suffix score argument.       │
> │ C2   │ HOLDS        │ W and phase support give the common pivot.           │
> │ C3   │ HOLDS        │ Same effective service and height production.        │
> │ C4   │ HOLDS        │ Same phase count; 1292Δ remains a weaker bound.      │
> │ C5   │ HOLDS        │ Only its corrected bounded-event/P1 claim.           │
> │ W    │ NEEDS-CHANGE │ Prove receiver admission of W by crossing first.     │
> ```

> _fgsa-protocol-bd942ca0.tex, lines 169–190:_
>
> ```latex
> \paragraph{Relay.}  The run premise is the receipt premise of~\cite{DC}.
> An honest node forwards every block that it accepts and every vote and
> row that it accepts, also when it accepts the object from a block
> (\cite{DC}, lines 203 and 530).  When an honest node accepts an object
> at time~$t$, every honest node that does not hold it calls the handler
> of that object before $\max\{t,t_{\rm GST}\}+\Delta$, with its
> dependencies present.  This is DC's \textsf{PartialSynchrony.relay}
> (\textsf{handlesAt}).  The handler can refuse the object; for example,
> the vote pool refuses a third distinct vote of one seat.  The premise
> does not require acceptance.  As in DC's \textsf{NamedReceipt.excludes},
> a receiver can skip a block incompatible with its current~$F$.  This
> exclusion never applies to a vote or row.  It does not exclude an
> already stored finalized ancestor.  Admission still requires
> $F\preceq B$ before the handler unpacks a new block.
>
> The proofs use admission-or-coverage~\cite[\S3]{FB}.  Once a protected
> prefix~$B$ is known to be compatible with the receiving~$F$, either
> $F\preceq B$ and the required support paths can be admitted by the
> receipt deadline, or $B\preceq F$ and finality covers~$B$.  The
> vote-or-equivocation and timely honest-row arguments of~\cite[\S3]{RR}
> still apply.  At an honest proposal, score equality is needed on the
> retained suffix only~\cite[\S4.3]{RR},~\cite[\S6.2]{FB}.
> ```

> _fgsa-protocol-bd942ca0.tex, lines 1038–1060:_
>
> ```latex
> \Function{ghost}{$\mathit{anchor},\mathit{tree},
>   \mathit{score},\mathit{eligible}$}
>   \Comment{\DC{7}, unchanged}
>   \State $H\gets\mathit{anchor}$
>   \Loop
>     \State $\mathit{children}\gets\{B:B\text{ is a child of }H\text{ in }
>       \mathit{tree},\ \mathit{eligible}(B)\}$
>     \If{$\mathit{children}=\emptyset$} \State \Return $H$ \EndIf
>     \State $H\gets\arg\max_{B\in\mathit{children}}\mathit{score}(B)$,
>       ties by root order
>   \EndLoop
> \EndFunction
> \vspace{1pt}
> \Function{goldfish\_eligible}{$\Sigma,\mathit{votes},
>   \mathit{support\_votes},s,B$}
>   \Comment{\DC{7}, redefined (a): band floor}
>   \State $\mathit{voters\_count}\gets
>     |\{i:\mathit{votes}\text{ holds a vote by seat }i\}|$
>   \State \Return $\Sigma.\sigma[B.\parent].h<\Call{band\_floor}{\Sigma}$
>     or $2\,\Call{goldfish\_score}{\mathit{votes},
>       \mathit{support\_votes},s,B}>\mathit{voters\_count}$
>     or $B.\slot=\Sigma.s$
> \EndFunction
> ```

> _fgsa-protocol-bd942ca0.tex, lines 1074–1086:_
>
> ```latex
> \Function{live\_root}{$\Sigma$}
>   \Comment{\DC{7} \fname{get\_sg\_root}, redefined (b); \SAS{} \fname{live\_root}}
>   \State $\mathit{tree}\gets\Call{get\_filtered\_block\_tree}{\Sigma}$
>   \Comment{the full filtered tree, not a view}
>   \State $\mathit{targets}\gets\{B\in\mathit{tree}:\Sigma.\lease[B]\neq\bot\}$
>   \Comment{they lie on one chain}
>   \If{$\mathit{targets}=\emptyset$}
>     \State \Return $\Call{get\_fg\_root}{\Sigma}$
>     \Comment{no live lease in the tree}
>   \EndIf
>   \State \Return the deepest $B\in\mathit{targets}$
>   \Comment{the deepest live lease in place of grade~1}
> \EndFunction
> ```

> _fgsa-protocol-bd942ca0.tex, lines 1088–1095:_
>
> ```latex
> \Function{get\_head\_in\_tree}{$\Sigma,\mathit{tree},
>   \mathit{votes},\mathit{support\_votes},k$}
>   \Comment{\DC{7}, adapted (b): live root}
>   \State $A\gets\Call{live\_root}{\Sigma}$
>   \Comment{in place of \fname{get\_sg\_root}}
>   \State \Return $\Call{goldfish\_fork\_choice}{\Sigma,A,
>     \mathit{tree},\mathit{votes},\mathit{support\_votes},k}$
> \EndFunction
> ```

> _fgsa-protocol-bd942ca0.tex, lines 1271–1285:_
>
> ```latex
>     \State $\mathit{votes}\gets\{\mathit{vote}\in\Sigma.\gfPool[s-1]:
>       \Sigma.\timestamp(\mathit{vote})<t_{s-1}+3\Delta\}$
>     \Comment{received before the freeze}
>     \State $\mathit{support\_votes}\gets\{\mathit{vote}\in\mathit{votes}:
>       \Sigma.\resolutionTime(\mathit{vote})<t_{s-1}+3\Delta\}$
>     \ForAll{$B\in\Sigma.\T$ with $B.\slot=s$}
>       \Comment{admitted proposals, as in \DC{7}}
>       \State $\mathit{votes}\gets\mathit{votes}\cup
>         \{\mathit{vote}\in B.\votesf:\mathit{vote}.\slot=s-1\}$
>       \State $\mathit{support\_votes}\gets\mathit{support\_votes}\cup
>         \{(i,s-1,H')\in B.\supportf:H'\in\Sigma.\T,\ H'.\slot\leq s-1\}$
>     \EndFor
>     \State $\mathit{tree}\gets\Call{voter\_filtered\_block\_tree}{\Sigma,s}$
>     \State $H\gets\Call{get\_head\_in\_tree}{\Sigma,\mathit{tree},
>       \mathit{votes},\mathit{support\_votes},s-1}$
> ```

- Status: 2026-09-28 — PROVED (paper; SA under ALFS, spec bd942ca0;
  r158 §4, r160 §§3–4, r161 §§3 and 6). It is not a Lean theorem: there
  is no checked mixed FG-SA Lean instance (spec OPEN items, lines
  1845–1858).
- Status: 2026-09-28 (r162) — paper, unchanged: there is no FG-SA Lean
  instance. The plain SA Lean base now uses DC's receipt premise (merge
  `1a3f73a`; see `ap.headReachesLo.v4`). Plain SA has no F, so its
  receipt premise has no receiver exclusion; the receiver exclusion of
  this entry's premise is an FG-SA part.
- Note: `ap.headReachesLo.v1` is the view form and is not superseded.
  `ap.headReachesLo.v2`, `v3` and `v4` are SUPERSEDED; v5 is the current
  form.
- Status: 2026-09-29 — WITHDRAWN for current use (§0; not SUPERSEDED).
  Still true in its stated scope (R≥3, 4Δ, spec bd942ca0; the HEAD
  functions are unchanged in 4e85ff34 and bp.genuineFromF.v1 with F⪯P
  transfers clause 5); successor ap.headReachesLo.v6. H.6 gives the
  direct current-spec proof; H.8 gives θ=3Δ. The change of hypotheses
  invokes registry §0. The note above ("v5 is the current form") is
  history.


### `ap.headReachesLo.v6` — the AP head under FG-SA (R ≥ 2, strict receipt, θ = 3Δ)

- Variant `fj` (its premise is the frame `fj.frame.v4`, spec `fgsa3`).
  Source: blueprint 21, registry restatement after H.8, file
  `blueprint/archive/21-healing-9b7f5af8.md` (key `bp21`), lines
  1059–1098, sha256
  `9b7f5af8d013a473f9c5361f72377df63f79728599e02d0b9414cd58789c3ac9`.
  Proofs: 21 H.3 (clauses 1–4), H.5–H.6 (clause 5), H.8 (clause 6).
- Lean pin: not yet pinned (2026-09-29): `AvailableChainKitFG/Pins.lean`
  cites this id through `.ap` only; the entry has no clause table yet.
- Lean plan: — (an AP service fact). FG inputs of clauses 1–3, as for
  v5: `filteredFrom_reachesLo`, `filteredFrom_Z_mem`,
  `filteredFrom_viable_child`.
- Hypotheses: clauses 1–3: the live-cache FJ frame, the frozen voter
  domain, the full-domain live start and the exact HEAD merge. Clauses
  4–6: Recovery₂ (`a≤f`, `R≥2`, `δ_t=2R`), strict receipt `<Δ` with
  receiver exclusion, and the phase premises of the statement.
- Statement (pinned):

> _21-healing-9b7f5af8.md, lines 1059–1098:_
>
> ### Registry restatement — ap.headReachesLo.v6 — PROVED-paper
>
> _2026-09-29. ap.headReachesLo.v5 is WITHDRAWN for current use under
> registry §0: changed statements or hypotheses get a new id. It is still
> true in its stated scope (R≥3, 4Δ, spec bd942ca0). The HEAD functions
> are unchanged in 4e85ff34. Clause 5 transfers by bp.genuineFromF.v1
> (01 §6.5) with F⪯P in a settled phase: a lower F has certificate height
> below lo≤ht(P), and in top J one has F⪯J⪯P. Strict 3Δ settlement also
> implies the weaker 4Δ bound. Keep its old pins. Successor:
> ap.headReachesLo.v6 (spec 4e85ff34, R≥2, strict receipt, θ=3Δ).
> This is WITHDRAWN, not SUPERSEDED._
>
> Authority is the current spec 4e85ff34. Clauses 1–3 use its live-cache
> FJ frame, frozen voter domain, full-domain live start, and exact HEAD
> merge. Clauses 4–6 use Recovery₂ (`a≤f`, `R≥2`, `δ_t=2R`), strict
> receipt `<Δ` with receiver exclusion, and the stated phase premises.
>
> 1. If start A is in `D(V_s)`, or has an eligible child there, the HEAD
>    is in `D(V_s)` at height at least lo.
> 2. Otherwise the HEAD is A, including when `D(V_s)` is nonempty.
> 3. If A=Z and `D(V_s)` is nonempty, Z belongs to `D(V_s)`.
> 4. In a settled phase, every honest HEAD K has a full-store witness
>    `W⪰K` with `ht(W)≥lo`. Every honest receiver admits W and its path
>    before `e_s`; for a protected prefix of K use admission or finality
>    coverage. This does not assert `ht(K)≥lo` for an outside start.
> 5. Let β be the first proposal label strictly after settlement u and
>    `ℓ=β+2k−1`. Every honest P at `t_s>t_ℓ` has exact HEAD and fresh
>    fast-write service if the phase persists through d_s. Such a gate
>    occurs by `u+ρΓ`, or the phase stops sooner. Service continues for
>    later honest proposals in that phase. Equal scores are required
>    only on the retained comparison suffix, with H.5's path premises.
> 6. Evidence first accepted at `w≥GST` is in all full stores before
>    `w+Δ`, and in every HEAD view with `v_s≥w+3Δ`, unless a frontier
>    rise ends the task. Thus one effective event costs `θ=3Δ` before
>    repair starts. Lower F moves and individual outside-start returns
>    do not add event charges. A later effective event stops the attempt.
>
> **Proof.** H.3 proves 1–4; H.5–H.6 prove 5; H.8 proves 6, including
> equality at `v_s=w+3Δ` under strict delivery. H.21 checks `R≥2`.
> This is a paper theorem. It does not assert a new Lean discharge.

- Status: 2026-09-29 — PROVED (paper; blueprint 21 H.3, H.5–H.6, H.8).

## 3. `SimplexFG.nj` lemmas (`Kit.FG`)

### `fg.provenance.v1` — row, entry and finality provenance

- Variant `both`. Source r146 §3.1, lines 244–247. File
  `fgsa-adjudicate.md`, sha256
  `0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017`. Rule
  sources: r143 §3.1 and §3.3. FJ: r148 §5 F7, lines 400–403 (same facts).
- Statement (pinned):

> _fgsa-adjudicate.md, lines 244–247:_
>
> Every progress or target QC contains an honest height row since `q_F>a`.
> Its entry T is a prefix of its successful fast source C. Each such C
> has an honest supporter since `τ>a`. Finality names an already justified
> entry and thus has this earlier target origin.

- Status: 2026-09-28 — PROVED.
- Status: 2026-09-28 — SUPERSEDED (audit W02 split, agreed with
  ethereum-f1). The statement mixes a pure FG fact, an SA fact and the
  Simplex source rule. Successors: `fg.provenance.v2` (pure FG),
  `ap.fastSupport.v1` (SA: a fast write has an honest supporter) and
  `comp.provenance.v1` (the source C is the signer's `C_fg`). Their
  conjunction is this statement.

### `fg.provenance.v2` — honest row, entry and finality provenance (pure FG)

- Variant `both`. Sources: r146 §3.1, lines 244–247 (file
  `fgsa-adjudicate.md`, sha256
  `0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017`); r143
  §3.3, lines 275–283 (file `fgsa-fast.md`, sha256
  `8907540c5c71fe06703bc8d2ec2d30bc6cbc752a5f7577219a69196e2fd8ef37`); bp
  F-table row F1, lines 294–295 (file `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`). FJ:
  r148 §5 F7, lines 400–403 (file `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`).
- Lean plan: DC-fj module (user 2026-09-28).
- Hypotheses: `q_F > a` (from `a≤f`); honest identities do not
  equivocate; the DC height-pair and finality-pair rules of r143 §3.3.
- Statement (registry): (1) every target, progress or finality QC has an
  honest row, since `q_F > a`. (2) An honest height row names the entry
  `T = σ[C].T_h` of the signer's source C, so `T ⪯ C`. (3) A finality row
  names the justified pair `(h_j, J)` of the signer's head state; hence a
  finality QC names an already justified entry, with an earlier target
  QC. The statement does not say how C is chosen or supported.
- Statement (pinned):

> _fgsa-adjudicate.md, lines 244–247 (excerpt; the first, second and
> fourth sentences; line breaks reflowed):_
>
> Every progress or target QC contains an honest height row since `q_F>a`.
> Its entry T is a prefix of its successful fast source C. Finality names
> an already justified entry and thus has this earlier target origin.

> _fgsa-fast.md, lines 275–283:_
>
> ```text
> finality_pair(Λ,hj,J,hF):
>     if hj>hF and Λ.target[hj]∈{none,J}
>        and not Λ.timeout[hj] and Λ.lock[hj]∈{none,J}:
>         return (hj,J)
>     return empty
>
> height_pair(Λ,C_fg,fp):
>     if C_fg absent: return empty
>     (h,T,nj) := (σ[C_fg].h, σ[C_fg].T_h, σ[C_fg].nj)
> ```

> _fgsa-healing-blueprint.md, lines 294–295:_
>
> ```text
> │ F1  │ Each target, progress, or finality QC   │ q_F>a                               │
> │     │ has an honest row.                      │                                     │
> ```

> _fj-redteam.md, lines 400–403:_
>
> Every target or progress QC contains an honest row because q>a. Each
> honest height row has a successful fresh fast source, with τ>a surviving
> supporters. Its named entry is an ancestor of that source. Finality has
> an earlier justified target origin.

- Status: 2026-09-28 — PROVED.
- Note: the word "successful fast" in the r146 excerpt and the second
  sentence of the r148 lines are not part of this entry. They are
  `ap.fastSupport.v1` and `comp.provenance.v1`.

### `fg.causalCap.v1` — causal cap at the cut

- Variant `both`. Sources: r147 §6, lines 642–651 (file
  `fgsa-conditional.md`, sha256
  `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`); r144
  §2.2, lines 168–193 (file `fgsa-no-nj.md`, sha256
  `1eaf728ffc4d56cc54fbccf581a8dffe457da02b96bd59cedb012bbf5ee1e03a`).
- Statement (pinned):

> _fgsa-conditional.md, lines 642–651:_
>
> **The causal cap used by the other job.** At an actual event-prefix cut
> with honest archival frontier M, each previously emitted honest height
> row has height at most M [DC6]. A crossing uses q_F distinct matching
> identities and hence an honest row. A carrier made only from pre-cut
> rows therefore has height at most M+1 and justified height at most M
> [DC7]. This includes later assembly from old signatures. The cap does
> not bound carriers that use new honest rows. It affects an R1 HEAD
> only when its own view contains the required height witness. These
> facts are consistent with N2's explicit first-q_s boundary; they do
> not replace its proof at NJ+1.

> _fgsa-no-nj.md, lines 168–193:_
>
> Use exactly the requested cut:
>
> ```text
> r_G = first action round at or after GST;
> u0  = a_(r_G+2), inclusive event prefix;
> M   = honest archival frontier at u0.
> ```
>
> Every honest height row in that prefix has height at most M, because its
> source was already in its signer's store. Every crossing has an honest
> row, since `q_F>a`. Hence a carrier whose height evidence uses only such
> old honest rows has height at most M+1, and its justified height is at
> most M. Faulty rows can be new; without a new honest row they cannot
> cross the next height. This includes a newly constructed carrier with
> old target rows. See [fg-frame-recovery §§2.3–2.4](fg-frame-recovery.md)
> and [WeakHeightBounds][height-bound].
>
> At a duty with `H_V≥M+2`, an old-only justification satisfies
>
> ```text
> j_old≤M < H_V−1,
> ```
>
> so it cannot be the active root. This is a duty-view statement. An
> archival rise must first reach the frozen HEAD view. Allow the R1 relay
> and freeze margin; do not substitute an unseen archival maximum.

- Status: 2026-09-28 — PROVED (r147 §6; r144 claims N1 and N2).
- Note: r144 claim N3 ("thus all later justifications are permanent") is
  REFUTED. The cap does not bound carriers that use new honest rows.
- Status: 2026-09-28 — SUPERSEDED (split agreed with ethereum-f1).
  Successors: `fg.causalCap.core.v1` (the cap for any bound M) and
  `comp.cut.v1` (the DC cut r_G, `u_0 = a_(r_G+2)` and M at `u_0`, with
  the duty-view clause, which also uses `comp.settle.v1`).

### `fg.causalCap.core.v1` — causal cap for a bound M

- Variant `both`. Sources: r147 §6, lines 642–651 (file
  `fgsa-conditional.md`, sha256
  `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`); bp
  F-table row F2, lines 296–297 (file `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`); DC
  Lean, vcW lines 42–48 (file
  `DecoupledConsensusProofs/Protocol/ValidatorClient/WeakHeightBounds.lean`,
  sha256 `f0d45fa7fd93a0a1c9f4dfccaf6c3f7c63c43245c5deee7182a25f3963c22b5d`).
- Lean plan: DC-fj module (user 2026-09-28).
- Hypotheses: `fg.provenance.v2` (each crossing and each target QC has an
  honest row); the honest DC client (a row names its source's own height).
- Statement (registry): (a) an honest row of height h, emitted by v at
  time t, has `h ≤` the archival maximum of v's store before t. (b) Let M
  be a height. A carrier whose honest rows all have height at most M has
  height at most M+1 and justified height at most M: a crossing of M+1
  and a target QC at M+1 each need an honest row at M+1. Faulty rows can
  be new; they cannot cross a height alone. The cap does not bound a
  carrier that uses a new honest row above M.
- Statement (pinned):

> _fgsa-conditional.md, lines 642–651:_
>
> **The causal cap used by the other job.** At an actual event-prefix cut
> with honest archival frontier M, each previously emitted honest height
> row has height at most M [DC6]. A crossing uses q_F distinct matching
> identities and hence an honest row. A carrier made only from pre-cut
> rows therefore has height at most M+1 and justified height at most M
> [DC7]. This includes later assembly from old signatures. The cap does
> not bound carriers that use new honest rows. It affects an R1 HEAD
> only when its own view contains the required height witness. These
> facts are consistent with N2's explicit first-q_s boundary; they do
> not replace its proof at NJ+1.

> _fgsa-healing-blueprint.md, lines 296–297:_
>
> ```text
> │ F2  │ Causal cap: an honest row at height h   │ WeakHeightBounds.lean:42            │
> │     │ has h ≤ the signer's archival maximum.  │ honestEmittedHeight_le_localHMax... │
> ```

> _WeakHeightBounds.lean, lines 42–48:_
>
> ```lean
> theorem honestEmittedHeight_le_localHMaxBeforeTime
>     (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
>     {v : V} {a : NamedAttestation V}
>     {t : Time} {h : Height}
>     (hemit : rho.emits S v (Object.attest a) t)
>     (hh : a.height_pair.erase.height? = some h) :
>     h ≤ (rho.storeBeforeTime S v t).h_max := by
> ```

- Status: 2026-09-28 — PROVED. Part (a) is LEAN for DC
  (`honestEmittedHeight_le_localHMaxBeforeTime`); there is no FG-SA Lean
  instance. Part (b) is the paper step of r147 §6 and r144 §2.2.
- Note: the pinned r147 text states the cap at a cut. This entry states
  it for any M; `comp.cut.v1` sets M to the DC cut maximum.

### `fg.uniqueJust.v1` — one justified entry per height (blueprint F3)

- Variant `both` (FJ keeps the certificate syntax and E1/E2, r148 F8).
  Sources: bp F-table row F3, line 298 (file `fgsa-healing-blueprint.md`,
  sha256 `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`);
  DC Lean L7 (Lemma U), vcE lines 229–249 (file
  `DecoupledConsensusProofs/Protocol/ValidatorClient/Engine.lean`, sha256
  `92fb0e64c1288afea98b53212cb3ad5c843c9c720187367eea578d17a9d53454`).
- Lean plan: DC-fj module (user 2026-09-28).
- Hypotheses: `a≤f`, so `2q_F−n > a`; honest identities follow E2 (at most
  one target per height).
- Statement (registry): at each height h, at most one entry is justified
  in the whole run (on any chain, in any store).
- Statement (pinned):

> _fgsa-healing-blueprint.md, line 298:_
>
> ```text
> │ F3  │ One justified entry per height (L7).    │ ValidatorClient/Engine.lean, a≤f    │
> ```

> _Engine.lean, lines 229–249:_
>
> ```lean
> /-- **Lemma U** (rev. 3 §1.3; PROTOCOL.md#the-complete-protocol): two target quorums at one
> height for **different** roots expose `2q − W` of E2 weight, at that height,
> against those two roots.
>
> Hence *"absent `2q − W` of E2-slashable weight, at most one target is justified
> at any height, on any chain, anywhere in the run"* — and hence the lex tiebreak
> on `(h_j, J.root)` never arbitrates between two real certificates
> (`Finality.lean:52–70`, rev. 3 §1.3): the root component separates only events
> at the same height, and by this lemma two real justifications never share one.
>
> Nothing about chains, stores or reachability enters. The quorums are abstract
> sets with per-member witnesses drawn one from each attestation pool, which is the
> same evidence discipline `SlashableBetween` uses — the pool a witness comes
> from is named, never existentially closed. -/
> theorem justification_unique_per_height (E : Env V)
>     {A₁ A₂ : Finset (CombinedAttestation V)} {Q₁ Q₂ : Finset V} {h : Height}
>     {T₁ T₂ : BlockId}
>     (hQ₁ : E.electorate.IsQuorum Q₁) (hQ₂ : E.electorate.IsQuorum Q₂)
>     (hw₁ : ∀ i ∈ Q₁, ∃ a ∈ A₁, a.val_index = i ∧ a.height_pair = .target h T₁)
>     (hw₂ : ∀ i ∈ Q₂, ∃ b ∈ A₂, b.val_index = i ∧ b.height_pair = .target h T₂) :
>     HasE2WeightAt E h T₁ T₂ A₁ A₂ := by
> ```

- Status: 2026-09-28 — LEAN (DC). The Lean theorem is the certificate
  form: two target quorums for different entries at one height give
  `2q−W` of E2 weight. The step to "at most one entry" uses
  `2q_F−n > a` and honest E2 compliance; it is one line of paper proof. The
  companion `justification_unique_per_height_slashable` is at vcE line
  261. There is no FG-SA Lean instance.

### `fg.finalLock.v1` — finality lock (blueprint F4)

- Variant `both`. Sources: bp F-table row F4, lines 299–300 (file
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`); DC
  Lean L8, vcF lines 50–56 (file
  `DecoupledConsensusProofs/Protocol/ChainState/FinalityComparison.lean`,
  sha256 `aa0ed92740eb1ec8ee69e90fd2ae75f03179a27c05accf5f631e7a254589b94c`).
  r148 calls the same fact the "finalized-crossing law" (line 226; file
  `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`).
- Lean plan: DC-fj module (user 2026-09-28).
- Hypotheses: the run satisfies the DC slashable bound (`a≤f`); roots are
  collision-free (in the Lean port `RootInjectiveOn`, discharged by
  `rootInjectiveOn_all` (I9, 2026-09-29); the DC pin below keeps
  `NamedRootCollisionFree`); the honest DC client (E1).
- Statement (registry): if D is a block of the run with finalized
  checkpoint `F(D)` at height `h_F(D)`, then every block C of the run with
  `h(C) > h_F(D)` extends `F(D)`.
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 299–300:_
>
> ```text
> │ F4  │ Finality lock: every block of height    │ FinalityComparison.lean:50          │
> │     │ > h_F(D) extends F(D) (L8).             │ finalized_preceq_of_height_lt       │
> ```

> _FinalityComparison.lean, lines 50–56:_
>
> ```lean
> theorem finalized_preceq_of_height_lt
>     (S : Setup V) (rho : NamedRun V) (C D : NamedBlock V)
>     (hsb : Internal.NamedOutageEntry.SlashableBound S rho)
>     (hroot : NamedRootCollisionFree S rho)
>     (hC : NamedRun.blockInRun S rho C) (hD : NamedRun.blockInRun S rho D)
>     (hlt : (derive_named S.E S.cfg D).h_F < (derive_named S.E S.cfg C).h) :
>     Block.Preceq (derive_named S.E S.cfg D).F C.erase := by
> ```

> _fj-redteam.md, lines 224–226:_
>
> Every frontier block has height above the height of accepted F: a
> finalization at y has a justification carrier at height at least y+1.
> The finalized-crossing law puts every such frontier block above F.

- Status: 2026-09-28 — LEAN (DC). There is no FG-SA Lean instance. bp
  §7.9, lines 831–843 (pinned in `fg.base.finalized.v1`), explains why
  the proof also covers crossings signed before the finality pairs.
- Status: 2026-09-29 — WITHDRAWN for current use (§0); successor
  `fg.finalLock.v2` (the accepted threshold, with genesis, and the
  evidence alternative without a fault bound). The pinned theorem stays
  true (carrier h_F, `a ≤ f`); `AvailableChainKitFG/Pins.lean` keeps the
  pin as a historical pin.


### `fg.finalLock.v2` — finality lock at the accepted threshold

- Variant `both`. Sources: blueprint 01 §8.2, file
  `blueprint/archive/01-foundations-200c9c07.md` (key `bp01`), lines
  701–723 (the carrier-form proof) and 725–743 (the statement), sha256
  `200c9c07a01bd5826750d0e89a985be87e588f98132a68534cdd719531302a99`;
  blueprint 00 §3, file `blueprint/archive/00-outline-e6dcbcc1.md` (key
  `bp00`), lines 643–651.
- Lean plan: DC-fj module (pin `fg.finalLock.v2` of
  `AvailableChainKitFG/Pins.lean`, sources `bp01`, `bp00`). The carrier
  form is Lean: `KFG.finalLock_e1` (the evidence alternative) and
  `KFG.finalLock` (the slashable-or form), with the carrier's h_F as the
  threshold. The accepted-carrier wrapper (the entry height of the
  accepted certificate; 0 for genesis; certificate provenance): Lean
  OPEN (r213b item 2); paper: bp01 734–736.
- Hypotheses: none for the evidence alternative; `a ≤ f` and honest
  client discipline for `F ⪯ W`. Dependencies: bp.carrier.v1,
  bp.chainCertificates.v1, bp.clientSafety.v1 (blueprint ids).
- Statement (pinned):

> _01-foundations-200c9c07.md, lines 701–723:_
>
> ### 8.2 Crossing and accountability — fg.finalLock.v2, fg.accountable.v1
>
> **REUSE of KFG.finalLock_e1 and accountable; proof expanded.**
> `KFG.accountable` requires `KFG.RootInjectiveOn` and gives the weight
> inequality `2q≤W+w(Slashable)`. Section 2 supplies root injectivity;
> unit weights give the identity count used here. The DC declaration
> `DecoupledConsensusModel.Proofs.NamedFinalizationBridge.finalized_preceq_of_height_lt`
> requires `SlashableBound` and root-collision freedom. It proves the
> fault-bounded ancestry clause only. The evidence alternative below uses
> `KFG.finalLock_e1`. The finalized height is the carrier's `h_F`;
> for genesis this can be 0 initially or 1 after its height-1 finalization.
> For two quorums Q₁,Q₂⊆V,
> |Q₁∩Q₂|=|Q₁|+|Q₂|−|Q₁∪Q₂|≥2q_F−n.
>
> Let D finalize F at height m, and ht(W)>m. If m=0, F=g by the
> genesis invariant, so F⪯W. If m>0, §3 supplies a finality quorum
> Q_f for (m,F) on D and a progress quorum Q_c matching the height-m
> entry E on W. If E=F, that entry is an ancestor of W, so F⪯W.
> If E≠F, root injectivity gives different roots. For each i∈Q_f∩Q_c,
> select its finality row on D and matching progress row on W.
> If the progress row is a timeout, the pair is E1. If it is a target,
> it targets E≠F, so the pair is E1. Distinct identities count once.
> This proves the evidence alternative of finalLock without any time bound.

> _01-foundations-200c9c07.md, lines 725–743:_
>
> **fg.finalLock.v2 — accepted-finalization threshold — PROVED-paper.**
> Let an honest node's accepted finalized block at e be F. Define
> `finheight(F,e)=0` for genesis, and otherwise the entry height of its
> accepted certificate. For every authenticated run block W emitted by
> e, if `ht(W)>finheight(F,e)`, then `F⪯W` or the certificate carrier
> and W expose at least `2q_F−n` slashable identities. This statement
> has no fault bound for the evidence alternative; under `a≤f` and
> honest client discipline it gives `F⪯W`.
>
> For non-genesis F, its admitted certificate carrier D has
> `σ[D].h_F=finheight(F,e)` by provenance; the proof above applies.
> For genesis, every block extends F, also when a carrier has `h_F=1`.
> This proves exactly the 4e85ff34 threshold (lines 494–497).
> The external registry's v1 is pinned to the carrier h_F and to the
> DC fault-bounded ancestry theorem. It does not state this normalized
> threshold and evidence alternative. Keep that pin as historical text;
> v2 supplies the new clause. Lean reuse: `KFG.finalLock_e1` for evidence,
> `KFG.finalLock` for the bounded corollary, and an accepted-carrier
> wrapper with the genesis case. The wrapper still needs a Lean proof.

> _00-outline-e6dcbcc1.md, lines 643–651:_
>
> **fg.finalLock.v2 — NEW — PROVED-paper.** For accepted F, put
> `finheight=0` for genesis and otherwise use its certificate entry height.
> For an authenticated run block W emitted by the event read with
> `ht(W)>finheight`, either `F⪯W` or its rows with the F carrier expose
> at least `2q_F−n` slashable identities. Under a≤f and client discipline,
> `F⪯W`. Proof and the genesis normalization: 01 §8.2. Dependencies:
> bp.carrier.v1, bp.chainCertificates.v1, bp.clientSafety.v1 (last clause).
> Keep fg.finalLock.v1's pinned text; mark it WITHDRAWN for current use
> under registry §0, successor fg.finalLock.v2. Its old theorem stays true.

- Status: 2026-09-29 — PROVED (paper; blueprint 01 §8.2). Clause 1 of
  `fj.frame.v4` cites this entry. Lean: the carrier form. The
  accepted-carrier wrapper: Lean OPEN; paper: bp01 734–736.

### `fg.trunk.v1` — F advance below the band

- Variant `nj`. Source bp §4.1, lines 352–375 (H2). File
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`. r149
  §4.1, lines 324–334, proves it again.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Hypotheses (named 2026-09-28; §0 rule (b)): `fg.finalLock.v1` (the "F4"
  of item 1); B2 of bp §3 (live leases at one reader form a chain);
  `a≤f`.
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 352–375:_
>
> Let d be a duty in F-mode with `H_d = m ≥ 2`. Then `h(F_d) ≤ m−2`: an F at
> m−1 is a justified checkpoint at m−1, its J carrier is in V_d (the F
> basis), and `F_d⪯F_d`, so j_d ≥ m−1 and d is in J-mode. Let F′ be a finalized block with `F_d⪯F′` and `h(F′) ≤ m−2`.
> Compare the frame of V_d with root F_d and with root F′.
>
> 1. Every W∈V_d with `h(W) ≥ m−1` extends F′, by F4. Hence every block of
>    D(F_d) is comparable with F′, and `D(F′) = D(F_d) ∩ desc(F′)`. F′ is in
>    D(F_d), since the maximizing carrier of height m extends F′.
> 2. Let M_d be the deepest live lease target in D(F_d), or F_d. By B2
>    the leases are a chain. If F′⪯M_d, M_d is also the start with root F′.
>    If M_d≺F′, no live lease lies in D(F′), since it would be deeper than
>    M_d in D(F_d). The start with root F′ is F′. The walk from M_d has
>    exactly one child on each step below F′, since every block of D(F_d)
>    is comparable with F′. Each such child has a parent of height
>    ≤ m−2 < m−1, so it is eligible. The walk from M_d therefore reaches F′.
> 3. Above F′ the two domains, scores, and eligibility tests are equal. The
>    score reads votes, not the domain. Hence both walks return the same
>    block. This applies to proposal, HEAD, and finality-head walks.
> 4. A fresh candidate of height ≥ m−1 is in both domains, by item 1. Thus
>    C_fg is the same whenever either choice has height ≥ m−1. A candidate
>    below that height gives a row at height ≤ m−2; such a row produces
>    carriers of height ≤ m−1 and cannot change the frontier m.
>
> So an F advance in F-mode changes no walk result and no band source.

- Status: 2026-09-28 — PROVED (a≤f).
- Note: the lemma compares one view with two roots. It does not transport a
  comparison between two views (r149 §4.3).
- Note (2026-09-29; current use): `fg.finalLock.v1` is WITHDRAWN for current
  use. The citations above are history. A current use of this entry
  reads them as §9, "Current reading of withdrawn ids".


### `fg.oneBullet.v1` — at most one effective filter change

- Variant `nj`. Source bp §4.2, lines 383–409 (H3). File
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 383–409:_
>
> Fix m. Let t_m be the time at which the honest frontier first equals m.
>
> 1. **Settling.** Every object that an honest store holds at t is in every
>    honest full view from t+Δ, and in every honest HEAD view at a time
>    ≥ t+θ. Proof: relay gives receipt by t+Δ at every honest reader. A HEAD
>    at `v_s ≥ t+4Δ` has freeze `t_s−Δ ≥ t+2Δ`. Since views are subsets of
>    stores, `H_d ≤ m` while the frontier is m. Thus `H_d = m` at every
>    honest duty in `[t_m+θ, ·)` until the frontier rises.
> 2. **Modes.** At `H_d = m`, J-mode means `j_d = m−1`. A justified entry at
>    m−1 is unique (F3). F_d has height ≤ m−1, and an F at m−1 equals
>    J_(m−1). An F at a lower height precedes J_(m−1) by F4. Thus J-mode at
>    d means `Ẑ_d = J_(m−1)`, for one fixed block. No justification above
>    m−1 exists at frontier m, because `h_j < h` on every chain.
> 3. **One change.** Let t_J be the first time at which an honest store
>    holds a carrier of J_(m−1), or ∞. Views are subsets of stores, so every
>    duty before t_J is in F-mode. By item 1, every duty at a time ≥
>    `max(t_m, t_J)+θ` is in J-mode, since stores only grow. Hence Φ_d
>    takes at most two values at frontier m, first (m,◇) and then
>    (m,J_(m−1)).
> 4. **No other change.** Lower J values do not act: `H_d = m ≠ j+1` for
>    `j ≤ m−2`. F advances in F-mode do not act (§4.1). A finalization of
>    J_(m−1) in J-mode leaves Ẑ_d unchanged. New blocks only add witnesses.
>
> Count: at a fixed frontier there is **at most one effective filter change**
> (the arrival of J_(m−1)). The adversary needs a higher frontier for a new
> change. This agrees with the one-exclusion count of
> [fgsa-fast §9.1](fgsa-fast.md) and [fgsa-fast-opus §6.5](fgsa-fast-opus.md).

- Status: 2026-09-28 — PROVED (a≤f).
- Notes: [async] r147 §6 counts control EVENTS (`m−1−f0+ε_J`, F advances
  included); bp counts EFFECTIVE filter values after the trunk lemma. θ is
  4Δ in bp and 3Δ in r147. [async] r149 §3 (lines 305–315) fixes θ = 4Δ.
- Status: 2026-09-28 — SUPERSEDED (split agreed with ethereum-f1). Item 1
  (settling) and the step "By item 1" of item 3 are run facts:
  `comp.settle.v1`. Items 2–4 without that step are the pure core:
  `fg.oneBullet.core.v1`. Their conjunction is this statement.

### `fg.oneBullet.core.v1` — effective filter at a fixed frontier (pure core)

- Variant `nj`. Source bp §4.2, items 2–4 and the count, lines 391–409
  (H3). File `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Hypotheses: `fg.frame.v2` (with `fg.frameCompat.v1`); `fg.uniqueJust.v1`
  (F3); `fg.finalLock.v1` (F4); `fg.trunk.v1` (F advances in F-mode do not
  act); `h_j < h` on every chain (DC transition, bp F5).
- Statement (registry): fix a frontier m. Let J_(m−1) be the justified
  entry at m−1, if one exists (unique by `fg.uniqueJust.v1`). For an
  honest duty d with `H_d = m`, let `E_J(d)` mean "V_d holds a carrier of
  J_(m−1)". Then:
  1. `Ẑ_d = J_(m−1)` if `E_J(d)`, and `Ẑ_d = ◇` otherwise. So
     `Φ_d ∈ {(m,◇), (m,J_(m−1))}`.
  2. If `E_J(d)` is false at every such duty before a time t1 and true at
     every such duty from a time t2 ≥ t1, then `Φ_d = (m,◇)` before t1 and
     `Φ_d = (m,J_(m−1))` from t2. Lower J values, F advances in F-mode, a
     finalization of J_(m−1) in J-mode and new blocks do not change Φ_d.
  Thus the effective filter changes at most once per frontier: one event
  (the arrival of J_(m−1)), with the interval `[t1,t2)` as its settling
  interval. The core does not say when t1 and t2 occur.
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 391–409:_
>
> 2. **Modes.** At `H_d = m`, J-mode means `j_d = m−1`. A justified entry at
>    m−1 is unique (F3). F_d has height ≤ m−1, and an F at m−1 equals
>    J_(m−1). An F at a lower height precedes J_(m−1) by F4. Thus J-mode at
>    d means `Ẑ_d = J_(m−1)`, for one fixed block. No justification above
>    m−1 exists at frontier m, because `h_j < h` on every chain.
> 3. **One change.** Let t_J be the first time at which an honest store
>    holds a carrier of J_(m−1), or ∞. Views are subsets of stores, so every
>    duty before t_J is in F-mode. By item 1, every duty at a time ≥
>    `max(t_m, t_J)+θ` is in J-mode, since stores only grow. Hence Φ_d
>    takes at most two values at frontier m, first (m,◇) and then
>    (m,J_(m−1)).
> 4. **No other change.** Lower J values do not act: `H_d = m ≠ j+1` for
>    `j ≤ m−2`. F advances in F-mode do not act (§4.1). A finalization of
>    J_(m−1) in J-mode leaves Ẑ_d unchanged. New blocks only add witnesses.
>
> Count: at a fixed frontier there is **at most one effective filter change**
> (the arrival of J_(m−1)). The adversary needs a higher frontier for a new
> change. This agrees with the one-exclusion count of
> [fgsa-fast §9.1](fgsa-fast.md) and [fgsa-fast-opus §6.5](fgsa-fast-opus.md).

- Status: 2026-09-28 — PROVED (a≤f; bp H3 without its item 1).
- Composition: with `comp.settle.v1`, take `t1 = t_J` (views are subsets
  of stores) and `t2 = max(t_m, t_J)+θ`, and restrict to duties in
  `[t_m+θ, t_up)`, where `H_d = m`. This gives the full bp §4.2 count.
- Note (2026-09-29; current use): `fg.finalLock.v1` is WITHDRAWN for current
  use. The citations above are history. A current use of this entry
  reads them as §9, "Current reading of withdrawn ids".


### `fg.H19.v1` — HNI-a

- Variant `nj`. Source bp §7.9, lines 803–809 (H19). File
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Hypotheses: `fg.HNI.v1` for m.
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 803–809:_
>
> **Lemma HNI-a — PROVED.** Assume HNI(m). At every honest duty d with
> `H_d = m`, every block B∈V_d with `h(B) ≥ m` is kept. This holds whatever
> F_d is and whether J at m−1 is known.
>
> Proof. At H_d = m, Z_d is J_d at m−1 or F_d with `h(F_d) ≤ m−1`. By (h1)
> or (h2), `Z_d ⪯ B`. The band threshold is m−1 ≤ h(B), so B is its own
> witness. Hence B∈D_d. ∎

- Status: 2026-09-28 — PROVED.

### `fg.HNIb.v1` — HNI-b

- Variant `nj`. Source bp §7.9, lines 815–827. File
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Hypotheses: `fg.HNI.v1` for m.
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 815–827:_
>
> **Lemma HNI-b — PROVED.** Assume HNI(m). At every honest duty d with
> `H_d ≥ m`, either `h(Z_d) ≥ m`, or Z_d precedes every block of V_d of
> height ≥ m. In the first case Z_d is a justified entry at a height ≥ m.
>
> Proof. If `h(Z_d) ≤ m−1`, then Z_d is F_d (with h ≤ m−1) or a J at
> `H_d−1`. The second option forces `H_d = m` and J at m−1. Apply (h2) or
> (h1). ∎
>
> So the only FG objects that can remove a block of height ≥ m are
> justified entries at heights ≥ m, and band thresholds above m. Both are
> made from honest rows at heights ≥ m (F1, F11). This is the split that
> Lemma K uses. In Lemma K, (K2) with F3 and F4 is exactly HNI(x+1), and
> (K1) controls the objects at heights ≥ x+1.

- Status: 2026-09-28 — PROVED.

### `fg.base.finalized.v1` — finalized arm gives HNI(x+1) run-wide

- Variant `nj`. Source bp §7.9, lines 831–843 (H20). File
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Hypotheses: the finalized arm of `fg.baseSel.nj.v1` (x = hF0 and the
  actual checkpoint F*); `a≤f`; `fg.uniqueJust.v1` (F3) and
  `fg.finalLock.v1` (F4), named 2026-09-28 (§0 rule (b)).
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 831–843:_
>
> - *Finalized arm — PROVED.* x = hF0 and F* is finalized at x. (h1): every
>   justified entry at x equals F* (F3), and F* precedes every block of
>   height > x (F4). (h2): a finalized checkpoint of height ≤ x precedes
>   every block of height > its own height (F4). F4 is
>   [finalized_preceq_of_height_lt][dc-finality]. Its proof uses only the
>   existence of the finality quorum in the run and the honest record
>   order: a height crossing at x with another entry and the finality
>   quorum share an honest identity, and that identity's first signature
>   forbids the second, in either order. So HNI(x+1) holds for the whole
>   run, including crossings signed **before** the finality pairs, and
>   including honest nodes that sign rows at x+1 without knowing F*. The
>   revelation of F* at a view with H_d = x+1 moves the root to F*; by
>   HNI-a it prunes only blocks that never reach x+1.

- Status: 2026-09-28 — PROVED.
- Note (audit W09): this is a lemma. The base-selection output is the
  witness record of `fg.baseSel.nj.v1`.
- Note (2026-09-29; current use): `fg.finalLock.v1` is WITHDRAWN for current
  use. The citations above are history. A current use of this entry
  reads them as §9, "Current reading of withdrawn ids".


### `fg.base.nj.v1` — NJ arm gives HNI(H+1) run-wide

- Variant `nj`. Source bp §7.9, lines 844–847 (H21). File
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Hypotheses: the NJ arm of `fg.baseSel.nj.v1`; `ap.S.v2`; `ap.Sslow.v1`;
  `fg.finalLock.v1` (F4, for (h2)), named 2026-09-28 (§0 rule (b)).
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 844–847:_
>
> - *NJ arm — PROVED from (S).* x = H. (h2) is F4. (h1) holds vacuously
>   because no justified entry at H ever exists. In the DC prefix this is
>   F7. For the whole run it is Theorem N clause (ii) with F1 (N-b). The NJ
>   arm therefore needs an induction, and the finalized arm does not.

- Status: 2026-09-28 — PROVED (FG-SA). bp has PROVED* from (S) (H21). Its
  hypothesis (S) is `ap.S.v2` (PROVED, r149), and r150 §2 (lines 131–133)
  states Theorem N clause (ii) as PROVED.
- Note (audit W09): run-wide HNI(H+1) is DERIVED inside the joint induction
  of `comp.theoremN.v1` (clause (ii) with F1). It is not a base-selection
  input. The base returns only the prefix NJ facts.
- Note (2026-09-29; current use): `fg.finalLock.v1` is WITHDRAWN for current
  use. The citations above are history. A current use of this entry
  reads them as §9, "Current reading of withdrawn ids".


### `fg.baseSel.nj.v1` — base-selection witness record (NJ or finalized)

- Variant `nj`. Sources: bp §1.2 and §6, lines 138–145, 483–492 and 500–514
  (file `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`); bp
  §7.1, lines 524–531; r150 §1, lines 94–112 (file `fgsa-theorem-h.md`,
  sha256
  `8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`); r146
  §4, lines 406–415 (file `fgsa-adjudicate.md`, sha256
  `0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017`).
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Hypotheses: `env.bp` (or `env.r150`); the honest frontier reaches H+3 (the
  deadline is in `comp.healedLit.v1` or `comp.arrivalNJ.v1`); for the
  finalized arm `fg.uniqueJust.v1` (F3) and `fg.finalLock.v1` (F4, also
  "DC's finalized-crossing law" in the r146 quote); `comp.cut.v1` and
  `fg.causalCap.core.v1` (F2, item 4). Named 2026-09-28 (§0 rule (b)).
- Returned witness (audit W09; FRAMEWORK-DESIGN.md §7.4). The base does not
  return HNI.
  1. Cut: `u_0 = a_(r_G+2)`, its inclusive event prefix, and M = the honest
     archival frontier at `u_0`; `GST+2P ≤ u_0 < GST+3P`. H is the first
     multiple of K above `M+D+2`; `H+3 ≤ M+D+K+5`.
  2. Height x > M, from the DC consumer: NJ arm `x = H`; finalized arm
     `x = hF0` with `M < x ≤ H+1`.
  3. Arm witness. NJ arm: the prefix NJ record facts F6 and F7 (nj = true at
     H before `first`; no honest lock, target record or target row at H in
     that prefix). Finalized arm: the actual finalized checkpoint F* at x in
     an honest store, with F3 (`fg.uniqueJust.v1`) and F4
     (`fg.finalLock.v1`).
  4. First row above x: r* = the least round of an honest row at height x+1,
     `s* = r*R`, its fresh fast source body C* and its entry T*.
     `r* > r_G+2`, `t_(s*) ≥ GST+2P`, s* and every later label are
     synchronous, and every honest row at height ≥ x+1 has round ≥ r*.
  5. First-transfer view facts of C*: C* is in every honest store before
     `z_(s*)` and in every honest view from its first freeze; each `q_(s*)`
     view has maximum exactly x+1; the root is below C*; every `q_(s*)` HEAD
     covers C*; `H_d ≥ x+1` at every honest duty from `q_(s*)`.
- Statements (pinned):

> _fgsa-healing-blueprint.md, lines 138–145:_
>
> Let r_G be the first action round with `a_(r_G) ≥ GST`. The DC cut is the
> inclusive event prefix at `u_0 = a_(r_G+2)`. Then `GST+2P ≤ u_0 < GST+3P`.
> Let M be the honest archival frontier at u_0. As in DC,
>
> ```text
> H = the first multiple of K strictly above M+D+2;
> M+D+3 ≤ H ≤ M+D+K+2;  H+3 ≤ M+D+K+5.
> ```

> _fgsa-healing-blueprint.md, lines 483–492:_
>
> **Consumer — PROVED port.** Apply F9 unchanged. Let `first` be the first
> event index at which the frontier is H+2, and let hF0 be the greatest h_F
> in honest stores before it.
>
> - **NJ arm:** `K | H` and `D < H−hF0`. Put `x = H`. Every chain state at H
>   in an honest store before `first` has nj = true (F6). F7 gives no honest
>   lock, target record, or target row at H in that prefix.
> - **Finalized arm:** otherwise `M < hF0 ≤ H+1`, and a finalized checkpoint
>   F* at height hF0 exists in an honest store. Put `x = hF0`. By F3, every
>   justified entry at x is F*. By F4, every block of height > x extends F*.

> _fgsa-healing-blueprint.md, lines 500–514:_
>
> **Reset round.** Let r* be the least round of an honest row at height x+1.
> Put `s* = r*R`, let C* be that row's source body, and T* its entry.
>
> - r* exists before the frontier reaches x+2, because that crossing folds
>   a quorum at x+1 with an honest row (F1). In both arms `x+2 ≤ H+3`, so
>   `a_(r*) < u_0 + (D+K+5)Λ_lvl`.
> - `x+1 > M`, so by F2 the signer's archival maximum exceeds M at a_(r*).
>   Hence `r* > r_G+2` and `t_(s*) = T_(r*) ≥ GST+2P`. The label s* and all
>   later labels are synchronous. This is the blueprint's causal cap.
> - Rows emitted before u_0 have heights ≤ M. A carrier that uses only them
>   has height ≤ M+1 and a justification ≤ M, since each crossing needs an
>   honest row. Since `x ≥ M+3` in the NJ arm and `x ≥ M+1` in the finalized
>   arm, such objects never set `H_d ≥ x+1` and never supply a root at x.
> - Every honest row at a height ≥ x+2 is later than some honest row at x+1.
>   Hence every honest row at a height ≥ x+1 has round ≥ r* and label ≥ s*.

> _fgsa-healing-blueprint.md, lines 524–531:_
>
> Every B∈𝒫 at label s is in every honest store before z_s, hence in every
> honest view from its first freeze on. Proof: a fast body has an honest
> supporter (B3) whose HEAD at v_s extends B. A slow body lies in the
> label-s genuine result, which has more than |D_s|/2 > a surviving
> supporters, one of them honest. That HEAD's path relays to every honest
> reader by `v_s+Δ = e_s < z_s`.
>
> At every honest duty d with `t_d ≥ q_(s*)`, `C*∈V_d` and so `H_d ≥ x+1`.

> _fgsa-theorem-h.md, lines 103–112:_
>
> Use the actual DC consumer, with both outcomes. In the NJ outcome,
> `x=H` and the retained prefix has no honest target or lock at H. In
> the finalized outcome, x is its actual finalized height, `M<x≤H+1`,
> and F* is the named checkpoint at x. Every block of height greater
> than x extends F*. Do not replace this outcome by an assumed NJ bit.
>
> Let r* be the least round of an honest height-(x+1) row, let `s*=r*R`,
> and let C* be its fresh fast source body. The causal cap gives a wholly
> post-GST source label s*. Every honest row at height at least x+1 has
> label at least s*. These are the reset facts in blueprint §6.

> _fgsa-adjudicate.md, lines 406–415:_
>
> **First transfer.** An honest surviving supporter held the complete C*
> path at v_s*. Relay puts that path in every freeze z_s*. No earlier
> honest row at x+1 exists, so no earlier carrier at x+2 can exist.
> Each q_s* view has maximum exactly x+1. The NJ record induction excludes
> J at x in this prefix. In the finalized arm, any J at x equals F*;
> every block above height x extends F* by DC's finalized-crossing law.
> In either case the root is below C*. The path is viable. The τ release
> removes every conflicting lease, and the strict score transfer makes
> every q_s* HEAD cover C*. Same-label genuine compatibility excludes a
> conflicting pending write at d_s*.

- Status: 2026-09-28 — PROVED (FG-SA). bp §6 "Consumer — PROVED port"; r146
  claims 2a and 2b; r143 claim C12 (first transfer).
- Note: a Lean port of the consumer must re-derive the DC chain-state facts
  for a mixed instance (bp lines 494–498).
- Note (2026-09-29; current use): `fg.finalLock.v1` is WITHDRAWN for current
  use. The citations above are history. A current use of this entry
  reads them as §9, "Current reading of withdrawn ids".


### `fg.accountable.v1` — accountable FG safety

- Variant `both`. Sources: r143 §6, lines 474–485 (file `fgsa-fast.md`,
  sha256 `8907540c5c71fe06703bc8d2ec2d30bc6cbc752a5f7577219a69196e2fd8ef37`)
  for `nj`; r148 §5 F8, lines 452–462 (file `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`) for
  `fj`.
- Lean plan: DC-fj module (user 2026-09-28).
- Statement (pinned):

> _fgsa-fast.md, lines 474–485:_
>
> Each justification has q_F distinct matching targets. Each height crossing
> has q_F distinct matching progress identities. Each finalization has q_F
> matching finality identities. DC's crossed-height certificate argument
> therefore extracts at least `2q_F−n` identities with E1/E2 evidence from
> two conflicting finalizations. It uses full fixed identities, not base
> seats. Under `a≤f`, `2q_F−n>a`, so conflicting finalizations are impossible.
> Above that cap the accountable statement still holds. It is not an
> unconditional agreement claim.
>
> The live finality update advances F only to a proper descendant; local F
> never retreats. The accessor in §4 gives `finalized⪯available` at every
> read. These results do not depend on the missing base-history proof.

> _fj-redteam.md, lines 452–462:_
>
> F8 — PROVED. The certificate syntax, exact-entry transition, E1/E2,
> and signing client are unchanged. The pure DC accountable-finality
> proof still extracts at least 2q−n slashable identities from conflicting
> finalizations. A finite no-NJ prefix can be checked with a finite K
> larger than every height in it; no NJ bit is then set. Alternatively,
> repeat the certificate argument, which does not require scheduled NJ
> heights. With a≤f, conflicting finalizations are impossible.
>
> Pointwise finalized ⪯ available follows directly from the two accessor
> cases, even outside the fault bound. It does not imply F⪯S in every
> damaged local state.

- Status: 2026-09-28 — PROVED (r143 C7, C8; r148 F8). LEAN for DC only (the
  DC accountable-finality theorem); there is no FG-SA Lean instance.
- Status: 2026-09-28 (r158) — under ALFS: FG accountable safety, and
  safety at `a≤f`, are PROVED (the DC certificate result; FJ, SA source
  selection and timeout maturity do not change the certificate
  implications; r158 table line 889 and lines 909–915).
- Status: 2026-09-28 (r161) — under ALFS (spec bd942ca0): HOLDS (same
  signed pairs and certificate fold; r161 §6.1 table). r161 N1 with
  `n=7, a=3` gives a concrete FG safety failure at `f<a<h` (two
  conflicting finalizations; the quorums intersect in the three faulty
  identities; r161 lines 463–466). This is outside the premise `a ≤ f`.
- Note (2026-09-28): the output-nesting clause is `comp.outputNesting.v1`;
  the "local F never retreats" clause stays here (Lean
  `update_finality_F_mono`).

## 4. `SimplexFG.fj` — FJ root rule, own frame and interface (audit W06)

FJ changes the frame rule: a frontier test, root F and band `{H}` in a
contest. It is a module variant, not a base selector. HNI is NOT the FJ
interface. FJ can keep a height-(M+1) source that does not extend an old
justified entry at M; this is a failure of HNI(M+1).(h1), while FJ's filter
still protects the source:

> _fgsa-no-nj-opus.md, lines 612–620:_
>
> **N14: NJ-free reset — PROVED.** Under FJ every step of a descent chain
> has `x ≥ σ[C].h`. So every abandoned post-GST source has height at most
> M (§3.3). Every honest row at height ≥ M+1 has a synchronous label, so
> its source is extended by every honest HEAD from its label on. The next
> unanimous batch then puts it in every S by `t_s+10Δ` (fgsa-fast-opus
> §5.1 step 7). This is Lemma R with `x=M` and no NJ. It also follows the
> proof in fgsa-adjudicate §4: the only change is its "old J at x" clause.
> Under FJ an old J at M cannot pass a source C* at M+1, because C* is a
> frontier block that does not extend it.

Thus `fg.HNI.v1`, `fg.H19.v1`, `fg.HNIb.v1`, `fg.trunk.v1`,
`fg.oneBullet.v1` (now `fg.oneBullet.core.v1`), `fg.base.finalized.v1`,
`fg.base.nj.v1` and `fg.baseSel.nj.v1` do not apply to FJ. The FJ
noninterference interface is `fj.descent.v1`, `fj.canonical.v1` (F9),
`fj.inBandLock.v1` (F10) and `fj.twoChanges.v1` (F12; now
`fj.twoChanges.core.v1` with `comp.settle.v1`); its reset witness is
`fj.reset.v1`. The `both` entries `fg.provenance.v2`,
`fg.causalCap.core.v1`, `fg.uniqueJust.v1`, `fg.finalLock.v1`,
`fg.frameCompat.v1`, `comp.provenance.v1`, `comp.settle.v1` and
`comp.cut.v1` apply to FJ. The FJ cap M
is the cap on old honest rows (`env.r148`); it is at most DC's archival
M0. r151 calls this cap μ and calls M0 simply M.

### `fj.frame.v1` — FJ frame and walk

- Variant `fj`. Source r148 §2, lines 148–185 and 188–192. File
  `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`. Rule
  origin: r144o §5.3, lines 565–583 (file `fgsa-no-nj-opus.md`, sha256
  `7df2a540134deddede78ea711754bb322911fced62271868f8b5034164db9f4e`).
- Lean plan: DC-fj module (user 2026-09-28).
- Hypotheses (named 2026-09-28; §0 rule (b): the pinned text uses the
  lex order `(h_j, J.root)` and ties by root): `ViewRootInj` (§0.4);
  discharged by `viewRootInj_all` (I9, 2026-09-29).
- Lean coverage (DC-fj module): frame only (F, H, j, J, Z, lo, D,
  contest, viability). `fgsa_head`, eligibility and the walk are AP data;
  see `ap.headReachesLo.v1` (user design correction 2026-09-28).
- Note (2026-09-28): this is the view form, and it is not superseded. The
  protocol's HEAD uses `fj.frame.v2` (ALFS). v1's controls equal v2's
  store controls on the full store under `StoreInv`.
- Statement (pinned):

> _fj-redteam.md, lines 148–185:_
>
> ```text
> FJ_FRAME(V):
>     F := current accepted F
>     H := max({1} ∪ {h(W): W∈V})
>     (j,J) := lex-greatest (σ[W].h_j, root(σ[W].J)) witnessed in V
>              with F ⪯ σ[W].J
>     front := {W∈V: h(W)=H}
>     contest := (H=j+1 and exists W∈front with not J⪯W)
>
>     if H=j+1 and not contest:
>         Z := J
>         lo := H−1
>     else if contest:
>         Z := F
>         lo := H
>     else:
>         Z := F
>         lo := H−1
>
>     viable := {B∈V: F⪯B and
>                     exists W∈V with B⪯W and h(W)≥lo}
>     D := {B∈viable: Z⪯B}
>     return (F,H,j,J,Z,lo,D,contest)
>
> get_fg_root(V):
>     return FJ_FRAME(V).Z
>
> get_filtered_block_tree_from(V):
>     return FJ_FRAME(V).D
>
> fgsa_head(V, raw, declared, currentSlot):
>     frame := FJ_FRAME(V)
>     A := deepest live lease target in frame.D, else frame.Z
>     score(B) := raw equivocators
>                 + clean declared supporters whose HEAD extends B
>     eligible(B) := h(B.parent)<frame.lo
>                    or 2*score(B)>number_of_raw_participants
>                    or B.slot=currentSlot
>     return GHOST(A, frame.D, score, eligible)
> ```

> _fj-redteam.md, lines 188–192:_
>
> Full proposal and finality-head reads use OTHER_VIEW. HEADs use
> HEAD_VIEW. A lease outside D stays in the raw guard and release test.
> The code must change both viability and below-band eligibility in a
> contest. Changing only one does not supply the proof that the walk
> reaches H.

- Status: 2026-09-28 — def (r148 claim F1, exact FJ delta, PROVED).
- Note (2026-09-28): the contest test is the local witness of r148 lines
  260–270: an admitted W in the view with `h(W) = j+1` and `J ⋠ W`. By
  ancestor closure this is a conflicting crossing of j in the view, so
  `fj.crossingNoFinal.v1` shows that J cannot finalize. The converse is
  false (r148 F3, REFUTED): J can be unable to finalize without a contest.
  `fg.frameCompat.v1` shows that the `F ⪯ σ[W].J` test selects the same
  pair as "compatible with F" (`env.r151`, line 44).

> _fj-redteam.md, lines 260–270:_
>
> The exact local geometric witness used by FJ at H=j+1 is:
>
> ```text
> exists admitted W in this duty view:
>     h(W)=j+1 and not J⪯W.
> ```
>
> Ancestor closure makes this equivalent to a conflicting crossing of j
> materialized in this view. All frontier blocks extending J is exactly
> the absence of this geometric witness. It is not exactly the absence
> of every possible proof that J cannot finalize.

- Note (2026-09-28; §0 rule (a)): `fj.frame.v2` is SUPERSEDED by
  `fj.frame.v3` (spec bd942ca0: Σ.T in place of Σ.T_F, the same set;
  `update_finality` also calls `reconcile_with_finality`, which writes no
  frame input). A citation of `fj.frame.v2` here reads as `fj.frame.v3`.
- Note (2026-09-29; current use): `fj.frame.v3` is WITHDRAWN for current
  use; its successor is `fj.frame.v4` (spec `fgsa3`). The frame controls
  do not change; the Trees clauses change (no deletion from Σ.T, the SA
  walk starts at Σ.F). The note above is history. A current citation of
  `fj.frame.v2` or `fj.frame.v3` here reads as `fj.frame.v4`.

### `fj.frame.v2` — FJ frame from the live store caches (ALFS)

- Variant `fj`. Source: the ALFS spec (DC form), file
  `spec/archive/fgsa-protocol-1c6952b6.tex` (key `alfs3`), sha256
  `1c6952b6e6ef92bf9111121f0fb283671af6ce936b6db3c33d056b9dda35ffcd`:
  `fg_contest` lines 926–932, `band_floor` 934–942, `viable_tree_from`
  944–950, `viable_tree` (acceptance) 952–958, `get_fg_root` 960–967,
  `get_filtered_block_tree_from` and `get_filtered_block_tree` 969–981,
  `live_root` 1030–1042, `get_head_in_tree` 1044–1051,
  `voter_processed_block_tree` and `voter_filtered_block_tree`
  1160–1175, the HEAD duty call 1236–1238, and the cache update
  `update_finality` 825–838. Re-pinned 2026-09-28 from
  `spec/archive/fgsa-protocol-c7c41a43.tex` (key `alfs2`; the same
  functions at lines 919–925, 927–935, 937–943, 945–951, 953–960,
  962–974, 1023–1035, 1037–1044, 1153–1168, 1229–1231 and 818–831), and
  before that from
  `spec/archive/fgsa-protocol-183f2c40.tex` (key `alfs`; the same
  functions at lines 910–916, 918–926, 928–934, 936–942, 944–951,
  953–965, 1014–1026, 1028–1035, 1144–1159, 1220–1222 and 809–822). Proof file:
  `tsc/fgsa-live-dc-port.md` (key ldp; ALFS is its §1).
- Lean plan: DC-fj module (user 2026-09-28). Lean names (f1's plan):
  `storeControls`, `fjControls`, `filteredFrom`,
  `storeControls_eq_fjControls` (under `StoreInv` and `ViewRootInj`;
  `ViewRootInj` is discharged by `viewRootInj_all`, I9, 2026-09-29);
  `fjFrame = filteredFrom (fjControls V) V` is the special case.
- Hypotheses: `ViewRootInj` (§0.4), for the lex order of `update_finality`
  (lines 828–831); discharged by `viewRootInj_all` (I9, 2026-09-29).
- Summary (registry): controls from the live store caches (F, J, h_j,
  hmax; the contest from the full T_F, never a view); the domain filter
  applied to any block set; the HEAD walks the frozen voter tree from
  `live_root` (the deepest live lease in the full filtered tree, else the
  FG root), which may lie outside the walked tree.
- Statement (pinned):

> _fgsa-protocol-1c6952b6.tex, lines 926–932:_
>
> ```latex
> \Function{fg\_contest}{$\Sigma$}
>   \Comment{new (a): \FJ{2}, on the live caches (\LDP{1})}
>   \State \Return $\Sigma.\hmax=\Sigma.h_j+1$ \textbf{and} some
>     $W\in\Sigma.\TF$ has $\Sigma.\sigma[W].h=\Sigma.\hmax$ and
>     $\Sigma.J\not\preceq W$
>   \Comment{full store, never a view}
> \EndFunction
> ```

> _fgsa-protocol-1c6952b6.tex, lines 934–942:_
>
> ```latex
> \Function{band\_floor}{$\Sigma$}
>   \Comment{new (a): \FJ{2}}
>   \If{$\Call{fg\_contest}{\Sigma}$}
>     \State \Return $\Sigma.\hmax$
>     \Comment{band $\{H\}$}
>   \EndIf
>   \State \Return $\Sigma.\hmax-1$
>   \Comment{\cite{DC}: band $\{H-1,H\}$}
> \EndFunction
> ```

> _fgsa-protocol-1c6952b6.tex, lines 944–950:_
>
> ```latex
> \Function{viable\_tree\_from}{$\Sigma,\mathit{blocks}$}
>   \Comment{\DC{7}, redefined (a): band floor; choice only}
>   \State $\lo\gets\Call{band\_floor}{\Sigma}$
>   \State \Return $\{B\in\mathit{blocks}:\Sigma.F\preceq B,\
>     \exists B'\in\mathit{blocks},\ B\preceq B',\
>     \Sigma.\sigma[B'].h\geq\lo\}$
> \EndFunction
> ```

> _fgsa-protocol-1c6952b6.tex, lines 952–958:_
>
> ```latex
> \Function{viable\_tree}{$\Sigma$}
>   \Comment{\DC{7}, adapted: admitted tree; acceptance only}
>   \State \Return $\{B\in\Sigma.\TF:\Sigma.F\preceq B,\
>     \exists B'\in\Sigma.\TF,\ B\preceq B',\
>     \Sigma.\sigma[B'].h\geq\Sigma.\hmax-1\}$
>   \Comment{\cite{DC}'s band, also in a contest (\FJ{2})}
> \EndFunction
> ```

> _fgsa-protocol-1c6952b6.tex, lines 960–967:_
>
> ```latex
> \Function{get\_fg\_root}{$\Sigma$}
>   \Comment{\DC{7}, redefined (a) by \FJ{2}}
>   \If{$\Sigma.\hmax=\Sigma.h_j+1$ \textbf{and not} $\Call{fg\_contest}{\Sigma}$}
>     \State \Return $\Sigma.J$
>   \EndIf
>   \State \Return $\Sigma.F$
>   \Comment{a contest roots at $F$}
> \EndFunction
> ```

> _fgsa-protocol-1c6952b6.tex, lines 969–981:_
>
> ```latex
> \Function{get\_filtered\_block\_tree\_from}{$\Sigma,\mathit{blocks}$}
>   \Comment{\DC{7}, unchanged}
>   \State $\mathit{root}\gets\Call{get\_fg\_root}{\Sigma}$
>   \State \Return
>     $\{B\in\Call{viable\_tree\_from}{\Sigma,\mathit{blocks}}:
>       \mathit{root}\preceq B\}$
> \EndFunction
> \vspace{1pt}
> \Function{get\_filtered\_block\_tree}{$\Sigma$}
>   \Comment{\DC{7}, adapted: admitted tree}
>   \State \Return
>     $\Call{get\_filtered\_block\_tree\_from}{\Sigma,\Sigma.\TF}$
> \EndFunction
> ```

> _fgsa-protocol-1c6952b6.tex, lines 1030–1042:_
>
> ```latex
> \Function{live\_root}{$\Sigma$}
>   \Comment{\DC{7} \fname{get\_sg\_root}, redefined (b); \SAS{} \fname{live\_root}}
>   \State $\mathit{tree}\gets\Call{get\_filtered\_block\_tree}{\Sigma}$
>   \Comment{the full filtered tree, not a view}
>   \State $\mathit{targets}\gets\{B\in\mathit{tree}:\Sigma.\lease[B]\neq\bot\}$
>   \Comment{they lie on one chain}
>   \If{$\mathit{targets}=\emptyset$}
>     \State \Return $\Call{get\_fg\_root}{\Sigma}$
>     \Comment{no live lease in the tree}
>   \EndIf
>   \State \Return the deepest $B\in\mathit{targets}$
>   \Comment{the deepest live lease in place of grade~1}
> \EndFunction
> ```

> _fgsa-protocol-1c6952b6.tex, lines 1044–1051:_
>
> ```latex
> \Function{get\_head\_in\_tree}{$\Sigma,\mathit{tree},
>   \mathit{votes},\mathit{support\_votes},k$}
>   \Comment{\DC{7}, adapted (b): live root}
>   \State $A\gets\Call{live\_root}{\Sigma}$
>   \Comment{in place of \fname{get\_sg\_root}}
>   \State \Return $\Call{goldfish\_fork\_choice}{\Sigma,A,
>     \mathit{tree},\mathit{votes},\mathit{support\_votes},k}$
> \EndFunction
> ```

> _fgsa-protocol-1c6952b6.tex, lines 1160–1175:_
>
> ```latex
> \Function{voter\_processed\_block\_tree}{$\Sigma,s$}
>   \Comment{\DC{7}, adapted: admitted tree}
>   \State $\mathit{freeze}\gets t_{s-1}+3\Delta$
>   \State $\mathit{proposals}\gets\{P\in\Sigma.\TF:P.\slot=s\}$
>   \State \Return $\{B\in\Sigma.\TF:
>     \Sigma.\timestamp(B)<\mathit{freeze}\ \textbf{or}\
>     \exists P\in\mathit{proposals},\ B\preceq P\}$
> \EndFunction
> \vspace{1pt}
> \Function{voter\_filtered\_block\_tree}{$\Sigma,s$}
>   \Comment{\DC{7}, unchanged}
>   \State $\mathit{blocks}\gets
>     \Call{voter\_processed\_block\_tree}{\Sigma,s}$
>   \State \Return
>     $\Call{get\_filtered\_block\_tree\_from}{\Sigma,\mathit{blocks}}$
> \EndFunction
> ```

> _fgsa-protocol-1c6952b6.tex, lines 1236–1238:_
>
> ```latex
>     \State $\mathit{tree}\gets\Call{voter\_filtered\_block\_tree}{\Sigma,s}$
>     \State $H\gets\Call{get\_head\_in\_tree}{\Sigma,\mathit{tree},
>       \mathit{votes},\mathit{support\_votes},s-1}$
> ```

> _fgsa-protocol-1c6952b6.tex, lines 825–838:_
>
> ```latex
> \Function{update\_finality}{$\Sigma,\sigma$}
>   \Comment{\DC{7}, adapted (b): no grades to cut back}
>   \State $\Sigma.\hmax\gets\max(\Sigma.\hmax,\sigma.h)$
>   \If{$\Sigma.F\preceq\sigma.J$ \textbf{and}
>       $(\sigma.h_j,\sigma.J.\rootf)>(\Sigma.h_j,\Sigma.J.\rootf)$}
>     \Comment{lex order}
>     \State $(\Sigma.J,\Sigma.h_j)\gets(\sigma.J,\sigma.h_j)$
>   \EndIf
>   \If{$\Sigma.F\prec\sigma.F$ \textbf{and} $\sigma.F\preceq\Sigma.J$
>       \textbf{and} $\sigma.F\in\Call{viable\_tree}{\Sigma}$}
>     \State $\Sigma.F\gets\sigma.F$
>     \Comment{does not change $S$ or leases}
>   \EndIf
> \EndFunction
> ```

- Status: 2026-09-28 — def (spec text; red-team pending).
- Status: 2026-09-28 (r158) — def; r158 found no issue in the frame
  functions. The r158 function audit against DC §7 (r158 §2, lines
  126–203; table lines 138–194) finds `update_finality`, `advance_height`,
  `fg_contest`, `band_floor`, `viable_tree_from`, `viable_tree`,
  `get_fg_root` and `get_filtered_block_tree(_from)` equal to DC or to DC
  with the declared FJ and SA replacements, and "No further unlisted
  executable FG rule was found" (line 203). The r158 findings M1–M3 and
  L1–L3 (lines 55–124) are not in these functions: M1 concerns the HEAD
  anchor (`ap.headReachesLo.v2`), M2 the raw-proposal vote merge in
  `goldfish_vote` (lines 186–187).
- Status: 2026-09-28 (r159) — def; re-pinned in place to spec c7c41a43
  (`alfs2`). The text of all 11 pinned blocks is unchanged; only the line
  numbers moved (+9). r159 changes only the HEAD vote merge (the
  current-slot proposal scan of `goldfish_vote`, spec lines 1222–1223)
  and the prose next to it (lines 555–565); the other function-text
  change is a comment of `advance_height` (r159 lines 223–226). The vote
  merge is AP data, not a frame function, so no `fj.frame.v3` is needed.
- Status: 2026-09-28 (r160) — def; re-pinned in place to spec 1c6952b6
  (`alfs3`). The text of all 11 pinned blocks is unchanged; only the line
  numbers moved (+7). The r160 spec change is in the Relay paragraph, the
  Clean and Recovery premises, §5 row 29, the OPEN list and the
  bibliography; no frame function changed. `fj.frame.v2` has no relay
  hypothesis.
- Status: 2026-09-28 (r161) — SUPERSEDED by `fj.frame.v3` (spec
  bd942ca0). Five pinned blocks changed their text: `fg_contest`,
  `viable_tree`, `get_filtered_block_tree` and `voter_processed_block_tree`
  read Σ.T in place of Σ.T_F, and `update_finality` now calls
  `reconcile_with_finality`. By §0 the pinned text does not change, so
  the changed text is a new id. The frame controls are the same: Σ.T of
  bd942ca0 and Σ.T_F of this entry are the same set (see
  `fj.frame.v3`). This entry keeps its spec 1c6952b6 pins.
- Note: `fj.frame.v1` is the view form and is not superseded. Its
  controls equal this entry's store controls on the full store under
  `StoreInv`. The acceptance tree `viable_tree` keeps DC's band `hmax−1`
  also in a contest (lines 956–957). The spec has no F basis and no J carrier
  (compare `fg.frame.v2`, `fg.frameCompat.v1`).

### `fj.frame.v4` — FJ frame from the live store caches (FG-SA, spec c1ea1db0)

- Variant `fj`. Source: the adopted FG-SA spec, file
  `spec/archive/fgsa-protocol-c1ea1db0.tex` (key `fgsa3`), sha256
  `c1ea1db08f1da37bcde075df5d70f23af7c9941bd05ae5e8aca1bb48d1b777ed`:
  the Trees paragraph, lines 489–515, `on_block` 944–969,
  `fg_contest` 1122–1128, `band_floor` 1130–1138,
  `viable_tree_from` 1140–1146, `viable_tree` (acceptance) 1148–1154,
  `get_fg_root` 1156–1163, `get_filtered_block_tree_from` and
  `get_filtered_block_tree` 1165–1177, `live_root` 1226–1238,
  `get_head_in_tree` 1240–1247, `voter_processed_block_tree` and
  `voter_filtered_block_tree` 1361–1376, the HEAD duty call 1437–1439, and
  the cache update `update_finality` 999–1012. Clause split: blueprint 00
  §3, file `blueprint/archive/00-outline-e6dcbcc1.md` (key `bp00`), lines
  589–641, sha256
  `e6dcbcc1859dca4e9f30f7f947b6608ac4e1ab55b99cd1c562bd1f827965647d`.
  Proofs: blueprint 01 §4, §6.5–§6.6, §8.2 and §11 (key `bp01`). The
  blueprint cites 4e85ff34 lines; add 9 for `fgsa3` (§0.1). Proof sources
  of the carried clauses: ldp §1 and r161 §2, as for `fj.frame.v3`.
- Lean plan: DC-fj module. The clause-level coverage is the pin
  `fj.frame.v4` of `AvailableChainKitFG/Pins.lean`. Clauses 2 and 3a also
  cite FG-SA constants (`leanIn "AvailableChainFGSA"`): the pin gate is
  `scripts/check-fg.sh` plus `scripts/check-fgsa.sh`. Lean names of the
  carried clauses, as for `fj.frame.v3`: `storeControls`, `fjControls`,
  `filteredFrom`, `storeControls_eq_fjControls` (under `StoreInv`;
  `ViewRootInj` is discharged by `viewRootInj_all`, I9).
- Hypotheses: `ViewRootInj` (§0.4), for the lex order of `update_finality`
  (lines 1002–1005); discharged by `viewRootInj_all` (I9). Clause 1 uses
  `fg.finalLock.v2`.
- Clauses. The Trees clauses replace those of `fj.frame.v3`. Each clause
  has one evidence kind:

```text
┌────┬──────────────────────────────────────────┬────────────────────────────────┐
│ #  │ Clause (fgsa3 lines)                     │ Evidence                       │
├────┼──────────────────────────────────────────┼────────────────────────────────┤
│ 0  │ Σ.T is parent-closed and cumulative; a   │ Lean with hypotheses (v3's):   │
│    │ new block enters only if it extends F    │ Store, storeInv_init,          │
│    │ (489–492)                                │ storeInv_on_block,             │
│    │                                          │ on_block_TF_subset,            │
│    │                                          │ update_finality_TF             │
│ 1  │ A block of Σ.T outside the active view   │ fg.finalLock.v2 (external).    │
│    │ with state height above the entry height │ The accepted-carrier wrapper:  │
│    │ of the accepted finalization (0 for      │ Lean OPEN; paper: bp01 734–736 │
│    │ genesis) needs a slashable conflict      │                                │
│    │ (502–506)                                │                                │
│ 2  │ No rule deletes a block of Σ.T; storage  │ Lean: on_block_TF_subset,      │
│    │ pruning is a retention item (506–511)    │ update_finality_TF (FG store); │
│    │                                          │ Lean in AvailableChainFGSA:    │
│    │                                          │ process_cumulative,            │
│    │                                          │ clock_cumulative (FG-SA store) │
│    │ Remark: deletion can change the HEAD and │ paper (FR M1, N2; blueprint 01 │
│    │ S, also at a ≤ f (507–510)               │ §11.1–§11.2)                   │
│ 3a │ The confirmation walk starts at Σ.F in   │ Lean in AvailableChainFGSA:    │
│    │ act(Σ); its result passes the strict-    │ gateStep, fastSet,             │
│    │ majority test, also at Σ.F (511–513)     │ gateStep_fresh (the saved      │
│    │                                          │ result is SA.confirmationFrom  │
│    │                                          │ from Σ.F),                     │
│    │                                          │ clock_eq_saClockFrom_gate      │
│ 3b │ The FJ viability and band filter does    │ AP data (the SA walk; the      │
│    │ not restrict that walk (514–515)         │ HEAD and FG duties filter)     │
│ 4  │ act(Σ) is a view of Σ.T (493–496); the   │ Lean: activeView,              │
│    │ SA base reads only the active view       │ activeView_subset; AP data:    │
│    │ (497–499)                                │ the SA base runs on actView    │
└────┴──────────────────────────────────────────┴────────────────────────────────┘
```

- Change against `fj.frame.v3` (2026-09-29): only the Trees paragraph
  changes (clauses 1, 2 and 3a above; clauses 0, 3b and 4 have the same
  text at new lines). The other pinned blocks are byte-identical to those
  of `fj.frame.v3`, at bd942ca0 lines + 152 (`on_block` to
  `get_head_in_tree`, `update_finality`) and + 154 (the voter trees and
  the HEAD duty call). `reconcile_with_finality` (lines 1014–1034) is
  also byte-identical and writes no frame input.
- Statement (pinned):

> _00-outline-e6dcbcc1.md, lines 589–641:_
>
> **fj.frame.v4 — NEW — PROVED-paper (2026-09-29).**
> Authority: spec 4e85ff34, Trees at lines 480–507, controls at 747–792.
> Keep v3's unchanged store projection, cumulative-cache controls, and
> FJ-domain clauses with their existing proofs. Replace its Trees clauses
> as follows. **fj.frame.v3: WITHDRAWN for current use (2026-09-29)**
> under registry §0; successor fj.frame.v4. Not true as pinned: its
> deletion clause (bd942ca0 368–369) is refuted also under bd942ca0
> (01 §11.2 N2), and 4e85ff34 502–504 changes its genesis-walk clause.
> Its other clauses carry into v4. Retain its old pins.
> The clauses below are separate so that each has its own evidence kind.
>
> ```text
> ┌────┬─────────────────────────────────────────┬───────────────────────────────┐
> │ #  │ Clause (4e85ff34 lines)                 │ Evidence                      │
> ├────┼─────────────────────────────────────────┼───────────────────────────────┤
> │ 0  │ Σ.T is parent-closed and cumulative;    │ unchanged: keep v3 .leanHyp   │
> │    │ a new block enters only if it extends F │ evidence: Store,              │
> │    │ (480–483).                              │ storeInv_init,                │
> │    │                                         │ storeInv_on_block,            │
> │    │                                         │ on_block_TF_subset,           │
> │    │                                         │ update_finality_TF            │
> │ 1  │ An inactive stored block with state     │ .external fg.finalLock.v2;    │
> │    │ height above the accepted certificate's │ normalized threshold and      │
> │    │ entry height (0 for genesis) requires   │ evidence alternative, 01 §8.2 │
> │    │ a slashable conflict (494–497).         │                               │
> │ 2  │ No rule deletes a block of Σ.T          │ .lean process_cumulative,     │
> │    │ (497–502). Deletion can change HEAD and │ clock_cumulative (TF grows);  │
> │    │ S, also at a≤f. Pruning is a retention  │ .paper remark FR M1/N2,       │
> │    │ item.                                   │ 01 §11.1–§11.2                │
> │ 3a │ The confirmation walk starts at Σ.F in  │ .lean after the F-start sync; │
> │    │ act(Σ). Its result must pass strict     │ confirmationFrom, gateStep,   │
> │    │ majority, also at Σ.F (502–504).        │ fastSet and clock bridge      │
> │ 3b │ The FJ viability/band filter does not   │ .apData; separate HEAD/FG     │
> │    │ restrict that walk (505–506).           │ and SA call paths             │
> │ 4  │ act(Σ) is a view of Σ.T; only the SA    │ unchanged: .lean activeView,  │
> │    │ base reads act(Σ) (484–490).            │ activeView_subset; .apData    │
> │    │                                         │ for which module reads it     │
> └────┴─────────────────────────────────────────┴───────────────────────────────┘
> ```
>
> Clause 1 uses v2 because the external v1 states the carrier-h_F,
> fault-bounded DC theorem. For genesis the ancestry alternative is
> immediate. For non-genesis F, certificate provenance identifies the
> threshold with the carrier h_F. An inactive block conflicts with F,
> so the ancestry alternative fails and the evidence alternative follows.
> Clause 2 follows by event induction from `process_cumulative` and
> `clock_cumulative`; `st.fg.TF` is monotone. Its deletion remark is a
> counterexample fact, not an output-preservation claim. Clause 3a is
> proved on paper by 01 §6.5–§6.6 and spec 1280–1297. The Lean pin needs
> `SA.confirmationFrom`, `FGSA.gateStep`, `fastSet`, and
> `clock_eq_saClockFrom_gate` after the sync. It is not discharged by the
> current genesis-walk code. Clause 3b follows from the separate filter
> arguments; clause 4 keeps the existing active-view proof and read audit.

> _fgsa-protocol-c1ea1db0.tex, lines 489–515:_
>
> ```latex
> \paragraph{Trees.}  $\Sigma.\T$ is DC's admitted tree, with the same
> name and the same rules as in~\DC{7}.  It is parent-closed and
> cumulative: a new block enters it only if it extends~$F$, and no block
> leaves it~\cite{DC}.  A node never computes the state of, or unpacks, a
> block that does not extend its~$F$.  The \emph{active view} is
> \[
>  \act(\Sigma)=\{B\in\Sigma.\T: B\preceq\Sigma.F\ \text{or}\ \Sigma.F\preceq B\}.
> \]
> The SA base reads only the active view: the gate, release, resolution,
> saved-result tests, leases, and the confirmation walk~\cite[\S2]{FB}.
> Thus a node ignores every block that conflicts with its finality.  The
> FG functions read $\Sigma.\T$ as in~\DC{7}; their filters already
> require $\Sigma.F\preceq B$.  The caches $\Sigma.\hmax$ and the contest
> test read the cumulative $\Sigma.\T$, as the caches of~\DC{5} do.  A
> block of $\Sigma.\T$ outside the active view whose state height exceeds
> the height of the accepted finalization (the entry height of its
> certificate; $0$ for genesis) needs a slashable conflict
> (\textsf{fg.finalLock}).  As in~\cite{DC}, no rule deletes a block of
> $\Sigma.\T$.  A block outside the active view can still carry
> current-slot votes, support declarations, and rows that later reads
> use; deleting it can change the HEAD and~$S$, also at
> $a\leq f$~\cite[M1, N2]{FR}.  Storage pruning belongs to the retention
> item of Section~\ref{sec:open}.  The confirmation walk starts at $\Sigma.F$ in $\act(\Sigma)$.
> It returns a block only if that block passes the strict-majority
> test, including when the block is $\Sigma.F$.
> The FJ viability and band filter is a further filter for HEAD,
> proposal, and FG duties; it does not restrict the SA confirmation walk.
> ```

> _fgsa-protocol-c1ea1db0.tex, lines 944–969:_
>
> ```latex
> \Function{on\_block}{$\Sigma,B$}
>   \Comment{\DC{7}; $B$ passed the input check}
>   \If{$B.\slot>\Sigma.s$ or $B\in\Sigma.\T$ or
>       $B.\parent\notin\Sigma.\T$} \State \Return \EndIf
>   \If{$\Sigma.F\not\preceq B$} \State \Return \EndIf
>   \Comment{refuse before unpacking}
>   \If{$B.\parent.\slot\geq B.\slot$ or
>       the slot-$B.\slot$ proposer key does not sign $B$}
>     \State \Return
>   \EndIf
>   \If{some $a\in B.\attsf$ has $a.\round>\round(B.\slot)$}
>     \State \Return
>     \Comment{no row from the block's future}
>   \EndIf
>   \State $\Sigma.\sigma[B]\gets
>     \Call{state\_transition}{\Sigma.\sigma[B.\parent],B}$
>   \State add $B$ to $\Sigma.\T$; $\Sigma.\timestamp(B)\gets\Sigma.t$
>   \ForAll{$\mathit{vote}\in B.\votesf$}
>     \State \Call{on\_goldfish\_vote}{$\Sigma,\mathit{vote}$}
>   \EndFor
>   \State \Call{update\_finality}{$\Sigma,\Sigma.\sigma[B]$}
>   \ForAll{$a\in B.\attsf$}
>     \State \Call{on\_attestation}{$\Sigma,a$}
>     \Comment{after the finality update, as in DC}
>   \EndFor
> \EndFunction
> ```

> _fgsa-protocol-c1ea1db0.tex, lines 1122–1128:_
>
> ```latex
> \Function{fg\_contest}{$\Sigma$}
>   \Comment{new (a): \FJ{2}, on the live caches (\LDP{1})}
>   \State \Return $\Sigma.\hmax=\Sigma.h_j+1$ \textbf{and} some
>     $W\in\Sigma.\T$ has $\Sigma.\sigma[W].h=\Sigma.\hmax$ and
>     $\Sigma.J\not\preceq W$
>   \Comment{full store, never a view}
> \EndFunction
> ```

> _fgsa-protocol-c1ea1db0.tex, lines 1130–1138:_
>
> ```latex
> \Function{band\_floor}{$\Sigma$}
>   \Comment{new (a): \FJ{2}}
>   \If{$\Call{fg\_contest}{\Sigma}$}
>     \State \Return $\Sigma.\hmax$
>     \Comment{band $\{H\}$}
>   \EndIf
>   \State \Return $\Sigma.\hmax-1$
>   \Comment{\cite{DC}: band $\{H-1,H\}$}
> \EndFunction
> ```

> _fgsa-protocol-c1ea1db0.tex, lines 1140–1146:_
>
> ```latex
> \Function{viable\_tree\_from}{$\Sigma,\mathit{blocks}$}
>   \Comment{\DC{7}, redefined (a): band floor; choice only}
>   \State $\lo\gets\Call{band\_floor}{\Sigma}$
>   \State \Return $\{B\in\mathit{blocks}:\Sigma.F\preceq B,\
>     \exists B'\in\mathit{blocks},\ B\preceq B',\
>     \Sigma.\sigma[B'].h\geq\lo\}$
> \EndFunction
> ```

> _fgsa-protocol-c1ea1db0.tex, lines 1148–1154:_
>
> ```latex
> \Function{viable\_tree}{$\Sigma$}
>   \Comment{\DC{7}; acceptance only}
>   \State \Return $\{B\in\Sigma.\T:\Sigma.F\preceq B,\
>     \exists B'\in\Sigma.\T,\ B\preceq B',\
>     \Sigma.\sigma[B'].h\geq\Sigma.\hmax-1\}$
>   \Comment{\cite{DC}'s band, also in a contest (\FJ{2})}
> \EndFunction
> ```

> _fgsa-protocol-c1ea1db0.tex, lines 1156–1163:_
>
> ```latex
> \Function{get\_fg\_root}{$\Sigma$}
>   \Comment{\DC{7}, redefined (a) by \FJ{2}}
>   \If{$\Sigma.\hmax=\Sigma.h_j+1$ \textbf{and not} $\Call{fg\_contest}{\Sigma}$}
>     \State \Return $\Sigma.J$
>   \EndIf
>   \State \Return $\Sigma.F$
>   \Comment{a contest roots at $F$}
> \EndFunction
> ```

> _fgsa-protocol-c1ea1db0.tex, lines 1165–1177:_
>
> ```latex
> \Function{get\_filtered\_block\_tree\_from}{$\Sigma,\mathit{blocks}$}
>   \Comment{\DC{7}, unchanged}
>   \State $\mathit{root}\gets\Call{get\_fg\_root}{\Sigma}$
>   \State \Return
>     $\{B\in\Call{viable\_tree\_from}{\Sigma,\mathit{blocks}}:
>       \mathit{root}\preceq B\}$
> \EndFunction
> \vspace{1pt}
> \Function{get\_filtered\_block\_tree}{$\Sigma$}
>   \Comment{\DC{7}; DC's tree $\Sigma.\T$}
>   \State \Return
>     $\Call{get\_filtered\_block\_tree\_from}{\Sigma,\Sigma.\T}$
> \EndFunction
> ```

> _fgsa-protocol-c1ea1db0.tex, lines 1226–1238:_
>
> ```latex
> \Function{live\_root}{$\Sigma$}
>   \Comment{\DC{7} \fname{get\_sg\_root}, redefined (b); \SAS{} \fname{live\_root}}
>   \State $\mathit{tree}\gets\Call{get\_filtered\_block\_tree}{\Sigma}$
>   \Comment{the full filtered tree, not a view}
>   \State $\mathit{targets}\gets\{B\in\mathit{tree}:\Sigma.\lease[B]\neq\bot\}$
>   \Comment{they lie on one chain}
>   \If{$\mathit{targets}=\emptyset$}
>     \State \Return $\Call{get\_fg\_root}{\Sigma}$
>     \Comment{no live lease in the tree}
>   \EndIf
>   \State \Return the deepest $B\in\mathit{targets}$
>   \Comment{the deepest live lease in place of grade~1}
> \EndFunction
> ```

> _fgsa-protocol-c1ea1db0.tex, lines 1240–1247:_
>
> ```latex
> \Function{get\_head\_in\_tree}{$\Sigma,\mathit{tree},
>   \mathit{votes},\mathit{support\_votes},k$}
>   \Comment{\DC{7}, adapted (b): live root}
>   \State $A\gets\Call{live\_root}{\Sigma}$
>   \Comment{in place of \fname{get\_sg\_root}}
>   \State \Return $\Call{goldfish\_fork\_choice}{\Sigma,A,
>     \mathit{tree},\mathit{votes},\mathit{support\_votes},k}$
> \EndFunction
> ```

> _fgsa-protocol-c1ea1db0.tex, lines 1361–1376:_
>
> ```latex
> \Function{voter\_processed\_block\_tree}{$\Sigma,s$}
>   \Comment{\DC{7}; DC's tree $\Sigma.\T$}
>   \State $\mathit{freeze}\gets t_{s-1}+3\Delta$
>   \State $\mathit{proposals}\gets\{P\in\Sigma.\T:P.\slot=s\}$
>   \State \Return $\{B\in\Sigma.\T:
>     \Sigma.\timestamp(B)<\mathit{freeze}\ \textbf{or}\
>     \exists P\in\mathit{proposals},\ B\preceq P\}$
> \EndFunction
> \vspace{1pt}
> \Function{voter\_filtered\_block\_tree}{$\Sigma,s$}
>   \Comment{\DC{7}, unchanged}
>   \State $\mathit{blocks}\gets
>     \Call{voter\_processed\_block\_tree}{\Sigma,s}$
>   \State \Return
>     $\Call{get\_filtered\_block\_tree\_from}{\Sigma,\mathit{blocks}}$
> \EndFunction
> ```

> _fgsa-protocol-c1ea1db0.tex, lines 1437–1439:_
>
> ```latex
>     \State $\mathit{tree}\gets\Call{voter\_filtered\_block\_tree}{\Sigma,s}$
>     \State $H\gets\Call{get\_head\_in\_tree}{\Sigma,\mathit{tree},
>       \mathit{votes},\mathit{support\_votes},s-1}$
> ```

> _fgsa-protocol-c1ea1db0.tex, lines 999–1012:_
>
> ```latex
> \Function{update\_finality}{$\Sigma,\sigma$}
>   \Comment{\DC{7}; SA reconciliation replaces grade clipping}
>   \State $\Sigma.\hmax\gets\max(\Sigma.\hmax,\sigma.h)$
>   \If{$\Sigma.F\preceq\sigma.J$ \textbf{and}
>       $(\sigma.h_j,\sigma.J.\rootf)>(\Sigma.h_j,\Sigma.J.\rootf)$}
>     \Comment{lex order}
>     \State $(\Sigma.J,\Sigma.h_j)\gets(\sigma.J,\sigma.h_j)$
>   \EndIf
>   \If{$\Sigma.F\prec\sigma.F$ \textbf{and} $\sigma.F\preceq\Sigma.J$
>       \textbf{and} $\sigma.F\in\Call{viable\_tree}{\Sigma}$}
>     \State $\Sigma.F\gets\sigma.F$
>     \State \Call{reconcile\_with\_finality}{$\Sigma$}
>   \EndIf
> \EndFunction
> ```

- Status: 2026-09-29 — PROVED (paper; blueprint 00 §3, 01 §4, §6.5–§6.6,
  §8.2, §11; spec `fgsa3`). Lean coverage per clause: the pin
  `fj.frame.v4` in `AvailableChainKitFG/Pins.lean`.
- Note: `fj.frame.v1` is the view form. `fj.frame.v3` is WITHDRAWN for
  current use; this entry is its successor.

### `fj.frame.v3` — FJ frame from the live store caches (ALFS, filtered base)

- Variant `fj`. Source: the ALFS spec with the filtered SA base, file
  `spec/archive/fgsa-protocol-bd942ca0.tex` (key `alfs4`), sha256
  `bd942ca0bce0b4251b969a503a8c8175db87494ab93bf028e3a2303b7683dda7`:
  the Trees paragraph, lines 352–371, `on_block` 792–817,
  `fg_contest` 970–976, `band_floor` 978–986,
  `viable_tree_from` 988–994, `viable_tree` (acceptance) 996–1002,
  `get_fg_root` 1004–1011, `get_filtered_block_tree_from` and
  `get_filtered_block_tree` 1013–1025, `live_root` 1074–1086,
  `get_head_in_tree` 1088–1095, `voter_processed_block_tree` and
  `voter_filtered_block_tree` 1207–1222, the HEAD duty call 1283–1285, and
  the cache update `update_finality` 847–860. Proof sources: ldp §1 (ALFS)
  and r161 §2 (file `filtered-base.md`, archived as
  `tsc/archive/filtered-base-fd8e07fe.md`, sha256
  `fd8e07fe667afae28dee2bc9a54d6c7fc46b49f9bb268865f98818decc308354`).
- Lean plan: DC-fj module (user 2026-09-28). Lean names (f1's plan), as
  for `fj.frame.v2`: `storeControls`, `fjControls`, `filteredFrom`,
  `storeControls_eq_fjControls` (under `StoreInv` and `ViewRootInj`;
  `ViewRootInj` is discharged by `viewRootInj_all`, I9, 2026-09-29);
  `fjFrame = filteredFrom (fjControls V) V` is the special case.
- Hypotheses: `ViewRootInj` (§0.4), for the lex order of `update_finality`
  (lines 850–853); discharged by `viewRootInj_all` (I9, 2026-09-29).
- Summary (registry): controls from the live store caches (F, J, h_j,
  hmax; the contest from the full cumulative Σ.T, never a view); the
  domain filter applied to any block set; the HEAD walks the frozen voter
  tree from `live_root` (the deepest live lease in the full filtered
  tree, else the FG root), which may lie outside the walked tree. Σ.T is
  DC's cumulative admitted tree: a new block enters it only if `F ⪯ B`,
  before the handler unpacks it, and no block leaves it.
- Change against `fj.frame.v2` (registry, 2026-09-28): the pinned text
  names Σ.T in place of Σ.T_F, and `update_finality` calls
  `reconcile_with_finality` after an F advance. The frame controls do
  not change:
  1. Σ.T here and Σ.T_F of spec 1c6952b6 are the same set, as a function
     of the received blocks. Both admit B only if `F ⪯ B` at the handler
     call, with the parent admitted, and both are cumulative. In
     1c6952b6 the F test came after the raw insertion and the carried
     votes; those steps do not call `update_finality` (spec 1c6952b6,
     line 790 is its only call), so F at the test is the same. A parent
     outside Σ.T_F conflicts with an earlier F, so its child fails
     `F ⪯ B` (r158 lines 211–213).
  2. `reconcile_with_finality` (lines 862–882) writes only SA fields
     (leases, fastWrite, saved results, S). It does not write F, J, h_j,
     hmax or Σ.T, which are the frame inputs.
  3. The SA base reads the active view act(Σ) (Trees paragraph); the
     frame functions read Σ.T. The acceptance band of `viable_tree` is
     still `hmax−1`, also in a contest (lines 1000–1001).
- Statement (pinned):

> _fgsa-protocol-bd942ca0.tex, lines 352–371:_
>
> ```latex
> \paragraph{Trees.}  $\Sigma.\T$ is DC's admitted tree, with the same
> name and the same rules as in~\DC{7}.  It is parent-closed and
> cumulative: a new block enters it only if it extends~$F$, and no block
> leaves it~\cite{DC}.  A node never computes the state of, or unpacks, a
> block that does not extend its~$F$.  The \emph{active view} is
> \[
>  \act(\Sigma)=\{B\in\Sigma.\T: B\preceq\Sigma.F\ \text{or}\ \Sigma.F\preceq B\}.
> \]
> The SA base reads only the active view: the gate, release, resolution,
> saved-result tests, leases, and the confirmation walk~\cite[\S2]{FB}.
> Thus a node ignores every block that conflicts with its finality.  The
> FG functions read $\Sigma.\T$ as in~\DC{7}; their filters already
> require $\Sigma.F\preceq B$.  The caches $\Sigma.\hmax$ and the contest
> test read the cumulative $\Sigma.\T$, as the caches of~\DC{5} do.  A
> block of $\Sigma.\T$ outside the active view with height above
> $\Sigma.h_F$ needs a slashable conflict (\textsf{fg.finalLock}).  A
> node can delete blocks outside the active view; with $a\leq f$ this
> changes no output.  The confirmation walk starts at genesis.  The FJ
> viability and band filter is a further filter for HEAD, proposal, and
> FG duties; it does not restrict the SA confirmation walk.
> ```

> _fgsa-protocol-bd942ca0.tex, lines 792–817:_
>
> ```latex
> \Function{on\_block}{$\Sigma,B$}
>   \Comment{\DC{7}; $B$ passed the input check}
>   \If{$B.\slot>\Sigma.s$ or $B\in\Sigma.\T$ or
>       $B.\parent\notin\Sigma.\T$} \State \Return \EndIf
>   \If{$\Sigma.F\not\preceq B$} \State \Return \EndIf
>   \Comment{refuse before unpacking}
>   \If{$B.\parent.\slot\geq B.\slot$ or
>       the slot-$B.\slot$ proposer key does not sign $B$}
>     \State \Return
>   \EndIf
>   \If{some $a\in B.\attsf$ has $a.\round>\round(B.\slot)$}
>     \State \Return
>     \Comment{no row from the block's future}
>   \EndIf
>   \State $\Sigma.\sigma[B]\gets
>     \Call{state\_transition}{\Sigma.\sigma[B.\parent],B}$
>   \State add $B$ to $\Sigma.\T$; $\Sigma.\timestamp(B)\gets\Sigma.t$
>   \ForAll{$\mathit{vote}\in B.\votesf$}
>     \State \Call{on\_goldfish\_vote}{$\Sigma,\mathit{vote}$}
>   \EndFor
>   \State \Call{update\_finality}{$\Sigma,\Sigma.\sigma[B]$}
>   \ForAll{$a\in B.\attsf$}
>     \State \Call{on\_attestation}{$\Sigma,a$}
>     \Comment{after the finality update, as in DC}
>   \EndFor
> \EndFunction
> ```

> _fgsa-protocol-bd942ca0.tex, lines 970–976:_
>
> ```latex
> \Function{fg\_contest}{$\Sigma$}
>   \Comment{new (a): \FJ{2}, on the live caches (\LDP{1})}
>   \State \Return $\Sigma.\hmax=\Sigma.h_j+1$ \textbf{and} some
>     $W\in\Sigma.\T$ has $\Sigma.\sigma[W].h=\Sigma.\hmax$ and
>     $\Sigma.J\not\preceq W$
>   \Comment{full store, never a view}
> \EndFunction
> ```

> _fgsa-protocol-bd942ca0.tex, lines 978–986:_
>
> ```latex
> \Function{band\_floor}{$\Sigma$}
>   \Comment{new (a): \FJ{2}}
>   \If{$\Call{fg\_contest}{\Sigma}$}
>     \State \Return $\Sigma.\hmax$
>     \Comment{band $\{H\}$}
>   \EndIf
>   \State \Return $\Sigma.\hmax-1$
>   \Comment{\cite{DC}: band $\{H-1,H\}$}
> \EndFunction
> ```

> _fgsa-protocol-bd942ca0.tex, lines 988–994:_
>
> ```latex
> \Function{viable\_tree\_from}{$\Sigma,\mathit{blocks}$}
>   \Comment{\DC{7}, redefined (a): band floor; choice only}
>   \State $\lo\gets\Call{band\_floor}{\Sigma}$
>   \State \Return $\{B\in\mathit{blocks}:\Sigma.F\preceq B,\
>     \exists B'\in\mathit{blocks},\ B\preceq B',\
>     \Sigma.\sigma[B'].h\geq\lo\}$
> \EndFunction
> ```

> _fgsa-protocol-bd942ca0.tex, lines 996–1002:_
>
> ```latex
> \Function{viable\_tree}{$\Sigma$}
>   \Comment{\DC{7}; acceptance only}
>   \State \Return $\{B\in\Sigma.\T:\Sigma.F\preceq B,\
>     \exists B'\in\Sigma.\T,\ B\preceq B',\
>     \Sigma.\sigma[B'].h\geq\Sigma.\hmax-1\}$
>   \Comment{\cite{DC}'s band, also in a contest (\FJ{2})}
> \EndFunction
> ```

> _fgsa-protocol-bd942ca0.tex, lines 1004–1011:_
>
> ```latex
> \Function{get\_fg\_root}{$\Sigma$}
>   \Comment{\DC{7}, redefined (a) by \FJ{2}}
>   \If{$\Sigma.\hmax=\Sigma.h_j+1$ \textbf{and not} $\Call{fg\_contest}{\Sigma}$}
>     \State \Return $\Sigma.J$
>   \EndIf
>   \State \Return $\Sigma.F$
>   \Comment{a contest roots at $F$}
> \EndFunction
> ```

> _fgsa-protocol-bd942ca0.tex, lines 1013–1025:_
>
> ```latex
> \Function{get\_filtered\_block\_tree\_from}{$\Sigma,\mathit{blocks}$}
>   \Comment{\DC{7}, unchanged}
>   \State $\mathit{root}\gets\Call{get\_fg\_root}{\Sigma}$
>   \State \Return
>     $\{B\in\Call{viable\_tree\_from}{\Sigma,\mathit{blocks}}:
>       \mathit{root}\preceq B\}$
> \EndFunction
> \vspace{1pt}
> \Function{get\_filtered\_block\_tree}{$\Sigma$}
>   \Comment{\DC{7}; DC's tree $\Sigma.\T$}
>   \State \Return
>     $\Call{get\_filtered\_block\_tree\_from}{\Sigma,\Sigma.\T}$
> \EndFunction
> ```

> _fgsa-protocol-bd942ca0.tex, lines 1074–1086:_
>
> ```latex
> \Function{live\_root}{$\Sigma$}
>   \Comment{\DC{7} \fname{get\_sg\_root}, redefined (b); \SAS{} \fname{live\_root}}
>   \State $\mathit{tree}\gets\Call{get\_filtered\_block\_tree}{\Sigma}$
>   \Comment{the full filtered tree, not a view}
>   \State $\mathit{targets}\gets\{B\in\mathit{tree}:\Sigma.\lease[B]\neq\bot\}$
>   \Comment{they lie on one chain}
>   \If{$\mathit{targets}=\emptyset$}
>     \State \Return $\Call{get\_fg\_root}{\Sigma}$
>     \Comment{no live lease in the tree}
>   \EndIf
>   \State \Return the deepest $B\in\mathit{targets}$
>   \Comment{the deepest live lease in place of grade~1}
> \EndFunction
> ```

> _fgsa-protocol-bd942ca0.tex, lines 1088–1095:_
>
> ```latex
> \Function{get\_head\_in\_tree}{$\Sigma,\mathit{tree},
>   \mathit{votes},\mathit{support\_votes},k$}
>   \Comment{\DC{7}, adapted (b): live root}
>   \State $A\gets\Call{live\_root}{\Sigma}$
>   \Comment{in place of \fname{get\_sg\_root}}
>   \State \Return $\Call{goldfish\_fork\_choice}{\Sigma,A,
>     \mathit{tree},\mathit{votes},\mathit{support\_votes},k}$
> \EndFunction
> ```

> _fgsa-protocol-bd942ca0.tex, lines 1207–1222:_
>
> ```latex
> \Function{voter\_processed\_block\_tree}{$\Sigma,s$}
>   \Comment{\DC{7}; DC's tree $\Sigma.\T$}
>   \State $\mathit{freeze}\gets t_{s-1}+3\Delta$
>   \State $\mathit{proposals}\gets\{P\in\Sigma.\T:P.\slot=s\}$
>   \State \Return $\{B\in\Sigma.\T:
>     \Sigma.\timestamp(B)<\mathit{freeze}\ \textbf{or}\
>     \exists P\in\mathit{proposals},\ B\preceq P\}$
> \EndFunction
> \vspace{1pt}
> \Function{voter\_filtered\_block\_tree}{$\Sigma,s$}
>   \Comment{\DC{7}, unchanged}
>   \State $\mathit{blocks}\gets
>     \Call{voter\_processed\_block\_tree}{\Sigma,s}$
>   \State \Return
>     $\Call{get\_filtered\_block\_tree\_from}{\Sigma,\mathit{blocks}}$
> \EndFunction
> ```

> _fgsa-protocol-bd942ca0.tex, lines 1283–1285:_
>
> ```latex
>     \State $\mathit{tree}\gets\Call{voter\_filtered\_block\_tree}{\Sigma,s}$
>     \State $H\gets\Call{get\_head\_in\_tree}{\Sigma,\mathit{tree},
>       \mathit{votes},\mathit{support\_votes},s-1}$
> ```

> _fgsa-protocol-bd942ca0.tex, lines 847–860:_
>
> ```latex
> \Function{update\_finality}{$\Sigma,\sigma$}
>   \Comment{\DC{7}; SA reconciliation replaces grade clipping}
>   \State $\Sigma.\hmax\gets\max(\Sigma.\hmax,\sigma.h)$
>   \If{$\Sigma.F\preceq\sigma.J$ \textbf{and}
>       $(\sigma.h_j,\sigma.J.\rootf)>(\Sigma.h_j,\Sigma.J.\rootf)$}
>     \Comment{lex order}
>     \State $(\Sigma.J,\Sigma.h_j)\gets(\sigma.J,\sigma.h_j)$
>   \EndIf
>   \If{$\Sigma.F\prec\sigma.F$ \textbf{and} $\sigma.F\preceq\Sigma.J$
>       \textbf{and} $\sigma.F\in\Call{viable\_tree}{\Sigma}$}
>     \State $\Sigma.F\gets\sigma.F$
>     \State \Call{reconcile\_with\_finality}{$\Sigma$}
>   \EndIf
> \EndFunction
> ```

- Status: 2026-09-28 — def (spec text). r161 §6.3 (lines 587–613) finds
  that the frame and cache items (L2, L6) HOLD with the filtered base.
- Note (2026-09-28): the reading of r161 §2 is DC's. r161 §2 says
  "Remove conflicting stored branches on an F advance. Physical deletion
  can be deferred, but no base query may read those branches" (r161
  lines 133–135). The spec (the authority) keeps Σ.T cumulative, as DC
  does (DC never deletes an admitted block; hmax only grows), and the
  active view act(Σ) is the removal for the SA base; a node can delete
  blocks outside the active view, and with `a ≤ f` this changes no output
  (pinned Trees paragraph, spec lines 352–371). Source of the decision:
  `research/async-resilient-committees/tip-stability/log.md`, lines 934
  and 936–937 (team-lead, 2026-09-28; an append-only log, not archived).
  The spec intermediate a3e12c57 (r163), which deleted blocks from Σ.T,
  is not this reading.
- Note: `fj.frame.v1` is the view form and is not superseded.
  `fj.frame.v2` is SUPERSEDED by this entry.
- Status: 2026-09-29 — WITHDRAWN for current use (§0); successor
  `fj.frame.v4` (spec `fgsa3`). Not true as pinned: the deletion clause
  (lines 368–369) is refuted also under bd942ca0 (blueprint 01 §11.2 N2),
  and `fgsa3` lines 511–513 change the genesis-walk clause (lines
  369–371). The other clauses carry into v4. The pinned text and the
  source pins stay as history; `AvailableChainKitFG/Pins.lean` keeps the
  pin as a historical pin.


### `fj.frameFeasible.v1` — the FJ domain reaches lo and is not empty

- Variant `fj`. Source r148 §2, lines 223–230 (the "finalized-crossing
  law" is line 226). File `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`.
- Lean plan: DC-fj module (user 2026-09-28). Lean names on
  `lean/available-chain` main `64651ad`
  (`AvailableChainKitFG/Correspondence.lean`, verified in the source):
  `filteredFrom_reachesLo` = part (1) (lines 531–540), `fjFrame_D_nonempty` = part (2) (line 602),
  `fjFrame_Z_mem_D` = part (3) (line 629), `filteredFrom_viable_child` =
  part (4) (lines 556–577). The Lean forms of parts (1) and (4) are
  generalizations of the registry forms: they hold for any controls and
  any block set (part (4): any ancestor-closed block set). The registry
  form is the special case `fjFrame = filteredFrom (fjControls V) V`.
  The plan names `fjFrame_D_reachesLo` and `fjFrame_viable_child` (plan
  commit `befb5d5`) are not Lean declarations
  (`AvailableChainKitFG/Pins.lean`, lines 189–190).
- Kind: FG frame lemma (audit W02: an `ap.*` id does not carry a pure
  frame lemma). It is the frame side of the feasibility of
  `ap.headReachesLo.v1`.
- Hypotheses: `fj.frame.v1`; for part (2) also (a) the view holds a block
  K whose chain finalizes F (the accepting carrier of the F basis), with
  `h(K) > h_F` (DC `ChainOrder.finalized_below_height`, `Chain.lean:442`),
  and (b) every W ∈ V with `h(W) > h_F` extends F (the pure form of
  `fg.finalLock.v1`, without slashable weight); for part (2) in the
  uncontested phase and for part (3), `ViewRootInj` (§0.4), named 2026-09-28 (§0
  rule (b): the selected pair is the lex-max by root), discharged by
  `viewRootInj_all` (I9, 2026-09-29); V is
  ancestor-closed and not empty.
- Statement (registry, 2026-09-28): let (F, H, j, J, Z, lo, D) be the FJ
  frame of a view V.
  1. Pure: if D ≠ ∅, then some W ∈ D has state height ≥ lo. Proof: take
     B ∈ D and its witness W ∈ V, with `B ⪯ W` and `h(W) ≥ lo`. Then
     `F ⪯ B ⪯ W` and `Z ⪯ B ⪯ W`, and W is its own witness, so W ∈ D.
  2. Under (a) and (b), D ≠ ∅. By (a), `H ≥ h(K) > h_F`. Gap or contested
     phase (Z = F, lo ≤ H): a frontier block W with `h(W) = H` extends F by
     (b), and it is its own witness, so W ∈ D. Uncontested phase (Z = J,
     lo = H−1): every frontier block W extends J, and `F ⪯ J` by the
     selection rule, so W ∈ D.
  3. Under (a) and (b), Z ∈ D (added 2026-09-28). Uncontested phase:
     Z = J, `F ⪯ J`, and a frontier block W extends J with
     `h(W) = H ≥ lo`, so J has a witness. Gap or contested phase: Z = F,
     and a frontier block W extends F by (a) and (b), with `h(W) = H ≥ lo`.
     This is the Z-instance of part (2).
  4. Pure: below lo every viable block of D has a child in D toward its
     witness (added 2026-09-28). Let X ∈ D with `h(X) < lo` and witness W,
     `X ⪯ W`, `h(W) ≥ lo`. Then X ≠ W. The child Y of X on the path to W is
     in V (ancestor closure), and `F ⪯ Y`, `Z ⪯ Y`, `Y ⪯ W`, so Y ∈ D.
     Pinned line 229: "Below lo every viable node has a viable child".
- Note (2026-09-28, ALFS): parts (1) and (4) hold for any block set;
  part (4) needs an ancestor-closed set, and the frozen voter tree
  (`voter_processed_block_tree`, `fj.frame.v2`) is ancestor-closed. Parts
  (2) and (3) are stated on `fjFrame` and Σ.T_F. Their frozen-tree forms
  are ALFS L5 and L6 (ldp lines 316–360), which are comp/AP facts: in L6
  a contest can leave the frozen domain empty, and then the HEAD returns
  its anchor.
- Statement (pinned):

> _fj-redteam.md, lines 223–230:_
>
> Under a≤f, this distinction does not create an empty choice domain.
> Every frontier block has height above the height of accepted F: a
> finalization at y has a justification carrier at height at least y+1.
> The finalized-crossing law puts every such frontier block above F.
> In the J case, the carrier witnesses J's viability. In the contested
> case, a frontier witness makes F viable at lo=H. Below lo every viable
> node has a viable child, so the walk reaches lo. Clean and P1 runs with
> a<h use the source argument in §5 instead of this BFT crossing law.

- Status: 2026-09-28 — PROVED (r148 lines 223–228; registry argument).
- Note: the last two sentences of the pinned lines (the walk below lo)
  are AP data: `ap.headReachesLo.v1`. Hypothesis (b) holds in a run under
  `a≤f` by `fg.finalLock.v1`. Clean and P1 runs with `a<h` need another
  argument (r148 §5).
- DC Lean source of hypothesis (a): file
  `DecoupledConsensusProofs/Protocol/ChainState/Chain.lean`, line 442,
  at vc commit `b97b902`, sha256
  `a4dc5f00c8741615c229b636742aa14de43f4ef51b0aa81aa75f747102a5a25d`.
- Note (2026-09-28; §0 rule (a)): `fj.frame.v2` is SUPERSEDED by
  `fj.frame.v3` (spec bd942ca0: Σ.T in place of Σ.T_F, the same set;
  `update_finality` also calls `reconcile_with_finality`, which writes no
  frame input). A citation of `fj.frame.v2` here reads as `fj.frame.v3`.
- Note (2026-09-29; current use): `fj.frame.v3` is WITHDRAWN for current
  use; its successor is `fj.frame.v4` (spec `fgsa3`). The frame controls
  do not change; the Trees clauses change (no deletion from Σ.T, the SA
  walk starts at Σ.F). The note above is history. A current citation of
  `fj.frame.v2` or `fj.frame.v3` here reads as `fj.frame.v4`.
- Note (2026-09-29; current use): `fg.finalLock.v1` is WITHDRAWN for current
  use. The citations above are history. A current use of this entry
  reads them as §9, "Current reading of withdrawn ids".

- Note (2026-09-29; Lean pin): the pin `fj.frameFeasible.v1` of
  `AvailableChainKitFG/Pins.lean` cites `ap.headReachesLo.v6` (the FG-SA
  form: frame `fj.frame.v4`, spec `fgsa3`) for its frozen-tree clauses, with
  `fgsa3` line numbers. The ALFS notes above are history.


### `fj.crossingNoFinal.v1` — r148 F2: a conflicting crossing of j proves that J cannot finalize

- Variant `fj`. Source r148 §3 F2, lines 234–258. File `fj-redteam.md`,
  sha256 `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`.
- Lean plan: DC-fj module (user 2026-09-28).
- Hypotheses: `a≤f`, so `2q−n > a`; honest identities follow E1 and E2;
  the uniform timeout maturity of the DC transition.
- Statement (pinned):

> _fj-redteam.md, lines 234–258:_
>
> F2 — PROVED. Suppose J is justified at j and a valid block W has
> h(W)>j with J not a prefix of W. On W's path, take the first crossing
> of j. It consumes q progress identities naming an entry T≠J at j.
> A target QC for T would conflict with J's target QC. Their intersection
> has at least 2q−n>a identities, so an honest identity would violate E2.
> Thus this crossing cannot be an all-target crossing. It needs the
> timeout branch, at the uniform maturity slot.
>
> More precisely, intersect J's target QC with the progress QC for T.
> At least one honest member of the intersection has already targeted J.
> Its row for T cannot be a target; it is a timeout. “Through timeouts”
> therefore means a mixed or all-timeout progress QC with at least one
> honest timeout. It does not mean that every progress row is a timeout.
>
> Now suppose a finality QC for J exists, before or after that crossing.
> Intersect it with the progress QC for T. Again an honest member must
> occur. If its progress row is a target for T, E1 forbids its finality
> pair for J. If it is a timeout, E1 also forbids that pair, regardless
> of the entry named by the timeout. This argument is independent of the
> order of emission. Therefore J has not finalized and cannot finalize
> in any continuation that retains the fault bound and honest client.
>
> This is the argument in [finalized_preceq_of_height_lt][crossing],
> with its direction reversed. It applies to a privately finalized J,
> and to a crossing held only by the adversary.

- Status: 2026-09-28 — PROVED (r148 F2).
- Note: this is the contrapositive form of `fg.finalLock.v1` for one
  justified J: a block above j that does not extend J excludes a
  finalization of J. It is registered for `fj` because FJ uses it in the
  contested phase (`fj.twoChanges.core.v1`); the argument uses only the DC
  certificate rules, so it also holds for `nj`.
- Note (2026-09-29; current use): `fg.finalLock.v1`, `fj.twoChanges.core.v1` are WITHDRAWN for current
  use. The citations above are history. A current use of this entry
  reads them as §9, "Current reading of withdrawn ids".


### `fj.descent.v1` — descent lemma under FJ

- Variant `fj`. Source r144o §3.1 and §5.3, lines 162–182 and 601–610. File
  `fgsa-no-nj-opus.md`, sha256
  `7df2a540134deddede78ea711754bb322911fced62271868f8b5034164db9f4e`. r148
  §6 (lines 479–527) proves the same descent per actual duty view, with R1
  split cases.
- Hypotheses: `env.r148`; old row, M and first abandonment as defined in
  r144o §1 (lines 108–121).
- Statement (pinned):

> _fgsa-no-nj-opus.md, lines 108–121:_
>
> ```text
> synchronous label s:  v_s ≥ GST (its HEADs reach every reader before e_s).
> old row:              an honest height pair whose source label has v_s < GST.
> M:                    the highest height of an old row (M=1 if none).
> post-GST source:      a fresh fast source C at a synchronous label s.
> abandonment of C:     an honest HEAD at a label s' > s that does not extend C.
> first abandonment:    the earliest abandonment of that C.
> flip:                 a duty frame whose root or band excludes the branch
>                       that the previous honest HEADs extended.
> frontier, level:      H_V of the duty view.
> ```
>
> M is the Opus r143 definition. It is at most DC's archival frontier at
> `r_GST+2`. Every honest row at a height above M has a synchronous label.

> _fgsa-no-nj-opus.md, lines 162–182:_
>
> **Lemma D.** Let (C, v) be the first abandonment of a post-GST source C
> with label s. Then the HEAD view V at v holds a QC with an honest row ρ.
> The row ρ names an entry that conflicts with C, at a height x. Exactly one
> of these holds:
>
> 1. ρ is old, so `x ≤ M`;
> 2. ρ has a post-GST source C′ with label `s′<s`, and the first
>    abandonment of C′ is at or before `v_s < v`.
>
> The height x depends on the cause:
>
> ```text
> ┌──────────────────────────┬──────────────────────────────┬──────────────┐
> │ Cause at v               │ Condition                    │ x            │
> ├──────────────────────────┼──────────────────────────────┼──────────────┤
> │ F root or F floor        │ F_V conflicts with C         │ ≥ σ[C].h     │
> │ band {H−1,H}             │ C's branch in V is below H−1 │ ≥ σ[C].h+1   │
> │ DC J root (Z=J at H=j+1) │ J_V conflicts with C         │ ≥ σ[C].h−1   │
> │ lease or score           │ —                            │ not possible │
> └──────────────────────────┴──────────────────────────────┴──────────────┘
> ```

> _fgsa-no-nj-opus.md, lines 601–610:_
>
> **Lemma D under FJ — PROVED.** Two cases change:
>
> - Uncontested J root: every frontier block of V extends J_V, and C ∈ V
>   conflicts with J_V, so `σ[C].h ≤ H_V−1 = j_V = x`.
> - Strict band: C's branch in V has no block at H_V, so `σ[C].h ≤ H_V−1`.
>   Both QC entries E at `H_V−1` have a frontier descendant. If
>   `σ[C].h=H_V−1`, at least one E differs from C's entry at `H_V−1`, and
>   two different entries at one height conflict. If `σ[C].h<H_V−1`, then
>   `C ⋠ E` (else C has a witness at H_V) and `E ⋠ C` (height). So a row
>   on a conflicting entry exists at `x=H_V−1 ≥ σ[C].h`.

- Status: 2026-09-28 — PROVED (r144o N3 and "Lemma D under FJ — PROVED";
  r148 F9 proof).
- Status: 2026-09-29 — WITHDRAWN for current use under `fgsa3` (§0);
  successor `fj.descent.v2`. Its conclusion reads the controlling QC in
  the duty view; current controls read the cumulative store and the live
  caches. The pinned text stays as history.


### `fj.descent.v2` — descent at the first bad event, cumulative controls

- Variant `fj`. Source: blueprint 21, registry restatement after H.13,
  file `blueprint/archive/21-healing-9b7f5af8.md` (key `bp21`), lines
  2585–2631, sha256
  `9b7f5af8d013a473f9c5361f72377df63f79728599e02d0b9414cd58789c3ac9`.
  Proof: 21 H.13 (four exclusion cases, joint first-event argument).
- Lean pin: not yet pinned (2026-09-29): no clause table yet.
- Hypotheses: H.13's reachable-run premises, IF.1–IF.6, and μ. μ is a
  function of the run and GST (μ(run,GST), 21 H.11: the maximum of 1 and
  the heights of honest rows with a source vote before GST). It is not a
  field of an existential witness.
- Statement (pinned):

> _21-healing-9b7f5af8.md, lines 2585–2631:_
>
> ### Registry restatement — fj.descent.v2 — PROVED-paper
>
> _2026-09-29. fj.descent.v1 is WITHDRAWN for use under 4e85ff34.
> Its conclusion puts the controlling QC in the failing HEAD view, but
> live-cache controls can use evidence outside that frozen view. Thus its
> pinned descent step is unusable here. Keep its old pins as history;
> use fj.descent.v2 with cumulative controls and the event-index measure._
>
> Use H.13's reachable-run premises, IF.1–IF.6, and μ as the maximum of
> 1 and the heights of honest rows with source vote before GST. An
> abandonment of source C of synchronous label s is an honest HEAD at
> label i≥s+1 that does not cover C. Choose the first event among a loss
> of a source above μ and the emission of two incompatible sources above μ.
> Controls F,J,H,Z,lo come from cumulative Σ.T and its live caches. They
> are not duty-view controls, and a controlling QC need not be frozen.
>
> For an alleged loss of C at height c>μ, a lease or score failure cannot
> be first while C is kept, by H.1–H.2 and same-label compatibility. The
> remaining cause analysis gives a conflicting honest source C′ at
> height c′≥c, whose row precedes the failing duty, in the following cases:
> conflicting F; conflicting uncontested top J; ordinary-band exclusion;
> or contested exclusion with c=H−1. For ordinary-band exclusion c′=H−1>c;
> for top J and the equal-height contested case c′=H−1≥c.
>
> 1. If C′ has a pre-GST source vote, `c′≤μ`, which contradicts c′≥c>μ.
> 2. If its synchronous source label `s′>s`, its honest supporter voted
>    at `v_(s′)≥q_s`. That vote is an earlier abandonment of C, before
>    the row of C′ and before this failing duty. v1 excluded this case
>    by its per-source first-abandonment definition; v2 needs it because
>    its measure is the global event index, not the source label.
> 3. If `s′<s`, C's honest supporter at `v_s≥q_(s′)` is an earlier
>    abandonment of C′. Equal labels are excluded by IF.6.
>
> For contested exclusion with `c<H−1`, do not infer a frozen height-H
> witness from a source body of height H−1. The two different entries
> at H−1 have incompatible honest sources above μ. Both rows precede
> the contest read, so their emissions give an earlier bad event. If a
> pair emission is the proposed first bad event, equal labels contradict
> IF.6; at different labels the later source's supporter already abandoned
> the earlier source before the pair emission. This closes that case too.
>
> **Proof.** These are the four exclusion cases and the joint first-event
> argument of H.13. Source-body timing is H.12; certificate provenance and
> crossing are IF.3. The earlier event in every case contradicts the choice
> of the first bad event. Hence no high synchronous source is lost and no
> incompatible pair above μ is emitted. The proof uses the source body
> when it needs a frozen witness; it never substitutes a late carrier.

- Status: 2026-09-29 — PROVED (paper; blueprint 21 H.13).

### `fj.canonical.v1` — F9: sources above M stay canonical

- Variant `fj`. Source r148 §6 F9, lines 479–486, 518–528 and 549–561. File
  `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`.
- Hypotheses: `env.r148` (recovery regime); M as in `env.r148`.
- Statement (pinned):

> _fj-redteam.md, lines 479–486:_
>
> F9 — PROVED under the recovery regime.
>
> Let C be a synchronous selected source at label s. Consider its first
> honest HEAD failure after that label. This includes a failure of its
> first transfer at q_s. Its complete path is in the failing view:
> at the first transfer, a surviving honest supporter relays it before
> z_s; at later transfers, the previous honest batch supplies it.
> Accepted F above C already protects C.

> _fj-redteam.md, lines 518–528:_
>
> The source C' of this row extends its conflicting entry and hence
> conflicts with C. If it is old, y≤M. If it is synchronous, its label
> s' must be earlier than s. Equality contradicts same-label genuine
> compatibility. A later label would have an honest supporter departing
> C before the proposed first failure. The supporter of C at v_s
> already witnesses a failure of C' after C's earlier source label s'.
>
> Repeat this step on C'. The labels strictly decrease, so the descent
> terminates at an old row. At each step the new source height is y,
> at least the previous source height. Therefore a lost C has h(C)≤M.
> No selected source above M can be lost.

> _fj-redteam.md, lines 549–561:_
>
> After each retained source transfers, the next all-honest batch covers
> it. Its gate has a genuine result above it and no conflicting live
> lease. Every S therefore covers that source by t_s+10Δ. As in the
> adjudication, retain all source bodies in the induction, not only one
> named entry. Two retained sources at the same state height have the
> same immutable entry. Their later target and timeout rows cannot name
> another entry.
>
> In fact, with nj=false all honest rows at a height y>M are targets.
> There is no old honest height row or old lock at y. An old lock would
> require an old target QC and hence an old honest row at y. Later
> honest sources at y have one entry; the client therefore adopts or
> repeats it, and never creates the first timeout there.

- Status: 2026-09-28 — PROVED (r148 F9). r144o N14 states the same reset
  result, PROVED.
- Note: retention starts at the transfer HEAD `q_s`, not at `v_s`
  (`env.r148`, lines 116–119). r144o N14 (line 615) says "from its label
  on"; r148 corrects this timing.

### `fj.inBandLock.v1` — F10: no lock stall for an in-band source

- Variant `fj`. Source r148 §7 F10, lines 577–597. File `fj-redteam.md`,
  sha256 `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`.
- Lean plan: DC-fj module (user 2026-09-28).
- Hypotheses (named 2026-09-28; §0 rule (b): the pinned text uses the
  lex order `(h_j, J.root)` and ties by root): `ViewRootInj` (§0.4);
  discharged by `viewRootInj_all` (I9, 2026-09-29).
- Statement (pinned):

> _fj-redteam.md, lines 577–597:_
>
> F10 — PROVED for an in-band selected source. Let C_fg have height m≥lo
> in its full action view. Suppose a lock on J'≠T_c at m suppresses its
> height row. Its finality pair required a justification carrier at
> height at least m+1. This carrier is retained in the full store.
> A same-action finality pair has the same property.
>
> Since m≤H and lo≥H−1, this gives H=m+1 and lo=m. A strict contest would
> give lo=m+1, a contradiction. The lock's J' is compatible with F;
> otherwise finalized crossing or source descent from F already excludes
> this case. Same-height justification uniqueness gives j=m and J=J'.
> The remaining FJ case is uncontested, with root J'. C_fg at height m
> must then have entry J'. This contradicts the mismatched lock.
>
> In a contest, an actual head reaches H. A lock at H would require an
> already known carrier at H+1, contrary to the fixed frontier. Locks at
> H−1 do not block rows at H. Old different targets cause timeouts there,
> which still contribute progress.
>
> This does not say every action has a source, or that every selected
> prefix of a raw result is in band. The no-source and below-band cases
> are handled by the producer in §9. F10 alone is not a liveness theorem.

- Status: 2026-09-28 — PROVED (r148 F10; r144o N15).
- Note (2026-09-28; §0 rule (b)): "finalized crossing" in the pinned text
  is `fg.finalLock.v1`, and "same-height justification uniqueness" is
  `fg.uniqueJust.v1`.
- Note (2026-09-28; §0 rule (b)): the step "In a contest, an actual head
  reaches H" is `ap.headReachesLo.v1` (AP data after the user design
  correction of 2026-09-28). Hypotheses add `ap.headReachesLo.v1`.
- Note (2026-09-28): under ALFS: `ap.headReachesLo.v2`, with the charged
  fallback slots.
- Note (2026-09-28): under ALFS (spec c7c41a43): `ap.headReachesLo.v3`
  (supersedes v2), with θ = 4Δ per effective event in place of the
  charged fallback slots.
- Note (2026-09-28): under ALFS (spec 1c6952b6): `ap.headReachesLo.v4`
  (supersedes v3; DC's receipt premise in place of accepted-object
  relay).
- Note (2026-09-28): under ALFS (spec bd942ca0): `ap.headReachesLo.v5`
  (supersedes v4; filtered base, admission-or-coverage).
- Note (2026-09-28): Lean: hFJ′ (F ⪯ J′) is a hypothesis now (partial
  coverage). A later helper lemma derives it in pure form from
  `fg.finalLock.v1` and the F carrier in the view; it will be pinned to
  this entry.
- Note (2026-09-28): the clause "A lock at H would require an already
  known carrier at H+1" will be the Lean lemma
  `finalityPair_carrier_above`: the emitted finality pair is the head
  state's `(h_j, J)`, and `justified_below_height` gives
  `h(head) ≥ h_j+1`. Only the retention of that carrier in the full store
  is a run fact.
- Note: the old-band variant (FJ root test, band `{H−1,H}`) stalls (r148
  F11, REFUTED by the exact N12 execution, lines 599–711).
- Note (2026-09-29; current use): `fg.finalLock.v1`, `ap.headReachesLo.v5` are WITHDRAWN for current
  use. The citations above are history. A current use of this entry
  reads them as §9, "Current reading of withdrawn ids".

- Note (2026-09-29; Lean pin): the pin `fj.inBandLock.v1` of
  `AvailableChainKitFG/Pins.lean` cites `ap.headReachesLo.v6` (the FG-SA
  form: frame `fj.frame.v4`, spec `fgsa3`) for its frozen-tree clauses, with
  `fgsa3` line numbers. The ALFS notes above are history.


### `fj.twoChanges.v1` — F12: at most two effective changes per frontier

- Variant `fj`. Source r148 §8 F12, lines 762–789. File `fj-redteam.md`,
  sha256 `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`.
- Statement (pinned):

> _fj-redteam.md, lines 762–789:_
>
> F12 — PROVED for effective changes after relay settling. Fix an honest
> archival frontier m during a no-rise interval. After one P margin,
> a maximizing witness is in every duty view. Under a≤f there is at
> most one justified entry at m−1. There are at most these phases:
>
> ```text
> gap: no top J
>     -> uncontested top J
>     -> contested top J
>
> or gap -> contested top J.
> ```
>
> The first top-J evidence and the first contest evidence can each
> interrupt an attempt once. Within P of each event, accepted-object
> relay and a later freeze put the relevant evidence in every view.
> Repeated copies do not start a new phase. Later frontier blocks only
> add witnesses once the phase is settled.
>
> A finalization below m−1 is below every band witness and cannot cause
> an independent exclusion. A finalization at m−1 is the same unique
> top J. It is impossible in the contested phase by F2; in the
> uncontested phase the root already enforces it. A finalization at m
> requires a carrier above m, which ends the no-rise interval.
>
> Hence k_eff≤2, with at most three complete attempts. This count is
> independent of SA's slow-window parameter k. It is not a strictly
> increasing potential on each full/HEAD call.

- Status: 2026-09-28 — PROVED (r148 F12; r144o N16).
- Note: the count is for effective changes after relay settling. For raw
  successive R1 duty frames it is false (r148 F13, REFUTED, lines 737–760).
- Note (r151): r151 confirms F13 as REFUTED (claim table line 24) and
  replays the receipt schedule (r151 §9, lines 801–805). The frame cycle
  occurs below the cap μ, so it does not refute `fj.theoremN.v1`:

> _fj-theorem-h.md, line 24:_
>
> ```text
> │ At most two changes of successive R1 duty frames          │ REFUTED │
> ```

- Status: 2026-09-28 — SUPERSEDED (split agreed with ethereum-f1). The
  settling sentences (lines 763–764 "After one P margin, a maximizing
  witness is in every duty view" and lines 775–777) are run facts:
  `comp.settle.v1`. The phase count is the pure core:
  `fj.twoChanges.core.v1`. Their conjunction is this statement.

### `fj.twoChanges.core.v1` — FJ phases at a fixed frontier (pure core)

- Variant `fj`. Source r148 §8 F12, lines 764–773 and 778–789. File
  `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`.
- Lean plan: DC-fj module (user 2026-09-28).
- Hypotheses: `fj.frame.v1`; `fg.uniqueJust.v1` (at most one justified
  entry at m−1); `fg.finalLock.v1`; `fj.crossingNoFinal.v1` (the "F2" of
  line 783, r148 numbering); `ViewRootInj` (§0.4), named 2026-09-28 (§0 rule (b):
  "the same unique top J" compares entries by root), discharged by
  `viewRootInj_all` (I9, 2026-09-29).
- Statement (registry): fix a frontier m in a no-rise interval. Let
  J_(m−1) be the justified entry at m−1, if one exists. For an honest duty
  d with `H_d = m`, let `E_J(d)` mean "V_d holds a carrier of J_(m−1)",
  and `E_C(d)` mean "V_d holds a block of height m that does not extend
  J_(m−1)". Then:
  1. The effective FJ frame `(H_d, lo_d, Ẑ_d)` is a function of the phase
     of d: gap (not `E_J(d)`): `(m, m−1, ◇)`; uncontested (`E_J(d)` and not
     `E_C(d)`): `(m, m−1, J_(m−1))`; contested (`E_J(d)` and `E_C(d)`):
     `(m, m, ◇)`.
  2. Each evidence bit is false at every duty before the first time an
     honest store holds that evidence (views are subsets of stores). If
     each bit, once true at every duty from some time, stays true, then
     the phases occur in the order gap → uncontested → contested, or gap
     → contested. So there are at most two effective changes per frontier,
     one for each evidence event.
  3. Finalizations add no change: below m−1 they are below every band
     witness; at m−1 it is the same J_(m−1), impossible in the contested
     phase (`fj.crossingNoFinal.v1`) and enforced by the root in the
     uncontested phase; at m it needs a carrier above m, which ends the
     no-rise interval.
  The core does not say when the bits become true at every duty.
- Statement (pinned):

> _fj-redteam.md, lines 764–773 (excerpt; from "Under a≤f"):_
>
> Under a≤f there is at most one justified entry at m−1. There are at
> most these phases:
>
> ```text
> gap: no top J
>     -> uncontested top J
>     -> contested top J
>
> or gap -> contested top J.
> ```

> _fj-redteam.md, lines 778–789:_
>
> Repeated copies do not start a new phase. Later frontier blocks only
> add witnesses once the phase is settled.
>
> A finalization below m−1 is below every band witness and cannot cause
> an independent exclusion. A finalization at m−1 is the same unique
> top J. It is impossible in the contested phase by F2; in the
> uncontested phase the root already enforces it. A finalization at m
> requires a carrier above m, which ends the no-rise interval.
>
> Hence k_eff≤2, with at most three complete attempts. This count is
> independent of SA's slow-window parameter k. It is not a strictly
> increasing potential on each full/HEAD call.

- Status: 2026-09-28 — PROVED (a≤f; r148 F12 without its settling
  sentences; r144o N16).
- Status: 2026-09-28 (FG module, `lean/available-chain` main `64651ad`) —
  Lean coverage of item 3 (ii) is BY HYPOTHESIS: `Fmove_atTop`
  (`AvailableChainKitFG/TwoChanges.lean:653`) takes `hext`, the pure form
  of `fg.finalLock.v1`, as a premise. The premise is discharged by
  `fg.finalLock.v1` at `a ≤ f` with `StoreInv.Fcar`, or by
  `fj.crossingNoFinal.v1` (`crossingNoFinal_QC`). The paper status stays
  PROVED.
- Note (2026-09-28): scope of the line above, under the corrected §0
  definition. `AvailableChainKitFG/Pins.lean` gives item 3 (ii) two rows.
  (1) "F move at m−1 keeps the uncontested phase, Z = F′, lo = m−1 and
  D" (line 376) is PARTIAL: `Fmove_atTop` derives it from extra premises
  (`m ≥ 2`, a carrier K of F′ with `h_F(K) = m−1`, `huniq`, `hext`,
  `ViewRootInj`; `ViewRootInj` is discharged by `viewRootInj_all` (I9,
  2026-09-29)). (2) "at m−1 the contested phase is impossible" (line
  381) is BY HYPOTHESIS: at frontier m, `hext` (every view block above
  m−1 extends F′) is equivalent to ¬E_C(m, F′), so this step is assumed,
  not derived. The BY HYPOTHESIS kind applies to row (2) only.
- Formal reading (2026-09-28) of "finalizations add no change" (item 3)
  for an F move F → F′ at one fixed view V at frontier m ≥ 2 (at m = 1 no
  change can act):
  (i) if `h(F′) < m−1` and every W ∈ V with `h(W) > h(F′)` extends F′
  (`fg.finalLock.v1`, pure form), then the phase, lo, and Z up to
  F → F′ are unchanged; (j, J) is unchanged if j = m−1 (in the gap phase
  the lex-max pair below m−1 may change, which does not act); and
  `D_new = {B ∈ D_old : F′ ⪯ B}`. (Correction 2026-09-28: the first text
  said "(j, J) unchanged" without the condition j = m−1.) Every removed block is an
  ancestor of F′: its witness W has `h(W) ≥ lo ≥ m−1 > h(F′)`, so
  `F′ ⪯ W`, and B ⪯ W makes B and F′ comparable. This is "a common prefix
  below every band witness"; it is NOT "D unchanged".
  (ii) If `h(F′) = m−1` and ∃ K ∈ V with `σ[K].F = F′` (a carrier of F′
  in the view), then F′ is the unique top J (`fg.uniqueJust.v1`), and the
  phase is not gap: K's chain has `h_F = m−1 ≤ h_j < h(K) ≤ m`, so K
  carries the justified entry at m−1, which is F′. The contested phase is
  impossible (`fj.crossingNoFinal.v1`). In the uncontested phase
  Z = J = F′, so D is unchanged. Without the carrier hypothesis, (ii)
  does not cover the gap phase: a witness at height exactly m−1 that does
  not extend F′ can leave D, because `fg.finalLock.v1` needs
  `h(W) > h(F′)` (G02, line 69). The F basis puts the carrier in later
  views, which is a view change. (Revision 2026-09-28: `m ≥ 2` and the
  carrier hypothesis of (ii) added.)
  Source: the Astra plan audit, G02, which refuted "D unchanged" with a
  4-validator example (file
  `lean/available-chain/docs/audit/fg-plan-audit-report.md`, lines 60–69,
  commit `ea8ca7e`, sha256
  `c57a50e7e863139073c7d27b9688903550f21f3ba8fde0b0e3c006771ed11813`).
  r153 breaks this count only through view changes (a lower F advance adds
  an F-basis witness to later views), not at a fixed view.
- Note (2026-09-28, ALFS): case (i) is `Fmove_filtered` for any block set
  (ldp §9.3 (1), lines 630–659, claim C1); `Fmove_below` and
  `Fmove_atTop` are its `fjFrame` special cases.
- Note: the count is for settled phases, not for raw successive R1 duty
  frames (r148 F13, REFUTED; r151 line 24). Between an evidence event and
  its settling, duties can disagree on the phase.
- Composition: with `comp.settle.v1`, each evidence bit is true at every
  duty from (first store time)+θ, or +P in r148's margin. This gives the
  full r148 F12 count.
- Status: 2026-09-29 — WITHDRAWN for current use under `fgsa3` (§0);
  successor `fj.twoChanges.core.v2`. Its evidence is read from duty
  views; current controls read the cumulative store and the live caches.
  The pinned text and the partial Lean coverage stay as history;
  `AvailableChainKitFG/Pins.lean` keeps the pin as a historical pin.


### `fj.twoChanges.core.v2` — FJ phases at a fixed frontier, cumulative evidence

- Variant `fj`. Source: blueprint 21, registry restatement after H.8,
  file `blueprint/archive/21-healing-9b7f5af8.md` (key `bp21`), lines
  1003–1057, sha256
  `9b7f5af8d013a473f9c5361f72377df63f79728599e02d0b9414cd58789c3ac9`.
  Proof: 21 H.7 (uniqueness, contest exclusion, phase order), H.5 (the
  fixed-set domain identity); H.8 adds the settlement deadline.
- Lean pin: not yet pinned (2026-09-29): no clause table yet.
- Lean plan: —. The v1 Lean coverage (`AvailableChainKitFG/TwoChanges.lean`)
  is fixed-view algebra; it stays as history of v1.
- Hypotheses: IF.1–IF.4, injective roots, unique justification at the
  top height, finalized crossing at `a≤f`.
- Statement (pinned):

> _21-healing-9b7f5af8.md, lines 1003–1057:_
>
> ### Registry restatement — fj.twoChanges.core.v2 — PROVED-paper
>
> _2026-09-29. fj.twoChanges.core.v1 is WITHDRAWN for use under 4e85ff34.
> Its duty-view evidence does not determine the current live-cache frame:
> new evidence can be in Σ.T but outside the frozen view. Its fixed-view
> algebra and Lean coverage remain historical. Use fj.twoChanges.core.v2
> with its cumulative-store premises; do not change the old pins._
>
> Assume IF.1–IF.4, injective roots, unique justification at the top height,
> and finalized crossing at `a≤f`. Fix a no-rise interval at frontier
> `m≥2`. If a justification at m−1 exists, denote its unique entry by
> J_(m−1); otherwise both evidence bits are false. At a local read with
> `H_x=m`, define E_J from a carrier of this justification in cumulative
> `Σ.T_x`. Define E_C
> from a height-m off-J block in that same `Σ.T_x`. The live caches and
> these evidence predicates give the effective phases
>
> ```text
> ┌─────────┬───────────────────┬─────┬────────────────┐
> │ Phase   │ Evidence in Σ.T_x │ lo  │ Effective root │
> ├─────────┼───────────────────┼─────┼────────────────┤
> │ Gap     │ ¬E_J              │ m−1 │ F              │
> │ Top J   │ E_J ∧ ¬E_C        │ m−1 │ J_(m−1)        │
> │ Contest │ E_J ∧ E_C         │ m   │ F              │
> └─────────┴───────────────────┴─────┴────────────────┘
> ```
>
> 1. The frame reads `Σ.T_x` and its caches. It does not recompute E_J,
>    E_C, H, J, Z, or lo from a frozen duty view. A duty view V only
>    supplies the arguments and witnesses of `D(V)` with those controls.
> 2. At each store both evidence bits persist once true. Thus the phase
>    order is gap → top J → contest, with phases possibly absent. There
>    are at most two evidence changes at one frontier. Stores can differ
>    during delivery. The bound for common settled phases uses H.8; the
>    pure core makes no claim that every successive duty has one frame.
> 3. Lower F moves add no phase. At a fixed block set V, once top-J
>    evidence is accounted for, an F-only move to F′ below height m−1
>    gives `D_new(V)={B∈D_old(V):F′⪯B}` in an F-root phase.
>    A removed member is a strict ancestor of F′: its band witness has
>    height at least m−1 and extends F′ by finalized crossing. A top-J
>    domain is unchanged. Here the height of an F move is its certificate
>    height. No step asserts that the whole domain stays unchanged.
> 4. Acceptance of finality at m−1 brings a finality carrier into Σ.T_x.
>    It therefore also supplies top J if absent. Count that top-J evidence
>    event once. The unique top is F′, and contest is impossible by H.7.
>    If the top phase was already present, its domain is unchanged.
>    Finality at height m requires a carrier above m and ends the interval.
>
> **Proof.** H.7 proves uniqueness, contest exclusion, and the phase order
> from cumulative evidence. IF.4 gives the cache invariant. H.5 proves the
> fixed-set domain identity and the retained-suffix statement. A finality
> carrier has `h_F≤h_j<h`, so one at m−1 with height at most m also carries
> the unique top justification. These facts prove items 1–4. H.8 alone
> adds the common settlement deadline. At m=1 no positive lower F move
> acts. This statement does not import the old duty-view evidence premise.

- Status: 2026-09-29 — PROVED (paper; blueprint 21 H.7, H.5, H.8).

### `fj.armedSafe.v1` — F7: clean safety and P1 under FJ

- Variant `fj`. Source r148 §5 F7, lines 398–413 and 431–443. File
  `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`.
- Statement (pinned):

> _fj-redteam.md, lines 398–413:_
>
> F7 — PROVED under the original base premises.
>
> Every target or progress QC contains an honest row because q>a. Each
> honest height row has a successful fresh fast source, with τ>a surviving
> supporters. Its named entry is an ancestor of that source. Finality has
> an earlier justified target origin.
>
> In a clean run the adjudicated induction retains all genuine source
> bodies, including a raw result whose write was vetoed. Their controlling
> entries lie on one retained chain. Two different entries at the same
> height cannot both have those honest origins. Hence no FJ contest can
> occur in the clean induction. FJ has the same choice as the adjudicated
> rule, including its exact proposal/HEAD comparison and pending-gate step.
> Clean safety, monotonicity, and honest-proposal inclusion in 6Δ follow
> for all a<h. This uses [fgsa-adjudicate §3.2](fgsa-adjudicate.md), not
> the incorrect whole-view inclusion shortcut in fgsa-fast-opus §3.2.

> _fj-redteam.md, lines 431–443:_
>
> Consequently the strict band retains B. F and J are comparable with B.
> A root above B already covers it; otherwise its live lease is an
> effective anchor. FJ cannot create the first departure. Conflicting
> release support is at most a<τ. Pending renewal, expiry, and the raw
> whole-result guard are exactly the adjudicated outage proof.
>
> The constants remain:
>
> ```text
> fast P1:  lag 4Δ, with h_t≥τ throughout the required healthy prefix;
> slow P1:  lag L−3Δ, with its original healthy-prefix premises;
> outage budget: Π=min(η,L).
> ```

- Status: 2026-09-28 — PROVED (r148 F7; r144o N13).
- Status: 2026-09-28 (ldp) — under ALFS (spec 183f2c40): clean safety, 6Δ service and
  fast and slow P1 for all `a<h` are PROVED (paper) with the original
  constants (L8, ldp lines 41 and 378–394; §10.3, lines 849–857). The r157
  outage execution (r157 lines 5–10, §3) is REFUTED as an attack on ALFS:
  r157 takes the lease start from the HEAD tree's domain, ALFS from the
  full live domain (ldp lines 749–758).
- Status: 2026-09-28 (r158) — under ALFS (spec 183f2c40), independently
  checked by r158: clean chain safety, monotone S, 6Δ inclusion, fast P1
  with lag 4Δ and slow P1 with lag `L−3Δ`, for all `a<h`, are PROVED
  (paper) (r158 §5, lines 560–613; table lines 885–887). r158 replaces
  the count `h>2a` of ldp §10 by a count that needs only `a<h` (L2, lines
  72–73 and 562–572). The proof uses no FG safety theorem that needs
  `a≤f` (line 595). r158 §3.1 replays the r157 outage under ALFS: the two
  honest groups keep B to the outage end (lines 295–301). P1 under a
  view-domain anchor stays REFUTED (a different rule; table line 888).
- Status: 2026-09-28 (r159) — under ALFS (spec c7c41a43): P1 and L8
  hold with the admitted merge (r159 M-C, lines 56–65; table lines 74
  and 88); the spec cites r158 §5 and r159 §1 (spec lines 1432–1440).
- Status: 2026-09-28 (r160) — under ALFS (spec 1c6952b6, receipt premise):
  HOLDS. Clean origin and P1 hold (r160 lines 675–676 and 703). The
  clean proposal comparison NEEDS-CHANGE: replace exact vote sets by
  r160 §4.3; clean safety and 6Δ inclusion still HOLD (lines 677–678).
- Status: 2026-09-28 (r161) — under ALFS (spec bd942ca0, filtered base):
  HOLDS for all `a<h`, with the complete healthy-prefix premises and
  the original constants (r161 §4, lines 227–374; spec lines 1494–1520
  and 1585–1593). An S read whose origin is an F assignment is traced to
  its earlier honest fast source, so the arming lag does not change
  (r161 lines 311–314). A local lease formed under an asynchronous prefix
  is not P1-armed (`comp.leaseVsFinal.v1`).

### `fg.base.fj.v1` — FJ reset and base handoff witness

- Variant `fj` (moved from §3 of v1). Source r148 §9 F14, lines 852–900.
  File `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`.
- Hypotheses: `env.r148`; `fj.canonical.v1`; `fj.inBandLock.v1`;
  `fj.twoChanges.core.v1`; `comp.settle.v1`.
- Note (2026-09-28; §0 rule (a)): `fj.twoChanges.v1` was replaced by
  `fj.twoChanges.core.v1` and `comp.settle.v1`. The cut `u0` and M0 of the
  witness are `comp.cut.v1`.
- Note (2026-09-28; §0 rule (b)): the contested-band producer of r148
  §9 (lines 820–828: "the proposer parent has height at least lo") uses
  the head in band. That step is `ap.headReachesLo.v1` (AP data after the
  user design correction of 2026-09-28). Hypotheses add
  `ap.headReachesLo.v1`.
- Note (2026-09-28): under ALFS: `ap.headReachesLo.v2`, with the charged
  fallback slots.
- Note (2026-09-28): under ALFS (spec c7c41a43): `ap.headReachesLo.v3`
  (supersedes v2), with θ = 4Δ per effective event in place of the
  charged fallback slots.
- Note (2026-09-28): under ALFS (spec 1c6952b6): `ap.headReachesLo.v4`
  (supersedes v3; DC's receipt premise in place of accepted-object
  relay).
- Note (2026-09-28): under ALFS (spec bd942ca0): `ap.headReachesLo.v5`
  (supersedes v4; filtered base, admission-or-coverage).
- Returned witness (audit W09): the caps M ≤ M0 and the cut `u0`
  (`env.r148`); an honest row at height ≥ M0+1 > M by `B_R`; its fresh
  source, permanent by `fj.canonical.v1` from its transfer HEAD; the repair
  start and `B_base`. FJ has no NJ arm. An actual finalized checkpoint F*
  above the cut can serve as an earlier reset (r148 §5, lines 471–475).
- Statement (pinned):

> _fj-redteam.md, lines 852–900:_
>
> Thus the old conservative (3g+6)P producer budget covers both cases.
> Non-opening consumption can only finish the required rise earlier.
> One attempt, including settling and alignment, costs at most
>
> ```text
> c       = ceil(ρ/P)
> w       = c+3g+8
> P+ρ+P+(3g+6)P ≤ wP.
> ```
>
> At most two phase events interrupt an attempt. If an event arrives
> after an attempt would have completed, the frontier has already
> risen. Otherwise charge that event once and restart with its own
> settling margin and local repair. Therefore
>
> ```text
> β_FJ = 3w = 3ceil(ρ/P)+9g+24
> ```
>
> is a sufficient number of rounds per frontier rise. No common global
> SA handoff was assumed to obtain those rises. In particular, a
> permanent lock or record stall is impossible under these recovery
> premises, including when every action initially has an empty source.
>
> At u0 the honest archival maximum is M0. A crossing to M0+2 requires
> an honest row at M0+1 or higher, because every progress QC contains
> an honest signer and advances only one height. Its height exceeds
> M, so §6 makes its source permanent. Two frontier rises suffice to
> force such a row. Since u0<GST+3P,
>
> ```text
> B_R = P[3+2β_FJ]
> ```
>
> bounds the existence of this reset row, and also the public height
> rise used to force it. A statement that *all duty views already see
> the high witness* needs the extra settling margin. Do not silently
> replace the event bound by that duty-view claim.
>
> From the reset, retain all selected source bodies. Allow P for a
> common start and then run the new SA source-window calculation for
> raw fast and slow sources, including older leases on divergent
> descendants of the retained prefix. The exact repair proposal
> replaces old S tips and starts the safe, monotone suffix with 6Δ
> service. This is fgsa-adjudicate §5.3 with FJ's descent result:
>
> ```text
> B_base = B_R+P+ρ.
> ```

- Status: 2026-09-28 — PROVED (r148 F14, paper bounds at the level of the
  adjudicated r143 producer). Example (`R=3, k=2, G=8Δ, g=3`):
  `B_R = 1476Δ`, `B_base = 1518Δ` (r148 §11, lines 988–989).
- Status: 2026-09-28 (r153) — the uniform (M-independent) bounds `B_R`
  and `B_base` of this entry are REFUTED under the current rules. r153 (`fj-reach.md`, lines 6–18 and 24–28)
  gives a legal execution with no height rise for any fixed λ; r153a (`fj-reach-adjudicate.md`,
  lines 6–11 and 31–33) confirms it. The broken steps are r148 F12, lines
  781–782, and F14, lines 824–832: a lower F advance adds a view-dependent
  viability witness to HEAD views through the F basis (spec lines 742–749
  and 494; r153a lines 13–19 and 243–269). The reset witness
  (`fj.reset.v1`) and the local results from an actual reset stay PROVED
  (r153a lines 34 and 281–286). The valid arrival bound is M-dependent
  (`fj.rise.fixedF.v1`).
- Note: r144o N17 (lines 645–677) marks the same bounds SKETCH, because the
  contested-band producer port was missing. r148 §9 supplies that port. This
  entry does not discharge HNI (§4 introduction).
- Note (r151): the reset witness is now pinned as `fj.reset.v1`. This
  entry keeps the supplied arrival `B_R` and handoff `B_base`; r151
  §5.4 uses `B_R` as the supplied uniform producer.
- Note (2026-09-29; current use): `fj.twoChanges.core.v1`, `ap.headReachesLo.v5` are WITHDRAWN for current
  use. The citations above are history. A current use of this entry
  reads them as §9, "Current reading of withdrawn ids".


### `fj.firstFinality.v1` — F17: first finality after damage

- Variant `fj`. Source r148 §10 F17, lines 941–945. File `fj-redteam.md`,
  sha256 `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`.
- Statement (pinned):

> _fj-redteam.md, lines 941–945:_
>
> F17 — SKETCH for the post-damage numerical expression
>
> ```text
> B_first = B_base+(g+2)P+9Δ.
> ```

- Status: 2026-09-28 — SKETCH (r148 F17; three timed steps are missing,
  lines 947–966).
- Status: 2026-09-28 (r152, r153) — r152 (`fj-first-finality.md`,
  lines 20–26) proves FF1–FF7 on paper, from the healed state at t_h
  (r153a lines 37 and 464–466). The r152 uniform total 1541Δ is REFUTED:
  it uses `B_R` (r153a lines 38 and 466–469). The r148 expression
  `B_first = B_base+(g+2)P+9Δ` pinned here is REFUTED as a uniform bound
  for the same reason. The M-dependent form `B_lit+gP+9Δ` is PROVED
  relative to r147 (r153a line 470). Under the fix candidate FV (§8) the
  1541Δ form is SKETCH (r153a line 471).
- Status: 2026-09-28 (ldp) — under ALFS (spec 183f2c40): first finality before
  `GST+B+gP+9Δ` = 1049Δ is PROVED (paper) (ldp lines 44 and 515; r152
  FF5, with `δ_t ≥ 2R−1`). It imports r156 §§4–7, r151 Theorems N/H and r152 FF1–FF7 as paper
  results, not independently checked (ldp lines 68–71 and 527–531). The REFUTED lines for the old spec stay.
- Status: 2026-09-28 (r158) — under ALFS (spec 183f2c40), independently
  checked by r158: r152 FF1–FF7 are PROVED after healing, with `δ_t=2R`
  and strong recurrence (r158 §6, lines 715–751; table line 895). First
  finality before `GST+1049Δ` is PROVED (paper) (Theorem H plus FF5;
  table line 896). With the H12 transfer, first finality before
  `GST+B′+gP+9Δ` = `GST+1041Δ` is PROVED (paper) (lines 788–794; table
  line 899). This replaces "not independently checked" in the ldp line.
  r158 checks the slice `R≥3, δ_t=2R` (lines 112–116); `R=2` and other
  δ_t are OPEN (line 900). The weak recurrence does not replace the three
  openings (line 747).
- Status: 2026-09-28 (r159) — under ALFS (spec c7c41a43): FF1–FF7 hold
  with the admitted merge (r159 lines 133–152), and the spec states first
  finality before `GST+B′+gP+9Δ` = 1041Δ as its claim (spec lines
  1460–1462). The δ_t scope is `δ_t = 2R`, `R ≥ 3` (lines 1356–1361);
  `δ_t < 2R` and `R = 2` stay OPEN.
- Status: 2026-09-28 (r160) — under ALFS (spec 1c6952b6, receipt premise):
  HOLDS. FF1–FF7 and the total 1041Δ keep their constants (r160 lines
  726–737). The FF §1 delivery premise NEEDS-CHANGE: use the receipt
  premise and the exact honest-row corollary (r160 §3.1, §3.4; line 725).
- Status: 2026-09-28 (r161) — under ALFS (spec bd942ca0, filtered base):
  HOLDS. FF1–FF7 keep their endpoints; the FF4 carrier extends the
  receiving F by the height cap and crossing (r161 lines 646–652); first
  finality before 1041Δ (r161 lines 656–664; spec lines 1616–1618).

**FJ composite entries (`Kit.Compose`, from r151).** r151 renames the
caps. Its μ is the old-source cap that r148 and r144o call M. Its M is
the DC cut maximum at `u_0` that r148 calls M0. The entries below use the
r151 names; `μ ≤ M`.

### `fj.reset.v1` — reset at the first honest row of height M+1

- Variant `fj`. Source r151 §2, lines 106–143. File `fj-theorem-h.md`, sha256
  `16b69dba55d889b9ae20dd55b228cfd83ad22037d796c6219cdb65831718bba3`.
- Hypotheses: `env.r151`; `fj.frame.v1`; `fg.causalCap.core.v1`;
  `comp.cut.v1`; `fg.finalLock.v1`.
- Note (2026-09-28; §0 rules (a) and (b)): `fg.causalCap.v1` was replaced
  by `fg.causalCap.core.v1` and `comp.cut.v1`. `fg.finalLock.v1` is the
  "finalized crossing" of the pinned text.
- Returned witness (audit W09): the cut `u_0`, its maximum M and the
  old-source cap μ ≤ M; r* = the least round with an honest row at
  height M+1, `b = s* = r*R`, and its fresh fast source C* with
  `ht(C*) = M+1`; every honest row at height ≥ M+1 has source label ≥ b;
  first-transfer view facts at `q_b`: every freeze `z_b` has the C* path,
  each transfer frame has H = M+1, and C* is kept. FJ has no NJ or
  finalized case split; an actual finalized reset F* can replace the cut
  only with its source-label boundary (r151 §7.2, lines 639–645).
- Statement (pinned):

> _fj-theorem-h.md, lines 106–143:_
>
> There are two related maxima. Keep them distinct:
>
> ```text
> μ = max({1} ∪ {height of an honest row with source v_s<GST});
> r_G = first action round at or after GST;
> u_0 = a_(r_G+2), with its inclusive event prefix;
> M = honest archival maximum at u_0.
>
> μ≤M;       GST+2P≤u_0<GST+3P.
> ```
>
> Here M is the DC cut maximum, called M0 in r148. The old-source cap
> called M in r148 and in the descent lemma is μ here. This distinction
> is needed for the two-rise arrival proof.
>
> Let r* be the least round containing an honest row at height M+1.
> Set `s*=r*R`, `b=s*`, and let C* be a selected fresh fast source of
> such a row. Then `ht(C*)=M+1`. A higher row cannot precede this row:
> its source path must first cross M+1, and that crossing needs an
> honest row at M+1. Thus every honest row at height at least M+1
> has source label at least b. The cut and causal cap make b a wholly
> synchronous label.
>
> This is the required reset. “Above M+1” must not mean that one must
> wait for a row of height M+2. The first row at M+1 already suffices.
> Equivalently, this is Lemma R with predecessor x=M. One can use the
> earlier cap μ for a local reset; the cut maximum M gives the stated
> arrival accounting without an additional search.
>
> The transfer boundary is `q_b=a_(r*)−Δ`, not the action time a_(r*).
> A surviving honest supporter of C* sends its complete path at v_b.
> Relay places that path in every freeze z_b. At q_b no carrier above
> M+1 can already exist: such a carrier would require an earlier
> honest row at M+1. Thus each transfer frame has H=M+1. If it roots
> at J of height M, the absence of a contest means `J⪯C*`. If C*
> conflicts with J, C* itself forces the contest and witnesses lo=M+1.
> The F case follows from finalized crossing. Therefore C* is kept at
> its first transfer, including when readers see different old J evidence.

- Status: 2026-09-28 — PROVED (r151 claim table line 21).
- Note (2026-09-29; current use): `fg.finalLock.v1` is WITHDRAWN for current
  use. The citations above are history. A current use of this entry
  reads them as §9, "Current reading of withdrawn ids".


### `fj.theoremN.v1` — Theorem N for all protected fast and slow bodies

- Variant `fj`. Source r151 §3.2 and §4, lines 204–214, 246–249, 267–269 and
  290–291. File `fj-theorem-h.md`, sha256
  `16b69dba55d889b9ae20dd55b228cfd83ad22037d796c6219cdb65831718bba3`.
- Hypotheses: `env.r151`; `fj.reset.v1`; `fj.canonical.v1` (r151 §3.1
  re-proves F9 with the source boundary explicit and the cap μ);
  `ap.S.v2`; `ap.Sslow.v1`; `fg.provenance.v2`; `ap.fastSupport.v1`;
  `comp.provenance.v1`. No service entry is used.
- Note (2026-09-28; §0 rule (a)): `fg.provenance.v1` was replaced by
  `fg.provenance.v2`, `ap.fastSupport.v1` and `comp.provenance.v1`.
- Protected set: 𝒫 = all fast bodies at labels ≥ b and all slow bodies
  whose window lies in `[b,∞)` (blueprint §7.1), as for
  `comp.fgHealed.v1`.
- Statement (pinned):

> _fj-theorem-h.md, lines 204–214:_
>
> **High contest exclusion — PROVED.** A contest at H=j+1 with j≥M+1
> would give a justified J at j and a conflicting crossing of j. Each
> QC contains an honest row. Those rows would name different entries
> at j, contrary to the preceding result. This also excludes a private
> conflicting carrier. Consequently every post-reset duty satisfies
>
> ```text
> H_d≥M+1;
> contest_d ⇒ H_d=M+1;
> lo_d ≤ max(M+1,H_d−1).
> ```

> _fj-theorem-h.md, lines 246–249:_
>
> Let 𝒫 be exactly the protected family in blueprint §7.1: all successful
> fast bodies at labels s≥b and all successful slow bodies whose complete
> k-label windows lie in `[b,∞)`. Include qualifying prefixes, not only
> the deepest FG-selected source. Put `q(B)=q_s` for a body of label s.

> _fj-theorem-h.md, lines 267–269:_
>
> **Lemma K_FJ — PROVED.** Fix an honest duty d after q_b and a present
> body B with q(B)≤t_d. Suppose B is compatible with C* and with every
> earlier controlling high source, of height at least M+1. Then B is kept.

> _fj-theorem-h.md, lines 290–291:_
>
> **Theorem N_FJ — PROVED.** For every B∈𝒫 and every honest choice duty
> d with `t_d≥q(B)`, B is kept. S1, S2, and S3 therefore hold forever.

- Status: 2026-09-28 — PROVED (r151 claim table lines 20 and 22).
- Note: this is the FJ counterpart of `comp.theoremN.v1` and
  `comp.fgHealed.v1`. It does not use HNI: an active J at M precedes C*
  by the frontier test (r151 lines 273–275).

### `fj.rise.fixedF.v1` — literal-N1 split and M-dependent arrival

- Variant `fj`. Source r151 §5.1–§5.3, lines 328–332, 371–374 and 384–398.
  File `fj-theorem-h.md`, sha256
  `16b69dba55d889b9ae20dd55b228cfd83ad22037d796c6219cdb65831718bba3`.
- Hypotheses (audit W02): the FJ port of `comp.rise.fixedF.v1`, with lo
  fixed and the contested threshold m (r151 §5.2, lines 342–355);
  `fj.twoChanges.core.v1`; `fj.inBandLock.v1`; `comp.settle.v1` (the
  settling constant θ = 4Δ); `fj.reset.v1` (a crossing to M+2 needs the
  reset row). It is a comp-level rise, not an AP service fact.
- Note (2026-09-28; §0 rule (a)): `fj.twoChanges.v1` was replaced by
  `fj.twoChanges.core.v1` and `comp.settle.v1`.
- Note (2026-09-28; §0 rule (b)): the FJ port in the hypotheses (r151
  lines 342–348: "Below lo, a supporter's actual path supplies
  viability. At or above lo, the extra eligibility clause is off") uses
  the head in band. That step is `ap.headReachesLo.v1` (AP data after the
  user design correction of 2026-09-28). Hypotheses add
  `ap.headReachesLo.v1`.
- Note (2026-09-28): under ALFS: `ap.headReachesLo.v2`, with the charged
  fallback slots.
- Note (2026-09-28): under ALFS (spec c7c41a43): `ap.headReachesLo.v3`
  (supersedes v2), with θ = 4Δ per effective event in place of the
  charged fallback slots.
- Note (2026-09-28): under ALFS (spec 1c6952b6): `ap.headReachesLo.v4`
  (supersedes v3; DC's receipt premise in place of accepted-object
  relay).
- Note (2026-09-28): under ALFS (spec bd942ca0): `ap.headReachesLo.v5`
  (supersedes v4; filtered base, admission-or-coverage).
- Statement (pinned):

> _fj-theorem-h.md, lines 328–332:_
>
> For FJ, literal N1 must fix `(H,F,Z,lo)`, not only `(H,F,Z)`.
> Effective N1 fixes `(H,lo,Zhat)`, where Zhat records the active top-J
> restriction or the absence of that restriction; lower common-trunk F
> advances are allowed. This explicit lo coordinate is necessary even
> if a root name happens to stay equal during a phase change.

> _fj-theorem-h.md, lines 371–374:_
>
> With literal N1, additionally charge lower F advances. If n_F(m) is
> their count at frontier m, the bound is `(3+n_F(m))W`. Evidence
> delivered to different readers is one event with one settling interval,
> not n events for n readers.

> _fj-theorem-h.md, lines 384–398:_
>
> Let f_0 be the least honest finalized height at u_0. Before the first
> arrival at M+2, every accepted F has height at most M: its evidence
> contains a carrier of height at least `ht(F)+1`. Thus distinct lower
> F advances total at most M−f_0. A finalization which itself gives a
> carrier at M+2 ends the search and needs no new attempt. Literal
> composition gives the **PROVED**, M-dependent bound
>
> ```text
> a_(r*) < GST+A_lit;
> A_lit = 3P+[6+M−f_0](λ+4Δ).
> ```
>
> Allowing one extra terminal F event gives the weaker expression with
> `7+M−f_0`; it is also valid. Neither expression is a uniform bound
> independent of the damaged prefix.

- Status: 2026-09-28 — PROVED (r151 claim table line 25). Example
  (`Δ=1, R=3, k=2, G=8, g=3`, `M=1, f_0=0`):
  `B_lit = A_lit + δ_H = 1498Δ` (r151 line 720).
- Status: 2026-09-28 (r153) — PROVED, unchanged, relative to r147's
  literal (L) (r153a lines 35 and 317–329: literal N1 fixes F, so the F
  basis is fixed; r153 line 31). It is the valid arrival bound under the
  current rules. r153a did not re-audit r147.
- Note (2026-09-29; current use): `fj.twoChanges.core.v1`, `ap.headReachesLo.v5` are WITHDRAWN for current
  use. The citations above are history. A current use of this entry
  reads them as §9, "Current reading of withdrawn ids".


### `fj.rise.movingF.v1` — effective-N1 split and arrival

- Variant `fj`. Source r151 §5.2–§5.3, lines 357–364 and 400–412. File
  `fj-theorem-h.md`, sha256
  `16b69dba55d889b9ae20dd55b228cfd83ad22037d796c6219cdb65831718bba3`.
- Hypotheses: effective (L) for the FJ frame, with effective N1 fixing
  `(H,lo,Zhat)` (r151 lines 329–331); `fj.twoChanges.core.v1`;
  `comp.settle.v1` (θ = 4Δ).
- Note (2026-09-28; §0 rule (a)): `fj.twoChanges.v1` was replaced by
  `fj.twoChanges.core.v1` and `comp.settle.v1`.
- Note (2026-09-28; §0 rule (b)): effective (L) for the FJ frame uses the
  same producer as `fj.rise.fixedF.v1`, so it uses `ap.headReachesLo.v1`.
  Hypotheses add `ap.headReachesLo.v1`.
- Note (2026-09-28): under ALFS: `ap.headReachesLo.v2`, with the charged
  fallback slots.
- Note (2026-09-28): under ALFS (spec c7c41a43): `ap.headReachesLo.v3`
  (supersedes v2), with θ = 4Δ per effective event in place of the
  charged fallback slots.
- Note (2026-09-28): under ALFS (spec 1c6952b6): `ap.headReachesLo.v4`
  (supersedes v3; DC's receipt premise in place of accepted-object
  relay).
- Note (2026-09-28): under ALFS (spec bd942ca0): `ap.headReachesLo.v5`
  (supersedes v4; filtered base, admission-or-coverage).
- Statement (pinned):

> _fj-theorem-h.md, lines 357–364:_
>
> If effective (L) holds with a uniform λ, split at the first top-J and
> contest events. If an event has not occurred by the end of a complete
> settled attempt, (L) already gives a rise. Otherwise settle its evidence
> and restart. With two interruptions the bound is
>
> ```text
> one height rise: at most 3(λ+4Δ).
> ```

> _fj-theorem-h.md, lines 400–412:_
>
> With effective (L) the **PROVED conditional implication** is
>
> ```text
> a_(r*) < GST+A_eff(λ);
> A_eff(λ) = 3P+6(λ+4Δ).
> ```
>
> Effective (L), for every reachable pre-reset start with the candidate
> `λ=ρ+2σ`, remains OPEN. r149/r150's missing common supported band
> prefix can occur as an obligation in an ordinary FJ phase too. The
> trunk lemma compares two roots within one view; it does not supply
> that prefix across different views. Neither the stricter contested
> band nor the count of two events proves this missing service premise.

- Status: 2026-09-28 — OPEN as a result from the execution premises
  alone (r151 claim table line 27). The split and arrival implication
  from effective (L) is PROVED (r151 claim table line 26).
- Status: 2026-09-28 (r153) — effective (L) for the FJ frame is REFUTED
  under the current rules: r153 (`fj-reach.md`, lines 6–18 and 24–28); r153a (`fj-reach-adjudicate.md`, lines 6–11 and 30: no finite
  M-independent healing or arrival bound). The split and the implication
  from effective (L) stay PROVED; their premise fails. Under FV (§8) a
  restored uniform bound is SKETCH (r153a line 43).
- Status: 2026-09-28 (ldp) — under ALFS (spec 183f2c40): effective (L) with
  `λ = ρ+2σ` is PROVED (paper) in the DC form (C3, ldp lines 57 and
  661–675), so the arrival implication applies. It imports r156 §§4–7, r151 Theorems N/H and r152 FF1–FF7 as paper
  results, not independently checked (ldp lines 68–71 and 527–531). The REFUTED lines
  for the old spec stay.
- Status: 2026-09-28 (r158) — under ALFS, independently checked by r158:
  effective (L) (C3) is PROVED after the witness repair W (r158 table
  line 641; §4, lines 429–558). The count does not depend on M, on old
  private stock or on lower F advances (lines 553–558).
- Status: 2026-09-28 (r159) — under ALFS (spec c7c41a43): C3 holds with
  the admitted merge; λ = ρ+2σ is unchanged (r159 table lines 92–93).
- Status: 2026-09-28 (r160) — under ALFS (spec 1c6952b6, receipt premise):
  HOLDS. C3 holds with r160 §4.3 and honest row inclusion (r160
  line 705).
- Status: 2026-09-28 (r161) — under ALFS (spec bd942ca0, filtered base):
  HOLDS. C3 HOLDS (r161 line 608).
- Note: the missing premise is the same common supported band prefix as
  `ap.reach.v1` (r151 lines 408–412).
- Note (2026-09-29; current use): `fj.twoChanges.core.v1`, `ap.headReachesLo.v5` are WITHDRAWN for current
  use. The citations above are history. A current use of this entry
  reads them as §9, "Current reading of withdrawn ids".


### `fj.Xplus.v1` — FJ (X+), band stated with lo

- Variant `fj`. Source r151 §6.2, lines 464–485. File `fj-theorem-h.md`, sha256
  `16b69dba55d889b9ae20dd55b228cfd83ad22037d796c6219cdb65831718bba3`.
- Hypotheses: `env.r151`; x0–x3 as pinned, with the threshold `lo_d` of
  each compared read.
- Statement (pinned):

> _fj-theorem-h.md, lines 464–485:_
>
> Use r149's (X+) proof with the actual threshold lo_d. Specifically,
> for an honest proposal P with parent A require:
>
> ```text
> x0: A is the ordinary proposal walk result, with no lease start.
> x1: every live lease at each same-slot honest HEAD precedes A.
> x2: every compared FG root precedes A, and ht(A)≥lo_d.
> x3: some T⪯A is present and kept at all compared reads,
>     every honest preceding-label HEAD contains T,
>     and ht(T)≥max_d lo_d.
> ```
>
> Then every honest HEAD names exactly P and every honest S contains P
> at d_u. This is **PROVED** by the r149 transport argument. Below T,
> all h honest supporters give strict score dominance. At or above T,
> the below-band clause is off in every compared view. Any old majority
> competitor has an honest supporter whose path reached the proposer;
> it was already available to the ordinary parent comparison. A new
> unsupported F-basis edge has no such majority. The unique current-slot
> child P is eligible and available. These comparisons give exact P.
> At q_u its h≥τ clean votes release every conflict, and its d_u raw
> result is exactly P.

- Status: 2026-09-28 — PROVED (r151 claim table line 28).
- Use rule (audit W03): a composite must prove x0–x3 at each call. The
  form `ht(T) ≥ max H_d−1` of `ap.Xplus.v1` alone does not suffice in a
  contest (r151 lines 487–489).
- Note (2026-09-28): this entry takes x2 as a premise, so it does not use
  `ap.headReachesLo.v1`. A caller discharges `ht(A) ≥ lo_d` of x2 with
  `ap.headReachesLo.v1` (see `fj.healed.v1`).

### `fj.healed.v1` — Theorem H for FJ and the proved bound

- Variant `fj`. Source r151 §7.3 and §8, lines 649–663 and 722–736. File
  `fj-theorem-h.md`, sha256
  `16b69dba55d889b9ae20dd55b228cfd83ad22037d796c6219cdb65831718bba3`.
- Hypotheses: `env.r151`; `fj.reset.v1`; `fj.theoremN.v1`; `ap.S.v2`;
  `ap.Sslow.v1`; `fj.Xplus.v1`; for the global clause also
  `fj.rise.fixedF.v1` (literal route) and the supplied r148 F14 arrival
  `B_R` (`fg.base.fj.v1`). It does not use `fj.rise.movingF.v1`.
- (X+) discharge (audit W03): at each honest proposal with `u ≥ ℓ+1`,
  `ℓ = b+2k−1`, r151 proves x0 and x1 (§6.3, lines 493–508) and x2 and
  x3 with `ht(T) = max(M+1, m_u−1) ≥ lo_d` (§6.4, lines 512–547),
  including views that disagree on the contest bit.
- Note (2026-09-28; §0 rule (b)): the x2 part `ht(A) ≥ lo_d` of the
  (X+) discharge is `ap.headReachesLo.v1` for the ordinary proposal walk
  A. Hypotheses add `ap.headReachesLo.v1`.
- Note (2026-09-28): under ALFS: `ap.headReachesLo.v2`, with the charged
  fallback slots.
- Note (2026-09-28): under ALFS (spec c7c41a43): `ap.headReachesLo.v3`
  (supersedes v2), with θ = 4Δ per effective event in place of the
  charged fallback slots.
- Note (2026-09-28): under ALFS (spec 1c6952b6): `ap.headReachesLo.v4`
  (supersedes v3; DC's receipt premise in place of accepted-object
  relay).
- Note (2026-09-28): under ALFS (spec bd942ca0): `ap.headReachesLo.v5`
  (supersedes v4; filtered base, admission-or-coverage).
- Clauses: (local) `t_h ≤ q_(s*)+2L+G−Δ` (§7.3), with no arrival input.
  (global) `t_h < GST+B_proved` (§8), uniform choice
  `B_FJ,H = B_R+δ_H`.
- Statement (pinned):

> _fj-theorem-h.md, lines 649–663:_
>
> Under §1 and the actual reset in §2, all protected bodies have permanent
> FG non-interference from their own transfer times. There is a repair
> gate t_h such that, from t_h onward, all honest S values form one
> chain, each S is monotone, each accepted honest F precedes every
> honest S, and every honest proposal emitted from t_h onward is included
> in every honest S within 6Δ. The available accessor is then S.
>
> The bound is
>
> ```text
> t_h=d_u≤t_ℓ+G+6Δ
>           =t_b+2L+G+4Δ
>           =q_(s*)+2L+G−Δ
>           =a_(r*)+2L+G−2Δ.
> ```

> _fj-theorem-h.md, lines 722–736:_
>
> **Final healing theorem for FJ — PROVED.** Under §1, with r148 F14
> as a supplied proved arrival result, define
>
> ```text
> B_proved=min(3P+[6+M−f_0](ρ+2σ+4Δ),
>              P[3+2(3ceil(ρ/P)+9g+24)])+2L+G−2Δ.
> ```
>
> There exists `t_h<GST+B_proved` from which all honest S values lie
> on one chain, each honest S is monotone, every accepted honest F
> satisfies `F⪯S_i` at every honest reader i, and every honest proposal
> emitted in this suffix is included in all honest S values within 6Δ.
> Thus `available=S` throughout this suffix. The uniform proved choice
> is **B_FJ,H**, which is **1496Δ** for the first example. Independently
> of the arrival route, `t_h≤q_(s*)+2L+G−Δ` at the actual reset.

- Status: 2026-09-28 — PROVED (r151 claim table lines 29–32). Example
  (`Δ=1, R=3, k=2, G=8, g=3`): `B_FJ,H = 1496Δ`, 22Δ below r148's
  `B_base = 1518Δ` (r151 lines 705–716).
- Status: 2026-09-28 (r153) — split. (local) `t_h ≤ q_(s*)+2L+G−Δ`
  after an actual reset stays PROVED (r151 §7.3; r153a lines 34 and
  281–286). (global) The `B_R` arm of `B_proved` and the uniform choice
  `B_FJ,H = 1496Δ` are REFUTED under the current rules (r153 lines 24–28;
  r153a lines 31–33). `B_proved` is a minimum that contains the refuted
  arm, so the global clause as stated is REFUTED. The literal-N1,
  M-dependent bound `B_lit = 3P+[6+M−f_0](λ+4Δ)+2L+G−2Δ` is PROVED
  relative to r147 (r153a lines 317–329): `t_h < GST+B_lit`.
- Status: 2026-09-28 (ldp, h12) — under ALFS (spec 183f2c40): the uniform FJ healing
  bound `B = 6ρ+[9+13g+7τ_t]P+60Δ+δ_H` = 1004Δ (reference parameters) is
  PROVED (paper) (ldp lines 8–11, 43 and 506–516). It imports r156 §§4–7, r151 Theorems N/H and r152 FF1–FF7 as paper
  results, not independently checked (ldp lines 68–71 and 527–531).
  Local full healing by `q_(s*)+G+5Δ` (Theorem H′, h12 lines 18–28 and
  39–41) is PROVED with R1 views; its transfer to ALFS is not yet
  checked. The REFUTED lines for the old spec stay.
- Status: 2026-09-28 (r158) — under ALFS (spec 183f2c40), independently
  checked by r158 (`alfs-redteam.md`): the uniform FJ healing bound
  `GST+1004Δ` (reference parameters, `R≥3, δ_t=2R`) is PROVED (paper),
  after the r158 repair of the ldp witness step (the full-store witness W;
  r158 §4, lines 429–558; budgets lines 541–551; table line 893). With the
  H12 transfer (Lemma U and Theorem H′; r158 §7, lines 753–800): healing
  from `d_u ≤ q_(s*)+G+5Δ`, and the uniform bound `B′ = B−2L+6Δ` = 996Δ,
  is PROVED (paper) (lines 788–793; table lines 897 and 899). Local r151 N
  and H under ALFS: PROVED (§6, lines 667–703; table line 894). This
  replaces "its transfer to ALFS is not yet checked" in the ldp line.
  OPEN: `R=2` or other δ_t (line 900), a bound that pays ρ once (line
  904), a checked mixed ALFS Lean theorem (line 905).
- Status: 2026-09-28 (r159) — under ALFS (spec c7c41a43, admitted vote
  merge): the healing steps hold (r159 §1, lines 105–131), and the spec
  states `B′ = B−2L+6Δ` = 996Δ as its healing claim (spec lines 1448–1451;
  local healing, lines 1452–1456). The δ_t scope is `δ_t = 2R`, `R ≥ 3`
  (lines 1356–1361).
- Status: 2026-09-28 (r160) — under ALFS (spec 1c6952b6, receipt premise):
  HOLDS. The uniform bounds 1004Δ and 996Δ and local healing by
  `q_(s*)+G+5Δ` keep their constants (r160 §7: "redteam §6 Theorem H",
  "redteam §7 U, U′, H′", "H12 H′, Corollary F, bounds", lines 685–688
  and 723–724). Proof steps that NEED-CHANGE, with the same conclusion:
  r158 §4 exact service and r156 §5.1 service (equal scores, not equal
  vote sets, r160 §4.3; lines 669–670 and 679) and H12 FT (its literal
  "each vote is in x's late pool" FAILS by N1; r160 §4.2 proves its
  conclusions; lines 717–718).
- Status: 2026-09-28 (r161) — under ALFS (spec bd942ca0, filtered base):
  HOLDS. The bounds 1004Δ and 996Δ and local healing by
  `q_(s*)+G+5Δ` keep their constants, with `a ≤ f` and the other
  Recovery premises (r161 §6.4, lines 629–668; spec lines 1604–1612).
  F-origin assignments to S need one extra case in the "S has a genuine
  gate origin" lemma (r161 lines 640–644).
- Note (2026-09-29; current use): `ap.headReachesLo.v5` is WITHDRAWN for current
  use. The citations above are history. A current use of this entry
  reads them as §9, "Current reading of withdrawn ids".


### `fj.healedUnif.v1` — uniform bound under effective N1

- Variant `fj`. Source r151 §8, lines 692–698. File `fj-theorem-h.md`, sha256
  `16b69dba55d889b9ae20dd55b228cfd83ad22037d796c6219cdb65831718bba3`.
- Hypotheses: `fj.rise.movingF.v1` (OPEN); the local clause of
  `fj.healed.v1`.
- Statement (pinned):

> _fj-theorem-h.md, lines 692–698:_
>
> The **PROVED conditional** uniform expression is
>
> ```text
> effective (L) with λ ⇒ B_eff(λ)=3P+6(λ+4Δ)+δ_H.
> ```
>
> Its use with `λ=ρ+2σ` as a bound from execution premises alone is OPEN.

- Status: 2026-09-28 — OPEN as a bound from the execution premises
  alone; the implication is PROVED (r151 claim table lines 26–27).
  Example with `λ = ρ+2σ`: 1292Δ, conditional (r151 line 708).
- Status: 2026-09-28 (r153) — the uniform bound is REFUTED under the
  current rules (r153a line 30: no finite M-independent healing or
  arrival bound, PROVED; r153 line 27). The implication stays PROVED; its
  premise, effective (L), fails (`fj.rise.movingF.v1`). Under FV (§8) the
  restored uniform bound is SKETCH (r153a line 43).
- Status: 2026-09-28 (ldp) — under ALFS (spec 183f2c40): effective (L) with
  `λ = ρ+2σ` in the DC form is PROVED (paper) (C3, ldp lines 57 and
  661–675), and the uniform bound `3P+6(λ+4Δ)+δ_H` = 1292Δ is PROVED
  (paper) (C4, ldp lines 58 and 677–693); 1004Δ (`fj.healed.v1`) is the
  smaller bound. It imports r156 §§4–7, r151 Theorems N/H and r152 FF1–FF7 as paper
  results, not independently checked (ldp lines 68–71 and 527–531). The REFUTED lines for the old spec stay.
- Status: 2026-09-28 (r158) — under ALFS, independently checked by r158:
  C3 (effective (L), `λ = ρ+2σ`) is PROVED after the witness repair W, and
  C4 (1292Δ) is PROVED (r158 table lines 641–642; §4, lines 429–558).
  1004Δ and 996Δ (`fj.healed.v1`) are smaller.
- Status: 2026-09-28 (r159) — under ALFS (spec c7c41a43): C3 and C4
  hold with the admitted merge (r159 table lines 92–94).
- Status: 2026-09-28 (r160) — under ALFS (spec 1c6952b6, receipt premise):
  HOLDS. C3 and C4 keep their constants (r160 lines 705–706).
- Status: 2026-09-28 (r161) — under ALFS (spec bd942ca0, filtered base):
  HOLDS. C3 and C4 (1292Δ) HOLD (r161 §6.3, lines 608–609).

### `fj.healedAtQ.v1` — full healing already at `q_(s*)`

- Variant `fj`. Source r151 §3.3 and §7.3, lines 241–242 and 668–669. File
  `fj-theorem-h.md`, sha256
  `16b69dba55d889b9ae20dd55b228cfd83ad22037d796c6219cdb65831718bba3`.
- Statement (pinned):

> _fj-theorem-h.md, lines 241–242 (excerpt; line breaks reflowed):_
>
> Full healing of arbitrary S tips exactly at q_b is still OPEN.

> _fj-theorem-h.md, lines 668–669 (excerpt; line breaks reflowed):_
>
> Immediate full healing at q_b is not established by this argument.

- Status: 2026-09-28 — OPEN (r151 claim table line 33).
- Status: 2026-09-28 (h12) — REFUTED with R1 views (the old spec):
  an exact reachable execution with `n=7, a=2, k=13, G=8Δ` has an honest S
  reorganization at `q_(s*)+G+5Δ` (h12 lines 6–10, 43–45). Not checked
  under ALFS.
- Status: 2026-09-28 (r158) — under ALFS (spec 183f2c40), independently
  checked by r158: REFUTED. The h12 §6 execution survives the view change:
  an honest S changes from C14 to the conflicting P18 at
  `1248 = q_(s*)+G+5Δ` (r158 §3.4, lines 404–427; table line 898). Local
  full healing by `q_(s*)+G+5Δ` transfers to ALFS (lines 788–791). If
  `2τ−2 ≤ n−a`, full healing starts at `d_(s*+1) = q_(s*)+5Δ` (lines
  797–798). r158 does not establish tightness for k=2 (lines 426–427) or
  an optimal bound for small L (line 800).
- Status: 2026-09-28 (r159) — under ALFS (spec c7c41a43): REFUTED; the
  spec cites the r158 check (spec lines 1457–1459). The corollary
  (healing at `q_(s*)+5Δ` when `2τ−2 ≤ n−a`) holds with the admitted
  merge (r159 lines 128–129).
- Status: 2026-09-28 (r160) — under ALFS (spec 1c6952b6, receipt premise):
  REFUTED, unchanged: a relay edit does not change a prior refutation
  (r160 lines 650–653). The corollary at `q_(s*)+5Δ` HOLDS (r160
  lines 723–724).
- Status: 2026-09-28 (r161) — under ALFS (spec bd942ca0, filtered base):
  REFUTED, unchanged (spec lines 1613–1615). r161 makes no claim of
  healing at the reset itself (r161 lines 666–668).

## 5. Composite entries (`Kit.Compose`, `SimplexFG.nj`)

The first three entries (added 2026-09-28) are variant `both`. They are
the run parts of the f1 splits (§8).

### `comp.provenance.v1` — each honest-containing QC has an honest-supported source

- Variant `both`. Sources: r146 §3.1, lines 244–247 (file
  `fgsa-adjudicate.md`, sha256
  `0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017`); r148
  §5 F7, lines 400–403 (file `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`). Rule
  source: r143 §3.1, lines 226–237 (pinned in `ap.honestSourced.v2`).
- Hypotheses: `fg.provenance.v2`; `ap.honestSourced.v2` (the Simplex
  source rule: the row source is the signer's `C_fg`, a member of
  `FastWrite_i[s]`); `ap.fastSupport.v1`.
- Statement (registry): every target, progress or finality QC contains an
  honest row (`fg.provenance.v2`; for a finality QC, through its earlier
  justified target). The source C of an honest height row is the signer's
  `C_fg`, so C is a successful fast write at the signer, and C has an
  honest supporter (`ap.fastSupport.v1`). The row's entry T satisfies
  `T ⪯ C`. Thus every QC with an honest row has an honest-supported
  source.
- Statement (pinned):

> _fgsa-adjudicate.md, lines 244–247:_
>
> Every progress or target QC contains an honest height row since `q_F>a`.
> Its entry T is a prefix of its successful fast source C. Each such C
> has an honest supporter since `τ>a`. Finality names an already justified
> entry and thus has this earlier target origin.

> _fj-redteam.md, lines 400–403:_
>
> Every target or progress QC contains an honest row because q>a. Each
> honest height row has a successful fresh fast source, with τ>a surviving
> supporters. Its named entry is an ancestor of that source. Finality has
> an earlier justified target origin.

- Status: 2026-09-28 — PROVED (FG-SA; r146 §3.1; r148 F7).
- Note: this is the Simplex-policy part of the SUPERSEDED
  `fg.provenance.v1`. It holds for the Simplex source rule only, not for
  every policy σ (§0).

### `comp.settle.v1` — relay and freeze settle store objects into duty views

- Variant `both`. Sources: bp §4.2 item 1, lines 385–390 (file
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`); r149
  §3, lines 305–315 (file `fgsa-conditional-close.md`, sha256
  `1ea1ccc5c944335b7e7793afe2c6675a056762e35eeaeee13ec1f6066460a902`); r148
  §8 F12, lines 763–764 and 776–777 (file `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`).
- Hypotheses: `env.r149` (strict Δ delivery and accepted-object return
  relay after GST); R1 duty views (the HEAD at `v_s` freezes at
  `z_(s−1) = t_s − Δ = v_s − 2Δ`); the object is held by an honest store at
  a time `w ≥ GST`.
- Statement (registry): let an honest store hold an object at `w ≥ GST`.
  The object is in every honest full view from `w+Δ` and in every honest
  HEAD view at a HEAD time `≥ w+θ`, θ = 4Δ. Views are subsets of stores,
  and stores only grow. Consequences: (1) if the honest frontier first
  equals m at t_m and rises at t_up, then `H_d = m` at every honest duty in
  `[t_m+θ, t_up)`; (2) an evidence object first held by an honest store at
  t_e is in no duty view before t_e and in every duty view from
  `max(t_e, GST)+θ`. r148 uses the larger margin P ≥ θ.
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 385–390:_
>
> 1. **Settling.** Every object that an honest store holds at t is in every
>    honest full view from t+Δ, and in every honest HEAD view at a time
>    ≥ t+θ. Proof: relay gives receipt by t+Δ at every honest reader. A HEAD
>    at `v_s ≥ t+4Δ` has freeze `t_s−Δ ≥ t+2Δ`. Since views are subsets of
>    stores, `H_d ≤ m` while the frontier is m. Thus `H_d = m` at every
>    honest duty in `[t_m+θ, ·)` until the frontier rises.

> _fgsa-conditional-close.md, lines 305–315:_
>
> Suppose a controlling object is accepted by an honest reader at time w.
> Strict relay delivers it to every honest full view before `w+Δ`. A HEAD
> at time v freezes at `v−2Δ`. If `v ≥ w+4Δ`, that freeze is at least
> `w+2Δ`, after delivery. Its frozen view contains the complete object.
> The retained F basis supplies the required accepted-control evidence.
>
> This proves settling at every duty after `w+4Δ`. Under the strict cutoff
> convention, `3Δ` also suffices: a freeze at `w+Δ` is after all strict
> receipts. This file uses only **4Δ** in bounds. It avoids a change of
> constant when a statement is read with a non-strict delivery endpoint.
> It is a sufficient constant, not a lower bound.

> _fj-redteam.md, lines 763–764 (excerpt; line breaks reflowed):_
>
> After one P margin, a maximizing witness is in every duty view.

> _fj-redteam.md, lines 776–777 (excerpt; line breaks reflowed):_
>
> Within P of each event, accepted-object relay and a later freeze put the
> relevant evidence in every view.

- Status: 2026-09-28 — PROVED (FG-SA; bp §4.2 item 1; r149 §3, M4).
- Status: 2026-09-28 (r160) — the pinned text uses accepted-object relay.
  r160 does not audit this R1-view source (bp §4.2, r149). Its ALFS
  counterparts HOLD under DC's receipt premise: event settlement relays
  admitted certificate carriers and needs no acceptance of ancient
  standalone rows (r160 lines 673–674 and 699–700; §7, lines 741–747).
- Note: this is the run part of the SUPERSEDED `fg.oneBullet.v1` and
  `fj.twoChanges.v1`. It is a statement about delivery and R1 views, not
  about FG rules. For an object held only before GST, the return-relay
  premise gives the same bound from GST.

### `comp.cut.v1` — the DC cut `u_0` and its maximum M

- Variant `both`. Sources: r144 §2.2, lines 168–193 (file `fgsa-no-nj.md`,
  sha256 `1eaf728ffc4d56cc54fbccf581a8dffe457da02b96bd59cedb012bbf5ee1e03a`);
  bp §1.2, lines 138–140 (file `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`).
- Lean plan: DC-fj module, item 4 partial (FG module, 2026-09-28; see the
  dated line below).
- Hypotheses: `fg.causalCap.core.v1`; the action schedule
  `a_r = T_r+6Δ`, `T_r = rP`; for clause 4, `comp.settle.v1`.
- Statement (registry):
  1. Definition: r_G = the first action round with `a_(r_G) ≥ GST`;
     `u_0 = a_(r_G+2)`, with its inclusive event prefix; M = the honest
     archival frontier at `u_0`.
  2. `GST+2P ≤ u_0 < GST+3P`.
  3. Every honest height row emitted in the prefix has height at most M.
     A carrier whose honest rows all come from the prefix has height at
     most M+1 and justified height at most M (`fg.causalCap.core.v1` with
     this M).
  4. At a duty with `H_V ≥ M+2`, an old-only justification has
     `j ≤ M < H_V−1`, so it is not the active root. H_V is the duty view's
     own maximum: an archival rise acts only after it reaches the view
     (`comp.settle.v1`).
- Statement (pinned):

> _fgsa-no-nj.md, lines 168–193:_
>
> Use exactly the requested cut:
>
> ```text
> r_G = first action round at or after GST;
> u0  = a_(r_G+2), inclusive event prefix;
> M   = honest archival frontier at u0.
> ```
>
> Every honest height row in that prefix has height at most M, because its
> source was already in its signer's store. Every crossing has an honest
> row, since `q_F>a`. Hence a carrier whose height evidence uses only such
> old honest rows has height at most M+1, and its justified height is at
> most M. Faulty rows can be new; without a new honest row they cannot
> cross the next height. This includes a newly constructed carrier with
> old target rows. See [fg-frame-recovery §§2.3–2.4](fg-frame-recovery.md)
> and [WeakHeightBounds][height-bound].
>
> At a duty with `H_V≥M+2`, an old-only justification satisfies
>
> ```text
> j_old≤M < H_V−1,
> ```
>
> so it cannot be the active root. This is a duty-view statement. An
> archival rise must first reach the frozen HEAD view. Allow the R1 relay
> and freeze margin; do not substitute an unseen archival maximum.

> _fgsa-healing-blueprint.md, lines 138–140:_
>
> Let r_G be the first action round with `a_(r_G) ≥ GST`. The DC cut is the
> inclusive event prefix at `u_0 = a_(r_G+2)`. Then `GST+2P ≤ u_0 < GST+3P`.
> Let M be the honest archival frontier at u_0. As in DC,

- Status: 2026-09-28 — PROVED (r144 claims N1 and N2; r147 §6; bp §1.2).
- Status: 2026-09-28 (FG module, `lean/available-chain` main `64651ad`) —
  LEAN for the arithmetic of item 4 only; the entry stays PROVED (paper).
  `causalCap_notRoot` (`AvailableChainKitFG/CausalCap.lean`, lines 53–64,
  verified in the source) proves: if every honest row on the chain of B
  whose height pair is a vote has height at most M (`hrows`), and the faulty weight
  is below q, then `h_j + 1 ≠ H` for every `H ≥ M+2`. Not in Lean: that M
  is the frontier at `u_0` and that an old-only justification satisfies
  `hrows` (run facts), and the link "active root ⇔ `H = h_j+1`"
  (`Controls.rootIsJ`). Items 1–3 are run facts or external (the carrier
  bound of item 3 is `fg.causalCap.core.v1` (b), `causalCap`); item 4's
  view maximum is `comp.settle.v1`. `AvailableChainKitFG/Pins.lean`,
  lines 283–300, pins this entry with these clause kinds.
- Note: this is the run part of the SUPERSEDED `fg.causalCap.v1`. The FJ
  entries call this M "M0" (r148) or "M" (r151). The old-source cap of
  `env.r148` (μ in `fj.reset.v1`) is at most this M.

### `comp.rise.fixedF.v1` — height rise under literal N1

- Variant `nj`. Source r147 §5, lines 409–429 (statement); proof lines
  435–523. File `fgsa-conditional.md`, sha256
  `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Hypotheses (audit W02): the AP service facts `ap.repair.fixedF.v1`,
  `ap.source.v1`, `ap.rowService.v1` and `ap.carrierKeep.v2`, specialized
  to the Simplex policy; the Simplex client and transition: the lock
  cases (r147 lines 451–483), `fg.provenance.v2`, `ap.fastSupport.v1`,
  `comp.provenance.v1`, row folding at the exact entry, maturity and
  consumption (r147 lines 485–507); `env.r147` (premises 4 and 5);
  `fg.N1.v1` with F and Z fixed on `[u,min(t_up,u+B_static))`; `u ≥ GST`.
- Note (2026-09-28; §0 rule (a)): `fg.provenance.v1` was replaced by
  `fg.provenance.v2`, `ap.fastSupport.v1` and `comp.provenance.v1`.
- Statement (pinned):

> _fgsa-conditional.md, lines 409–429:_
>
> **Exact statement (L).** Under §1, let `u≥GST` and let the honest
> archival frontier at u be m. Let t_up be the first later time at which
> that frontier exceeds m, or infinity if there is none. Suppose fixed
> F and Z make N1 hold on `[u,min(t_up,u+B_static))`, and suppose the
> execution premises and horizon are available through `u+B_static`.
> Then `t_up≤u+B_static`; that is, a rise above m occurs by
>
> ```text
> u+B_static = u+ρ+2σ,
> ρ = 2L+G+8Δ,     σ = (g+3)P+G+6Δ.
> ```
>
> If no earlier rise ends the interval, base repair completes by u+ρ.
> Every later honest proposal whose full service interval remains in
> that interval receives exact honest HEAD service and a fresh fast
> write at all honest readers at its +6Δ gate. A selected honest
> opening supplies `C_fg` and a nonempty matching target or timeout row
> at every honest validator. Its next two honest slot proposers carry
> the branch and fold the rows. At most two such production steps are
> needed to exceed m. Statements about duties after the first rise are
> not part of (L).

- Status: 2026-09-28 — PROVED (FG-SA; r147 §5). r149 §4.4 (lines
  443–445) confirms that the literal-N1 form stays PROVED.
- Note: this is the statement of the withdrawn `ap.L.fixedF.v1`, refiled
  in `Kit.Compose`. It states FG progress, so it holds for the Simplex
  policy only.

### `comp.rise.movingF.v1` — height rise under effective N1

- Variant `nj`. Source r149 §4.4, lines 436–441. File
  `fgsa-conditional-close.md`, sha256
  `1ea1ccc5c944335b7e7793afe2c6675a056762e35eeaeee13ec1f6066460a902`.
- Hypotheses: `ap.repair.movingF.v1` (OPEN), `ap.source.v1`,
  `ap.rowService.v1`, `ap.carrierKeep.v2`, the Simplex client and
  transition as in `comp.rise.fixedF.v1`; `env.r149`; `fg.N1eff.v1` on
  `[u,u+λ]`; `u ≥ GST`.
- Statement (pinned):

> _fgsa-conditional-close.md, lines 436–441:_
>
> > **(L), OPEN under effective N1.** Set `u_L=GST` and
> > `λ=ρ+2σ`, where `σ=(g+3)P+G+6Δ`. For every `u≥u_L`, m, and Zhat,
> > if the honest archival frontier at u is m and
> > `N1(u,u+λ;m,Zhat)` holds, then the frontier at `u+λ` exceeds m.
> > All execution, proposer, row-inclusion, and horizon premises in §1
> > apply. The initial reachable base state at u is arbitrary.

- Status: 2026-09-28 — OPEN (r149 claim table line 32; r150 claim table
  line 25). The proposed M1 argument is SKETCH (r149 line 33).
- Status: 2026-09-28 (r153a) — OPEN, at risk (r153a lines 44 and
  499–505). The FJ form is REFUTED (`fj.rise.movingF.v1`).
- Status: 2026-09-28 (r153b) — the at-risk mark is withdrawn: r153b §C
  refutes the NJ transfer (C5) by an integer check on r153's numbers
  (r153b lines 45–46, 53–55, 900–963; the NJ consequence is lines
  956–961). The entry returns to its status before dd2f5e7: OPEN. The FJ form stays REFUTED
  (`fj.rise.movingF.v1`).
- Notes: this is the statement of the withdrawn `ap.L.movingF.v1`,
  refiled in `Kit.Compose`. The only missing input is
  `ap.repair.movingF.v1` (r149 lines 443–450); `ap.reach.v1` suffices for
  it (r150 §5). bp marks the same claim H16 SKETCH (bp §10, lines
  1086–1101); r149 §4.3 shows that the bp argument misses one case.

### `comp.theoremN.v1` — no FG interference for ever from `q_(s*)`

- Variant `nj`. Sources: bp §7.1, §7.2 and §7.4, lines 520–522, 535–541 and
  605–606 (file `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`); r150
  §2, lines 131–133 (file `fgsa-theorem-h.md`, sha256
  `8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`).
- Hypotheses: `env.r150`; `fg.baseSel.nj.v1`; `ap.S.v2`; `ap.Sslow.v1`;
  `fg.base.finalized.v1` (finalized arm); `fg.provenance.v2`;
  `ap.fastSupport.v1`; `comp.provenance.v1`; `fg.causalCap.core.v1`;
  `comp.cut.v1`. No service entry is used (r150 lines 135–136).
- Note (2026-09-28; §0 rule (a)): `fg.provenance.v1` was replaced by
  `fg.provenance.v2`, `ap.fastSupport.v1` and `comp.provenance.v1`;
  `fg.causalCap.v1` was replaced by `fg.causalCap.core.v1` and
  `comp.cut.v1`.
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 520–522:_
>
> Let 𝒫 be the set of all fast bodies at labels s ≥ s*, and all slow bodies
> at labels s whose windows lie in `[s*, ∞)`. For B∈𝒫 at label s put
> `q(B) = q_s`. The FG sources of all honest rows at rounds ≥ r* are in 𝒫.

> _fgsa-healing-blueprint.md, lines 535–541:_
>
> For a time t let IH(t) be the conjunction of:
>
> - (i) (N2)(𝒫;t′) for every t′<t;
> - (ii) in the NJ arm, no honest target row at height x is emitted before t.
>
> (i) is a statement about duties strictly before t. So IH(t) never uses a
> conclusion at t itself.

> _fgsa-healing-blueprint.md, lines 605–606:_
>
> **Theorem N.** For every t, IH(t) holds. In particular (N2)(𝒫;t) holds
> for every t.

> _fgsa-theorem-h.md, lines 131–133:_
>
> **Theorem N — PROVED.** Every B in 𝒫 is kept at every honest duty from
> its transfer time. In the NJ outcome no honest target at x is ever
> emitted. Therefore all three source conclusions above hold forever.

- Status: 2026-09-28 — PROVED (FG-SA; r150 claim table line 20). bp has
  PROVED* from (S) and (S_slow) (H7); r149 proves both.

### `comp.fgHealed.v1` — FG-healed from `q_(s*)`

- Variant `nj`. Sources: bp §7.1 and §7.7, lines 520–522, 684–693 and
  695–696 (file `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`); r150
  §2, lines 116–118 and 154–155 (file `fgsa-theorem-h.md`, sha256
  `8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`).
- Protected set (audit W05): 𝒫 = ALL fast bodies at labels ≥ s* and ALL slow
  bodies whose window lies in `[s*,∞)` (bp §7.1). It is not restricted to
  row sources.
- Hypotheses: `comp.theoremN.v1`; `ap.S.v2` (fast bodies, PROVED, r149);
  `ap.Sslow.v1` (slow bodies, PROVED, r149).
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 520–522:_
>
> Let 𝒫 be the set of all fast bodies at labels s ≥ s*, and all slow bodies
> at labels s whose windows lie in `[s*, ∞)`. For B∈𝒫 at label s put
> `q(B) = q_s`. The FG sources of all honest rows at rounds ≥ r* are in 𝒫.

> _fgsa-healing-blueprint.md, lines 684–693:_
>
> **Definition.** The run is *FG-healed from q_(s*)* iff (N2)(𝒫;t) holds
> for every t, and every B∈𝒫 at label s is in every honest HEAD from q_s
> and in every honest S from `t_s+10Δ`. The run is *healed from t_h* iff it
> is FG-healed and, for every t ≥ t_h:
>
> - (A) all honest S values at t lie on one chain;
> - (B) every honest S at a time t′ ≥ t extends its value at t (monotone,
>   no reorganization), and `F ⪯ S`, so `available = S`;
> - (C) every honest proposal at a slot u with t_u ≥ t_h is in every honest
>   S by `t_u+6Δ`.

> _fgsa-healing-blueprint.md, lines 695–696:_
>
> **Theorem H-FG — PROVED from (S), (S_slow).** The run is FG-healed from
> `q_(s*)`. This is Theorem N with N-a.

> _fgsa-theorem-h.md, lines 154–155:_
>
> Consequently the run is FG-healed from q_s*. This proves preservation
> of the protected bodies; full healing of arbitrary S tips needs §4.

- Status: 2026-09-28 — PROVED (FG-SA; r150 §2). bp has PROVED* (H10).
- Note: the row-source form `ap.S.v1` does not give this protected set. bp
  H17 ("H-FG composes with r147's (S)") concerns a row-source reading; this
  entry does not cite it (audit W05).

### `comp.healed.v1` — full healing (Theorem H) and the proved bound

- Variant `nj`. Source r150 §3.4, §4.5 and §6.4, lines 248–251, 374–392 and
  546–569. File `fgsa-theorem-h.md`, sha256
  `8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`.
- Hypotheses: `env.r150`; `fg.baseSel.nj.v1`; `comp.theoremN.v1`;
  `comp.fgHealed.v1`; `ap.S.v2`; `ap.Sslow.v1`; `ap.Xplus.v1`; for the
  global clause also the literal-N1 arrival count (`comp.rise.fixedF.v1`,
  `fg.oneBullet.core.v1`, `comp.settle.v1`, the r147 §6 counts; r150 §6.1,
  bp §9.4) and `comp.arrivalNJ.v1`. It does not use `ap.X.v1`,
  `ap.repair.movingF.v1` or `comp.rise.movingF.v1`.
- Note (2026-09-28; §0 rule (a)): `fg.oneBullet.v1` was replaced by
  `fg.oneBullet.core.v1` and `comp.settle.v1`.
- Clauses: (local) Theorem H, r150 §4.5, lines 374–392: the run is healed
  from `t_h ≤ q_(s*)+2L+G−Δ`; it needs none of the arrival inputs.
  (global) r150 §6.4, lines 546–569: `t_h < GST+B_proved`. The global
  clause does not cite `comp.healedLit.v1` or `comp.healedUnif.v1`; those
  entries cite only the local clause, so there is no cycle.
- (X+) discharge (audit W03): at each call of `ap.Xplus.v1`, that is, at
  every honest proposal with slot `u ≥ ℓ+1`, `ℓ = s*+2k−1`, this entry
  proves x0 (r150 §3.2, lines 187–202: every proposal-time lease is in 𝒫 and
  on the ordinary walk), x1 (lines 204–206), x2 and x3 (r150 §3.3, lines
  208–240: T = C* if `m_u = x+1`, else the source body of an honest row in
  the last crossing of a maximizing carrier).
- Statement (pinned):

> _fgsa-theorem-h.md, lines 248–251:_
>
> **Service after the boundary — PROVED.** At every honest proposal
> with `u≥ℓ+1`, x0, x1, x2, and x3 hold. The delivery and declared-view
> premises hold by §1. Hence r149's (X+) gives exact P HEADs at v_u
> and `P⪯S_i(d_u)` at every honest reader.

> _fgsa-theorem-h.md, lines 374–392:_
>
> **Theorem H — PROVED.** Under §1 and the actual reset of §1, the run
> is FG-healed from q_s*. There is a repair gate `t_h=d_u` such that,
> for all times from t_h onward, all honest S values lie on one chain,
> each honest S is monotone, every accepted honest F is a prefix of
> every honest S, and every honest proposal emitted from t_h onward
> is in every honest S within 6Δ.
>
> The bound is
>
> ```text
> t_h ≤ t_(s*) + 2L+G+4Δ
>     = q_(s*) + 2L+G−Δ
>     = a_(r*) + 2L+G−2Δ.
> ```
>
> Proof: choose `t_ℓ<t_u≤t_ℓ+G`, use §3.4 at d_u, and apply §§4.1–4.4.
> Then `d_u≤t_ℓ+G+6Δ=t_(s*)+2L+G+4Δ`. The strict proposal choice
> costs no additional G or Δ: its next grid point already exceeds
> E_old. All conclusions also hold from the displayed upper bound. ∎

> _fgsa-theorem-h.md, lines 546–569:_
>
> Under exactly the reachable-execution, count, delivery, recurrence,
> row-inclusion, and horizon premises in §1, and using r146's proved
> arrival result as supplied, define
>
> ```text
> B_proved = min(B_lit, B_NJ,H)
>          = min(3P+[2N+H+2−f_0](ρ+2σ+4Δ), P[3+Nβ])
>            + 2L+G−2Δ.
> ```
>
> There exists `t_h<GST+B_proved` from which all honest S values lie
> on one chain, every honest S is monotone, every honest proposal has
> 6Δ inclusion at all honest readers, and every accepted honest F is
> a prefix of every honest S. Hence `available=S` throughout this
> suffix. The construction allows either the NJ or the named finalized
> outcome of the DC consumer. The uniform proved choice is B_NJ,H;
> the supplied B_base is also valid and is larger by `P+10Δ`.
>
> At the actual reset the local bound, independent of the chosen
> arrival proof, is
>
> ```text
> t_h ≤ q_(s*) + 2L+G−Δ.
> ```

- Status: 2026-09-28 — PROVED (FG-SA; r150 claim table lines 21–23).
- Status: 2026-09-28 (r153a) — (local) PROVED, unchanged (r150 §4.5).
  (global) OPEN, at risk: `B_proved` is a minimum that contains the
  `B_NJ,H` arm (5816Δ), which uses `comp.arrivalNJ.v1` (r153a lines 495
  and 499–505). The `B_lit` arm is `comp.healedLit.v1`; r153a does not
  re-adjudicate the NJ literal bound.
- Status: 2026-09-28 (r153b) — the at-risk mark is withdrawn: r153b §C
  refutes the NJ transfer (C5) by an integer check on r153's numbers
  (r153b lines 45–46, 53–55, 900–963; the NJ consequence is lines
  956–961). The entry returns to its status before dd2f5e7 for the global clause: PROVED (FG-SA). The local clause is
  unchanged (PROVED).
- Bounds: local `t_h ≤ q_(s*)+2L+G−Δ`. Global
  `GST + min{B_lit, B_NJ + 2L+G−2Δ}`. Example
  (`Δ=1, R=3, k=2, G=8, g=3, D=2, K=5`): `B_NJ,H = 5816Δ`; `B_lit = 7472Δ`
  for `M=1, H=10, f_0=0`; the minimum is 5816Δ (r150 §6.3, lines 528–541).

### `comp.healedLit.v1` — fixed-F (literal N1) arrival and bound

- Variant `nj`. Sources: r150 §6.1, lines 464–481 (file `fgsa-theorem-h.md`,
  sha256
  `8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`); bp
  §9.4, lines 1028–1047 (file `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`).
- Hypotheses: `comp.rise.fixedF.v1`; `fg.oneBullet.core.v1`;
  `comp.settle.v1`; the r147 §6 counts; the local Theorem H clause of
  `comp.healed.v1` (r150 §4.5). N = D+K+5, W = λ+4Δ, λ = ρ+2σ.
- Note (2026-09-28; §0 rule (a)): `fg.oneBullet.v1` was replaced by
  `fg.oneBullet.core.v1` and `comp.settle.v1`.
- Statement (pinned):

> _fgsa-theorem-h.md, lines 464–481:_
>
> r147's supplied literal-N1 theorem has `λ=ρ+2σ`. At each frontier
> there is at most one top-J event. Count lower F advances separately.
> Use the blueprint §9.4 count, with f_0 the least honest finalized
> height at u_0. Before reaching H+3 their total count is at most
> `H+2−f_0`. Settling costs θ=4Δ for each counted event.
>
> The arrival deadline and Theorem H give the **PROVED** bound
>
> ```text
> B_lit = 3P + [2N + H+2−f_0]W + δ_H;
> t_h < GST+B_lit.
>
> B_lit ≤ 3P + [3N+M]W + δ_H.
> ```
>
> This proof uses literal (L), the counted interruptions, Theorem N,
> and §§3–4. It has no use of original (X) or effective (L). Thus the
> old service qualification on this composition is removed.

> _fgsa-healing-blueprint.md, lines 1028–1047:_
>
> r147's N1 fixes F, Z, and H_d. Every F advance then interrupts the
> static interval, and r147 §6 charges a full `W = 3Δ+B_static` after
> each counted event. Put `λ = λ_147` and use θ=4Δ ≥ 3Δ. At frontier m
> the number of interruptions is at most `1 + n_F(m)`, where n_F(m) counts
> new finalized heights that first appear at frontier m. The case split
> of Theorem HP then gives at most `(2+n_F(m))(λ+θ)` per level. The
> accepted F only increases, and it stays ≤ H+1 before the frontier
> reaches H+3. Thus `Σ_m n_F(m) ≤ H+2−f_0`, with f_0 the least honest h_F
> at u_0, and
>
> ```text
> T_arr  ≤ u_0 + [2(D+K+5) + (H+2−f_0)](λ+θ)
>        ≤ u_0 + [3(D+K+5) + M](λ+θ);
> t_heal < GST + 3P + [3(D+K+5) + M](λ+θ) + 2L + G − 2Δ.
> ```
>
> This bound depends on the initial frontier M, which the pre-GST adversary
> controls. r147's per-level count `N ≤ m−1−f0+ε_J` is the same bound
> before summation. The trunk lemma of §4.1 removes the M term, provided
> that (L) holds under the effective filter (H16, §10).

- Status: 2026-09-28 — PROVED (FG-SA; r150 claim table line 26). bp has
  PROVED* (H14).
- Correction (audit W07): the extra term over the uniform `2N(λ+θ)` is
  `(H+2−f_0)(λ+θ)`, conservatively `(3N+M)(λ+θ)` in total, not `M(λ+θ)`.
  Example (`Δ=1, R=3, k=2, G=8, g=3, D=2, K=5`): 7472Δ for
  `M=1, H=10, f_0=0`; 8502Δ for `M=10, H=15, f_0=0` (bp §9.2 table; r150
  lines 540–541). The conservative form gives 7678Δ for `M=1`. The v1
  reading `2N(λ+θ) + M(λ+θ)` gives 5206Δ and is wrong.

### `comp.arrivalNJ.v1` — supplied arrival bound `B_NJ`

- Variant `nj`. Source r146 §5.1, lines 551–581. File `fgsa-adjudicate.md`,
  sha256 `0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017`.
- Statement (pinned):

> _fgsa-adjudicate.md, lines 551–581:_
>
> One attempt costs at most
>
> ```text
> P + ρ + P + (3g+6)P ≤ [ceil_div(ρ,P)+3g+8]P.
> ```
>
> A top-J event can interrupt once. Two complete attempts suffice. Set
>
> ```text
> β = 2*ceil_div(ρ,P)+6g+16.
> ```
>
> Take the actual inclusive causal cut at `a_(r_G+2)`, where r_G is the
> first action round at or after GST. Let M be its honest archival maximum.
> Set `H=K*ceil_div(M+D+3,K)`. Then `H+3≤M+D+K+5`.
> Each pre-cut row has height at most M; an old-only crossing can add at
> most one. The unchanged exact-entry/finality consumer in
> `HeightRegimeNamedBaseDeadline` chooses the actual first crossing and
> its actual finality cap. It yields either the uniformly NJ prefix at H
> or a named finalized checkpoint of height `M<x≤H+1`.
>
> With β as the replacement producer, a sufficient arrival budget is
>
> ```text
> B_NJ = P*[3+(D+K+5)*β].
> ```
>
> This is an environment-only paper bound. Source absence cannot deadlock
> it: either the frontier rises, or a long enough retained interval lets
> the base produce the required fast sources. No global base handoff is
> assumed before the NJ search.

- Status: 2026-09-28 — PROVED (FG-SA; r146 claim 3b). Example: 5796Δ. r150
  §6.2 (lines 497–501) uses it as the arrival bound of `a_(r*)`.
- Status: 2026-09-28 (r153a) — OPEN, at risk (r153a lines 44, 262–268
  and 499–505: fgsa-adjudicate §5.1 uses "A finalization below m−1 lies
  below every band witness"; the same false step is at fgsa-adjudicate
  lines 322–325 and fgsa-fast line 704). Do not cite `B_NJ` or r150's
  uniform numbers until this is checked. FV (§8) applies to the NJ
  variant without change.
- Status: 2026-09-28 (r153b) — the at-risk mark is withdrawn: r153b §C
  refutes the NJ transfer (C5) by an integer check on r153's numbers
  (r153b lines 45–46, 53–55, 900–963; the NJ consequence is lines
  956–961). The entry returns to its status before dd2f5e7: PROVED (FG-SA).

### `comp.handoffBase.v1` — supplied base handoff `B_base`

- Variant `nj`. Source r146 §5.3, lines 648–657. File `fgsa-adjudicate.md`,
  sha256 `0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017`.
- Statement (pinned):

> _fgsa-adjudicate.md, lines 648–657:_
>
> Paying ρ from this start removes arbitrary older descendant leases.
> An honest repair proposal has a slot later than all old S tips; it
> therefore replaces them, rather than retaining an old strict extension.
> The exact proposal and guard comparison of §3.2 then continues. This
> proves the full safe, monotone available suffix, not only its common
> ancestor. A sufficient handoff bound is
>
> ```text
> B_base = B_NJ+P+ρ.
> ```

- Status: 2026-09-28 — PROVED (FG-SA; r146 claim 3e). Example: 5838Δ.
  `comp.healed.v1` gives the smaller `B_NJ,H = B_base − P − 10Δ` (r150
  §6.2).
- Status: 2026-09-28 (r153a) — OPEN, at risk: `B_base = B_NJ+P+ρ` uses
  `comp.arrivalNJ.v1` (r153a lines 495 and 499–505).
- Status: 2026-09-28 (r153b) — the at-risk mark is withdrawn: r153b §C
  refutes the NJ transfer (C5) by an integer check on r153's numbers
  (r153b lines 45–46, 53–55, 900–963; the NJ consequence is lines
  956–961). The entry returns to its status before dd2f5e7: PROVED (FG-SA).

### `comp.healedUnif.v1` — uniform bound under effective N1

- Variant `nj`. Sources: r150 §6.3, lines 516–526 (file `fgsa-theorem-h.md`,
  sha256
  `8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`); bp
  §9.1, lines 958–967 (file `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`).
- Hypotheses: `comp.rise.movingF.v1` (effective (L), OPEN),
  `fg.oneBullet.core.v1`, `comp.settle.v1` and `fg.trunk.v1` (bp Theorem
  HP and Theorem A, PROVED from (L)); the local Theorem H clause of
  `comp.healed.v1` (r150 §4.5). N = D+K+5, θ = 4Δ.
- Note (2026-09-28; §0 rule (a)): `fg.oneBullet.v1` was replaced by
  `fg.oneBullet.core.v1` and `comp.settle.v1`.
- Statement (pinned):

> _fgsa-theorem-h.md, lines 516–526:_
>
> If effective (L) holds with λ, the blueprint's fixed-height split
> costs `2(λ+4Δ)` per gain. N gains suffice. Theorem H then gives
>
> ```text
> B_eff(λ) = 3P + 2N(λ+4Δ) + δ_H;
> t_h < GST+B_eff(λ).
> ```
>
> The implication is **PROVED**. Its instantiation as a new bound from
> the execution premises alone, with `λ=ρ+2σ`, is **OPEN** because §5
> is open. Neither original (X) nor a lease-only argument closes it.

> _fgsa-healing-blueprint.md, lines 958–967:_
>
> ```text
> θ        = 4Δ
> Λ_lvl    = 2(λ+θ)
> T_arr    = u_0 + (D+K+5)·Λ_lvl                 frontier ≥ H+3
> a_(r*)   < T_arr
> t_heal   = a_(r*) + 2L + G − 2Δ
>
> t_heal   < GST + 3P + 2(D+K+5)(λ+4Δ) + 2L + G − 2Δ.
> FG-healed from q_(s*) < GST + 3P + 2(D+K+5)(λ+4Δ) − Δ.
> ```

- Status: 2026-09-28 — OPEN as a bound from the execution premises alone
  (r150 claim table line 29; r149 claim table line 37). The implication from
  `comp.rise.movingF.v1` is PROVED (r150 claim table line 28). Example with
  `λ = ρ+2σ`: 5000Δ, conditional (r150 lines 528–537).
- Status: 2026-09-28 (r153a) — OPEN, at risk: the NJ variant can have
  the r153 obstruction (r153a lines 44 and 499–505).
- Status: 2026-09-28 (r153b) — the at-risk mark is withdrawn: r153b §C
  refutes the NJ transfer (C5) by an integer check on r153's numbers
  (r153b lines 45–46, 53–55, 900–963; the NJ consequence is lines
  956–961). The entry returns to its status before dd2f5e7: OPEN as a bound from the execution premises alone; the implication
  PROVED.

### `comp.healedAtQ.v1` — full healing already at `q_(s*)` (H12)

- Variant `nj`. Sources: bp claim table H12, line 62 (file
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`); r150
  §7, lines 576–579 (file `fgsa-theorem-h.md`, sha256
  `8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`).
- Statement (pinned):

> _fgsa-healing-blueprint.md, line 62:_
>
> ```text
> │ H12 │ Full healing already at q_s* (no base delay)         │ OPEN    │
> ```

> _fgsa-theorem-h.md, lines 576–579:_
>
> **H12 remains OPEN.** Theorem N proves FG healing at q_s*. Full
> healing of every S tip at that time does not follow. The raw-result
> induction in §4 needs the absence of conflicting unsupported leases
> above C*, which §3.1 establishes later.

- Status: 2026-09-28 — OPEN (r149 §7; r150 §7). The n=7 count stanza is not
  an execution at the actual reset (r149 lines 729–737).

### `comp.finality.v1` — first finality

- Variant `nj`. Sources: r146 §5.4, lines 676–711 (file
  `fgsa-adjudicate.md`, sha256
  `0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017`); bp
  §9.5, lines 1051–1054 (file `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`).
- Statement (pinned):

> _fgsa-adjudicate.md, lines 676–711:_
>
> 1. At the selected honest opening-plus-two-slots window, the separate
>    **current-slot finality head** is the slot-1 proposal, with the
>    required latest justification and permitted finality record.
> 2. Select a usable non-NJ height above the relevant frontier and, for
>    proposal inclusion, above the specified later proposal. Prove the
>    height-rate and NJ-spacing argument despite arbitrary non-opening
>    consumption and delayed old carriers.
> 3. Apply the precise strong recurrence and inclusion window to the
>    chosen target, justification, and finality carriers. Prove that
>    the matching rows remain included or already stored on the parent.
>
> The exact opening source after B_base follows from base service and
> the fast count. Named entry agreement follows from §4. These facts
> remove two parts of I, but they are not the current-slot head equality
> or the complete finality deadline construction.
>
> Opus's `(g+2)P+9Δ` is a proposed deadline from the reset for **some new
> finalization**. Astra's expression includes a **specified honest
> opening selected after base handoff**. These are different guarantees.
> Moreover, first finality need not be at H+1: recovery can leave that
> height before the required proposer window. DC's finality kernel also
> selects a justifiable height above a frontier, not necessarily H+1.
>
> Retain the following conditional arithmetic, with I denoting the three
> remaining timed obligations as well as the proved source clauses:
>
> ```text
> J_I     = (3g+6)P+9Δ
> B_first = B_base+(g+1)P+J_I
>         = B_NJ+ρ+(4g+8)P+9Δ.
> ```
>
> The arithmetic and the quorum/finality transition are PROVED given I.
> The environment-only first-finality claim remains SKETCH. Neither
> Opus's shorter expression nor the larger B_first is an unconditional
> proved finality deadline in this adjudication.

> _fgsa-healing-blueprint.md, lines 1051–1054:_
>
> This file claims no first-finality deadline. After t_heal, Theorem H gives
> exact opening service and one named entry per height. The finality-head
> cone, the choice of a non-NJ height, and the strong recurrence remain the
> three timed obligations of [fgsa-adjudicate §5.4](fgsa-adjudicate.md).

- Status: 2026-09-28 — SKETCH (r146 claim 3g). The arithmetic and the
  quorum/finality transition are PROVED given I. The three timed obligations
  are: the current-slot finality head (`ap.finalityHead.v2`) with its record
  permission (a Simplex client fact), a usable non-NJ height, and the timed
  target, justification and finality carriers under
  StrongMultiProposerRecurrence.
- Status: 2026-09-28 (r153a) — SKETCH, and its arithmetic `B_first`
  uses `B_base` and `B_NJ` (`comp.handoffBase.v1`, `comp.arrivalNJ.v1`),
  which are OPEN, at risk.
- Status: 2026-09-28 (r153b) — the at-risk mark is withdrawn: r153b §C
  refutes the NJ transfer (C5) by an integer check on r153's numbers
  (r153b lines 45–46, 53–55, 900–963; the NJ consequence is lines
  956–961). The entry returns to its status before dd2f5e7: SKETCH. The note on the at-risk
  bounds `B_base` and `B_NJ` is withdrawn.

### `comp.clean.v1` — AP claims carry over in clean and Outage regimes

- Variant `nj`. Source r146 §3.2, lines 359–364 (claims 1a–1c, claim table
  lines 26–28). File `fgsa-adjudicate.md`, sha256
  `0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017`.
- Hypotheses: `ap.armedSafe.v1` specialized to the Simplex policy;
  ArmedRetained B for Outage.
- Statement (pinned):

> _fgsa-adjudicate.md, lines 359–364:_
>
> This induction uses `a<h`, not `a≤f` and not FG quorum turnout. It
> proves clean safety, monotonicity, and 6Δ service. F and S remain on
> the same chain. The accessor is their greater prefix and is monotone.
> The changed proof follows the origin/root/parent/HEAD/guard order in
> `CleanInclusion.lean`; it does not instantiate that theorem on a
> different executable `Run`.

- Status: 2026-09-28 — PROVED (FG-SA; r146 1a–1c).
- Note: it has the same source as `ap.armedSafe.v1`. `ap.armedSafe.v1` is
  the AP-side statement; this entry is its composite form.

### `comp.outputNesting.v1` — finalized ⪯ available at every read

- Variant `both`. Sources: r143 §6, lines 483–485 (file `fgsa-fast.md`,
  sha256 `8907540c5c71fe06703bc8d2ec2d30bc6cbc752a5f7577219a69196e2fd8ef37`);
  r148 §5 F8, lines 460–462 (file `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`); spec
  "Outputs", lines 444–456, and `get_confirmed`, lines 660–667 (file
  `spec/archive/fgsa-protocol-ae4497ab.tex`, sha256
  `ae4497abc7c5b3a6f73697f341bf730a63c7d34bd2f7546154bd022bc95af223`).
- Lean plan: — (an AP accessor by construction).
- Hypotheses: none. No fault bound and no synchrony premise.
- Statement (registry): at every read, `finalized ⪯ available`, where
  `available = S if F ⪯ S, else F`. This holds by the two cases of the
  accessor. It does not give `F ⪯ S` in a damaged local state.
- Statement (pinned):

> _fgsa-fast.md, lines 483–485:_
>
> The live finality update advances F only to a proper descendant; local F
> never retreats. The accessor in §4 gives `finalized⪯available` at every
> read. These results do not depend on the missing base-history proof.

> _fj-redteam.md, lines 460–462:_
>
> Pointwise finalized ⪯ available follows directly from the two accessor
> cases, even outside the fault bound. It does not imply F⪯S in every
> damaged local state.

> _fgsa-protocol.tex, lines 444–456:_
>
> ```latex
> \paragraph{Outputs.}  FG-SA exposes two tips~\FAST{4}.  The finalized
> tip is $\Call{get\_finalized}{\Sigma}=\Sigma.F$.  The available tip is
> \[
>  \Call{get\_confirmed}{\Sigma}=
>  \begin{cases}
>   \Sigma.\latestConfirmed, & \Sigma.F\preceq\Sigma.\latestConfirmed,\\
>   \Sigma.F, & \text{otherwise}.
>  \end{cases}
> \]
> $\Call{get\_stable}{\Sigma}$ is equal to $\Call{get\_confirmed}{\Sigma}$.
> The two tips nest at every node and every time by these two cases alone,
> $\Sigma.F\preceq\Call{get\_confirmed}{\Sigma}$, with no fault bound and
> no synchrony premise.  This does not give $\Sigma.F\preceq S$ in a
> ```

> _fgsa-protocol.tex, lines 660–667:_
>
> ```latex
> \Function{get\_confirmed}{$\Sigma$}
>   \Comment{\DC{7}, redefined by \FAST{4}; user-facing}
>   \If{$\Sigma.F\preceq\Sigma.\latestConfirmed$}
>     \State \Return $\Sigma.\latestConfirmed$
>     \Comment{available $=S$ when $F\preceq S$}
>   \EndIf
>   \State \Return $\Sigma.F$
> \EndFunction
> ```

- Status: 2026-09-28 — PROVED (by construction of the accessor; r143 C8;
  r148 F8).
- Status: 2026-09-28 (r158) — under ALFS: `F ⪯` available by the accessor
  is PROVED (direct two-case rule; r158 table line 891).
- Status: 2026-09-28 (r161) — under ALFS (spec bd942ca0): `F ⪯ S` holds at
  every node for every a, by the output rule (after each F advance and
  after each gate, `S := F` if `F ⋠ S`; spec lines 546–556 and 1594–1595;
  r161 §7, lines 672–681). This is local nesting, not cross-node
  finality safety and not unconditional monotonicity (r161 N1). Without
  the rule, `F ⪯ S_record` FAILS (r161 lines 460–461 and 672–674).
- Note: this is the output-nesting clause of `fg.accountable.v1`, filed
  as a composite because the accessor reads S, an AP record.

### `comp.leaseVsFinal.v1` — a local lease or local S does not survive every F advance

- Variant `fj`. Source r161 §5, N1, lines 378–482 (file
  `filtered-base.md`, archived as `tsc/archive/filtered-base-fd8e07fe.md`,
  sha256 `fd8e07fe667afae28dee2bc9a54d6c7fc46b49f9bb268865f98818decc308354`);
  the ALFS spec `alfs4`, lines 559–563 and 1596–1598.
- Lean plan: —.
- Statement (the refuted claim, registry form): after an asynchronous
  prefix, every live local lease and every local S survives every later
  accepted F advance (it stays compatible with F).
- Premises of the refutation: an asynchronous delivery prefix before
  GST, all honest validators awake; `a ≤ f` (n=4, a=1) or `f<a<h`
  (n=7, a=3); `Δ=16, k=2, L=112, R=3, δ_t=6, w_F=1`.
- Consequence in the spec (finality priority): `update_finality` calls
  `reconcile_with_finality`, which deletes the conflicting lease and
  sets `S := F` (spec lines 559–563). A local value formed under such a
  prefix does not have the healthy-prefix protection of P1, so P1 is not
  affected (r161 lines 477–482).
- Statement (pinned):

> _filtered-base.md, lines 455–461:_
>
> Before receipt, U has S=K_U and a fast lease on X, renewed at 672 with
> deadline 784. It has seen no conflicting release batch. Hence at 712
> the lease is live, yet `X` conflicts with the new F=Y. The gate guard
> does not guard `update_finality`. The filtered rule deletes the lease
> and sets S=Y. This refutes unconditional local-lease preservation and
> unconditional monotonicity after arbitrary damage. Leaving S untouched
> instead gives `F⋠S`, refuting raw-record nesting.

> _filtered-base.md, lines 477–482:_
>
> This is not a Clean or P1 counterexample. Honest X and Y votes are
> withheld across the partition for much longer than Δ before the S read.
> It fails the healthy-prefix premise, even though `a<h` at every time.
> No choice of outage arming lag repairs that failed premise retroactively.
> The n=4 execution also shows why `a≤f` alone cannot protect every local
> lease against a private, nonconflicting finalization.

- Status: 2026-09-28 — REFUTED (r161 N1, an exact integer execution;
  spec lines 1596–1598).
- Note: this is not a Clean or P1 counterexample (r161 lines 477–480).
  The n=4 execution shows that `a ≤ f` alone does not protect every local
  lease against a private, nonconflicting finalization (lines 481–482).

## 6. Invariants used by the composition (V03)

Three separate invariants, each over execution prefixes:
- clean history (GST = 0 regimes);
- post-reset source history: from the reset boundary, each source body from
  its first transfer HEAD q_s (not all pre-reset sources: old justification
  disclosure is a counterexample, fgsa-fast.md);
- armed-prefix Outage history: B only, not every later body (two partition
  branches can both extend B).

`Harmless` is stated as compatibility with the body being protected, not as
provenance of one row of a new quorum.

## 7. Changes in v2 (2026-09-28)

- W08: every entry pins its statement and hypotheses, its variant, its
  source lines and the source SHA-256 (§0). Statuses are dated lines.
- W03: `ap.X.v1` is WITHDRAWN (REFUTED, r149 §5). `ap.Xplus.v1` is
  registered with x0 and x3. `comp.healed.v1` discharges x0–x3 at each call
  (r150 §3).
- W05: `comp.fgHealed.v1` covers all fast and slow protected bodies and
  cites `ap.S.v2` and `ap.Sslow.v1`.
- W07: the fixed-F bound is `comp.healedLit.v1` (r150 §6.1, bp §9.4).
  `comp.healedUnif.v1` lists `comp.rise.movingF.v1` (effective (L)) as a
  hypothesis.
- W06: `fg.base.fj.v1` moved to `SimplexFG.fj` (§4), with its own interface
  (`fj.descent.v1`, `fj.canonical.v1`, `fj.inBandLock.v1`,
  `fj.twoChanges.v1`). HNI and its lemmas are `nj` only.
- W09: `fg.baseSel.nj.v1` lists the returned witness. Run-wide HNI in the NJ
  arm is derived in `comp.theoremN.v1`.
- New ids: `fg.frame.v1`, `fg.N2.v2`, `ap.reach.v1`, `fg.causalCap.v1`,
  `fg.baseSel.nj.v1`, `fj.frame.v1`, `fj.descent.v1`, `fj.canonical.v1`,
  `fj.inBandLock.v1`, `fj.twoChanges.v1`, `fj.armedSafe.v1`,
  `fj.firstFinality.v1`, `comp.healedLit.v1`, `comp.arrivalNJ.v1`,
  `comp.handoffBase.v1`.
- W02: `ap.*` entries state only AP service facts. WITHDRAWN as misfiled
  (statuses unchanged): `ap.L.fixedF.v1` (PROVED) and `ap.L.movingF.v1`
  (OPEN), refiled as `comp.rise.fixedF.v1` and `comp.rise.movingF.v1`,
  with service parts `ap.repair.fixedF.v1`, `ap.repair.movingF.v1`
  (OPEN), `ap.source.v1` and `ap.carrierKeep.v2` (block retention);
  `ap.carrierKeep.v1` (FG entries, maturity, rise); `ap.honestSourced.v1`
  (client and plateau-entry facts; now `ap.honestSourced.v2`);
  `ap.finalityHead.v1` (record permission; now `ap.finalityHead.v2`);
  `ap.outputRecovered.v1` (depends on `comp.theoremN.v1`; covered by the
  local clause of `comp.healed.v1`). `comp.healedLit.v1` and
  `comp.healedUnif.v1` cite that local clause; the global clause of
  `comp.healed.v1` no longer cites `comp.healedLit.v1`.
- New ids for W02: `ap.repair.fixedF.v1`, `ap.repair.movingF.v1`,
  `ap.source.v1`, `ap.carrierKeep.v2`, `ap.honestSourced.v2`,
  `ap.finalityHead.v2`, `comp.rise.fixedF.v1`, `comp.rise.movingF.v1`.
- r151 (`fj-theorem-h.md`) registered: `env.r151`, `fj.reset.v1`,
  `fj.theoremN.v1`, `fj.rise.fixedF.v1`, `fj.rise.movingF.v1`,
  `fj.Xplus.v1`, `fj.healed.v1`, `fj.healedUnif.v1`, `fj.healedAtQ.v1`.
  r151 confirms F13 REFUTED. It does not address the Opus `B_reset`
  shortcut (r146 claim 3c stays SKETCH).
- Status changes from v1: `comp.theoremN.v1`, `comp.fgHealed.v1` and
  `fg.base.nj.v1` go from PROVED* to PROVED, because r149 proves (S) and
  (S_slow) and r150 §2 states Theorem N as PROVED.

## 8. Changes after v2: f1 registry splits (2026-09-28)

Agreed with the framework session ethereum-f1. The splits separate pure
FG facts (`fg.*`, `fj.*`) from run facts (`comp.*`) and SA facts (`ap.*`),
as audit W02 requires. No status of an existing claim changes: each
SUPERSEDED entry is the conjunction of its successors.

- §0: new status SUPERSEDED; two hypotheses-list edits keep an id (rules
  (a) and (b)). §0.1 registers `slow-arming.md` and the sources outside
  `tsc/`. §0.3 is a glossary of the two F-number systems (r148 and the
  blueprint F-table).
- `fg.frame.v1` → SUPERSEDED by `fg.frame.v2` (J selected with
  `F_d ⪯ J_d`, as in DC and spec `update_finality` and spec `fg_frame`).
  New lemma `fg.frameCompat.v1` (registry argument): the two rules select
  the same pair at every honest duty view, without `a≤f`. Spec line 357
  says "compatible"; its code tests `F ⪯ J`.
- `fg.provenance.v1` → SUPERSEDED by `fg.provenance.v2` (pure FG),
  `ap.fastSupport.v1` (a fast write has ≥ τ surviving supporters, so an
  honest one) and `comp.provenance.v1` (the source is the signer's
  `C_fg`).
- `fg.causalCap.v1` → SUPERSEDED by `fg.causalCap.core.v1` (the cap for
  any M; row bound LEAN in DC `WeakHeightBounds.lean:42`) and `comp.cut.v1`
  (r_G, `u_0 = a_(r_G+2)`, M at `u_0`).
- `fg.oneBullet.v1` → SUPERSEDED by `fg.oneBullet.core.v1` (items 2–4 of
  bp §4.2) and `comp.settle.v1` (item 1, settling within θ = 4Δ).
- `fj.twoChanges.v1` → SUPERSEDED by `fj.twoChanges.core.v1` (the phase
  count) and `comp.settle.v1` (settling within θ, or P in r148).
- New ids for the blueprint facts: `fg.uniqueJust.v1` (F3; DC Lemma U,
  `Engine.lean:243` `justification_unique_per_height`) and
  `fg.finalLock.v1` (F4; `FinalityComparison.lean:50`
  `finalized_preceq_of_height_lt`; r148's "finalized-crossing law", line
  226). Both are LEAN for DC only.
- New id `fj.crossingNoFinal.v1` (r148 F2, PROVED, lines 234–258).
  `fj.frame.v1` has a note: its contest test is the local witness of r148
  lines 260–270.
- Hypotheses lists that cited a SUPERSEDED id now cite its successors:
  `comp.rise.fixedF.v1`, `comp.theoremN.v1`, `comp.healed.v1`,
  `comp.healedLit.v1`, `comp.healedUnif.v1`, `fg.base.fj.v1`,
  `fj.reset.v1`, `fj.theoremN.v1`, `fj.rise.fixedF.v1`,
  `fj.rise.movingF.v1`. Lists that used F3 or F4 by number now name
  `fg.uniqueJust.v1` or `fg.finalLock.v1`: `fg.trunk.v1`,
  `fg.base.finalized.v1`, `fg.base.nj.v1`, `fg.baseSel.nj.v1`,
  `fj.inBandLock.v1` (note), `fj.reset.v1`.
- New ids: `fg.frame.v2`, `fg.frameCompat.v1`, `ap.fastSupport.v1`,
  `fg.provenance.v2`, `fg.causalCap.core.v1`, `fg.uniqueJust.v1`,
  `fg.finalLock.v1`, `fg.oneBullet.core.v1`, `fj.crossingNoFinal.v1`,
  `fj.twoChanges.core.v1`, `comp.provenance.v1`, `comp.settle.v1`,
  `comp.cut.v1`.
- SUPERSEDED: `fg.frame.v1`, `fg.provenance.v1`, `fg.causalCap.v1`,
  `fg.oneBullet.v1`, `fj.twoChanges.v1`.
- Lean scope (user decision 2026-09-28, relayed by ethereum-f1): the Lean
  FG module is DC-fj (DC's FG without SG and grades, with the FJ root rule
  in place of NJ; FRAMEWORK-DESIGN.md §7.1). NJ is not formalized now. The
  index has a new column "Lean plan". Each entry of the DC-fj plan has the
  line "Lean plan: DC-fj module": `fj.frame.v1`, `fg.accountable.v1`,
  `fj.inBandLock.v1`, `fg.uniqueJust.v1`, `fg.finalLock.v1`,
  `fg.provenance.v2`, `fg.causalCap.core.v1`, `fj.crossingNoFinal.v1`,
  `fj.twoChanges.core.v1`. The nj-only entries have the line "Lean plan:
  none (nj research entry)" and are not planned for Lean now: `fg.frame.v1`,
  `fg.frame.v2`, `fg.Ret.v1`, `fg.N1.v1`, `fg.N1eff.v1`, `fg.N2.v1`,
  `fg.N2.v2`, `fg.HNI.v1`, `fg.trunk.v1`, `fg.oneBullet.v1`,
  `fg.oneBullet.core.v1`, `fg.H19.v1`, `fg.HNIb.v1`,
  `fg.base.finalized.v1`, `fg.base.nj.v1`, `fg.baseSel.nj.v1`. They stay
  as research entries. `fg.frameCompat.v1` is not needed by the DC-fj
  module. `fg.frame.v2` points to its fj counterpart `fj.frame.v1`.
- Open item (2026-09-28): `ap.S.v2`, `ap.Sslow.v1` and `comp.theoremN.v1`
  use `fg.N2.v2` (NJ frame). An fj Kept/N2 form with lo is a new fj entry,
  needed for Kit.Compose. OPEN.
- New id `ap.headReachesLo.v1` (variant fj; PROVED (FG-SA); Lean plan
  —). User design correction 2026-09-28, relayed by ethereum-f1:
  eligibility, the majority test, the current-slot rule, the GHOST score
  and the walk are AP fork-choice machinery; the FG module exports only
  the frame Z, lo, D and viability. The entry states that the AP head of
  each duty view is in D at state height ≥ lo, in every phase, with a
  registry SA discharge. The weaker form "the AP does not block leaving
  H−1" is not enough (N12, r148 F11). `fj.frame.v1` has a "Lean coverage"
  line (frame only). `fj.inBandLock.v1`, `fg.base.fj.v1`,
  `fj.rise.fixedF.v1`, `fj.rise.movingF.v1` and `fj.healed.v1` add
  `ap.headReachesLo.v1` to their hypotheses (§0 rule (b)); `fj.Xplus.v1`
  has a note that its callers discharge x2 with it.
- New id `fj.frameFeasible.v1` (variant fj; PROVED; Lean plan DC-fj:
  `fjFrame_D_reachesLo`, `fjFrame_D_nonempty`; Lean since `64651ad`:
  `filteredFrom_reachesLo`, a generalization, for part (1)). It is the FG
  frame side
  of the feasibility of `ap.headReachesLo.v1`: D reaches lo when D ≠ ∅,
  and D ≠ ∅ when the view holds the F carrier and the pure finality lock
  holds. It is an `fj.*` entry, not `ap.*` (audit W02).
  `ap.headReachesLo.v1` has a pointer to it.
- `fg.frameCompat.v1`: Lean plan changed from "none" to "DC-fj module,
  partial: (ii) only, F ⪯ J form" (Lean `fBasis_lexMax`, plan `befb5d5`).
  The index column shows `DC-fj (ii)`.
- `fj.inBandLock.v1`: a dated note on Lean coverage. The hypothesis hFJ′
  (F ⪯ J′) stays a hypothesis for now (partial coverage); a later helper
  lemma will derive it from `fg.finalLock.v1` and the F carrier.
- Status updates from r153 and its adjudication r153a (2026-09-28). Under
  the current rules there is no uniform (M-independent) healing or
  reset-arrival bound (r153a line 30). New dated status lines:
  `fg.base.fj.v1` (`B_R`, `B_base` uniform: REFUTED); `fj.healed.v1`
  (local PROVED; global `B_proved` and 1496Δ REFUTED; `B_lit` PROVED
  relative to r147); `fj.healedUnif.v1` and `fj.rise.movingF.v1`
  (REFUTED; implications PROVED); `fj.rise.fixedF.v1` (PROVED, unchanged);
  `fj.firstFinality.v1` (r152 FF1–FF7 PROVED; 1541Δ REFUTED;
  `B_lit+gP+9Δ` PROVED relative to r147); NJ: `comp.arrivalNJ.v1`,
  `comp.handoffBase.v1`, `comp.healedUnif.v1`, `comp.rise.movingF.v1`
  (OPEN, at risk), `comp.healed.v1` (local PROVED; global OPEN, at risk),
  `comp.finality.v1` (SKETCH; its arithmetic uses the at-risk bounds).
  No entry pins spec rows for `B_R` or `B_base`; r153a lines 483–496 list
  the spec rows that need changes. The broken steps are r148 F12 lines
  781–782 and F14 lines 824–832 (a lower F advance adds a view-dependent
  viability witness to HEAD views through the F basis), and in NJ
  fgsa-adjudicate lines 322–325 and fgsa-fast line 704.
- Fix candidate FV (r153a §5.1, lines 333–348; not adopted): the frame's
  F comes from the view, `F_V` = the greatest `σ[W].F` over W ∈ V with
  `σ[W].F ⪯ Σ.F`; delete the F-basis arm of the HEAD view and the field
  `f_basis` (spec lines 746–749). FV closes r153 (PROVED) and keeps FG
  safety, P1, F9, F10 and Theorem N (PROVED; r153a lines 41–42). The
  restored uniform bound is SKETCH (r153a line 43). Pending r156. Note:
  FV changes `fg.frameCompat.v1` part (ii), `fj.frameFeasible.v1`
  hypothesis (a) and the F-basis hypotheses of `fg.frame.v2`; these
  entries need new ids if FV is adopted.
- §0 rule: pins to spec text resolve against `spec/archive/` by hash.
  §0.1 points the `ae4497ab` spec pins to
  `spec/archive/fgsa-protocol-ae4497ab.tex` (reconstructed by the spec
  owner; hash verified). No spec text was re-pinned.
- `fj.twoChanges.core.v1`: a dated "Formal reading" note for an F move at
  a fixed view: below m−1, D loses only ancestors of F′ (not "D
  unchanged"; Astra plan audit G02); at m−1, F′ is the unique top J and D
  is unchanged. r153 breaks the count only through view changes.
- New id `comp.outputNesting.v1` (both; PROVED; Lean plan —): finalized ⪯
  available at every read, by the accessor. `fg.accountable.v1` has a
  note: output nesting is `comp.outputNesting.v1`; "local F never
  retreats" stays in `fg.accountable.v1` (Lean `update_finality_F_mono`).
- Retraction (2026-09-28, r153b): r153b §C.4 refutes the NJ transfer C5
  by an integer check on r153's numbers, and withdraws r153a's NJ claim.
  The at-risk marks of dd2f5e7 on `comp.arrivalNJ.v1`,
  `comp.handoffBase.v1`, `comp.healedUnif.v1`, `comp.rise.movingF.v1`,
  the global clause of `comp.healed.v1` and the note on
  `comp.finality.v1` are withdrawn by new dated lines; each entry returns
  to its status before dd2f5e7. The FJ REFUTED lines of dd2f5e7 stay.
- DC comparison (r153b §C, lines 797–1000): DC blocks r153 through the
  `reflect` field of `NamedProposalPivotSuffixTransfer` (DC Lean
  `DecoupledConsensusInternal/Definitions/NamedProposalPivot.lean:78`, vc
  commit `b97b902`, sha256
  `c40efd31a51227609e800466e00206c6b728662002342de7220d10f9e8029c84`):
  every eligible candidate child in the voter's frozen tree is also a
  candidate at the proposer. In FG-SA, r153 needs FJ's contest band
  (lo = H) together with the late F-basis arm (r153b lines 47, 956–957).
  FV restores `reflect` (r153b lines 987–993). The uniform FJ bound also
  needs the common-anchor link 1d (every HEAD's live-root lease lies on the
  proposer's path to its parent), which is SKETCH (r153b lines 750–751,
  767–788 and 995–1000).
- §0 rule: research sources are archived by hash at registration, and
  pins resolve against the archive. All registered `tsc/` sources are
  copied to `tsc/archive/<name>-<hash8>.md` (hashes verified), except
  r153a (`c85c0dcc`), which the adjudicator overwrote. `dc/consensus.tex`
  is kept by Git (commit `9f5ed71`).
- Plan questions from ethereum-f1 (2026-09-28): §0.4 defines
  `ViewRootInj` (collision-free roots in a view; G03; discharged by
  `viewRootInj_all` (I9, 2026-09-29)). It is added by
  §0 rule (b) to `fj.frame.v1`, `fj.frameFeasible.v1` (part (2)
  uncontested and part (3)), `fg.frameCompat.v1`, `fj.inBandLock.v1` and
  `fj.twoChanges.core.v1`. `fj.twoChanges.core.v1`: the formal reading
  now requires `m ≥ 2`, and part (ii) has the hypothesis "a carrier of F′
  in the view", which excludes the gap phase. `fj.frameFeasible.v1`: new
  parts (3) Z ∈ D and (4) a viable child below lo (Lean
  `fjFrame_Z_mem_D`, `fjFrame_viable_child`; Lean since `64651ad`:
  `fjFrame_Z_mem_D` and `filteredFrom_viable_child`, a generalization).
  `fj.inBandLock.v1`: a note
  on the Lean lemma `finalityPair_carrier_above`. `fg.frameCompat.v1`:
  Lean covers step 1 and part (ii); part (i) and step 4 stay paper.
- ALFS registration (2026-09-28): the ALFS spec
  `spec/archive/fgsa-protocol-183f2c40.tex` (key `alfs`), `ldp`
  (`fgsa-live-dc-port.md`), `r157` (`fgsa-live-views.md`) and `h12`
  (`fj-h12.md`) are registered; the three codex files are archived by
  hash. New id `fj.frame.v2` (fj; def, spec text, red-team pending; Lean
  plan DC-fj): controls from the live store caches, the domain filter on
  any block set, and the HEAD walk of the frozen voter tree from
  `live_root`. `fj.frame.v1` stays (the view form). Notes on
  `fg.frameCompat.v1` (part (ii) without the F basis; `StoreInv.Fcar`),
  `fj.frameFeasible.v1` (parts (1), (4) for any block set; (2), (3) in
  frozen form are ALFS L5/L6), `fj.twoChanges.core.v1` (`Fmove_filtered`,
  C1) and `ap.headReachesLo.v1` (not re-proved for ALFS). Dated status
  lines "under ALFS": `fj.healed.v1` (1004Δ PROVED, paper; local
  `q_(s*)+G+5Δ` with R1 views, transfer unchecked), `fj.healedUnif.v1`
  and `fj.rise.movingF.v1` (effective (L) PROVED, paper; 1292Δ),
  `fj.firstFinality.v1` (1049Δ PROVED, paper), `fj.armedSafe.v1` and
  `ap.armedSafe.v1` (P1 and clean claims for all a<h PROVED, paper).
  `fj.healedAtQ.v1`: REFUTED with R1 views (h12); not checked under ALFS.
  The imported r156 §§4–7, r151 N/H and r152 FF1–FF7 are not
  independently checked. The refutations under the old spec stay.
- New id `ap.headReachesLo.v2` (fj; PROVED, paper, SA under ALFS; Lean
  plan —): the AP head under ALFS. The head is in D_V at height ≥ lo when
  the anchor `live_root` is in D_V or has an eligible child there;
  otherwise the head is the anchor. After the two-lease boundary a
  fallback needs an empty D_V and a contest event in `(t_s−Δ, v_s)`: at
  most 2 slots per frontier, 4 before the reset, none after (ldp C5). The
  unconditional form "D_V ≠ ∅ ⇒ head in D_V" is not registered: before
  the boundary a live lease outside D_V can be the head. v1 stays (view
  form) with a pointer. `fj.inBandLock.v1`, `fg.base.fj.v1`,
  `fj.rise.fixedF.v1`, `fj.rise.movingF.v1` and `fj.healed.v1` have a
  dated note: under ALFS, `ap.headReachesLo.v2` with the charged fallback
  slots.
- r158 results (2026-09-28): `r158` (`alfs-redteam.md`, archived as
  `tsc/archive/alfs-redteam-f1ddd1a8.md`) is registered. It has no
  critical or high finding (lines 55–77). `fj.frame.v2`: def; r158 found
  no issue in the frame functions (index: "def (r158: no issue)").
  Dated lines "under ALFS, independently checked by r158":
  `fj.healed.v1` (1004Δ PROVED after the witness repair W; 996Δ with the
  H12 transfer), `fj.healedUnif.v1` and `fj.rise.movingF.v1` (C3, C4),
  `fj.healedAtQ.v1` (REFUTED at `q_(s*)`; local `q_(s*)+G+5Δ` transfers;
  index: "REFUTED (h12, r158)", the index now also shows the h12
  refutation with R1 views), `fj.firstFinality.v1` (1049Δ; 1041Δ with
  H12), `fj.armedSafe.v1` and `ap.armedSafe.v1` (clean claims and P1 for
  all `a<h`), `fg.accountable.v1` (safety at `a≤f`) and
  `comp.outputNesting.v1`. `ap.headReachesLo.v2`: M1 is consistent with
  clauses 1–3 and with the note on the requested form; the ldp C5
  sentence "fallback only
  when the frozen domain is empty" is REFUTED as a general rule; the
  conclusion of clause 4 at a settled honest proposal is PROVED by W and
  the common pivot (r158 §4). The r158 findings M2 (the raw-proposal vote
  merge changes scores; the spec §5 class NOTE is wrong), M3 (`δ_t ≥ 0` is
  outside the DC port) and L1 (accepted-object relay is not in the §5
  ledger) are about the spec ledger. They change no registry entry. The
  spec is not re-pinned.
- 2026-09-28, user: FJ only. NJ entries are frozen as research history; no
  further NJ status work. The r158 status lines on the NJ comp entries
  (`comp.clean.v1`, `comp.rise.movingF.v1`, `comp.theoremN.v1`,
  `comp.healed.v1`, `comp.arrivalNJ.v1`, `comp.handoffBase.v1`,
  `comp.healedUnif.v1`, `comp.finality.v1`) and the NJ-appendix sentence
  of `ap.armedSafe.v1` were removed on the same day, before any use.
  Commit `ce0eca3` keeps them.
- r159 and the spec re-pin (2026-09-28): `r159` (`alfs-fixes.md`,
  archived as `tsc/archive/alfs-fixes-4587052c.md`) and the spec
  c7c41a43 (key `alfs2`, `spec/archive/fgsa-protocol-c7c41a43.tex`) are
  registered. Spec changes against 183f2c40: the HEAD vote merge reads
  admitted proposals, as in DC §7 (r158 M2; r159 §1 checks every proof
  step); the δ_t scope (the recovery, healing and first-finality bounds
  hold at `δ_t = 2R`, `R ≥ 3`; FG safety holds for every `δ_t ≥ 0`; `R = 2`
  has only the healthy pipeline); §5 row 29 (accepted-object relay is an
  SA run premise; r158 L1); the bounds 996Δ and 1041Δ are spec claims
  (`B′ = B−2L+6Δ`); the NJ appendix is removed; the marks for unchecked
  imports are removed, because r158 checked the imports. `fj.frame.v2` is
  re-pinned in place (11 blocks, text unchanged, +9 lines); no v3 is
  needed. New id `ap.headReachesLo.v3` (fj; PROVED, paper, SA under ALFS
  c7c41a43; Lean plan —): v2 clauses 1–3, plus the full-store witness W,
  the settled-proposal conclusion (every honest HEAD is P, through W and
  the common pivot) and θ = 4Δ per effective event. `ap.headReachesLo.v2`
  is SUPERSEDED and keeps its 183f2c40 pins. The five entries with the v2
  pointer have a v3 pointer. Dated r159 lines: `fj.healed.v1`,
  `fj.healedUnif.v1`, `fj.rise.movingF.v1`, `fj.healedAtQ.v1`,
  `fj.firstFinality.v1` and `fj.armedSafe.v1`.
- r160 and the receipt premise (2026-09-28; user decision: DC's receipt
  premise in place of accepted-object relay): `r160` (`receipt-relay.md`,
  archived as `tsc/archive/receipt-relay-a64d25b1.md`) and the spec
  1c6952b6 (key `alfs3`, `spec/archive/fgsa-protocol-1c6952b6.tex`) are
  registered. Spec changes against c7c41a43: the Relay paragraph (DC's
  receipt premise; a handler can refuse, for example a third distinct
  vote of one seat); the Clean and Recovery premises name the receipt
  premise; §5 row 29 (receipt premise; the raw tree has no receiver
  exclusion; class (b)); a new OPEN item "SA Lean under the receipt
  premise"; the bibitem RR. No frame function and no HEAD merge code
  changed. `fj.frame.v2` is re-pinned in place (11 blocks, text
  unchanged, +7 lines). New id `ap.headReachesLo.v4` (fj; PROVED, paper,
  SA under ALFS 1c6952b6; Lean plan —): the conclusions of v3 under DC's
  receipt premise, with equal counts and scores (r160 §4.3) in place of
  exact vote sets. §0 decides the new id: the relay hypothesis changed,
  and the change is not rule (a) or (b); v3's clause 4 text also names
  accepted-object relay. `ap.headReachesLo.v3` is SUPERSEDED and keeps
  its c7c41a43 pins. The five entries with the v3 pointer have a v4
  pointer. Dated r160 lines (HOLDS / NEEDS-CHANGE per r160 §7):
  `ap.headReachesLo.v2`, `ap.headReachesLo.v3`, `fj.healed.v1`,
  `fj.healedUnif.v1`, `fj.rise.movingF.v1`, `fj.healedAtQ.v1`,
  `fj.firstFinality.v1`, `fj.armedSafe.v1` and `comp.settle.v1`; notes
  on `env.r148` and `env.r151`. NJ-only entries and premise sets
  (`env.bp`, `env.r147`, `env.r149`, `env.r150`, `ap.armedSafe.v1`,
  `comp.clean.v1`) get no r160 line: NJ is frozen.
- Filtered SA base (2026-09-28; user decision: clients ignore blocks
  that conflict with finality, as in DC): `r161` (`filtered-base.md`),
  `r163` (`spec-filtered.md`) and the spec bd942ca0 (key `alfs4`) are
  registered and archived by hash. The intermediate spec a3e12c57 (r163's
  edit, which deleted blocks from Σ.T) is archived as history only;
  team-lead corrected it to the cumulative form. Spec changes against
  1c6952b6: Σ.T is DC's cumulative admitted tree; `on_block` refuses
  `F ⋠ B` before it unpacks the block; the SA base reads the active view
  act(Σ); `reconcile_with_finality` deletes incompatible leases and
  fastWrite entries, empties incompatible saved results and sets `S := F`;
  the outputs store DC's `get_stable` rule; the receipt premise has DC's
  receiver exclusion; §5 rows 2, 3/20/21, 12, 24 and 29 change. Decisions:
  `fj.frame.v2` → `fj.frame.v3` (a new id by §0: five pinned blocks
  changed their text, although the frame controls are the same; see the
  entry). `ap.headReachesLo.v4` → `v5` (admission-or-coverage and the
  admission of W by crossing replace raw-tree transport). New id
  `comp.leaseVsFinal.v1` (fj; REFUTED, r161 N1). Dated r161 lines:
  `fj.healed.v1`, `fj.healedUnif.v1`, `fj.rise.movingF.v1`,
  `fj.healedAtQ.v1`, `fj.firstFinality.v1`, `fj.armedSafe.v1`,
  `fg.accountable.v1` (N1 at n=7 is an FG safety failure at `f<a<h`)
  and `comp.outputNesting.v1` (`F ⪯ S` for every a by the output rule).
  Rule (a) notes on the entries that cite `fj.frame.v2`: `fj.frame.v1`,
  `fg.frameCompat.v1`, `fj.frameFeasible.v1`, `ap.headReachesLo.v1`.
- SA Lean on the receipt premise (2026-09-28, r162): merge `1a3f73a` in
  `lean/available-chain` (branch `receipt-relay`: `059669d`, `5d03d92`,
  `eec0f94`). The regimes have no accepted-relay field; the five public
  contract theorems keep their statements and standard axioms; SA-PC
  derives acceptance from receipt (`receipt_acceptedRelay`). The full
  build of main at `1a3f73a` passes (3,558 jobs; team-lead, 2026-09-28).
  `CatalogLock --check` fails at `1a3f73a`: eight Catalog L3 hashes
  changed (`Catalog.sleepy` and its dependents), because `SleepyRegime`
  lost its accepted-relay field; the lock is not rewritten yet (user
  decision pending).
  Registry effect: the only status line whose reason was "SA Lean
  assumes AcceptedObjectRelay" is in `ap.headReachesLo.v4`; it gets a
  dated r162 line, and its status does not change. `ap.headReachesLo.v5`
  gets a dated line; it stays paper (no FG-SA Lean instance). No entry
  becomes LEAN: no registered entry is a plain SA Lean theorem. The SA
  model file `acG` is unchanged at `1a3f73a` (sha256 `2cb079fd…`, as
  registered). The spec bd942ca0 still lists "SA Lean under the receipt
  premise" as OPEN (lines 1852–1858); the spec is not re-pinned.
  Build detail (team-lead, 2026-09-28): `lake build` on main at `1a3f73a`
  completed with 3,558 jobs, 0 errors, 0 warnings and 0 `sorry`; `#print
  axioms` for the five public theorems gives only `propext`,
  `Classical.choice` and `Quot.sound`. Team-lead will close the spec's
  OPEN item together with the r164 red-team fixes in one spec change;
  the re-pin waits for that change.
- FG module pins (2026-09-28; requested by ethereum-f1;
  `lean/available-chain` main `64651ad`, Tasks 1–14, full build passes;
  `AvailableChainKitFG/Pins.lean` covers 13 ids). `comp.cut.v1`: Lean plan
  "DC-fj (item 4 partial)" and a dated line: `causalCap_notRoot` proves
  the arithmetic of item 4 only; the other clauses are run facts or
  external. The index Lean-plan column is wider to hold that cell.
  `fj.frameFeasible.v1`: the Lean names of parts (1) and (4) are
  `filteredFrom_reachesLo` and `filteredFrom_viable_child`,
  generalizations of the registry forms (any controls, any block set);
  the two earlier §8 lines that give the plan names have a pointer.
  Both names and `causalCap_notRoot` were checked in the Lean source.
- Lean coverage kind BY HYPOTHESIS (2026-09-28; requested by ethereum-f1,
  approved by team-lead): a §0 rule defines it, and `fj.twoChanges.core.v1`
  has a dated line for item 3 (ii) (`Fmove_atTop` with the premise `hext`).
- BY HYPOTHESIS wording corrected (2026-09-28; ethereum-f1, team-lead):
  the §0 rule now requires that the named premise be equivalent to the
  clause or its key step, and separates the kind from PARTIAL. A note on
  `fj.twoChanges.core.v1` limits the kind to the row "at m−1 the contested
  phase is impossible"; the F-move row is PARTIAL.

## 9. Re-pin to the adopted FG-SA spec (2026-09-29)

Authority: spec `fgsa3` (c1ea1db0, adopted 2026-09-29) and the adopted
blueprint (keys `bp00`, `bp01`, `bp21`; §0.1). Source of the edit list:
`tsc/scratch/r213b/report.md`, section "Final FG-COMPOSITION/Pins edit
list" (an append-only scratch report, not archived).

- New ids: `fj.frame.v4`, `fg.finalLock.v2`, `ap.headReachesLo.v6`,
  `fj.descent.v2`, `fj.twoChanges.core.v2`.
- WITHDRAWN for current use (not SUPERSEDED): `fj.frame.v3`,
  `fg.finalLock.v1`, `ap.headReachesLo.v5`, `fj.descent.v1`,
  `fj.twoChanges.core.v1`. Their pinned text and source pins stay. Each
  entry has a dated status line; the index shows the new status.
- `AvailableChainKitFG/Pins.lean`: the new sources `fgsa3`, `bp00` and
  `bp01` (the pin check resolves the root `blueprint` like `spec`), the
  pins `fj.frame.v4` and `fg.finalLock.v2`, and three historical pins
  (`fj.frame.v3`, `fg.finalLock.v1`, `fj.twoChanges.core.v1`). Clauses 2
  and 3a of `fj.frame.v4` cite FG-SA constants with `leanIn`; the pin
  gate is `scripts/check-fg.sh` plus `scripts/check-fgsa.sh`.
  `fj.descent.v2`, `fj.twoChanges.core.v2` and `ap.headReachesLo.v6` are
  not yet pinned. References to
  `ap.headReachesLo.v5` move to `ap.headReachesLo.v6`. The pin check
  rejects a WITHDRAWN or SUPERSEDED id that a current pin names; the
  historical pins are on its dated allowlist.
- The "Lean names" lines of `fj.frame.v2` and `fj.frame.v3` mark
  `ViewRootInj` as discharged by `viewRootInj_all` (I9).
- Healing companion (r213; blueprint 21). Proof map: HG.8-SI, L2-W, L2
  (with the floor increase after w_a), L3, L4-R, L4-C, HG.8a. HG.8a holds
  on Recovery₂, k≤2R+1, any G with Γ≥4Δ; at k=2, G=8Δ its values are
  204Δ/240Δ. HG.7 stays at 268Δ/312Δ and B_H at 295Δ/343Δ; the cut and
  H-time do not change. The healing lower endpoints are 89Δ−1 / 105Δ−1
  ticks for Δ≥2, and 77Δ−1 / 93Δ−1 ticks for Δ≥1. No cut option B is
  adopted. These are blueprint statements; no registry id pins them.
- Channel proof map (blueprint 01 §1.2–§1.3). T-VOTE is a composition
  service from AC duties, admission and receipt. T-START holds at every
  event index (proof for F1.8). R-XING and R-CAP quantify over the blocks
  that honest nodes hold at the read, with no event cut and no run log of
  faulty emissions. R-CAP compares the emission times of honest rows;
  R-XING permits a later read e′≥e. The joint proposer head and the
  finality-head triple are named; the finality pair is the FG client
  function on that triple. The H3 exact-HEAD use map includes Q0 and QF4
  S2.
- Current reading of withdrawn ids (2026-09-29). Registry §0 says that no
  composite may cite a WITHDRAWN entry. Current entries and pins that
  still cite one carry a dated pointer to this item; their pinned text
  and status do not change. A current use reads the citation as follows:
  - `fg.finalLock.v1` ("F4", "pure form", "finalized crossing"): the
    carrier clause of `fg.finalLock.v2`, that is the Lean carrier theorem
    `finalLock` (with `finalLock_e1`), which stays true. Where the use
    needs the threshold of the accepted finalization, it reads as
    `fg.finalLock.v2` (the accepted-carrier wrapper: Lean OPEN; paper:
    bp01 734–736).
  - `fj.twoChanges.core.v1`: `fj.twoChanges.core.v2` (evidence in the
    cumulative Σ.T and the live caches). The v1 fixed-view Lean lemmas
    stay true for a fixed view; v2's premises apply to the current frame.
  - `ap.headReachesLo.v5`: `ap.headReachesLo.v6` (clauses 1–3 have the
    same form; clauses 4–6 use Recovery₂, R≥2, strict receipt, θ=3Δ).
  - `fj.descent.v1`: `fj.descent.v2`. `fj.frame.v3`: `fj.frame.v4` (see
    the notes at the frame citations).
  A use that needs more than the successor states needs its own proof.
  In `AvailableChainKitFG/Pins.lean` the pin check also scans the free
  text of each current pin (the `mention` records): a registry id there
  gets the status test, and a citation that is only history goes inside a
  `(history: …)` marker. The registry text is not checked by a script;
  the pointers above cover it.
- Lean tags (2026-09-29): the 21 FG constants tagged `[pin fj.frame.v3]`
  are now tagged `[pin fj.frame.v4]`, the current pin that cites them.
  Their alfs4 line references name the text that they follow; that text
  is byte-identical in `fgsa3`, except the Trees paragraph.
- μ (r213; blueprint 21 H.11 and both HEALING_INPUT copies): μ is
  μ(run,GST), a function of the run and GST. It is not a field of an
  existential witness; all uses have the same value. The interface text
  of bp.healingInput.v1 changed; its statement did not.
