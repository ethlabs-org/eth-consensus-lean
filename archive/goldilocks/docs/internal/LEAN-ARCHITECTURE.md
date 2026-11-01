# FG-SA Lean architecture

**Current policy — 2026-10-09.** APIs and anchors can change. Generate the current
snapshots, then review all additions, removals, statements, and dependency changes.
Older freeze, append-only, no-widening, and zero-rename rules below are history.
They do not set current acceptance rules. Kernel, proof, source, and import checks
still apply. A snapshot update does not approve a changed claim.


_Status: ADOPTED by the lead, 2026-09-29 (user: "don't block on me"; the
user reviews afterwards). Owner: DC-simplify (lead). §4 and §7 come from
lean-framework; §2 from fgsa-lean. Target: `docs/LEAN-ARCHITECTURE.md`.
Path: draft 1 reviews (both REVISE) → draft 2 → full audit (Astra REVISE,
Opus ADOPT WITH FIXES) → draft 3 fold (§12) → delta check on immutable
copies (Astra ADOPT WITH FIXES 0/1/4; Opus ADOPT WITH FIXES 0/3/17) →
adoption. The post-adoption fixes (§13) each carry a gate. Adoption
releases the holds on T7.3+, the F0–F2 plan and 1c, in the order of §9._

_Draft 1: `archive/LEAN-ARCHITECTURE-draft1-40f3baef.md`. Reviews:
`TS/codex/reports/a0-synthesis-review-{astra,opus}.md`. §11 maps every
review item to its fix._

**Purpose.** The user (2026-09-29): get the structure of the claims right
first, then the proof architecture; decide the common proof modules and how
each part reuses generic results, so that no idea (for example a safety
argument) is proved again with small changes to its premises; start broad
work only when this foundation is solid.

This document is the index and the rule set. The detail stays in the input
files; each section names the file that it takes as authoritative.

**Authorities.** Spec `spec/fgsa-protocol.tex` **8ef4ed3b** (c1ea1db0 +
the recurrence quantifier, `Honest(s)` with s > 0, Rec_c one-way, and the
exclusion-direction remark; `spec/archive/CHANGES-c1ea1db0-to-8ef4ed3b.md`).
Blueprint 00 2e67a980, 01 200c9c07, 02 4d724984, 03 3f90c688, 21 9aec3e9f,
22 d17eef99 (tip-stability). `docs/ARCHITECTURE.md` (the shared map); this
document adds the proof architecture below it.

```text
┌───────┬───────────────────────────────────────────────┬────────────────┬──────────────────────┐
│ Key   │ File                                          │ Owner          │ State (2026-09-30)   │
├───────┼───────────────────────────────────────────────┼────────────────┼──────────────────────┤
│ S1    │ TS/codex/scratch/a0-s1-reuse-map.md           │ lead           │ final                │
│       │ (G01–G38)                                     │                │                      │
│ S2    │ lean-framework scratchpad a0-s2.md            │ lean-framework │ final                │
│ S3    │ TS/codex/scratch/a0-s3-claim-structure.md     │ fgsa-lean      │ r3.4 1bedacd2        │
│       │ (D01–D79)                                     │                │ (fixes §11 applied)  │
│ GLY   │ AC/claude-files/a0/generic-layer.md           │ lean-framework │ r3.17 40a50839       │
│       │                                               │                │ (census; L40)        │
│ S4    │ lean-framework scratchpad a0-s4-build.md,     │ lean-framework │ build.md r3.7        │
│       │ a0-s4-port.md (S4p)                           │                │                      │
│ 1c    │ AC/claude-files/1c/plan.md r3.3 (+ r4-inputs) │ lean-framework │ r4 follows A0        │
│ P3    │ TS/codex/scratch/fgsa-f0-f2-plan-draft.md     │ fgsa-lean      │ r3.5.7 721a06c2      │
│ T7    │ FP/docs/plans/…-t7-t1.md                      │ fgsa-lean      │ r17 98129fb          │
│       │                                               │                │ (T7 done but T7.10)  │
└───────┴───────────────────────────────────────────────┴────────────────┴──────────────────────┘
```

`TS/` = `~/ethereum/research/async-resilient-committees/tip-stability/`,
`AC/` = `~/ethereum/lean/available-chain/`, `FP/` =
`~/worktrees/available-chain-fgsa-plan/`.

**Input freeze (review fix O16).** The audit runs on named hashes of this
document, GLY, S3, T7 and P3. From the start of the audit to adoption, no
input changes; a needed change stops the audit and goes through the register
(§8).

## 1. Principles

P1. **One statement per proof idea.** Each idea of the S1 catalogue
    (G01–G38) and each id-less idea row of GLY §B.2 (history, folds, base
    transport, property kernel) has one generic Lean statement in one
    module. A claim or a task cites it and does not restate it. A generic
    form needs two instances (GLY rule F-31); otherwise it stays in its
    lane. §3 gives the home of every idea that had two candidates.
P2. **Smallest regime input.** A lemma takes the smallest regime-facts
    record that its proof reads (`FaultQ`, `FaultX`, `Batch`, `LabelFacts`,
    `DeliveryWithin`), never a whole regime (S1 §2). The regime choice is a
    choice of producer, not a new statement (example: one T7.12 statement,
    two `DeliveryWithin` producers; one receipt core, two trigger
    producers, §5).
P3. **Claim shape.** A claim is `set → local premises → channel Prop`, and
    every `…Claim` is `∀ binders, Prem args → N₁ → … → Nₖ → Concl args` with
    `Concl` a named definition (S3 §2.3).
P4. **Typed premise packages.** Premises that depend on each other share one
    point tuple (1c M03; S3 §2.2).
P5. **Reuse class of every run-level lemma** (S3 §5): (ii) a generic
    v2/KitV2 lemma plus an instance; (iii) a store-level lemma through the
    (b2) wrapper route; transport only with a named step/handler
    correspondence; restatement only with a stated reason. An FG-SA run is
    not a Grid CO run, so no Grid CO run lemma transports.
P6. **Review current interfaces.** Update the generated snapshots after a claim
    or dependency change. Review the full diff. Keep one proof core and derive
    public contract wrappers from it when a consumer needs them.
P7. **Module system first** (the user's "import trick", confirmed
    2026-09-29). Statements and proofs are separate modules; a theorem's
    proof is not exported; `private` is for helper lemmas. An ordinary
    proof-only edit rebuilds one module. Three edits are interface edits and
    rebuild the cone: a change of a public theorem's axiom set (B3b); a new
    exported equation lemma; a change to an exposed computable definition
    (§7).
P8. **Set reads only.** Claim-relevant reads use sets. No statement or proof
    compares roots, whole proposals or `fgBlock` values across two runs or
    two delivery orders (1c D5).
P9. **Review public name changes.** The current API inventories record additions
    and removals. Compile consumers after a rename. Keep wrappers when a consumer
    needs them. Pin evidence checks remain independent.
P10. **One cross-lane rule (written once here; S3 §4.2 and BUILD §7.4
    cite it; L37).** A lane `Proofs/<F>/*` and a `Proofs/Shared/*` module
    import only: statement modules, the Generic and KitFG layers, the
    upstream libraries (EngineV2, KitV2, the FGSA store, FGSARun; they are
    not lanes) and `Proofs/Shared/*`. A lane never imports another lane's
    proof modules or `Export`; it takes another lane's result as a premise.
    Two exceptions, and only these: `Proofs/<F>/Export` imports
    `Claims/<F>`; `Proofs/Assembly/<Claim>` imports the Exports and joins
    lanes. SYN L58 adds one exact aggregate-proof home:
    `AvailableChainFGSAProofs.Proofs.Assembly.Root`. It may import the claim
    facade `AvailableChainFGSAClaims.FGSAClaims`, the named lower modules
    `Proofs.Assembly.Foundations`, `Proofs.Assembly.Shared` and
    `Proofs.Assembly.Clean`, and the existing foundation imports. All global
    checks still apply. Other Assembly modules may import neither Assembly
    modules nor the claim facade. Library roots remain import lists.
P11. **Producers before claims.** A claim needs the statements that it consumes
    and the stated inputs of each premise producer. A law with an instance
    obligation needs its generic proof and one instance proof in Lean (L34).
    The order of §9 implements this proof-quality rule.

## 2. Claim structure

Authority: **S3 §2** (and §3 for the machine inventory). Summary:

- **Families and packages.** Foundation (BaseSet), Clean (CleanSet,
  CleanCutSet b₀, CleanPrefixSet b₀), Healing (HealingSet G = Recovery₂
  core), Finality (core + a named recurrence form), P1/Outage (OutageSet).
  `G ≤ P` is a separate premise where a claim states it. `RecoveryCore`
  has no δ parameter: the 2R claims take `hδ : p.δt = 2 * p.R`, and the
  general-delay claims take their own binder on `p.δt`.
- **Inventory.** 306 keys, key = (claim, clause, form); deferred rows stay
  visible (S3a r3.3 e27f013f + INV 056c8c4c). `FGSAClaims` holds only the
  exported claims; the 21 lemmas and the channel and service Props are in
  `FGSAInterfaces` (EXEMPT, "internal interface"); T1 keeps one row per bp
  id (O15).
- **Window specs.** The bodies of cleanWinAt, cleanWin, cleanPrefixWin,
  cleanLabelWin, gapWin, formWin, formWinAt, kernelWin, trigWin and
  outProtWin, and the key-to-spec map, are APPROVED (lead, O16). `outWin`:
  shape approved; its body and the final `Outage₂` fields are ONE statement
  task, owner fgsa-lean (F3 owner), before G-F0a (L27: S3 D46 holds; X11
  changes to "F3 proves; the statement is fixed at G-F0a"). Home:
  `Statements/Windows`, imported by `Packages`. `windowEnd := windowEndA`
  ("pattern end + Δ") for every constructor; the F4 owner confirms the
  values before G-F0a (O04; OD10 is then closed at G-F0a, not G-F0b).
- **Recurrence start.** Every round window starts at q ≥ 1; Rec_c starts at
  t ≥ max(GST, 1); DC's `StrongMultiProposerRecurrence` implies it (equal on
  infinite runs; the horizon guards differ by 9Δ). The start is in `RecPat`
  once; there are no per-form GST guards. `HonestSlot rho I s := 0 < s ∧ …`.
  The form-to-form implications are theorems over `RecPat` in a Proofs
  module (S3 D34–D36; `RecPat.mono` moves out of Statements, §4). Spec
  8ef4ed3b now states the same quantifiers.
- **Fixed shapes.** `FGFoundation` (F1: store, cumul, mono, frame, geo,
  strat, reconcile) + `SrcFrame Φ` / `SrcFrameAbove Φ c₀`; `CoreServices`
  (TStart, TVote, TWalk with `Batch h m`); one output-property kernel
  (GLY r3.8: `CompatOn`, `CompatAt`, `MonoOn`, `BelowOn`, `ServedOn` in Gen
  S/Pure/Props; no separate `SafeOn`) under CleanSafetyClaim, Healed, the inclusion and
  P1 conclusions, TSMono and TExact (O09); `KernelPrem_W` and
  `KernelConclusion_W` for the W kernel claim and F6, with QF2/QF4 proved
  from the F4 phase lemmas; `tstarOf` + `H0.tstar_eq` and the joined kernel form in
  F0.8b (O14); `ResetArrivalStatement` and `ProgressAttemptStatement`
  frozen at G-F0b (O12).
- **Healing time (L21, replaces the premise part of L6).** The blueprint
  gives `HEALED(GST + B_best(g_h))` under the QUALIFIED-SEARCH premise, and
  Rec_c(g_h) supplies that search without implying Rec_s(g_h) (00:297–301;
  21:2970–2973). So the proof is over one contract `QualSearch g_h`
  (every aligned search from a q ≥ 1 with T_q ≥ GST finds a qualified
  round within its budget), with three producers `of_recS`, `of_recC`,
  `of_lit`, each with `hP : 0 < P` (L36). Body (L36): for every q ≥ 1
  with T_q ≥ GST and T_q + gP + 9Δ ≤ horizon, a qualified round r with
  T_q ≤ T_r ≤ T_q + gP (the "(g_h − 1)P" hint is withdrawn: it makes
  `of_recC` false). `HTimeBestStatement` (premise `Rec_s g`, horizon
  GST + B_best, B_best = min(B_heal, B_H)) stays frozen as a public
  corollary through `of_recS`. `HTimeStatement` has NO search premise; it
  is the independent general healing bound. The first-finality bound
  B_best(g_h) applies to EVERY finality form with g_h independent of g_f
  (22:1184, :1211–1213; 00:1147–1153): each FF5 alternative gets an
  optional `QualSearch g_h` premise, or a register row records the
  omission. Horizons: B_best(g_h) + (g_f + 2)P + 9Δ for Rec_F and Rec_F4
  (00:1147–1152); B_best(g_h) + γ(g_f)P + 9Δ for the strong forms
  (22:1211–1213, :1286). Owner: fgsa-lean (OPEN 7),
  statement before G-F0b.
- **Clean zero-cut (L22, revised in draft 3).** The "faulty certificate
  at time 0" attack is IMPOSSIBLE (both A0 auditors; lead check of
  Handlers.lean:45–53): no block passes admission before 4Δ, because
  `b.parent.slot < b.slot ≤ slot(now) = 0` has no solution, rows do not
  move F, and the tick at 0 runs no gate. The lead's blueprint edit
  (a < q_F) is REVERTED (00 2e67a980, 03 3f90c688). `CleanCut₂` drops the
  `quorum` field: for b₀ > 0 `a < q_F` follows from h₀ > a and h₀ + a ≤ n
  (`HealthyPrefix₂.faultQ_of_pos`), and at b₀ = 0 it is not needed. So
  `CleanCut₂` is an abbrev of `HealthyPrefix₂` and exact. The F2 internal
  lemmas take `hq : FaultQ`; only the public F2.7 `cleanCut` splits on b₀,
  with `cleanCut_zero` (one handler-side lemma "no admission before 4Δ");
  F3 has b₀ ≥ 4Δ (fgsa-lean check, audit-fgsa-items-bc9747f0.md). `CleanPrefix₂.partAt` (participation at
  b₀, OD16) stays a declared Clean-only strengthening: its claims are
  wrappers over the `CleanCut₂` claims.

## 3. Proof-module map

Authority: **S1** (catalogue, regime records, composites) and **S3 §4**
(layout), with the homes below.

- **Catalogue.** 38 ideas, G01–G38, each with one generic statement, a
  layer, a home and its instances (S1 §1). Of 16 claimed duplicate groups,
  7 are regime pairs (the regime input is the relay supplier or h, never the
  fault bound), 8 are exact duplicates and 1 is partial (R-CAP, G17). Client
  safety and row receipt get one statement each; store monotonicity has two
  (`RMono`, `RStoreCumul`; S3 D24, D37).
- **Composites.** C1 honest-batch walk (TWalk = C1 with m = n − h in
  Recovery and m = a in Clean), C2 source-bounded admission, C3 protected-B
  event step; the stage lemmas under HG.6/HG.7/HG.8a; the F4 phase module
  (S1 §3).
- **New pure work.** The suffix walk family G10/G11 (the Grid CO walk lemmas
  need a premise over the whole path, G/Walk.lean:218–221).
- **Homes decided in draft 2 (L24).** One home each; every other text that
  names a second home or a local copy is changed (S3 r3, P3 r3.4, T7 r13).

```text
┌──────────────────────────┬────────────────────────────────────┬────────────────┬──────────────────────────────┐
│ Idea                     │ One home                           │ Owner          │ Removed alternatives         │
├──────────────────────────┼────────────────────────────────────┼────────────────┼──────────────────────────────┤
│ Walk G09, suffix G10/G11,│ Gen: E-1, E-4 (GLY §E); G25 in     │ lean-framework │ S3 O02 local fallback;       │
│ score G25                │ P/AC/Votes                         │                │ P3 F1b.4 local re-proofs     │
│                          │                                    │                │ (P3:2561–2563, :2687–2750,   │
│                          │                                    │                │ :2796–2803)                  │
│ C1 batch_head_covers     │ FGSAProofs/Shared/HeadCover        │ fgsa-lean      │ "Gen Pure Walk" (S1:2004);   │
│                          │ (it composes KitFG and FC lemmas)  │                │ impossible under the KitFG   │
│                          │                                    │                │ rule                         │
│ G24 transfer             │ P/AC/Votes (count core Q, walk     │ lean-framework │ Gen AC Transfer; "(b2)       │
│                          │ use W; GLY §B)                     │                │ wrapper or Gen Pure"         │
│ G12 one row per honest   │ P/V2/Signatures                    │ lean-framework │ F1.2 honest_one_row_per_     │
│ seat and label           │ honest_unique_per_label            │                │ round and the argument in    │
│                          │                                    │                │ excludesS_honestRow_false    │
│                          │                                    │                │ become instances             │
│ G21 foldTrichotomy       │ FGSAClaims/Statements/Fold +       │ fgsa-lean (F4) │ Proofs/Finality/Fold (F4     │
│ (+ noMixed providers)    │ FGSAProofs/Shared/Fold             │                │ only); "FC" without gate     │
│ Phase contracts          │ Statements/Phases (public; F-26    │ fgsa-lean (F4) │ FGSAProofs/Shared/Phases     │
│ (JustifyFresh,           │ lint) + Statements/PhasesInternal  │                │ (KernelP holds Recovery₂,    │
│ FinalizePending, KernelP)│ (KernelP; imported by the F4 tree  │                │ HealingInput, CoreServices:  │
│                          │ only); proofs in the F4 tree; F5   │                │ F-23/F-26 forbid them in     │
│                          │ and F6 take the phase contracts as │                │ Shared; OPEN 7 C1)           │
│                          │ premises, Assembly supplies them   │                │                              │
│ G37 healed monotonicity  │ Statements/Healed + FGSAProofs/    │ fgsa-lean      │ —                            │
│                          │ Shared/Healed (P3:775, :3329–3333) │                │                              │
│ G17 row cap              │ instance of KitFG/CausalCap        │ fgsa-lean      │ a second rowCap core in F1.7 │
│ E-15 chain order         │ liveRoot_stored and fgHead_stored  │ fgsa-lean +    │ fgHead_stored re-proving     │
│                          │ both stay in the store library     │ lean-framework │ liveRoot membership; the     │
│                          │ (StoreInv.lean); fgHead_stored     │                │ earlier "liveRoot_stored is  │
│                          │ uses liveRoot_stored (fgHead is    │                │ a wrapper of fgHead_stored"  │
│                          │ the ghost walk result, possibly a  │                │ (impossible: fgHead ∈ blocks │
│                          │ strict descendant); only the       │                │ does not give liveRoot ∈     │
│                          │ ChainOrder facts move to           │                │ blocks)                      │
│                          │ KitFG/Certificates                 │                │                              │
│ F2 producers             │ P3:3138–3142 "1.8k lines to prove  │ fgsa-lean      │ the sizing text is rewritten │
│                          │ again" → routed through G03, G13,  │                │ with an S3 §8 row            │
│                          │ G24, E-14                          │                │                              │
└──────────────────────────┴────────────────────────────────────┴────────────────┴──────────────────────────────┘
```

  The Fold and Phases statements and the QualSearch contract have a
  statement gate before G-F0b; F4, F5 and F6 import the statement modules
  (P10). Shared/Fold is a Shared proof module; the phase proofs stay in the
  F4 tree. G32 (`Shared/Gate`) and G20, G30, G31, G33: homes as agreed
  between lean-framework and fgsa-lean in GLY r3.11 / S3 r3.3. Justified
  local copies stay with their reason stated (T7 HEAD exclusion and HEAD
  split re-proofs: the Grid CO proof modules are outside the FG import rule;
  the T7.W and FR3 conditional re-proofs; the E-14 history restatement,
  deleted after F2; full list P3 r3.5.1 :4470–4477, :5293–5297). No
  T7-local record-fold fallback: R1 is the route, and any other route
  needs a new register entry (L33). The local-K8 fallback text in P3
  (3243–3244, 3716) is removed: T7.12 is the one K8 statement.
- **Import DAG** (S3 §4.4, with O19 adopted): Generic statements first
  (`Gen.S.Pure` → `Gen.S.V2` → `Gen.S.AC` → the new KitFG modules), then
  the FG-SA claims library. Each F0 statement module imports only the
  modules that its definitions use; modules are joined only in `Packages`,
  `ComposeStmt` and `Claims/<Lane>`. The §4.4 line is the total order for
  the acyclicity check. Claims are closed in small assembly modules
  (`Proofs/Assembly/<Claim>`), so a claim edit rebuilds only its assembly,
  1c and the tests (S4 §3.3; P10).

## 4. Generic layer

Authority: **GLY r3.11** (r3.7 + the fixes of §11 and §12 + L29–L37). Summary:

- One library `AvailableChainGeneric`, namespaces
  `AvailableChain.Gen.{Pure,V2,AC}`, each layer split into Statements and
  Proofs. Model does not change. Kit v2 closes after 1c.
- **Statements modules** contain definitions, structures and the public
  `f_def` lemmas of B3a only. Every other theorem is in a Proofs module
  (`RecPat.mono` and the form-to-form implications move to Proofs).
- **Import rules (L25).**
  - KitFG DEFINITION modules import only `Gen.S.Pure` without `Walk`.
    KitFG PROOF modules may also import `Gen.P.Pure` without `Walk` (the
    quorum core of E-5/E-6; no second quorum proof). S3 D03 ("only
    Gen.S.Pure.Quorum") widens to this rule.
  - `Gen.S.V2` may import the KitV2 modules of an allow list whose closure
    is EngineV2 only. The list has one entry now: `AvailableChainKitV2.
    ClockLaws` (it imports `EngineV2.Engine.Run` only). No second clock
    structure.
  - `Run.nthIdx?` is defined in `Gen.S.V2.Reads` at E-12 (it does not
    exist yet, so this is no rename); 1c.2's `KitV2/Canonical` imports it
    and adds no twin.
  - A locked module may import `Gen.S.Pure` (not `Walk`) and `Gen.S.V2`
    only (GLY §A.4).
  - Only `Gen.S.Pure.Walk` imports a protocol module (`GridCO.Model.Walk`,
    allow-listed).
  - Enforcement: a MODULE-LEVEL import check (the GLY §F rules above) in
    addition to `CheckFGAxioms`. The closure-root check compares library
    roots only and cannot enforce "S/Pure only"; it stays as the axiom
    guard, with the one new root `AvailableChainGeneric`.
- The idea map is keyed by G id (GLY §B). 31 rules, 22 with a mechanical
  check (GLY §F); GLY r3.8 adds the module-level import rule.
- **KitV2 cores (P6, L33; replaces A3).** KitV2 `stateBefore_step_induction`
  and `ownRecord_fold_interval` are the CORES of the induction and
  record-fold ideas (G08, FOLDS). The Gen `P/V2/Induction` and `P/V2/Fields`
  forms, including the restart-tolerant own-record fold that T7.9 A needs,
  are corollaries proved from these cores, with no second proof.
  `invariant_clock_le` becomes a wrapper of `stateBefore_invariant` or is
  dropped. The frozen `ownRecord_fold` (NoRestart) stays. Client safety
  takes no `NoRestart` premise. Route for T7.9 A (lead, R1): one Gen
  theorem `ownRecord_fold_restart` in P/V2/Fields (projection laws for
  clock, process and recordOwn; a restart premise that the durable part
  keeps the projection); proof by induction on j, each non-restart step is
  the frozen `ownRecord_fold_interval` over [j, j+1). R2 (E-10
  `invariant_triple`) cannot carry the fold: its predicate reads the state,
  the fold reads the event prefix (`TS/codex/scratch/audit-fgsa-items-
  bc9747f0.md`).
- **Generic manifest (GLY Q-8).** The checker design (a second scope of
  `V2Manifest` or a copy) closes before the E-9 statements freeze.
- **Migration** (GLY §E), all additive and without renames. Timing by first
  consumer:
  - statement round before G-F0a: E-12 (generic skeleton, reads with
    `Run.nthIdx?`, rules), **E-9 statements** (receipt: DeliveryWithin,
    the trigger, TimelyClock, the acceptance and admission laws,
    `timely_*`, `accepted_by_deadline`, the first-acceptance bridge,
    LabelSync; their consumers T7.7, T7.12a and LabelSync come before
    G-F0a), **E-11 statement** (store-invariant bundle; T7.5 and T7.7 use
    it), E-1 (block order), E-3 (same-name split of the walk definitions
    into `GridCO/Model/Walk`, bodies byte-identical, importing only Mathlib
    and `Model.Objects.*`), E-19 (`KitFG.StoreInvDef`), E-15 (T7.W merge
    into KitFG/Certificates), the KitFG `ViewLock` and `HonestRows`
    definitions (owner lean-framework; T7.9 A needs HonestRows);
  - before F1: E-5 (KitFG `WeightsBridge`; the nine F1-cited statements
    stay on `Electorate`), **E-14** (history restatement; S3 D06 timing),
    E-16 (fold), E-18 (StoreKeys/StoreFacts; FGSA chain 40 → about 15);
  - before F1b.4: E-4 (suffix family); before F1.3: the E-7 statements;
    before F1.7: the FG part of E-13 (binder-free lemmas under new names;
    the old names stay as wrappers until after F2); before F3: the E-8
    core; E-10 (first-bad pure/run split; retires S1's interim Foundations
    copy) before its first run consumer, named in GLY r3.8;
  - E-9 and E-11 proofs: §9 step 3 (L34).
  After F2: the deletions of E-2, E-6, E-8, E-16, E-17, the E-13
  wrappers and the E-14 restatement. The Grid CO and SA-PC relocations wait behind fixed facade
  names.

## 5. Current interfaces

Write each signature in full. No current signature contains `…` (review fix O4).
Generate its current snapshot and review the complete change.

**Audit results (GLY r3.8 deviations).** A1 and A2 PASS in both A0
audits; A3 FAILED and is replaced by L33 (§4). A1: AdmitSound without `wellFormed`,
and the carried-child lemma. A2: j at the trigger time; `Monotone dl` and
`t < dl t` are fields of LabelSync and T7.12 (and `t < dl t` at the
trigger time is also a premise of `accepted_by_deadline`, L32); `hrestore : now
(restore d) = 0` (an equality: a restart has no time condition, so a
delivery can precede the next tick; both instances restore to 0). A3 (as
audited): no Gen twins of the KitV2 lemmas; superseded by L33.
Also recorded: the E-15 survivor is `fgHead_stored`; the first run consumer
of E-10 is T7.5 (inferred from G08).

- **V2-API:** no break. Additive fixes I-1 … I-7 (S2 §5; GLY §D).
- **Timeliness (L19).** `TimelyClock` keeps its GLY fields (`clock :
  ClockLaws P`, `actTime`, `clockOf`, `clockOf_eq`, `timely_iff`).
  `actTime o` is the ADMISSION THRESHOLD of the handler, not the honest
  send time: the start of slot s (4Δs) for a HEAD or a proposal of slot s;
  the start of round r (4ΔRr) for a row of round r. Then `timely_iff`
  matches the handler's future test exactly (GridCO Protocol.lean:304–306:
  `current < r`; FGSA Handlers.lean:20–22: `now < r`), and every honest
  emission is at or after its threshold. The Grid CO instance (SA
  milestone) uses the same rule.
- **Admission law, trigger, timeliness (L19, L30).** The written forms are
  in GLY §C.3 (`AdmitSound P C`, THE ONE WRITTEN FORM; `Trigger`;
  `timely_of_clock`, `timely_of_emit`, `timely_of_relay`); this document
  cites them and does not restate binders. Summary: `AdmitSound` concludes
  `Timely` only, under `0 ≤ clockOf st` (L30: false at a negative clock).
  Well-formedness of a handled object comes from `DeliveryWellFormed.wire`
  at the receiver's own envelope plus `handles_wellFormed` (T7.7).
  `Trigger` = honest emission or an honest `acceptsAt` (covers faulty
  signed objects). The producers bound `actTime o` by `pubFloor t` at the
  TRIGGER time t; `timely_of_relay` needs `hrestore : now (restore d) = 0`.
  `timely_of_clock` then gives `Timely` at any index i after the receiver's
  tick at that floor, over a restart-free interval.
- **I-3 acceptance law** `AcceptanceLaw P Timely Inv` (GLY §C.3, L3):
  handled ∧ depsPresent ∧ wellFormed ∧ Timely at the pre-state ⇒
  `processed st' o ∨ excludes st' o` at `st' = process st o′`, at every
  state that satisfies Inv, with `Inv := CStoreInv`. Inv is needed in
  THREE refusal cases, all covered by `CStoreInv`: (1) `B ⪯ F`; (2)
  `eraseF ⪯ b` strictly with `F ⋠ fgBlock P b rows` (Handlers.lean:49);
  (3) the FG test accepts and the base `admitProposal` refuses, so the
  carried HEADs are skipped (Handlers.lean:61–72; `CStoreInv.baseTree`).
  T7.7 lists all three, so its stop rule "a refusal in none of these cases"
  does not fire. The disjunct is needed: a carried batch can fill a
  per-(identity, round) cap inside one delivery. Negative controls: the
  FG-SA row cap (instance test); the Grid CO three HEADs of one faulty seat
  as a STORE-LEVEL test over `GridCO.process` (gridCO is a v1
  ProtocolSpec, so it is not a V2 instance test).
- **`excludes_process` (L20).** Not a field of the frozen law: no generic
  lemma consumes it (`accepted_by_deadline` uses
  `HooksSound.excludes_stable`). It stays as an instance lemma (FGSARun
  Proofs/Excludes.lean:455; GridCO Proofs/Hooks.lean:96–98).
- **`accepted_by_deadline` (written form in GLY r3.10).** Required
  premises, each named:
  1. the trigger at t (either producer) and the `DeliveryWithin` field that
     it uses; honest sender and honest receiver w;
  2. `t < dl t` for the trigger time (L32: without it the theorem is
     false; an acceptance at t = dl t is not before the deadline state;
     Astra O25 review) and `dl t ≤ cut` (no horizon premise: GLY r3.11
     dropped `hhor`, which no step used);
  3. schedule well-formedness and `HooksSound` (`excludes_stable`) and
     `processed_stable` as named premises (neither follows from the laws
     above: a protocol whose tick clears the processed store meets them and
     fails the conclusion);
  4. READINESS of the handled object at every handling event before the
     deadline: `wellFormed o` and `depsPresent st o`. `DeliveryWellFormed`
     covers only the delivered envelope, so Generic states readiness as a
     premise with producers: dependency-free kinds (FG-SA HEADs and rows,
     `depsS = true`, a structural law), `DeliveryWellFormed.wire` plus the
     carried-child lemma `handles_wellFormed` (T7.7; AdmitSound gives
     `Timely` only, A1), and honest emission (T7.9 B,
     `honest_emit_wellFormed`). T7.8 takes it
     as a premise; the assembly supplies it (P10), so T7.8 does not wait
     for T7.9 B;
  5. the admission-time bound through the timeliness core;
  6. the index interval: j = w's tick at `pubFloor t` (the TRIGGER time:
     the premises do not know the handling time; `restartFree rho w j k`
     then covers the tick at `pubFloor t′` that `timely_of_clock` uses;
     AUDIT FOCUS A2); k = the length of the
     STRICT event prefix before `dl t`, with `stateBefore k =
     stateBeforeTime (dl t)`, also when `dl t` is past the last event;
     `restartFree rho w j k` (half-open [j, k), Schedule.lean:37–41);
  7. `excludes (stateBeforeTime (dl t) w) o = false` (not excluded AT THE
     DEADLINE STATE; for an honest row from `excludesS_honestRow_false`).
     The earlier hNX form was false (S3 review M1).
  Conclusion: `processed (stateBeforeTime (dl t) w) o`. The relay case
  where w already processed o at the trigger index is closed by
  `processed_stable`. Argument names follow `Schedule.lean:40`
  (`restartFree rho v i j`) in every document.
- **First-acceptance bridge (new; 1c).** `accepted_by_deadline` concludes
  `processed`. 1c's `AcceptsAll` also needs "unprocessed before the
  emission" and an actual `acceptsAt` event in [t, deadline). One Gen V2
  lemma `firstAccept_of_processed` derives the event from the unprocessed
  pre-state and the processed deadline state; 1c proves the freshness
  facts (`EmitReady.fresh`, `Feasible.clock_unprocessed`, `Feasible.indep`)
  and instantiates it. Owner lean-framework, statement in the E-9 round.
  1c.7 does not repeat the handler partition.
- **Label timing** (GLY §C.5): `LabelSync E rho vt dt := ∃ dl cut,
  DeliveryWithin E rho dl cut ∧ Monotone dl ∧ (∀ t, t < dl t) ∧ (∀ t, dl t
  ≤ max t vt + Δ) ∧ vt + Δ ≤ dt ∧ dt ≤ cut ∧ dt ≤ horizon`, and `LabelFacts
  := {sync, batch}`. The `syncFrom` field bounds the relay of an
  acceptance at every t′ (also t′ > vt: `dl t′ ≤ t′ + Δ`). Producers
  `of_cleanCut`, `of_recovery`. The relay of early FAULTY votes goes
  through the relay trigger and `timely_of_relay` above. **O25 is CLOSED**:
  the written consumer check (r5 134eca23; durable copy
  `AC/claude-files/a0/labelsync-consumers.md`; two Astra reviews) covers
  same-label compatibility, forward and reverse transport, score equality,
  TVote, the release and healing uses, and found no field change.
- **I-4 `Obs V`:** the proposed block of a slot is optional (slot 0).
  **I-2:** Channels + base transport; `fgsaIso.base = State p.n` is forced.
- **One deadline read:** `HoldsBefore` over `stateBeforeTime`, with
  `holdsBefore_iff_exists_idx`.
- **Receipt:** `DeliveryWithin E rho dl cut` in Gen V2/Receipt (it
  replaces ReceiptForm/psForm/hpdForm), with two producers
  (PartialSynchrony: `max t GST + Δ`, horizon; HealthyPrefixDelivery b₀:
  `t + Δ`, b₀). ONE T7.12 statement for Clean, P1 and Recovery, in
  `FGSARun/Statements`; the slot-window premise is a named field whose
  trigger is the §5 `Trigger` (a faulty-proposed path block arrives by
  relay); the proof uses only `Monotone dl` and `t < dl t`.
  `Statements/ReceiptCoverage` for both forms is frozen at the T7.12a gate
  (S3c M3; O28).
- **Exclusion.** `excludes_inert_epoch` (one restart epoch, monotone clock)
  is the proof tool; the frozen HooksSound fields stay (one-state
  inertness, restart-free stability). TRowsSync.receipt uses
  `excludesS_honestRow_false` + `rowPool_provenance` + `processed_stable`.
  **Spec direction** (spec 8ef4ed3b Relay remark): Lean also lets the
  network skip a HEAD or row that the handler always refuses (old label,
  full cap). The Lean receipt premise is therefore weaker than the spec
  premise: every spec run meets it. T7 r13 adds this to its declared spec
  differences.
- **Claim-level shapes:** §2 "Fixed shapes"; the S1 §4.1 freeze items
  #16–#30 as adopted in S3.

## 6. Instantiation pattern

Authority: **GLY §C**: five mechanisms and two worked chains, quorum
intersection → FG finality lock → FG-SA view lock; DeliveryWithin + Trigger
→ AcceptanceLaw/AdmitSound → FG-SA receipt. A third chain of the same
pattern is planned in P3 (OPEN 7, before G-F0b): QualSearch (Rec_s | Rec_c
| Lit) → healing time → HTimeBestStatement. The pattern: a generic statement over
a small record; one producer lemma per regime, trigger or protocol; the
claim cites the generic statement through the producer; no second proof.

## 7. Build

Authority: **`claude-files/a0/build.md` r3.7 bf8b643a** (lean-framework;
r3.8 with the G-F0a package adds `gate.sh --critical-path`, L46;
final §Build; it replaces the draft-1 text and goes into
`docs/LEAN-ARCHITECTURE.md` §7 at adoption). Summary:

- 7.1 the module system is the primary rule (B0). A proof-only edit
  rebuilds 1 module (measured on rc2 and v4.34.1). Two exceptions: a new
  exported equation lemma (B3a prevents it) and a changed axiom set
  (B3b). An exposed computable definition is vocabulary: its edit is an
  interface edit.
- 7.2 rules B0–B10, B3a, B3b with their state on main a6733c2.
- 7.3 checks (a)–(g): no exception on the new libraries; a main baseline
  on the legacy libraries (875 eq-like findings). Check (e) is the
  module-level layer/import check of the §4 rules (L25) and the E-18 guard.
  (f) unused imports (O19, `shake` or a script) is scoped after the port.
  `AvailableChainCheckSupport` (imports only `Lean`) holds the shared
  check code.
- 7.4 FG-SA layout: FGSARun → FGSAClaims → FGSAProofs / FGSAInhabit /
  Tests → Assembly; cross-lane facts are `Prop`s in
  `FGSAClaims/Statements/ChannelProps` (`Statements/Channels` holds only the
  read definitions that the Props use), and only Assembly closes them (P10).
- 7.5 the port by the approved re-baseline procedure (L16).
- 7.6 the wrapper and the NUC rule; measured cold 724 s / critical path
  296 s (Mac, old wrapper) vs 264 s / 155 s (NUC). FG-SA critical path
  (FGSA + FGSARun, NUC, 3 slots, cold, dab6bf3): 100 s, the G-F0a
  target; a gate above 120 s blocks. Not comparable to 155 s (whole repo).
- 7.7 build agents and gates: `scripts/gate.sh` with MERGE and FULL tiers,
  one global slot cap (3 on the Mac and the NUC), and on the NUC a required
  MemoryMax=16G scope (after the 2026-09-30 OOM incident; L46).

build.md r2–r3 apply the lead amendments and record the port result:
`FGSAProofs/Shared/*` is not a lane and FGSAProofs may import it (check
(e)); Shared may also import the upstream libraries (L31; r3.1);
the lock and the manifest
hash elaborated statements and definition values (a proof term inside a
definition value counts), not theorem proofs.

## 8. Decision register (lead, 2026-09-29)

S3 §1 (D01–D79) is the claim-level register. The lead register (L1–L46;
L40–L46 added after adoption, 2026-09-30):

```text
┌─────┬──────────────────────────────────────────────────────┬────────────────┐
│ Id  │ Decision                                             │ Source         │
├─────┼──────────────────────────────────────────────────────┼────────────────┤
│ L1  │ excludes_inert_epoch is the proof tool; HooksSound   │ lead; Astra 1c │
│     │ fields stay; every exclusion is epoch-local          │ recheck        │
│ L2  │ TRowsSync.receipt via excludesS_honestRow_false,     │ S3c M11        │
│     │ rowPool_provenance, processed_stable                 │                │
│ L3  │ I-3: timeliness field (option B); post-state         │ lead; T7.2 R-A │
│     │ disjunction; Inv = CStoreInv (three cases)           │                │
│ L4  │ timely_* with local restartFree (RestartsPublic is a │ lean-framework,│
│     │ T7.14 option)                                        │ fgsa-lean      │
│ L5  │ KernelP internal; QF2/QF4 through the phase lemmas   │ S3d Q-6        │
│ L6  │ HTimeBestStatement: Rec_s g, horizon GST + B_best,   │ S3d Q-5; L21   │
│     │ now a wrapper over QualSearch (L21)                  │                │
│ L7  │ HonestSlot needs 0 < s; blueprint and spec edited    │ S3d Q-13       │
│ L8  │ One generic library, AvailableChain.Gen.*; Kit v2    │ lead; GLY §G   │
│     │ closes after 1c; rule F-31                           │                │
│ L9  │ fgsa_canon_accepts_all only for fgsaAdmissibleDelay; │ 1c B04; lead   │
│     │ fgsa_live_postGST (t ≥ GST + Δ); delay_eq_of_postGST │                │
│ L10 │ 1c-R: own design round; its NT-split output must     │ 1c r3.3; Astra │
│     │ pass before F5 closes                                │ 7              │
│ L11 │ T7.2 on its branch; merge after the port             │ lead; user     │
│ L12 │ ONE T7.12 statement over DeliveryWithin; slot-window │ fgsa-lean;     │
│     │ premise a named field with the §5 Trigger            │ lead (01 §10)  │
│ L13 │ SrcFrame (name); S1 §4.1 actions #16–#30 adopted     │ fgsa-lean      │
│ L14 │ Zero renames in F0–F2; E-3 same-name split; E-5      │ lead; reasons  │
│     │ additive bridge; plan lift P:178–183 additive only   │ corrected      │
│ L15 │ Recurrence windows start at q ≥ 1 (Rec_c: t ≥        │ user question; │
│     │ max(GST, 1)); examples at GST = 0                    │ Opus check     │
│ L16 │ Port to v4.34.1 + mathlib d13f23b7 by the S4p        │ user           │
│     │ procedure, before the final freeze                   │                │
│ L17 │ S3 §9: O09 kernel; O12; O14; O15 FGSAInterfaces;     │ lead           │
│     │ O16 window bodies; O19 flat imports; O22 GLY r3.7    │                │
│ L18 │ Throttle wrapper kept and fixed (cap, floor, guard); │ user delegated │
│     │ installed on v4.34.1; NUC for a second worktree      │                │
│ L19 │ actTime = admission threshold; AdmitSound; Trigger   │ Opus B1; Astra │
│     │ (emission | acceptance); timely core + 2 producers;  │ 1, 3           │
│     │ j = tick at T; k = strict deadline prefix            │                │
│ L20 │ excludes_process is an instance lemma, not a law     │ Opus §2.4      │
│     │ field                                                │                │
│ L21 │ QualSearch contract with Rec_s, Rec_c, Lit producers │ Opus §6; Astra │
│     │                                                      │ 8              │
│ L22 │ Clean zero-cut: superseded by L35                    │ Astra 8        │
│ L23 │ One cross-lane rule (P10); no lane imports another   │ Astra 6        │
│     │ lane's Export                                        │                │
│ L24 │ Homes of §3 (walk, C1, G24, G12, G21, phases, G17,   │ Opus D1–D10;   │
│     │ E-15); local fallbacks removed                       │ Astra 6        │
│ L25 │ Import rules of §4 (KitFG proof modules may import   │ Astra 4; Opus  │
│     │ Gen P/Pure; ClockLaws allow list; nthIdx? in Gen     │ C6, C7         │
│     │ S/V2/Reads; module-level check)                      │                │
│ L26 │ Spec 8ef4ed3b: quantifier, Honest(s) s > 0, Rec_c    │ Astra 9; Opus  │
│     │ one-way, exclusion-direction remark                  │ 18             │
│ L27 │ outWin body + Outage₂ fields fixed before G-F0a,     │ Opus §5.2      │
│     │ owner fgsa-lean (S3 D46 over X11)                    │                │
│ L28 │ G-F0a waits for its T7 and Gen producers (§9)        │ Opus B2; Astra │
│     │                                                      │ 7              │
│ L30 │ AdmitSound.timely takes `0 ≤ clockOf st` (false at a │ fgsa-lean      │
│     │ negative clock: slot-0 HEAD, now = −1); consumers    │ finding; lead  │
│     │ discharge it at run states (ClockLaws, in_horizon,   │                │
│     │ restore → 0). GLY r3.9 before the audit              │                │
│ L31 │ Shared import rule = lane rule without lanes:        │ fgsa-lean;     │
│     │ statement modules, Gen, KitFG, upstream libraries    │ lead           │
│     │ (EngineV2/KitV2, FGSA store, FGSARun), other Shared; │                │
│     │ never a lane proof or Export. HonestSlot home: Gen   │                │
│     │ S/V2/Reads (E-12)                                    │                │
│ L33 │ KitV2 stateBefore_step_induction and ownRecord_fold_ │ both A0 audits │
│     │ interval are the cores; Gen Induction/Fields forms   │ (Astra M1,     │
│     │ are corollaries (replaces A3); route for T7.9 A      │ Opus M1)       │
│     │ picked by the lead before T7.9 A                     │                │
│ L34 │ A law freezes after its generic proof and one        │ Opus M2        │
│     │ instance proof (E-9 proofs step 3; T7.7 before       │                │
│     │ G-F0a)                                               │                │
│ L35 │ Blueprint zero-cut edit reverted; CleanCut₂ without  │ Astra M2; Opus │
│     │ quorum (exact)                                       │ m1             │
│ L36 │ QualSearch body (T_q ≤ T_r ≤ T_q + gP, horizon       │ Opus M5; OPEN7 │
│     │ T_q + gP + 9Δ), hP : 0 < P on producers; B_best for  │ C3, C8;        │
│     │ every FF5 alternative ((g_f+2)P for Rec_F/Rec_F4,    │ s3-merge       │
│     │ γ(g_f)P for strong forms) or a register row          │ correction     │
│ L37 │ P10 written once with two exceptions (Export →       │ Opus M7        │
│     │ Claims/<F>; Assembly → Exports); same upstream list  │                │
│     │ everywhere                                           │                │
│ L32 │ accepted_by_deadline takes `t < dl t` at its trigger │ Astra (O25     │
│     │ time (r3.8 dropped it; counterexample: one node,     │ review); lead  │
│     │ dl t = t); Monotone dl not needed; GLY r3.10         │                │
│ L38 │ ACLaws is a law: its generic statement and the       │ Opus delta D1  │
│     │ T7.15 instance proof precede G-F0a (L34); S/AC/Reads │                │
│     │ statements in step 2                                 │                │
│ L39 │ Clean cut at b₀ = 0: F2 exports `cleanCut_zero`      │ Opus delta D3  │
│     │ (needs no F1 channel); Assembly splits on b₀ (F1     │                │
│     │ channels under FaultQ for b₀ > 0)                    │                │
│ L29 │ Gen RecoveryCore (P I E rho G) = {sync :             │ lean-framework │
│     │ PartialSynchrony E rho; gap : ∀ t ≥ GST, t + G ≤     │ answer to      │
│     │ horizon → ∃ s, t < proposalTime I s ≤ t + G ∧        │ fgsa-lean;     │
│     │ HonestSlot rho I s}. Recovery₂ extends it with base, │ GLY r3.9 after │
│     │ fault, awake, gapPos (FG-SA only); params dropped    │ the audit      │
│     │ (hδ binder); r3.3 names frozen; no rename or wrapper │                │
│ L40 │ count_rec takes hn : 0 < n (false at n = a = 0);     │ lean-framework │
│     │ count_clean concludes FaultQ n a, never FaultX       │ S4b-07; lead   │
│     │ (GLY r3.15, r3.16)                                   │                │
│ L41 │ Linked is required (Q5): FG safety fails without it  │ Q5 runs 1, 2;  │
│     │ (RowWire.toRow? drops the round; q5-wirecheck,       │ lead           │
│     │ q5b-check); spec 8ef4ed3b :189–191 implies it; Gen   │                │
│     │ linked_holder_eq, linked_card_le_of_holders          │                │
│ L42 │ P10 exact exceptions for Claims/*: the Claims root   │ fgsa-lean STOP;│
│     │ and facade FGSAClaims; Claims Tests/Axioms;          │ lead           │
│     │ FGSAProofs Proofs/Shared/Claims (claim → claim only) │                │
│ L43 │ hReady is a run premise, not an instance field;      │ fgsa-lean;     │
│     │ producers: non-block, wellFormed at handling, honest │ lead (c)+(iii) │
│     │ emission; proposal case by fgsa_hReady_of_parent-    │                │
│     │ Stored; K8 supplies hParent                          │                │
│ L44 │ SrcFrameAbove gets the genesis premise G1 (P3 form   │ F1.5 design;   │
│     │ refuted by Φ = False at index 0); certified = C1;    │ lead review    │
│     │ FrameBelow = FB1, cp*_of_srcFrame take RStore and    │                │
│     │ RFrameExact; T1 typing; every contest witness        │                │
│     │ extends B (P3 r3.5.7)                                │                │
│ L45 │ Freeze by per-entry manifest (FGSA, FGSARun,         │ lead           │
│     │ FGSAClaims Statements; D15 from G-F0a); later fields │                │
│     │ go in new structures extending FGSASafetyInterfaces  │                │
│     │ and FGSASafetyClaims; ReleasePrem: a < SA.release-   │                │
│     │ Threshold (bp 00:729)                                │                │
│ L46 │ One review or reviews from different models; fast    │ user;          │
│     │ tier only for bottleneck jobs; gate tiers, slots and │ lean-framework │
│     │ memory scope (BUILD r3.7); critical path 100 s, a    │                │
│     │ gate above 120 s blocks                              │                │
└─────┴──────────────────────────────────────────────────────┴────────────────┘
```

**T7.14 obligations:** (a) an old object re-admitted after a restart is
harmless, or the exclusion becomes durable; (b) the `restartFree`
premises of `timely_*` AND `accepted_by_deadline` (discharge or
RestartsPublic). Claims keep `NoRestart`, so claim Props do not change if
T7.14 picks durable exclusion; the AcceptanceLaw instance Inv and the
restartFree consumers can.

## 9. Gates and order of work

Historical gates (P3:242–247): **G-F0a** recorded the skeleton, reads, regimes,
recurrence forms, window specs (with OD10), safety claims and safety channel
tiers, and gates F2.0. **G-F0b** recorded HEALED, HEALING_INPUT, the
finality claims, the finality and healing tiers, QualSearch and the Shared
Fold/Phases statements, and gates F4 and F5.

G-F0a is gated BY T7 work: the regimes are F0b, and "F0b needs T7.2–T7.5"
(P3:242); F0.2 needs T7.6 item 3; F0.6a and F0.8a need T7.5 and T7.9 A.
The steps below are one dependency list. A step starts when every item it
names is done; items inside one step run in parallel.

```text
┌──────┬──────────────────────────────────────────────────────┬──────────────────────────────────────┐
│ Step │ Work                                                 │ Needs                                │
├──────┼──────────────────────────────────────────────────────┼──────────────────────────────────────┤
│ 0    │ Draft 3 fold (§12): GLY r3.11, S3 r3.3, T7 r14,      │ both audit reports                   │
│      │ P3 r3.5; delta check by both auditors → lead         │                                      │
│      │ adoption (user does not gate; reviews afterwards)    │                                      │
│ 1    │ Port (S4p procedure, §7): merge to main              │ final port gates                     │
│ 2    │ Statement round, a DAG (each item after the          │ steps 0 and 1                        │
│      │ declarations it uses): E-12 (+ nthIdx?, HonestSlot), │                                      │
│      │ Gen S/AC/Reads (ACReads, ACLaws; L38),               │                                      │
│      │ ownRecord_fold_restart statement (L33),              │                                      │
│      │ E-9 statements, E-11 statement, E-10 content, E-4    │                                      │
│      │ statements, E-1, E-3, E-19, E-15 (ChainOrder into    │                                      │
│      │ KitFG/Certificates), KitFG ViewLock/HonestRows,      │                                      │
│      │ checks (a)–(h), Generic manifest checker (Q-8);      │                                      │
│      │ T7.2 merge (rebase + R-A fix round)                  │                                      │
│ 3    │ E-9, E-11 and ownRecord_fold_restart PROOFS (lean-   │ step 2                               │
│      │ framework; seed AC/claude-files/a0/seeds); T7.3      │                                      │
│      │ (Interface), T7.4 (ClockLaws instance)               │                                      │
│ 4    │ T7.5 (CStoreInv; E-11); then T7.6 (after T7.4,       │ step 3                               │
│      │ T7.5), T7.9 A (after T7.5; HonestRows; the L33       │                                      │
│      │ fold route), T7.7 instances of AdmitSound,           │                                      │
│      │ AcceptanceLaw, HooksSound (after T7.4, E-11, E-9;    │                                      │
│      │ L34), FG part of E-13; T7.15 ACReads/ACLaws instance │                                      │
│      │ (after T7.3, T7.5, Gen S/AC/Reads; the ACLaws        │                                      │
│      │ instance PROOF before G-F0a, L38);                   │                                      │
│      │ T7.12a statement (T7.3 + E-9)                        │                                      │
│      │ → T7.12a gate (Astra + Opus; O28)                    │                                      │
│ 4b   │ E-5, E-14, E-16, E-18 and the E-7 proofs             │ step 2                               │
│      │ (lean-framework)                                     │                                      │
│ 5    │ F0 statements (P3 + S3 §8): Statements/Client,       │ step 4 (incl. the T7.7 instance      │
│      │ Statements/Windows (outWin + Outage₂), Receipt-      │ proofs); P3 reviewed                 │
│      │ Coverage; the G-F0a open items of §10; F4–F6 owners  │                                      │
│      │ confirm the horizon and pattern operations that      │                                      │
│      │ QualSearch/Fold/Phases need; FG-SA critical-path     │                                      │
│      │ measurement → **G-F0a** (FINAL freeze of A0)         │                                      │
│ 6    │ T7.8 (receipt)                                       │ T7.4–T7.7                            │
│      │ T7.11 (contentAgree_run)                             │ T7.5, FG part of E-13                │
│      │ T7.9 B; T7.10 (self-delivery)                        │ T7.7, T7.9 A                         │
│      │ T7.12 proof                                          │ T7.8, T7.11, T7.W                    │
│ 7    │ F lanes, needs per P3 §9.1. F1b.4: its store part    │ step 4b; G-F0a for F2.0              │
│      │ after T7.W + E-4, its run producer after T7.8. F2.8  │                                      │
│      │ after step 11                                        │                                      │
│ 8    │ Before G-F0b: healing and finality statements        │ G-F0a                                │
│      │ (F0.8b), QualSearch (L36), Statements/Fold and       │                                      │
│      │ /Phases (OPEN 7), O01 (paper check of H.11-Q and its │                                      │
│      │ QualSearch guard) → **G-F0b**                        │                                      │
│ 9    │ F4, F5 (F6 after the kernel)                         │ G-F0b                                │
│ 10   │ 1c r4 (written and reviewed in steps 0–2; whole-tick │ 1c:1782 list: T7.2, T7.5–T7.7,       │
│      │ freshness for firstAccept), each step after the T7   │ T7.9 B, T7.10, T7.W; T7.8/T7.12 for  │
│      │ tasks it reads; 1c-R design round; NT-split output   │ receipt                              │
│      │ before F5 closes                                     │                                      │
│ 11   │ T7.13 (assembly, report, audit, spec-citation tags)  │ 1c                                   │
│      │ T7.14 (durable restart; §8 obligations)              │ 2c                                   │
└──────┴──────────────────────────────────────────────────────┴──────────────────────────────────────┘
```

At every later step the same rule applies: a new shared statement is placed
by P1–P11 before its first consumer, and a claim change goes through the
register.

## 10. Open

```text
┌──────────┬────────────────────────────────────────────────────┬────────────────┬─────────────┐
│ Id       │ Item                                               │ Owner          │ Gate        │
├──────────┼────────────────────────────────────────────────────┼────────────────┼─────────────┤
│ O02      │ closed: local walk fallback removed (P3:5090)      │ —              │ closed      │
│ O04      │ F4 owner confirms windowEndA values                │ fgsa-lean      │ G-F0a       │
│ O05–O07, │ S3 §9.1 G-F0a items                                │ as in S3       │ G-F0a       │
│ O10, O13,│                                                    │                │             │
│ O18, O21 │                                                    │                │             │
│ O25      │ closed: LabelSync consumer check r5 (134eca23;     │ —              │ closed      │
│          │ AC/claude-files/a0/labelsync-consumers.md)         │                │             │
│ O27      │ S3a/INV follow-ups (sameLabel run field etc.)      │ fgsa-lean      │ G-F0a       │
│ O28      │ T7.12a field bodies                                │ T7 lead        │ T7.12a gate │
│ O29      │ 3d witness with δt ≠ 2R                            │ lean-framework │ none (3d)   │
│ O30      │ R4:18 GST = 1 note is stale                        │ lean-framework │ 1c r4       │
│ O31      │ GLY completion (now r3.8, §11)                     │ lean-framework │ G-F0a       │
│ O01      │ paper check of H.11-Q                              │ lead           │ G-F0b       │
│ ACLaws   │ Gen S/AC/Reads ACLaws: GateWrite/Reconcile/Gate-   │ lean-framework │ step 2      │
│          │ WriteSpec defs; output_step restart disjunct       │                │             │
│          │ (DECIDED); aclaws-inputs.md                        │                │             │
│ T7.15    │ FG-SA ACReads/ACLaws instance in FGSARun, with the │ fgsa-lean      │ T7 r15 §3.3 │
│          │ new store invariant lease_le_output (T7 r15        │                │             │
│          │ dfd3e96)                                           │                │             │
│ O20      │ G21 home: closed by L24                            │ —              │ closed      │
│ B-ZC     │ closed by L35: blueprint edit reverted; CleanCut₂  │ —              │ closed      │
│          │ = HealthyPrefix₂ (exact)                           │                │             │
│ other    │ O11, O17, O23, O24 (S3 §9, gates there)            │ as in S3       │ as in S3    │
└──────────┴────────────────────────────────────────────────────┴────────────────┴─────────────┘
```

Closed since draft 1: O03, O08 (D48), O12, O14 (S3:1385–1387); the spec
drift (spec 8ef4ed3b). Other notes: S1c §3.4 candidate strengthenings stay
with the blueprint owner (not claims); 01 §6.5 paired-run argument is
paper-only unless a Lean consumer appears.

## 11. Review fold (draft 1 → draft 2)

```text
┌───────────────────────────┬──────────────────────────────────────────────┬────────────────────┐
│ Review item               │ Fix (section)                                │ Document to change │
├───────────────────────────┼──────────────────────────────────────────────┼────────────────────┤
│ Opus B1, fixes 1–3;       │ actTime = admission threshold; AdmitSound;   │ GLY r3.8, T7 r13   │
│ Astra 1                   │ Trigger; timely core + 2 producers (§5)      │ (T7:1546–1547,     │
│                           │                                              │ T7.7, T7.8, T7.12) │
│ Opus fix 4 (§2.3);        │ accepted_by_deadline written form: 7 premise │ GLY r3.8           │
│ Astra 3                   │ groups, readiness producers, j/k (§5)        │                    │
│ Opus B2, fixes 5–6;       │ §9 one dependency list; G-F0a after T7.2–    │ this doc; P3 r3.4; │
│ Astra 7                   │ T7.5, T7.6, T7.9 A, T7.12a gate              │ T7 r13 (cites §9   │
│                           │                                              │ by step number)    │
│ Opus fix 7 (C2)           │ E-14 before F1 (§4)                          │ GLY r3.8           │
│ Opus fix 8 (C1)           │ S4p port procedure (§7)                      │ this doc           │
│ Opus fix 9; Astra 8a      │ QualSearch (§2, L21)                         │ S3 r3 (D11)        │
│ Opus fix 10 (D1–D6);      │ homes table (§3, L24); P3 reroute rows in    │ S3 r3, P3 r3.4     │
│ Astra 6                   │ S3 §8; S3 §2.4 Home column                   │                    │
│ Opus fix 11; Astra 10     │ three Inv cases listed (§5)                  │ T7 r13 (T7.7), GLY │
│ Opus fix 12               │ excludes_process not a field; Grid CO        │ GLY r3.8, T7 r13   │
│                           │ control store-level (§5, L20)                │                    │
│ Opus fix 13               │ O04 at G-F0a; open list; outWin owner (L27)  │ S3 r3 (X11)        │
│ Opus fix 14 (C4–C13)      │ T7 r12 cited; D01–D49; import rules;         │ this doc; GLY      │
│                           │ restartFree names per Schedule.lean:40;      │                    │
│                           │ TimelyClock fields; T7.13/T7.14 text; INV    │                    │
│                           │ 056c8c4c; build numbers and rule ids         │                    │
│ Opus fix 15               │ B3b; scoped checks + baseline; FG-SA         │ this doc; S4       │
│                           │ critical-path target (§7)                    │ §Build             │
│ Opus fix 16               │ input freeze (header)                        │ this doc           │
│ Opus fix 17               │ counts, TWalk m, P1 over GLY §B.2 (§1, §3)   │ this doc           │
│ Opus fix 18; Astra 9      │ spec 8ef4ed3b; exclusion direction           │ spec (done); T7    │
│                           │                                              │ r13 spec diffs     │
│ Astra 2                   │ O25 consumer check before G-F0a (§5)         │ fgsa-lean note     │
│ Astra 4                   │ import rules (§4, L25)                       │ GLY r3.8, S3 r3    │
│                           │                                              │ (D03)              │
│ Astra 5                   │ firstAccept_of_processed (§5)                │ GLY r3.8, 1c r4    │
│ Astra 8b                  │ Clean zero-cut: blueprint premise (§2, L22)  │ blueprint (done)   │
│ Astra 11                  │ build guarantee qualified (P7, §7);          │ this doc; GLY      │
│                           │ f_def exception; GLY Windows/Obs homes per   │                    │
│                           │ S3; RecoveryCore δ text                      │                    │
│ Opus D7–D11               │ K8 fallback text removed; KitV2 twins (P6);  │ P3, GLY, T7        │
│                           │ E-15 survivor; G17 instance; justified       │                    │
│                           │ copies keep their reason (§3, §4)            │                    │
└───────────────────────────┴──────────────────────────────────────────────┴────────────────────┘
```

## 12. Audit fold (draft 2 → draft 3)

Audits of draft 2 (ced1917d): `TS/codex/reports/a0-audit-astra.md`
(REVISE: B1, M1, M2, m1) and `TS/codex/reports/a0-audit-opus.md` (ADOPT
WITH FIXES: M1–M7, m1–m16, 24 fixes). Both passed every frozen generic
interface at the boundaries (Opus: 25 counterexample attempts) and the spec
edit 8ef4ed3b. Other inputs: fgsa-lean's OPEN 7 draft with its Astra review
(C1–C8), and `TS/codex/scratch/a0-audit-fold-inputs.md`.

```text
┌──────────────────────────────┬─────────────────────────────────────────┬────────────────────┐
│ Finding                      │ Fix                                     │ Document           │
├──────────────────────────────┼─────────────────────────────────────────┼────────────────────┤
│ Astra B1 FinForm.holds       │ one definition; public f.lo ≤ g apart   │ P3 r3.5            │
│                              │ from the transformed width; holds_iff   │                    │
│                              │ checked at the minimum g of every form  │                    │
│ Astra M1 / Opus M1 (A3)      │ L33 KitV2 cores; Gen forms corollaries  │ SYN; GLY r3.11     │
│                              │                                         │ (G08, E-10, FOLDS);│
│                              │                                         │ T7 r14 (T7.5,      │
│                              │                                         │ T7.9 A); S3:1388   │
│ Astra M2 / Opus m1 zero cut  │ L35 blueprint revert; CleanCut₂ without │ BP (done); S3 D56; │
│                              │ quorum                                  │ P3 r3.5            │
│ Opus M2 law freeze           │ L34, P11; §9 steps 3–5                  │ SYN (done); T7 r14 │
│ Opus M3, M4 missing steps    │ §9 steps 2, 3, 4, 4b                    │ SYN (done); GLY    │
│                              │                                         │ r3.11 (E-7 owner)  │
│ Opus M5; OPEN 7 C3, C4, C8   │ L36 QualSearch body, hP, FF5 B_best     │ P3 r3.5; S3 D50,   │
│                              │                                         │ :651; SYN (done)   │
│ Opus M6; Astra m1 homes      │ GLY §B G21, G35, G37, F-26 target;      │ GLY r3.11; S3 §4.1;│
│                              │ Shared homes of G20, G30, G31, G33;     │ P3; S1 note        │
│                              │ S1 supersession note → SYN §3           │                    │
│ Opus M7 P10 texts            │ L37, P10 written once                   │ SYN (done); BUILD  │
│                              │                                         │ r3.2; S3 §4.2      │
│ OPEN 7 C1, C2 (KernelP       │ PhasesInternal imported by the F4 tree  │ S3 r3.3, P3 r3.5   │
│ importer; proof order)       │ only (not Shared); one proof order,     │ (fgsa-lean, G-F0b) │
│                              │ decided in OPEN 7                       │                    │
│ OPEN 7 C5, C7                │ Rec_s out of the Healing premises;      │ S3; SYN P6 (done)  │
│                              │ P6 wording                              │                    │
│ Opus m2, m6, m10, item 24    │ hrestore = 0 text; readiness 4(b) at    │ T7 r14; GLY r3.11  │
│                              │ w's own envelope + handles_wellFormed;  │                    │
│                              │ proposal raw/support not transported;   │                    │
│                              │ spec runs with no-op deliveries dropped │                    │
│ Opus m3, m4, m5, m8          │ one written AdmitSound form (GLY);      │ GLY r3.11; SYN     │
│                              │ hhor reason or drop; delete GLY:310–312 │                    │
│ Opus m7, m9, m12, m14, m15   │ stale text; F-lane needs cite P3 §9.1;  │ SYN (done in §9),  │
│                              │ H-time summary (done); E-14 deletion    │ S3, P3             │
│                              │ row; best H-time witness X-row          │                    │
│ Opus m13; Astra m1 build     │ lane rule in check (e); FG-SA critical- │ BUILD r3.2         │
│                              │ path target (wall time) set at G-F0a    │                    │
└──────────────────────────────┴─────────────────────────────────────────┴────────────────────┘
```

## 13. Post-adoption fixes (delta checks: `TS/codex/reports/a0-delta-{astra,opus}.md`)

```text
┌──────────────────────────────────────────────┬────────────────┬────────────────────┐
│ Fix                                          │ Owner          │ Gate               │
├──────────────────────────────────────────────┼────────────────┼────────────────────┤
│ Phase-proof home = F4 tree everywhere (S3    │ fgsa-lean;     │ step 2 (before any │
│ D52/D78/§4.2 :451 :1225 :1877; P3 :920 :3219 │ lean-framework │ phase module)      │
│ :3633; build.md :178–181)                    │ (build.md)     │                    │
│ L38 ACLaws: T7.15 proof before G-F0a; S/AC/  │ fgsa-lean (T7),│ G-F0a              │
│ Reads in step 2 (T7 §1 step 4, §3.3; GLY     │ lean-framework │                    │
│ :466 step list)                              │ (GLY)          │                    │
│ L39 cleanCut_zero exported; Assembly split   │ fgsa-lean (S3, │ G-F0a              │
│ on b₀ (P3 :7058, :7085–7087)                 │ P3)            │                    │
│ AGREED: LeaseBelowOutputStore p st, a new    │ lean-framework │ statement step 2;  │
│ E-11 bundle conjunct (Reachable stores; FGSA │ (E-11), fgsa-  │ proof step 3;      │
│ Statements/Invariants); T7.5 lifts; T7.15    │ lean (T7)      │ T7.5, T7.15        │
│ derives the ACLaws field                     │                │                    │
│ Cite GLY §C.3 for AdmitSound/timely/receipt, │ fgsa-lean (S3  │ G-F0a              │
│ no restated binders (S3 :519 :1614 D35 hhor; │ D35, T7)       │                    │
│ T7 :1868–1871)                               │                │                    │
│ Remove T7-local record-fold fallback (T7     │ fgsa-lean      │ step 4 (T7.9 A)    │
│ :2288) and "route OPEN" text; T7 §1 step 4   │                │                    │
│ lists T7.15                                  │                │                    │
│ S3 D50/O33 match corrected L36               │ fgsa-lean      │ G-F0b              │
│ DONE: cross-lane Props in ChannelProps;      │ fgsa-lean +    │ step 2             │
│ Channels = read definitions only             │ lean-framework │                    │
│ BUILD: "three known exceptions" (P7); Shared │ lean-framework │ step 2             │
│ list current                                 │                │                    │
│ GLY E-14: Grid CO copies deleted after F2 (P3│ lean-framework │ step 2             │
│ r3.5.1 :5293–5297)                           │                │                    │
│ DONE: S3 r3.4 1bedacd2, T7 r16 4d11b505      │ fgsa-lean;     │ checked by lead    │
│ (535b930), P3 r3.5.1 c4e94221                │ lead check     │                    │
│ Hash and citation drift in S3/T7/P3/GLY      │ owners         │ next revision      │
└──────────────────────────────────────────────┴────────────────┴────────────────────┘
```

P0d7a3 owns FGCompose Statements/FinalityKernel and Proofs/Finality/MiddleSupport
and Middle. FG-SA keeps its public middle record and theorem signatures. Private
fieldwise adapters bind the same service point, selected early carrier, fresh entry,
and through-action caps. The conditional shield route uses the published d7a2 seed
leaves and historical transfer, including the cutoff-to-service-start gap.
