module
public import AvailableChainSimplexFG
public import AvailableChainKitFG.Ancestry
public import AvailableChainKitFG.Certificates
public import AvailableChainKitFG.Accountable
public import AvailableChainKitFG.ClientSafety
public import AvailableChainKitFG.Correspondence
public import AvailableChainKitFG.Provenance
public import AvailableChainKitFG.CausalCap
public import AvailableChainKitFG.CrossingNoFinal
public import AvailableChainKitFG.InBandLock
public import AvailableChainKitFG.TwoChanges

@[expose] public section

namespace AvailableChain.KitFG

/-! # The pin table of the FG module (DC-fj)

Each pin is one id of `docs/FG-COMPOSITION.md`. It records its coverage CLAUSE
BY CLAUSE (Astra G08); there is no `full` tag for an id. A clause is covered by
Lean names (with their extra hypotheses), or it names the paper step, the
registry id or the AP fact that carries it. A clause that the Lean statements
only ASSUME is `byHyp`: it names the hypothesis and the lemmas that can
discharge it. A row that a definition covers (with at most an unfolding lemma)
is `leanHyp … "definition only"`. A clause can also cite a `[helper]` theorem
that is one branch, a special case or a partial form of the clause
(`on_block_of_refused`, `crossing_other_entry`, `Fmove_below`,
`twoChanges_nested`); its docstring says which. Every other cited theorem has a
`[pin <id>]` docstring; a definition cited in `defPins` can be `[helper]`
(`derive`, `createRow`). A name can be cited under an id other than the id of its
tag: the tag names its main id, and a row of another id can use it (for example
`mem_filteredFrom`, tagged `fj.frame.v4`, in `fj.frame.v1`).

`scripts/FGPinIds.lean` prints `manifest` of the elaborated values, and
`scripts/check-fg-pins.sh` checks it against the registry. `scripts/FGPinIds.lean
--check-names` checks that every Lean name of this table is a constant of the
two FG libraries, so that `scripts/CheckFGAxioms.lean` checks its axioms.
`scripts/check-fg.sh` builds the two libraries and runs every check.

A clause can also cite constants of a library above the FG libraries with
`leanIn lib names` (single-backtick names, so this file does not import that
library). `scripts/FGPinIds.lean` rejects a `lib` that is not on its allowlist,
and `scripts/check-fgsa.sh` checks those names in the environment of `lib`. The
pin gate for a pin with `leanIn` evidence is `scripts/check-fg.sh` plus
`scripts/check-fgsa.sh`.

A registry id in the free text of a clause (its label or a string field) is a
dependency of the pin: the manifest records it (`mention`), and the pin check
applies the status rule to it as to an `.ap` or `.external` id. A citation that
is only history goes inside a `(history: …)` marker, which the scan skips. This
file does not import a library above the FG libraries; `scripts/CheckFGAxioms.lean`
checks the import closure of the two FG roots.

ROOT-DIGEST W1; DC RootInjectiveOnAncestors. `ViewRootInj` and `RootInjectiveOn`
are explicit local premises. The shared model stores a root field and makes
no global injectivity claim. FG-SA admission proves local store uniqueness;
its run contract supplies cross-store root equality on scoped bodies. -/

/-- A registered source: its §0.1 key in FG-COMPOSITION.md, its directory
root, its path under that root, and its full SHA-256. -/
structure Src where
  key : String
  root : String     -- "tsc" | "spec" | "blueprint" | "vc@b97b902" | "research@9f5ed71"
  path : String     -- tsc: the registered name, resolved to tsc/archive/ by hash
  sha256 : String
  deriving BEq

/-- How one clause of a registry entry is covered. -/
inductive Cov where
  | lean (names : List Lean.Name)                   -- a theorem proves it; no extra
                                                    -- hypothesis
  | leanIn (lib : String) (names : List Lean.Name)  -- as `lean`, with constants of the
    -- library `lib` above the FG libraries (not imported here: single-backtick names);
    -- scripts/check-fgsa.sh checks them in the environment of `lib`
  | leanHyp (names : List Lean.Name) (hyps : String) -- proved with these hypotheses, or
                                                    -- "definition only"
  | byHyp (names : List Lean.Name) (hyp : String) (discharge : String)
    -- NOT proved: the Lean statements `names` assume the clause as the hypothesis
    -- `hyp`; `discharge` names the lemmas or ids that can prove it
  | paper (step : String)                           -- a paper step in the entry
  | external (id : String) (note : String)          -- carried by another registry id
  | ap (id : String) (note : String)                -- an AP service fact (registry id)
  | apData (what : String)                          -- AP data; no registry id
  | runFact (what : String)                         -- a comp run fact; no registry id
  | open_ (why : String)                            -- not covered yet

/-- One clause of a registry entry and its coverage. -/
structure Clause where
  label : String
  cov : Cov

/-- One registry id, its sources, and the coverage of each clause. -/
structure Pin where
  id : String
  sources : List Src
  clauses : List Clause

/-- An executable definition and the spec text that it follows. -/
structure DefPin where
  lean : Lean.Name
  src : Src
  lines : String

/-! ## Sources (registry §0.1) -/

def r148 : Src := ⟨"r148", "tsc", "fj-redteam.md",
  "934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2"⟩
def r143 : Src := ⟨"r143", "tsc", "fgsa-fast.md",
  "8907540c5c71fe06703bc8d2ec2d30bc6cbc752a5f7577219a69196e2fd8ef37"⟩
def r144 : Src := ⟨"r144", "tsc", "fgsa-no-nj.md",
  "1eaf728ffc4d56cc54fbccf581a8dffe457da02b96bd59cedb012bbf5ee1e03a"⟩
def r146 : Src := ⟨"r146", "tsc", "fgsa-adjudicate.md",
  "0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017"⟩
def r147 : Src := ⟨"r147", "tsc", "fgsa-conditional.md",
  "940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5"⟩
def bp : Src := ⟨"bp", "tsc", "fgsa-healing-blueprint.md",
  "4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318"⟩
def spec : Src := ⟨"spec", "spec", "archive/fgsa-protocol-ae4497ab.tex",
  "ae4497abc7c5b3a6f73697f341bf730a63c7d34bd2f7546154bd022bc95af223"⟩
def alfs4 : Src := ⟨"alfs4", "spec", "archive/fgsa-protocol-bd942ca0.tex",
  "bd942ca0bce0b4251b969a503a8c8175db87494ab93bf028e3a2303b7683dda7"⟩
/-- The adopted FG-SA spec (2026-09-29): the SA walk starts at Σ.F, no rule
deletes a block of Σ.T, and the pre-GST delivery clause. -/
def fgsa3 : Src := ⟨"fgsa3", "spec", "archive/fgsa-protocol-c1ea1db0.tex",
  "c1ea1db08f1da37bcde075df5d70f23af7c9941bd05ae5e8aca1bb48d1b777ed"⟩
/-- The adopted blueprint (2026-09-29), chapters 00 and 01 (archive copies). -/
def bp00 : Src := ⟨"bp00", "blueprint", "archive/00-outline-e6dcbcc1.md",
  "e6dcbcc1859dca4e9f30f7f947b6608ac4e1ab55b99cd1c562bd1f827965647d"⟩
def bp01 : Src := ⟨"bp01", "blueprint", "archive/01-foundations-200c9c07.md",
  "200c9c07a01bd5826750d0e89a985be87e588f98132a68534cdd719531302a99"⟩
def ldp : Src := ⟨"ldp", "tsc", "fgsa-live-dc-port.md",
  "816776723e439f24612c409f2007c2a236bb3fa2dbde605c68516333ee4c7b38"⟩
def r161 : Src := ⟨"r161", "tsc", "filtered-base.md",
  "fd8e07fe667afae28dee2bc9a54d6c7fc46b49f9bb268865f98818decc308354"⟩
def dc : Src := ⟨"dc", "research@9f5ed71", "healing/rewrite/consensus.tex",
  "dc471b47a46896fe0a3df300c188fef1512f475615ce0fc0df18dbea6d2e5517"⟩
def vcE : Src := ⟨"vcE", "vc@b97b902",
  "DecoupledConsensusProofs/Protocol/ValidatorClient/Engine.lean",
  "92fb0e64c1288afea98b53212cb3ad5c843c9c720187367eea578d17a9d53454"⟩
def vcF : Src := ⟨"vcF", "vc@b97b902",
  "DecoupledConsensusProofs/Protocol/ChainState/FinalityComparison.lean",
  "aa0ed92740eb1ec8ee69e90fd2ae75f03179a27c05accf5f631e7a254589b94c"⟩
def vcW : Src := ⟨"vcW", "vc@b97b902",
  "DecoupledConsensusProofs/Protocol/ValidatorClient/WeakHeightBounds.lean",
  "f0d45fa7fd93a0a1c9f4dfccaf6c3f7c63c43245c5deee7182a25f3963c22b5d"⟩

/-! ## The pins -/

open AvailableChain.SimplexFG in
/-- The clause-level pin table. -/
def pins : List Pin := [
  -- The FG-SA frame (registry 2026-09-29; fgsa3 = spec c1ea1db0; blueprint 00 §3,
  -- 01 §4, §6, §11). Trees clauses 0, 1, 2, 3a, 3b, 4 of the registry entry; the
  -- other clauses are v3's, with fgsa3 line numbers (the pinned text is identical).
  { id := "fj.frame.v4", sources := [fgsa3, ldp, r161], clauses := [
    ⟨"Trees 0: Σ.T is parent-closed and cumulative; a new block enters it only if it \
      extends F (fgsa3 489–492)",
      .leanHyp [``Store, ``storeInv_init, ``storeInv_on_block, ``on_block_TF_subset,
          ``update_finality_TF]
        "parent closure is StoreInv.closed (storeInv_init, storeInv_on_block; \
        ViewRootInj on the new Σ.T when B is accepted, the local root premise); \
        cumulativity needs no hypothesis"⟩,
    ⟨"Trees 1: a block of Σ.T outside the active view whose state height exceeds the \
      entry height of the accepted finalization's certificate (0 for genesis) needs a \
      slashable conflict (fgsa3 502–506)",
      .external "fg.finalLock.v2" "the accepted-carrier wrapper (certificate entry \
        height, genesis normalization) is open in the pin fg.finalLock.v2"⟩,
    ⟨"Trees 2: no rule deletes a block of Σ.T; storage pruning is a retention item \
      (fgsa3 506–511); FG store: on_block and update_finality keep TF",
      .lean [``on_block_TF_subset, ``update_finality_TF]⟩,
    ⟨"Trees 2, FG-SA store: a delivery keeps st.fg.TF (⊆), a tick keeps it (=)",
      .leanIn "AvailableChainFGSA"
        [`AvailableChain.FGSA.process_cumulative, `AvailableChain.FGSA.clock_cumulative]⟩,
    ⟨"Trees 2, remark: deleting a block outside the active view can change the HEAD \
      and S, also at a ≤ f (fgsa3 507–510)",
      .paper "a counterexample fact (FR M1, N2; blueprint 01 §11.1–§11.2), not an \
        output-preservation claim"⟩,
    ⟨"Trees 3a: the confirmation walk starts at Σ.F in act(Σ); it returns a block only \
      if that block passes the strict-majority test, also when the block is Σ.F \
      (fgsa3 511–513, 1289–1306): gateStep_fresh states that the saved result of an \
      unsaved joined gate is SA.confirmationFrom (an AvailableChainSA constant, the anchor) \
      from Σ.F on the active view; clock_eq_saClockFrom_gate is the joined tick",
      .leanIn "AvailableChainFGSA"
        [`AvailableChain.FGSA.gateStep, `AvailableChain.FGSA.fastSet,
          `AvailableChain.FGSA.gateStep_fresh, `AvailableChain.FGSA.clock_eq_saClockFrom_gate]⟩,
    ⟨"Trees 3b: the FJ viability and band filter does not restrict the SA \
      confirmation walk (fgsa3 514–515)",
      .apData "the SA confirmation walk; the HEAD, proposal and FG duties use the \
        filter, the SA walk does not"⟩,
    ⟨"Trees 4: act(Σ) is a view of Σ.T (fgsa3 493–496)",
      .lean [``activeView, ``activeView_subset]⟩,
    ⟨"Trees 4: the SA base reads only the active view: the gate, release, resolution, \
      saved-result tests, leases and the confirmation walk (fgsa3 497–499)",
      .apData "the SA base of the composite runs on the active view (FG-SA actView); \
        no FG definition or lemma reads activeView"⟩,
    ⟨"on_block: duplicate, parent, F ⋠ B and parent-slot refusals before the state \
      computation (fgsa3 944–969)",
      .leanHyp [``on_block, ``on_block_of_refused, ``storeInv_on_block]
        "the refused branch changes nothing (on_block_of_refused); FG admission \
        input contract: the future-slot bound (line 946), the proposer signature \
        (lines 950–951) and the row-round check (lines 954–957)"⟩,
    ⟨"fg_contest, band_floor, get_fg_root on the live caches; contest over Σ.T \
      (fgsa3 1122–1138, 1156–1163)",
      .leanHyp [``storeControls, ``Controls.rootIsJ, ``Controls.Z, ``Controls.lo,
          ``storeControls_eq_fjControls]
        "StoreInv (ViewRootInj is used only by storeInv_on_block; the local root premise)"⟩,
    ⟨"viable_tree_from and get_filtered_block_tree_from on any block set \
      (fgsa3 1140–1146, 1165–1172)",
      .leanHyp [``filteredFrom, ``mem_filteredFrom]
        "definition only (mem_filteredFrom unfolds filteredFrom)"⟩,
    ⟨"get_filtered_block_tree: the filter of Σ.T (fgsa3 1173–1177)",
      .leanHyp [``storeFrame, ``storeFrame_full] "StoreInv"⟩,
    ⟨"viable_tree: acceptance only, band hmax−1 also in a contest (fgsa3 1148–1154)",
      .leanHyp [``acceptViable, ``frameViable_subset_accept]
        "a StoreInv binder that the proof does not use (the Lean fact holds for \
        every store: a stronger form)"⟩,
    ⟨"update_finality: hmax, lex-order J update, F acceptance (fgsa3 999–1012)",
      .leanHyp [``update_finality, ``storeInv_on_block]
        "ViewRootInj on the new Σ.T when B is accepted (lex order, lines 1002–1005); \
        the local root premise proves it"⟩,
    ⟨"reconcile_with_finality: SA fields only; Σ.T and hmax unchanged (fgsa3 1014–1034)",
      .apData "it writes no FG field"⟩,
    ⟨"live_root and get_head_in_tree (fgsa3 1226–1247)",
      .ap "ap.headReachesLo.v6" "clauses 1–2: the head is in D_V with height ≥ lo if \
        the anchor is in D_V or has an eligible child there; otherwise the head is \
        the anchor"⟩,
    ⟨"voter_processed_block_tree, voter_filtered_block_tree, the HEAD duty call \
      (fgsa3 1361–1376, 1437–1439)",
      .apData "the frozen block set; filteredFrom takes it as a parameter"⟩ ] },
  -- HISTORICAL (historicalPins): WITHDRAWN for current use 2026-09-29, successor
  -- fj.frame.v4. Not true as pinned: the deletion clause (alfs4 368–369) is refuted
  -- also under alfs4 (blueprint 01 §11.2 N2), and fgsa3 511–513 changes the
  -- genesis-walk clause. The pins below are the alfs4 history, unchanged.
  -- The ALFS frame with the filtered base (registry 648f255, note 504f5ae; alfs4).
  -- ALFS fields read only by the AP (act(Σ), the confirmation walk) are .apData clauses.
  -- History: fj.frame.v2 (4bc6690; alfs, alfs2, alfs3) is SUPERSEDED by v3.
  { id := "fj.frame.v3", sources := [alfs4, ldp, r161], clauses := [
    ⟨"Trees: Σ.T is parent-closed and cumulative (alfs4 352–356)",
      .leanHyp [``Store, ``storeInv_init, ``storeInv_on_block, ``on_block_TF_subset,
          ``update_finality_TF]
        "parent closure is StoreInv.closed (storeInv_init, storeInv_on_block; \
        ViewRootInj on the new Σ.T when B is accepted, the local root premise); \
        cumulativity needs no hypothesis"⟩,
    ⟨"Trees: act(Σ) is a view of Σ.T (alfs4 356–359)",
      .lean [``activeView, ``activeView_subset]⟩,
    ⟨"Trees: only the SA base reads act(Σ) (alfs4 360–362)",
      .apData "no FG definition or lemma reads activeView"⟩,
    ⟨"Trees: a block of Σ.T outside the active view above Σ.h_F needs a slashable \
      conflict (alfs4 365–367)",
      .external "fg.finalLock.v1" ""⟩,
    ⟨"Trees: a node can delete blocks outside the active view; with a ≤ f no output \
      changes (alfs4 368–369)",
      .paper "spec claim at a ≤ f; the Lean store keeps the cumulative tree"⟩,
    ⟨"Trees: the confirmation walk starts at genesis; the FJ filter does not restrict \
      it (alfs4 369–371)",
      .apData "the SA confirmation walk"⟩,
    ⟨"on_block: duplicate, parent, F ⋠ B and parent-slot refusals before the state \
      computation (alfs4 792–817)",
      .leanHyp [``on_block, ``on_block_of_refused, ``storeInv_on_block]
        "the refused branch changes nothing (on_block_of_refused); FG admission \
        input contract: the future-slot bound (line 794), the proposer signature \
        (lines 798–799) and the row-round check (lines 802–805)"⟩,
    ⟨"fg_contest, band_floor, get_fg_root on the live caches; contest over Σ.T \
      (alfs4 970–986, 1004–1011)",
      .leanHyp [``storeControls, ``Controls.rootIsJ, ``Controls.Z, ``Controls.lo,
          ``storeControls_eq_fjControls]
        "StoreInv (ViewRootInj is used only by storeInv_on_block; the local root premise)"⟩,
    ⟨"viable_tree_from and get_filtered_block_tree_from on any block set \
      (alfs4 988–994, 1013–1020)",
      .leanHyp [``filteredFrom, ``mem_filteredFrom]
        "definition only (mem_filteredFrom unfolds filteredFrom)"⟩,
    ⟨"get_filtered_block_tree: the filter of Σ.T (alfs4 1021–1025)",
      .leanHyp [``storeFrame, ``storeFrame_full] "StoreInv"⟩,
    ⟨"viable_tree: acceptance only, band hmax−1 also in a contest (alfs4 996–1002)",
      .leanHyp [``acceptViable, ``frameViable_subset_accept]
        "a StoreInv binder that the proof does not use (the Lean fact holds for \
        every store: a stronger form)"⟩,
    ⟨"update_finality: hmax, lex-order J update, F acceptance (alfs4 847–860)",
      .leanHyp [``update_finality, ``storeInv_on_block]
        "ViewRootInj on the new Σ.T when B is accepted (lex order, lines 850–853); \
        the local root premise proves it"⟩,
    ⟨"reconcile_with_finality: SA fields only; Σ.T and hmax unchanged (alfs4 862–882)",
      .apData "it writes no FG field"⟩,
    ⟨"live_root and get_head_in_tree (alfs4 1074–1095)",
      .ap "ap.headReachesLo.v5" "clauses 1–2: the head is in D_V with height ≥ lo if \
        the anchor is in D_V or has an eligible child there; otherwise the head is \
        the anchor"⟩,
    ⟨"voter_processed_block_tree, voter_filtered_block_tree, the HEAD duty call \
      (alfs4 1207–1222, 1283–1285)",
      .apData "the frozen block set; filteredFrom takes it as a parameter"⟩ ] },
  -- The view form of r148 FJ_FRAME (not superseded): fjControls and fjFrame.
  -- The (0, genesis) fallback of lexMax is the least key only because
  -- genesisRoot = ⟨0⟩ (lexKey_fallback_le and lexMax_mono use `rfl` for it).
  { id := "fj.frame.v1", sources := [r148, spec], clauses := [
    ⟨"FJ_FRAME: H, (j, J), contest, the Z/lo table, viable, D (r148 148–169)",
      .leanHyp [``fjControls, ``fjFrame, ``fjFrame_lo, ``fjFrame_D]
        "definition only; F is a parameter (the caller's F, not 'current accepted \
        F'); the definitions assume nothing; lexMax is the lex-greatest pair under \
        ViewRootInj (§0.4), an explicit local premise, so the \
        selector falls back to (0, genesis) only on an empty candidate set"⟩,
    ⟨"get_fg_root and get_filtered_block_tree_from (r148 171–175)",
      .leanHyp [``fjFrame] "definition only"⟩,
    ⟨"the contest witness at H = j+1: some W of the view with h(W) = j+1 and J ⋠ W \
      (r148 260–265)",
      .leanHyp [``fjControls, ``fjFrame] "definition only (the contest bit)"⟩,
    ⟨"ancestor closure makes the witness a conflicting crossing of j in the view \
      (r148 267–268), direction witness ⇒ crossing",
      .leanHyp [``crossing_other_entry]
        "PARTIAL: a W with h(W) > j and J ⋠ W has, on its chain, a crossing of j \
        that names X ≠ J with a matching quorum; RootInjectiveOn B W \
        (the pair root premise) and h_j ≠ 0; \
        that the crossing block is in the view (ancestor closure) is not stated; \
        J is `(derive B).J` of a carrier B, not the frame's J (the link to the \
        frame's (j, J) is `lexMax` under ViewRootInj, the local root premise)"⟩,
    ⟨"the converse (a conflicting crossing of j in the view gives a witness) \
      (r148 267–268)",
      .paper "r148 lines 267–268; no Lean"⟩,
    ⟨"all frontier blocks extend J exactly when there is no witness (r148 268–269)",
      .leanHyp [``fjControls] "definition only (the contest bit)"⟩,
    ⟨"fgsa_head: lease anchor, score, eligibility, GHOST (r148 177–185)",
      .ap "ap.headReachesLo.v1" ""⟩,
    ⟨"change viability in a contest (r148 188–192)",
      .leanHyp [``fjFrame_lo, ``mem_filteredFrom]
        "definition only (fjFrame_lo is rfl; mem_filteredFrom unfolds filteredFrom)"⟩,
    ⟨"change below-band eligibility in a contest (r148 188–192)",
      .ap "ap.headReachesLo.v1" ""⟩ ] },
  -- ALFS note (registry 4bc6690): frozen-tree forms of (2) and (3) are ldp L5/L6.
  -- The registry (548914c) uses the Lean names filteredFrom_reachesLo and
  -- filteredFrom_viable_child; the plan names at befb5d5 were fjFrame_D_reachesLo
  -- and fjFrame_viable_child.
  { id := "fj.frameFeasible.v1", sources := [r148], clauses := [
    ⟨"(1) a nonempty D reaches lo", .lean [``filteredFrom_reachesLo]⟩,
    ⟨"(2) D is not empty under (a) and (b)",
      .leanHyp [``fjFrame_D_nonempty, ``storeFrame_feasible]
        "fjFrame: (a) K ∈ V finalizes F, (b) the carrier clause of fg.finalLock.v2, Lean \
        finalLock, pure form (history: fg.finalLock.v1, registry §9), ViewRootInj \
        (the local root premise); \
        stronger form: the proof of fjFrame_D_nonempty does not use ViewRootInj or \
        σ[K].F = F (binders kept); store form: StoreInv gives (a) on Σ.T, (b) and \
        ViewRootInj on Σ.T are hypotheses"⟩,
    ⟨"(3) Z ∈ D under (a) and (b)",
      .leanHyp [``fjFrame_Z_mem_D, ``storeFrame_feasible]
        "(a); (b); ViewRootInj (the local root premise); V ancestor-closed"⟩,
    ⟨"(4) below lo every block of D has a child in D",
      .leanHyp [``filteredFrom_viable_child] "any controls; the block set is ancestor-closed"⟩,
    ⟨"(2), (3) on the frozen voter tree of a HEAD duty (the ALFS note; the same \
      functions in fgsa3: voter trees 1361–1376, get_head_in_tree 1240–1247)",
      .ap "ap.headReachesLo.v6" "not unconditional: a late contest can empty D_V, ldp \
        L6; the plan reads clause 3, Z ∈ D_V from D_V ≠ ∅, as filteredFrom_Z_mem (the \
        plan's reading, not a registry discharge)"⟩,
    ⟨"the walk below lo (last two pinned sentences), view form: the head read from a \
      duty view is in D with state height ≥ lo, under the v1 premises (fj.frame.v1, \
      R1 duty views, the carrier clause of fg.finalLock.v2 (history: fg.finalLock.v1, \
      registry §9) and a ≤ f); no unfiltered fallback",
      .ap "ap.headReachesLo.v1" ""⟩,
    ⟨"the walk below lo (last two pinned sentences), FG-SA form (fgsa3 1226–1247): the \
      HEAD is in D_V with state height ≥ lo if its anchor A = live_root is in D_V or \
      has an eligible child in D_V; otherwise the HEAD is A (v6 clause 2)",
      .ap "ap.headReachesLo.v6" "clauses 1–2"⟩ ] },
  -- Port difference: accountable_oriented (the helper behind `accountable`) gives
  -- HasE1WeightBetween of the two chains' rows; DC's namedAccountableSafety_oriented
  -- pins the pair (HasE1WeightAt). The Lean form is weaker, and enough for the clause.
  { id := "fg.accountable.v1", sources := [r143, r148], clauses := [
    ⟨"conflicting finalizations give 2q−n E1/E2 identities, without NJ",
      .leanHyp [``accountable] "RootInjectiveOn (the pair root premise)"⟩,
    ⟨"under a≤f conflicting finalizations are impossible", .paper "2q−n > a"⟩,
    ⟨"local F never retreats", .lean [``update_finality_F_mono, ``on_block_F_mono]⟩,
    ⟨"finalized ⪯ available at every read", .external "comp.outputNesting.v1" ""⟩ ] },
  { id := "fg.uniqueJust.v1", sources := [bp, vcE], clauses := [
    ⟨"Lemma U: two target quorums for different entries give 2q−W E2 weight",
      .lean [``uniqueJust]⟩,
    ⟨"Lemma U, chain form: two chains justified at one height have one J, or E2 \
      weight exists between their rows",
      .leanHyp [``uniqueJust_chains] "RootInjectiveOn (the pair root premise)"⟩,
    ⟨"at most one justified entry per height in the whole run",
      .paper "2q_F−n > a and honest E2 compliance"⟩ ] },
  -- The finality lock at the accepted threshold (registry 2026-09-29; blueprint 01
  -- §8.2, 00 §3). finalLock_e1 and finalLock are carrier forms: the threshold is
  -- h_F of a chain B. The accepted-carrier wrapper is open.
  { id := "fg.finalLock.v2", sources := [bp01, bp00], clauses := [
    ⟨"carrier form: for a chain B and a block W with h(W) > h_F(B), W extends F(B), or \
      B's finality rows and W's crossing rows give 2q−W E1 weight (no fault bound); \
      h_F(B) = 0 gives F(B) = genesis (bp01 701–723, 741–743)",
      .leanHyp [``finalLock_e1, ``finalLock]
        "RootInjectiveOn B W (the pair root premise); finalLock is the slashable-or \
        form; the threshold is the carrier's h_F, not yet the accepted certificate's \
        entry height"⟩,
    ⟨"accepted-carrier wrapper: for the accepted F at e, finheight(F,e) is 0 for \
      genesis and else the entry height of its accepted certificate; the carrier \
      form holds at that threshold (bp01 725–743, bp00 643–651; paper argument bp01 \
      734–736)",
      .open_ "accepted-carrier wrapper: proof pending (r213b item 2)"⟩,
    ⟨"under a ≤ f and honest client discipline, F ⪯ W (bp01 725–743)",
      .paper "2q_F − n > a removes the evidence branch"⟩ ] },
  -- HISTORICAL (historicalPins): WITHDRAWN for current use 2026-09-29, successor
  -- fg.finalLock.v2 (the accepted threshold, 0 for genesis). Its theorem stays true.
  { id := "fg.finalLock.v1", sources := [bp, vcF, r148], clauses := [
    ⟨"every block above h_F(D) extends F(D)",
      .leanHyp [``finalLock] "slashable-or form; RootInjectiveOn (the pair root premise)"⟩ ] },
  -- ALFS note (registry 4bc6690): part (ii) without the F basis; StoreInv.Fcar.
  { id := "fg.frameCompat.v1", sources := [spec, dc], clauses := [
    ⟨"step 1: checkpoint heights",
      .leanHyp [``entry_height, ``entry_first]
        "h_j ≠ 0 (a non-genesis pair); T_h ≠ genesis"⟩,
    ⟨"part (i): compatible with F ⇔ F ⪯ J when h_J ≥ h_F", .paper "registry proof, step 2"⟩,
    ⟨"part (ii), ALFS form: the live pair extends F and is the lex-max pair of Σ.T",
      .leanHyp [``storeControls_eq_fjControls, ``lexMax_of_candidate]
        "StoreInv (pair, FJ, Fcar) for storeControls_eq_fjControls; ViewRootInj for \
        lexMax_of_candidate (the local root premise)"⟩,
    ⟨"step 4: P1 = P2", .paper "registry proof, step 4"⟩ ] },
  { id := "fg.provenance.v2", sources := [r146, r143, bp, r148, spec], clauses := [
    ⟨"(1) every target, progress or finality QC has an honest row",
      .leanHyp [``provenance_honestRow, ``provenance_finalityQC]
        "faulty weight < q (the entry's q_F > a); a QC is a quorum with a row in the \
        pool for each member: for a chain's target and progress QCs, the witnesses \
        of RowWitnesses (justification_certificate, height_crossing); for a \
        finality QC, provenance_finalityQC"⟩,
    ⟨"(2) an honest height row names its source's entry, T ⪯ C",
      .leanHyp [``provenance_entry]
        "an honest row is a createRow output with source C (the emission fact is \
        comp work)"⟩,
    ⟨"(3) a finality row names the head's justified pair; a finality QC names a \
      justified entry",
      .leanHyp [``provenance_finalityRow, ``provenance_finalityQC]
        "head fields = HeadFields.ofBlock (caller obligation); QC form: faulty \
        weight < q (hcap; the entry's q_F > a) and the emission hypothesis hemit"⟩,
    ⟨"'earlier' target QC (emission order)", .external "comp.provenance.v1" ""⟩,
    ⟨"a successful fresh fast source with τ > a supporters (r148 401–402)",
      .ap "ap.fastSupport.v1" ""⟩ ] },
  { id := "fg.causalCap.core.v1", sources := [r147, bp, vcW], clauses := [
    ⟨"(a), FG part: an honest row of height h names its source's own height",
      .leanHyp [``provenance_entry] "an honest row is a createRow output with source C"⟩,
    ⟨"(a), store part: that source is in the signer's store before t, so h ≤ its \
      archival maximum",
      .runFact "not Lean here: DC's honestEmittedHeight_le_localHMaxBeforeTime (vcW \
        lines 42–48) is not ported; comp.cut.v1 item 3 applies it at the cut"⟩,
    ⟨"(b) a carrier of honest rows ≤ M has h ≤ M+1 and h_j ≤ M",
      .leanHyp [``causalCap]
        "honest = signer ∉ faulty, with faulty weight < q; hrows (honest rows ≤ M) \
        replaces 'pre-cut'; hrows bounds the .vote height pairs only (an .empty pair \
        cannot cross); h_j ≤ M comes from h_j < h ≤ M+1"⟩ ] },
  -- causalCap_notRoot is item 4 of this entry, not a clause of fg.causalCap.core.v1.
  { id := "comp.cut.v1", sources := [r144, bp], clauses := [
    ⟨"item 1: r_G, u_0 = a_(r_G+2) and M = the honest archival frontier at u_0",
      .runFact "the cut is a run object; no Lean"⟩,
    ⟨"item 2: GST+2P ≤ u_0 < GST+3P", .runFact "the action schedule; no Lean"⟩,
    ⟨"item 3: every honest height row of the prefix has height ≤ M",
      .runFact "fg.causalCap.core.v1 (a) at the cut; no Lean"⟩,
    ⟨"item 3: a carrier of prefix rows has height ≤ M+1 and justified height ≤ M",
      .external "fg.causalCap.core.v1" "(b) with this M: causalCap"⟩,
    ⟨"item 4: at a duty with H_V ≥ M+2 an old-only justification has j ≤ M < H_V−1, \
      so it is not the active root",
      .leanHyp [``causalCap_notRoot]
        "PARTIAL: arithmetic only, h_j + 1 ≠ H for every H ≥ M+2, under hrows and \
        faulty weight < q; M at u_0 and 'old-only ⇒ hrows' are run facts; the link \
        'active root ⇔ H = h_j+1' (Controls.rootIsJ) is not stated in Lean"⟩,
    ⟨"item 4: H_V is the duty view's own maximum; an archival rise acts only after it \
      reaches the view",
      .external "comp.settle.v1" ""⟩ ] },
  -- Chain form of clause 1: crossingNoFinal (helper). Its binder RootInjectiveOn W D
  -- is not used; in all four statements hJ : h_j ≠ 0 follows from hnot.
  { id := "fj.crossingNoFinal.v1", sources := [r148], clauses := [
    ⟨"a finality QC for J (any row pool, before or after the crossing) and the crossing \
      give E1 against it",
      .leanHyp [``crossingNoFinal_QC]
        "RootInjectiveOn B W (the pair root premise); stronger form: no honesty \
        hypothesis, E1 weight ≥ 2q−W \
        between the pool and W's rows"⟩,
    ⟨"an honest intersection member's crossing row is a timeout",
      .leanHyp [``crossingNeedsTimeout]
        "faulty weight + W < 2q (a < 2q−n); hhonest: no signer outside faulty has an \
        E1/E2 pair between B's and W's rows; RootInjectiveOn B W \
        (the pair root premise); static (no time \
        order: 'has ALREADY targeted J' is not in the statement)"⟩,
    ⟨"the timeout branch is at the uniform maturity slot, general form: a block that \
      raises its parent's height has a target quorum for the parent's entry, or a \
      slot ≥ T_h.slot + δ_t",
      .lean [``crossing_maturity]⟩,
    ⟨"the timeout branch is at the uniform maturity slot, at the crossing of j on W: \
      the target disjunct gives honest E2 against J's target QC, so s ≥ X.slot + δ_t",
      .paper "crossing_maturity with clause 2 (crossingNeedsTimeout); not composed in Lean"⟩,
    ⟨"J cannot finalize in any continuation", .paper "E1 weight ≥ 2q−W > a"⟩ ] },
  { id := "fj.inBandLock.v1", sources := [r148], clauses := [
    ⟨"an in-band source is not suppressed by a lock or same-action pair on J' ≠ T_c",
      .leanHyp [``inBandLock]
        "carrier hcar; F ⪯ J' (hFJ', partial coverage per the registry note); huniq \
        (uniqueness at h(C): paper fg.uniqueJust.v1, uniqueJust_chains gives it for \
        two chains); ViewRootInj (§0.4; the local root premise)"⟩,
    ⟨"derivation of F ⪯ J' from the finality lock, fg.finalLock.v2 (history: \
      fg.finalLock.v1 in the pinned text, registry §9)", .open_ "later helper pinned here"⟩,
    ⟨"view form: in a contest the AP head read from a duty view is in D with state \
      height ≥ lo = H, under the v1 premises (fj.frame.v1, R1 duty views, \
      the carrier clause of fg.finalLock.v2 (history: fg.finalLock.v1, registry §9) \
      and a ≤ f); no unfiltered fallback",
      .ap "ap.headReachesLo.v1" "view form"⟩,
    ⟨"FG-SA form (fgsa3 1226–1247, 1361–1376): in a contest the frozen HEAD reaches H \
      if its anchor A = live_root is in D_V (the filtered domain of the frozen voter \
      tree V) or has an eligible child in D_V; otherwise the HEAD is A (v6 clause 2), \
      which can be below H",
      .ap "ap.headReachesLo.v6" "clauses 1–2"⟩,
    ⟨"in a contest the FG action head (get_filtered_block_tree over the full tree Σ.T, \
      domain D; fgsa3 1173–1177) reaches H if A is in D or has an eligible child in D; \
      otherwise the head is A, which can be below H",
      .ap "ap.headReachesLo.v6" "the plan's reading of clauses 1–2 with Σ.T in place \
        of V (v6 is stated only for a HEAD duty's frozen voter tree); the anchor \
        premise is AP and comp work"⟩,
    ⟨"a lock at H needs a carrier at H+1",
      .leanHyp [``finalityPair_carrier_above] "head fields = HeadFields.ofBlock"⟩,
    ⟨"that carrier is retained in the full store", .runFact "comp layer; no registry id"⟩,
    ⟨"locks at H−1 do not block rows at H; old different targets cause timeouts, which \
      still contribute progress",
      .paper "r148 lines 590–593; no Lean"⟩ ] },
  -- HISTORICAL (historicalPins): WITHDRAWN for use under fgsa3 (2026-09-29),
  -- successor fj.twoChanges.core.v2 (live-cache evidence; not pinned here). Its pins
  -- and partial Lean coverage stay as history.
  -- hFJ (E_J → F ⪯ Jm) is an extra hypothesis of effFrame_of_bits, twoChanges,
  -- twoChanges_count and twoChanges_nested. Paper derivation: fg.finalLock.v1 if
  -- h(F) < m−1; fg.uniqueJust.v1 if h(F) = m−1; StoreInv.Fcar and Fmove_atFrontier
  -- if h(F) ≥ m. The G02 checks of TwoChanges.lean are examples (tests), not names.
  { id := "fj.twoChanges.core.v1", sources := [r148, ldp], clauses := [
    ⟨"item 1: the normalized frame is a function of the phase",
      .leanHyp [``effFrame_of_bits]
        "PARTIAL: m ≥ 2; frontier = m; pairs at m−1 name Jm (huniq; paper \
        fg.uniqueJust.v1); hFJ: F ⪯ Jm under E_J (extra; derivation above); \
        ViewRootInj (the local root premise)"⟩,
    ⟨"item 2: bits false before the first store holds the evidence",
      .leanHyp [``evidence_mono]
        "PARTIAL: a view ⊆ a store keeps each bit; 'before the first time an honest \
        store holds it' is a run fact"⟩,
    ⟨"item 2: phase order and at most two effective changes",
      .leanHyp [``twoChanges, ``twoChanges_count]
        "bit persistence hJ, hC (as in the entry); item 1 hypotheses for each view"⟩,
    ⟨"item 2, one node's nested views with one F (partial; Astra G07)",
      .leanHyp [``twoChanges_nested]
        "PARTIAL: monotone views and one F; item 1 hypotheses"⟩,
    ⟨"item 3 (i): F move below m−1 cuts D at F′",
      .leanHyp [``Fmove_filtered]
        "any block set; controls fixed except F; F′ below lo in the F-root phases; \
        F′ ⪯ J in the J-root phase; pure fg.finalLock.v1 at F′ (hext)"⟩,
    ⟨"item 3 (i), fjFrame special case (controls recomputed under F and F′)",
      .leanHyp [``Fmove_below]
        "h(F′) < m−1; frontier = m; pure fg.finalLock.v1 at F′ (hext); ViewRootInj \
        (the local root premise)"⟩,
    ⟨"item 3 (ii): F move at m−1 keeps the uncontested phase, Z = F′, lo = m−1 and D",
      .leanHyp [``Fmove_atTop]
        "m ≥ 2; a carrier K of F′ in the view with h_F(K) = m−1; uniqueness at m−1 \
        (huniq, pairwise; paper fg.uniqueJust.v1); pure fg.finalLock.v1 above m−1 \
        (hext); ViewRootInj (the local root premise)"⟩,
    ⟨"item 3 (ii): at m−1 the contested phase is impossible (the registry cites \
      fj.crossingNoFinal.v1)",
      .byHyp [``Fmove_atTop]
        "hext: every view block above m−1 extends F′ (at the frontier, the same as \
        ¬E_C(m, F′)); crossingNoFinal is not used"
        "finalLock (fg.finalLock.v1) under a ≤ f (this removes the slashable \
        branch), with the carrier (StoreInv.Fcar); or crossingNoFinal_QC \
        (fj.crossingNoFinal.v1)"⟩,
    ⟨"item 3 (iii): a finalization at m ends the no-rise interval",
      .lean [``Fmove_atFrontier]⟩,
    ⟨"when the bits become true at every duty", .external "comp.settle.v1" ""⟩ ] } ]

open AvailableChain.SimplexFG in
/-- Executable definitions and the archived spec text (`alfs4`), or for the view
form r148 `FJ_FRAME`, that they follow. -/
def defPins : List DefPin := [
  ⟨``derive, alfs4, "Fig. alg:chain-full, lines 890–954"⟩,
  ⟨``fjControls, r148, "FJ_FRAME, lines 148–169 (view form, fj.frame.v1)"⟩,
  ⟨``fjFrame, r148,
    "FJ_FRAME and get_filtered_block_tree_from, lines 148–175 (view form, fj.frame.v1)"⟩,
  ⟨``filteredFrom, alfs4,
    "viable_tree_from 988–994, get_fg_root 1004–1011, get_filtered_block_tree_from \
    1013–1020"⟩,
  ⟨``storeControls, alfs4, "fg_contest 970–976, band_floor 978–986, get_fg_root 1004–1011"⟩,
  ⟨``storeFrame, alfs4,
    "get_filtered_block_tree_from 1013–1020, get_filtered_block_tree 1021–1025"⟩,
  ⟨``Store.init, alfs4, "initialization, lines 474–482 (one tree; Trees 352–371)"⟩,
  ⟨``acceptViable, alfs4, "viable_tree (acceptance), lines 996–1002"⟩,
  ⟨``update_finality, alfs4, "lines 847–860 (the reconcile call, 858, writes SA fields only)"⟩,
  ⟨``on_block, alfs4, "lines 792–817 (refusals 794–796 and 798; state 806–807; insertion 808)"⟩,
  ⟨``activeView, alfs4, "act(Σ), Trees paragraph, line 358"⟩,
  -- The ν input of height_pair is always false (no NJ): the ν branch of alfs4 is dead,
  -- which is not a difference. Λ.timeouts is omitted: the spec only writes it.
  ⟨``createRow, alfs4, "Fig. alg:client, lines 1334–1402"⟩ ]

/-- Kit theorems with no pin (helpers). -/
def helpers : List Lean.Name := [
  ``uniqueJust_slashable, ``crossingNoFinal,
  ``frontier_mono, ``lexMax_mono, ``filteredFrom_Z_mem,
  ``frameViable_eq_accept_of_noContest, ``frameViable_eq_accept_cut, ``clientRun_noSlash,
  ``provenance_finality ]

/-- Registry ids that this module does not formalize, with the reason. -/
def notFormalized : List (String × String) := [
  ("fg.frame.v2", "nj frame; the module is fj only (user decision 2026-09-28)"),
  ("fg.oneBullet.core.v1", "nj only; fj uses fj.twoChanges.core.v1"),
  ("ap.headReachesLo.v1", "AP service fact, view form; the FG side is fj.frameFeasible.v1"),
  ("ap.headReachesLo.v6", "AP service fact, FG-SA form (spec c1ea1db0; R ≥ 2, θ = 3Δ); \
    obligation clauses 1–3; FG inputs (the plan's reading, not a registry discharge): \
    filteredFrom_reachesLo, filteredFrom_Z_mem (clause 3), filteredFrom_viable_child"),
  ("ap.headReachesLo.v5", "WITHDRAWN for current use (2026-09-29), successor v6; \
    still true in its stated scope (R ≥ 3, 4Δ, spec bd942ca0); ALFS form"),
  ("ap.headReachesLo.v2", "SUPERSEDED by v3, then v4"),
  ("ap.headReachesLo.v3", "SUPERSEDED by v4"),
  ("ap.headReachesLo.v4", "SUPERSEDED by v5 (648f255); the conclusions of clauses 1–3 \
    are unchanged; the hypotheses are v5's"),
  ("fj.frame.v2", "SUPERSEDED by fj.frame.v3 (648f255); same frame controls"),
  ("comp.outputNesting.v1", "AP accessor fact; the finalized ⪯ available clause") ]

/-- Pins kept only as history: their registry status is WITHDRAWN or
SUPERSEDED (`scripts/check-fg-pins.sh` step 5 checks it). No current pin names
them: not by `.ap` or `.external`, and not in its free text outside a
`(history: …)` marker (the `mention` records; step 4 checks both). The pin check
exempts them and their references from the status test, and each one must be
on the allowlist of that script, with a reason and a date. -/
def historicalPins : List String :=
  ["fj.frame.v3", "fg.finalLock.v1", "fj.twoChanges.core.v1"]

/-- The free text of a clause: its label and every string field of its coverage. -/
def Clause.texts (c : Clause) : List String :=
  c.label :: match c.cov with
    | .lean _ | .leanIn _ _ => []
    | .leanHyp _ h => [h]
    | .byHyp _ h d => [h, d]
    | .paper t | .apData t | .runFact t | .open_ t => [t]
    | .external _ n | .ap _ n => [n]

/-- The text without its history markers `(history: …)`, each to its matching
parenthesis, or `none` if a marker is not closed. -/
def dropHistory (s : String) : Option String :=
  let rec go : List Char → Nat → List Char → Option (List Char)
    | [], d, acc => if d == 0 then some acc.reverse else none
    | c :: cs, 0, acc =>
      if (c :: cs).take 9 == "(history:".toList then go cs 1 acc else go cs 0 (c :: acc)
    | c :: cs, d + 1, acc =>
      if c == '(' then go cs (d + 2) acc
      else if c == ')' then go cs d acc
      else go cs (d + 1) acc
  (go s.toList 0 []).map String.ofList

/-- `cs` has the registry's id grammar `[a-z][A-Za-z0-9.]*\.v[0-9]+`. -/
def isRegistryId (cs : List Char) : Bool :=
  let r := cs.reverse
  let ds := r.takeWhile Char.isDigit
  match cs, r.drop ds.length with
  | c :: _, 'v' :: '.' :: _ =>
    c.isLower && cs.all (fun c => c.isAlphanum || c == '.') && !ds.isEmpty
  | _, _ => false

/-- The maximal runs of `[A-Za-z0-9._]` in a text, trailing dots removed. -/
def words (cs : List Char) : List (List Char) :=
  let isW (c : Char) : Bool := c.isAlphanum || c == '.' || c == '_'
  let fin (cur : List Char) : List (List Char) :=
    match cur.dropWhile (· == '.') with
    | [] => []
    | w => [w.reverse]
  let rec go : List Char → List Char → List (List Char)
    | [], cur => fin cur
    | c :: cs, cur => if isW c then go cs (c :: cur) else fin cur ++ go cs []
  go cs []

/-- The registry ids that the free text of a pin names outside history markers
(`words` with the id grammar). An unclosed marker gives the id `!UNCLOSED`,
which the manifest grammar rejects. -/
def mentions (p : Pin) : List String :=
  (p.clauses.flatMap (·.texts)).flatMap (fun t =>
    match dropHistory t with
    | none => ["!UNCLOSED"]
    | some u => ((words u.toList).filter isRegistryId).map String.ofList)
  |>.eraseDups

/-- The manifest that `scripts/check-fg-pins.sh` checks, from the elaborated
values (Astra P01, Q01–Q03, T01), one record per line: `src <key> <root> <path>
<sha256>` for each source of the pins and `defPins`, `pin <id>`, `ap <id>` and
`external <id>` for each active reference (without repeats), and
`notFormalized <id>` for each id that this module does not formalize (historical
ids, and AP or comp ids that it does not formalize), `dep <pin> <id>` for each
`.ap` or `.external` id of a pin (without repeats in one pin), `hist <pin>`
for each entry of `hist` (repeats kept, so that the check sees them), and
`mention <pin> <id>` for each registry id in the free text of a pin outside
`(history: …)` markers (`mentions`). Eight trailer lines follow, one per kind in
this order: `END <kind> <n> <keys>`, where `<keys>` are the record keys of that
kind (the second field; for `dep` and `mention`, `<pin>/<id>`), sorted by
`String` order, which is byte order on these ASCII tokens. The trailer binds
the record set, not only the counts. -/
def manifest (ps : List Pin) (ds : List DefPin) (nf : List (String × String))
    (hist : List String) : List String :=
  let srcs := (ps.flatMap (·.sources) ++ ds.map (·.src)).eraseDups
  let ids (p : Pin) (ap : Bool) := p.clauses.filterMap fun c =>
    match c.cov with
    | .ap i _ => if ap then some i else none
    | .external i _ => if ap then none else some i
    | _ => none
  let refs (ap : Bool) := (ps.flatMap (ids · ap)).eraseDups
  let deps := ps.flatMap fun p => (ids p true ++ ids p false).eraseDups.map (p.id, ·)
  let recs : List (String × List (String × String)) :=
    [("src", srcs.map fun s => (s.key, s!"{s.key} {s.root} {s.path} {s.sha256}")),
     ("pin", ps.map fun p => (p.id, p.id)),
     ("ap", (refs true).map fun i => (i, i)),
     ("external", (refs false).map fun i => (i, i)),
     ("notFormalized", nf.map fun (i, _) => (i, i)),
     ("dep", deps.map fun (p, i) => (s!"{p}/{i}", s!"{p} {i}")),
     ("hist", hist.map fun i => (i, i)),
     ("mention", ps.flatMap fun p => (mentions p).map fun i => (s!"{p.id}/{i}", s!"{p.id} {i}"))]
  recs.flatMap (fun (t, rs) => rs.map fun (_, r) => s!"{t} {r}") ++
  recs.map fun (t, rs) =>
    " ".intercalate (["END", t, toString rs.length] ++
      (rs.map (·.1)).mergeSort (fun a b => decide (a ≤ b)))

/-- Every Lean name of the table (the pins, `defPins` and `helpers`), without
duplicates, for `scripts/FGPinIds.lean --check-names`. The `leanIn` names are
not in it: see `extNames`. -/
def pinNames (ps : List Pin) (ds : List DefPin) (hs : List Lean.Name) : List Lean.Name :=
  (ps.flatMap fun p => p.clauses.flatMap fun c =>
    match c.cov with
    | .lean ns => ns
    | .leanHyp ns _ => ns
    | .byHyp ns _ _ => ns
    | _ => []) ++ ds.map (·.lean) ++ hs |>.eraseDups

/-- The `leanIn` citations of the table as `(pin id, lib, name)`, for
`scripts/FGPinIds.lean` (the library allowlist, and the `--ext` records that
`scripts/check-fgsa.sh` checks). -/
def extNames (ps : List Pin) : List (String × String × Lean.Name) :=
  ps.flatMap fun p => p.clauses.flatMap fun c =>
    match c.cov with
    | .leanIn lib ns => ns.map (p.id, lib, ·)
    | _ => []

/-! ## Each Lean name of the table elaborates (the build fails when a name moves) -/

example := @AvailableChain.SimplexFG.Store
example := @storeInv_init
example := @storeInv_on_block
example := @on_block_TF_subset
example := @update_finality_TF
example := @AvailableChain.SimplexFG.activeView
example := @activeView_subset
example := @AvailableChain.SimplexFG.on_block
example := @on_block_of_refused
example := @on_block_F_mono
example := @crossing_other_entry
example := @AvailableChain.SimplexFG.storeControls
example := @AvailableChain.SimplexFG.Controls.rootIsJ
example := @AvailableChain.SimplexFG.Controls.Z
example := @AvailableChain.SimplexFG.Controls.lo
example := @storeControls_eq_fjControls
example := @AvailableChain.SimplexFG.filteredFrom
example := @mem_filteredFrom
example := @AvailableChain.SimplexFG.storeFrame
example := @storeFrame_full
example := @AvailableChain.SimplexFG.acceptViable
example := @frameViable_subset_accept
example := @AvailableChain.SimplexFG.update_finality
example := @AvailableChain.SimplexFG.fjControls
example := @AvailableChain.SimplexFG.fjFrame
example := @fjFrame_lo
example := @fjFrame_D
example := @filteredFrom_reachesLo
example := @fjFrame_D_nonempty
example := @storeFrame_feasible
example := @fjFrame_Z_mem_D
example := @filteredFrom_viable_child
example := @accountable
example := @update_finality_F_mono
example := @uniqueJust
example := @uniqueJust_chains
example := @finalLock
example := @finalLock_e1
example := @entry_height
example := @entry_first
example := @lexMax_of_candidate
example := @provenance_honestRow
example := @provenance_finalityQC
example := @provenance_entry
example := @provenance_finalityRow
example := @causalCap
example := @causalCap_notRoot
example := @crossingNoFinal_QC
example := @crossingNeedsTimeout
example := @crossing_maturity
example := @inBandLock
example := @finalityPair_carrier_above
example := @effFrame_of_bits
example := @evidence_mono
example := @twoChanges
example := @twoChanges_count
example := @twoChanges_nested
example := @Fmove_filtered
example := @Fmove_below
example := @Fmove_atTop
example := @Fmove_atFrontier
example := @AvailableChain.SimplexFG.derive
example := @AvailableChain.SimplexFG.Store.init
example := @AvailableChain.SimplexFG.createRow
example := @uniqueJust_slashable
example := @crossingNoFinal
example := @frontier_mono
example := @lexMax_mono
example := @filteredFrom_Z_mem
example := @frameViable_eq_accept_of_noContest
example := @frameViable_eq_accept_cut
example := @clientRun_noSlash
example := @provenance_finality

end AvailableChain.KitFG
end
