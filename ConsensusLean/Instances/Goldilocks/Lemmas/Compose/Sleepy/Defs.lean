module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Run

public section

/-! # Goldilocks under `Sleepy`: origins and the record invariant (definitions)

The vocabulary of the Sleepy safety invariant from genesis (fradamt-agent/workbench#11,
`repos/goldilocks/notes/healing-simple/sleepy-record-invariant.md`, §1), over a Goldilocks run,
read on its AC projection, with ancestry inside the honest blocks of the run:

* an **origin** of label `s` (`Origin`): the result `C ≠ ⊥` of an honest joined update of slot `s`
  (fast, slow, vetoed or not: `SA.ResultAt`), or the raw block an honest optimistic check of
  slot `s` selects (`SA.OptimisticLockAt`). Origins are actual events of the run, whatever their
  time relative to the votes that read them;
* `OnOriginChain B`: `B` is genesis or an ancestor of an origin (the ancestor closure of the
  origin chain);
* `SleepyInvariant` (S1–S3 of the note, at every cut): origins are pairwise compatible; every
  honest vote of a later slot extends an origin (label-strict transfer); every honest record is
  genesis or an origin; every honest `Σ.F`, `Σ.J`, stored lock and FG source is on the origin
  chain; and an origin that an honest node holds is at or below its `fc_root` or in its full
  viable tree;
* the bounded frontier of the induction (§4, repaired): `OriginsBelow s` (`P_s`: origins of labels
  below `s` compare pairwise) and `VotesBelow s` (`V_s`: every honest vote of a slot `m` with
  `j < m ≤ s` extends every origin of label `j < s`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- **An origin of label `s`**: the result `C ≠ ⊥` of the update of slot `s` of an honest node
(joined at `t_s + 6Δ`), or the block that an honest optimistic check of slot `s` selects. -/
def Origin (C : SA.Blk sp.n (List (FG.Att sp.n))) (s : Nat) : Prop :=
  ∃ x ∈ H, ∃ i CV, SA.ResultAt tr.projAC x i s C CV ∨ SA.OptimisticLockAt tr.projAC x i s C CV

/-- An origin of label `s` whose event is at a cut before `i` (the origins a read at cut `i` can
depend on). -/
def OriginBefore (C : SA.Blk sp.n (List (FG.Att sp.n))) (s i : Nat) : Prop :=
  ∃ x ∈ H, ∃ k < i, ∃ CV,
    SA.ResultAt tr.projAC x k s C CV ∨ SA.OptimisticLockAt tr.projAC x k s C CV

/-- `B` is on the ancestor closure of the origin chain: genesis, or an ancestor (inside the
honest blocks) of an origin. -/
def OnOriginChain (B : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  B.root = sp.genesisRoot ∨ ∃ C s, Origin tr H C s ∧ Anc (tr.HonestBlocks H) B C

/-- **`P_s`**: origins of labels below `s` are pairwise compatible. -/
def OriginsBelow (s : Nat) : Prop :=
  ∀ C j C' j', j < s → j' < s → Origin tr H C j → Origin tr H C' j' →
    Compatible (tr.HonestBlocks H) C C'

/-- **`V_s`**: every honest vote of a slot `m` with `j < m ≤ s` extends every origin of label
`j`. -/
def VotesBelow (s : Nat) : Prop :=
  ∀ C j, Origin tr H C j → ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → j < e.msg.slot →
    e.msg.slot ≤ s → SA.VoteExtends (tr.HonestBlocks H) e.msg C

variable {tr H}

theorem origin_iff {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} :
    Origin tr H C s ↔ ∃ x ∈ H, ∃ i CV,
      SA.ResultAt tr.projAC x i s C CV ∨ SA.OptimisticLockAt tr.projAC x i s C CV :=
  Iff.rfl

theorem originBefore_iff {C : SA.Blk sp.n (List (FG.Att sp.n))} {s i : Nat} :
    OriginBefore tr H C s i ↔ ∃ x ∈ H, ∃ k < i, ∃ CV,
      SA.ResultAt tr.projAC x k s C CV ∨ SA.OptimisticLockAt tr.projAC x k s C CV :=
  Iff.rfl

theorem OriginBefore.origin {C : SA.Blk sp.n (List (FG.Att sp.n))} {s i : Nat}
    (h : OriginBefore tr H C s i) : Origin tr H C s :=
  let ⟨x, hx, k, _, CV, h⟩ := h
  ⟨x, hx, k, CV, h⟩

/-- The result of an honest joined update is an origin of its slot. -/
theorem Origin.of_result {x : Fin sp.n} (hx : x ∈ H) {i s : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (h : SA.ResultAt tr.projAC x i s C CV) : Origin tr H C s :=
  ⟨x, hx, i, CV, Or.inl h⟩

/-- The selection of an honest optimistic check is an origin of its slot. -/
theorem Origin.of_optimistic {x : Fin sp.n} (hx : x ∈ H) {i s : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (h : SA.OptimisticLockAt tr.projAC x i s C CV) : Origin tr H C s :=
  ⟨x, hx, i, CV, Or.inr h⟩

theorem onOriginChain_iff {B : SA.Blk sp.n (List (FG.Att sp.n))} :
    OnOriginChain tr H B ↔
      B.root = sp.genesisRoot ∨ ∃ C s, Origin tr H C s ∧ Anc (tr.HonestBlocks H) B C :=
  Iff.rfl

theorem originsBelow_iff {s : Nat} :
    OriginsBelow tr H s ↔ ∀ C j C' j', j < s → j' < s → Origin tr H C j → Origin tr H C' j' →
      Compatible (tr.HonestBlocks H) C C' :=
  Iff.rfl

theorem votesBelow_iff {s : Nat} :
    VotesBelow tr H s ↔ ∀ C j, Origin tr H C j → ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e →
      j < e.msg.slot → e.msg.slot ≤ s → SA.VoteExtends (tr.HonestBlocks H) e.msg C :=
  Iff.rfl

variable (tr H)

/-- **The Sleepy record invariant** (workbench#11 S1–S3). -/
structure SleepyInvariant : Prop where
  /-- S1: any two origins are compatible. -/
  origins_compatible : ∀ C s C' s', Origin tr H C s → Origin tr H C' s' →
    Compatible (tr.HonestBlocks H) C C'
  /-- S2: every honest vote of a slot after an origin's label extends it. -/
  vote_extends : ∀ C s, Origin tr H C s → ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e →
    s < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg C
  /-- S1: every honest record names a block of the node's tree that is genesis or an origin. -/
  record : ∀ y ∈ H, ∀ i, ∃ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y i).ac.latestConfirmed ∧
    (C.root = sp.genesisRoot ∨ ∃ s, Origin tr H C s)
  /-- S1: every honest `Σ.F` and `Σ.J` is on the origin chain. -/
  caches : ∀ y ∈ H, ∀ i, OnOriginChain tr H (tr.state y i).fg.F ∧
    OnOriginChain tr H (tr.state y i).fg.J
  /-- S1: every honest stored lock names a block of the node's tree on the origin chain. -/
  locks : ∀ y ∈ H, ∀ i, ∀ l ∈ (tr.state y i).ac.locks,
    ∃ L ∈ (tr.state y i).fg.tree, L.root = l.block ∧ OnOriginChain tr H L
  /-- S1: every honest FG source (a block `ac_to_fg` returns) is on the origin chain. -/
  sources : ∀ y ∈ H, ∀ i ℓ C, SA.ToFGAt tr.projAC y i ℓ C → OnOriginChain tr H C
  /-- S3 (full reads): an origin that an honest node holds is at or below its `fc_root`, or in
  its full viable tree. -/
  viable : ∀ y ∈ H, ∀ i C s, Origin tr H C s → C ∈ (Node.frame (tr.state y i)).tree →
    (Node.frame (tr.state y i)).Anc C (Node.frame (tr.state y i)).fcRoot ∨
      C ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree

end Consensus.Goldilocks.Compose

end
