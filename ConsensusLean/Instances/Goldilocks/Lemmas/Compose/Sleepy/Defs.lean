module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection

public section

/-! # Goldilocks under `Sleepy`: origins (definitions)

The vocabulary of the Sleepy origins, over a Goldilocks run, read on its AC projection, with
ancestry inside the honest blocks of the run: an **origin** of label `s` (`Origin`) is the result
`C ≠ ⊥` of an honest joined update of slot `s` (fast, slow, vetoed or not: `SA.ResultAt`), or the
raw block an honest optimistic check of slot `s` selects (`SA.OptimisticLockAt`). Origins are actual
events of the run, whatever their time relative to the votes that read them. The finite service
premise of the Sleepy consumers is `SleepyServiceBefore`. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

/-- The finite Sleepy consumers need SA evidence and actual block acceptance relay,
not fresh processing of every repeated vote or attestation admission. -/
structure SleepyServiceBefore {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (ΔF b : Time) : Prop where
  deltaF : 0 < ΔF
  ac : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC
  relay : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → 0 ≤ tr.time i →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (tr.time i) sp.Δ ≤ b →
      tr.deadline y j (tr.time i) sp.Δ ≤ tr.time j →
      Anc (tr.HonestBlocks H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j (tr.time i) B

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

variable {tr H}

theorem originBefore_iff {C : SA.Blk sp.n (List (FG.Att sp.n))} {s i : Nat} :
    OriginBefore tr H C s i ↔ ∃ x ∈ H, ∃ k < i, ∃ CV,
      SA.ResultAt tr.projAC x k s C CV ∨ SA.OptimisticLockAt tr.projAC x k s C CV :=
  Iff.rfl

theorem OriginBefore.origin {C : SA.Blk sp.n (List (FG.Att sp.n))} {s i : Nat}
    (h : OriginBefore tr H C s i) : Origin tr H C s :=
  let ⟨x, hx, k, _, CV, h⟩ := h
  ⟨x, hx, k, CV, h⟩

variable (tr H)

/-! ### Origins up to a horizon `b`

The origins whose event is at a time `≤ b` (`OriginWithin`), the ancestor closure of their chain
(`OnOriginChainWithin`: `B` is genesis or an ancestor of such an origin), and their pairwise
compatibility below a label (`OriginsBelowUpTo`). -/

/-- An origin of label `s` whose event cut is at a time `≤ b`. -/
def OriginWithin (C : SA.Blk sp.n (List (FG.Att sp.n))) (s : Nat) (b : Time) : Prop :=
  ∃ x ∈ H, ∃ i CV, tr.time i ≤ b ∧
    (SA.ResultAt tr.projAC x i s C CV ∨ SA.OptimisticLockAt tr.projAC x i s C CV)

/-- `B` is on the ancestor closure of the origins within `b`: genesis, or an ancestor (inside the
honest blocks) of an origin whose event is at a time `≤ b`. -/
def OnOriginChainWithin (B : SA.Blk sp.n (List (FG.Att sp.n))) (b : Time) : Prop :=
  B.root = sp.genesisRoot ∨ ∃ C s, OriginWithin tr H C s b ∧ Anc (tr.HonestBlocks H) B C

/-- **`P_s` up to `b`**: origins within `b` of labels below `s` are pairwise compatible. -/
def OriginsBelowUpTo (s : Nat) (b : Time) : Prop :=
  ∀ C j C' j', j < s → j' < s → OriginWithin tr H C j b → OriginWithin tr H C' j' b →
    Compatible (tr.HonestBlocks H) C C'

variable {tr H}

theorem originWithin_iff {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {b : Time} :
    OriginWithin tr H C s b ↔ ∃ x ∈ H, ∃ i CV, tr.time i ≤ b ∧
      (SA.ResultAt tr.projAC x i s C CV ∨ SA.OptimisticLockAt tr.projAC x i s C CV) :=
  Iff.rfl

theorem onOriginChainWithin_iff {B : SA.Blk sp.n (List (FG.Att sp.n))} {b : Time} :
    OnOriginChainWithin tr H B b ↔
      B.root = sp.genesisRoot ∨ ∃ C s, OriginWithin tr H C s b ∧ Anc (tr.HonestBlocks H) B C :=
  Iff.rfl

theorem originsBelowUpTo_iff {s : Nat} {b : Time} :
    OriginsBelowUpTo tr H s b ↔ ∀ C j C' j', j < s → j' < s → OriginWithin tr H C j b →
      OriginWithin tr H C' j' b → Compatible (tr.HonestBlocks H) C C' :=
  Iff.rfl

/-- An origin whose event precedes a cut within `b` is within `b`. -/
theorem OriginBefore.within {C : SA.Blk sp.n (List (FG.Att sp.n))} {s i : Nat} {b : Time}
    (h : OriginBefore tr H C s i) (hi : ∀ k < i, tr.time k ≤ b) : OriginWithin tr H C s b :=
  let ⟨x, hx, k, hk, CV, h⟩ := h
  ⟨x, hx, k, CV, hi k hk, h⟩

end Consensus.Goldilocks.Compose

end
