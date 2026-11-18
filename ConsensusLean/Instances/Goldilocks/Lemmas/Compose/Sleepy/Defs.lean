module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection

public section

/-! # Goldilocks under `Sleepy`: origins and the record invariant (definitions)

The vocabulary of the Sleepy safety invariant from genesis, over a Goldilocks run,
read on its AC projection, with ancestry inside the honest blocks of the run:

* an **origin** of label `s` (`Origin`): the result `C ≠ ⊥` of an honest joined update of slot `s`
  (fast, slow, vetoed or not: `SA.ResultAt`), or the raw block an honest optimistic check of
  slot `s` selects (`SA.OptimisticLockAt`). Origins are actual events of the run, whatever their
  time relative to the votes that read them;
* the invariant up to a horizon `b`, `SleepyInvariantUpTo`, below. -/

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

variable (tr H)

/-! ### The invariant up to a horizon `b`

The origins whose event is at a time `≤ b` (`OriginWithin`), the ancestor closure of their chain
(`OnOriginChainWithin`: `B` is genesis or an ancestor of such an origin), and the invariant
restricted to them and to the cuts **within `b`** (every earlier cut at a time `≤ b`, so that the
state before the cut is the state at a time `≤ b`): `SleepyInvariantUpTo`. -/

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

variable (tr H)

/-- **The Sleepy record invariant up to `b`** (S1–S3 restricted to the origins within `b`, the
honest votes at times `≤ b`, and the cuts within `b`: every earlier cut at a time `≤ b`). -/
structure SleepyInvariantUpTo (b : Time) : Prop where
  /-- S1: any two origins within `b` are compatible. -/
  origins_compatible : ∀ C s C' s', OriginWithin tr H C s b → OriginWithin tr H C' s' b →
    Compatible (tr.HonestBlocks H) C C'
  /-- S2: every honest vote at a time `≤ b` of a slot after the label of an origin within `b`
  extends it. -/
  vote_extends : ∀ C s, OriginWithin tr H C s b → ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e →
    tr.time i ≤ b → s < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg C
  /-- S1: at a cut within `b`, every honest record names a block of the node's tree that is
  genesis or an origin within `b`. -/
  record : ∀ y ∈ H, ∀ i, (∀ k < i, tr.time k ≤ b) →
    ∃ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y i).ac.latestConfirmed ∧
      (C.root = sp.genesisRoot ∨ ∃ s, OriginWithin tr H C s b)
  /-- S1: at a cut within `b`, every honest `Σ.F` and `Σ.J` is on the chain of the origins
  within `b`. -/
  caches : ∀ y ∈ H, ∀ i, (∀ k < i, tr.time k ≤ b) →
    OnOriginChainWithin tr H (tr.state y i).fg.F b ∧
      OnOriginChainWithin tr H (tr.state y i).fg.J b
  /-- S1: at a cut within `b`, every honest stored lock names a block of the node's tree on the
  chain of the origins within `b`. -/
  locks : ∀ y ∈ H, ∀ i, (∀ k < i, tr.time k ≤ b) → ∀ l ∈ (tr.state y i).ac.locks,
    ∃ L ∈ (tr.state y i).fg.tree, L.root = l.block ∧ OnOriginChainWithin tr H L b
  /-- S1: at a cut within `b`, every honest FG source is on the chain of the origins within
  `b`. -/
  sources : ∀ y ∈ H, ∀ i, (∀ k < i, tr.time k ≤ b) → ∀ ℓ C, SA.ToFGAt tr.projAC y i ℓ C →
    OnOriginChainWithin tr H C b
  /-- S3 (full reads): at a cut within `b`, an origin within `b` that an honest node holds is at
  or below its `fc_root`, or in its full viable tree. -/
  viable : ∀ y ∈ H, ∀ i, (∀ k < i, tr.time k ≤ b) → ∀ C s, OriginWithin tr H C s b →
    C ∈ (Node.frame (tr.state y i)).tree →
    (Node.frame (tr.state y i)).Anc C (Node.frame (tr.state y i)).fcRoot ∨
      C ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree

/-! ### The invariant from a start label `s₀`

The step lemmas for an induction started at a label `s₀` (after a heal, R.6) run on a window
`[t_{s₀}, b]` (`SleepyWindow`), which `Sync[0, b − Δ]` and `f < h_t` at the slot points `≤ b`
give at `s₀ = 0`. The premises from
`t_{s₀}` on, the base facts that replace the pre-`s₀` history, and the invariant from `s₀` are not
stated. -/

/-- **The Sleepy premises on the window from slot `s₀` to `b`**: `Sync[t_{s₀}, b − Δ]` and
`f < h_t` at every `t ∈ {t_s, t_s + Δ, t_s + 2Δ}` with `s ≥ s₀` and `t ≤ b`. -/
def SleepyWindow (ΔF : Time) (s₀ : Nat) (b : Time) : Prop :=
  sp.ts s₀ ≤ b ∧ tr.SyncRun H ΔF (sp.ts s₀) (b - sp.Δ) ∧
    ∀ s : Nat, s₀ ≤ s → ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d)

variable {tr H}

theorem sleepyWindow_iff {ΔF b : Time} {s₀ : Nat} :
    SleepyWindow tr H ΔF s₀ b ↔ sp.ts s₀ ≤ b ∧ tr.SyncRun H ΔF (sp.ts s₀) (b - sp.Δ) ∧
      ∀ s : Nat, s₀ ≤ s → ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
        tr.FaultBound H (sp.ts s + d) :=
  Iff.rfl

/-- `t_0 = 0`. -/
theorem ts_natCast_zero : sp.ts ((0 : Nat) : Int) = 0 := by
  simp [SAParams.ts]

variable (tr H)

end Consensus.Goldilocks.Compose

end
