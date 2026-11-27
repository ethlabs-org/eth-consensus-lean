module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs

public section

/-! # The run-facts bundle of a finite reset (Option B)

`ResetRunCore`: the core of a Goldilocks run under growing faults (`GoldilocksRunCore`) with the
other premises of `ResetPremisesUpTo`, verbatim, at the committee starts. The stock
(`ResetPremisesUpTo`) and shadow (`ResetPremisesUpTo'`) premises both give one. The quarantine
provenance (`left_entry_origin_of_quarantine_at`) is derived from it, not a field. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- **The core of a finite reset**: `GoldilocksRunCore` at the committee starts, with the other
premises of `ResetPremisesUpTo`. -/
structure ResetRunCore
    (u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n))
    (frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (g ΔF a b : Time) (committee : Time → Finset (Fin sp.n)) (beta : ℚ) (hold : Time := 0) :
    Prop where
  core : GoldilocksRunCore u frameOf proposer dg H tr
    (AC.committeeStart sp.genesisRoot (Generic.dictOfTime sp committee))
  beta_le : beta ≤ 1 / 2
  committee_pos : 0 < sp.committeeSize
  committeeFacts : Compose.Growing.CommitteeFacts tr H (Generic.dictOfTime sp committee)
  committeeFaults : Generic.CommitteeFaultsUpTo beta committee H g b
  noColl : Compose.NoCollRun dg tr
  sync : ResetService tr H g ΔF b hold
  awake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t
  faults : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1
  reset : IsReset tr H g a
  reset_le : a ≤ b
  snapshot : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g) ∧ tr.time k ≤ b
  catchUp : CatchRun tr H g (2 * sp.Δ)
  noRestart : ∀ y k, y ∈ H (tr.time k) → tr.RestartAt y k →
    tr.time k ≤ b → tr.time k ≤ gbar g
  timeoutDelay : ∀ s, sp.toParams.slotTime s + 6 * sp.Δ + ΔF ≤
    sp.toParams.slotTime (s + sp.toParams.δt)
  nonempty : (H b).Nonempty
  deepCover : ∀ D, sp.deepDepth = some D →
    b ≤ cutZ sp.toParams g + 4 * D * sp.Δ ∨ HighSourceCover tr H g a b

end Consensus.Goldilocks.Healing.Growing

end
