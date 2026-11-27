module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ACProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare

public section

/-! # Shadow P-U: honest participants

A copy of stock `Compose/Sleepy/Compare` (`honest_participants_window_before`) over the shadow run
law `GoldilocksRun'`, through the shadow AC projection `Compose.goldilocks_ac_projection_from'`.
The statement is static; a growing consumer applies it to `hrun.upTo`. -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Vote Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace' sp ro} {proposer : Nat → Fin sp.n}

/-- If every honest member of the slot-`s` committee is awake, joined and permitted to vote,
windowed forwarding makes the faulty participants of the actual update pool fewer than half of
its participants (a copy of `honest_participants_window_before`). -/
theorem honest_participants_window_before' {ini} (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {K : AC.CommitteeDict sp.n}
    {a b : Time} {s : Nat}
    (hsync : AC.ServiceWindowBefore H (tr.HonestBlocks H) a b tr.projAC)
    (ha : a ≤ sp.ts s) {X : Fin sp.n} (hX : X ∈ H) {i₀ : Nat}
    {ℓX : ACLabel (goldilocksNode' sp ro)} (hu : AC.UpdateAt tr.projAC X i₀ s ℓX)
    (hib : tr.time i₀ ≤ b)
    (hready : ∀ y ∈ H, tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ))
    (hmv : ∀ y ∈ H, y ∈ K.committee s → ∀ i, (tr.state y i).ac.mayVote s = true)
    (hP : ∀ v ∈ (tr.projAC.state X i₀).pool s, v.val ∈ K.committee s)
    (hf : 2 * (K.committee s ∩ Hᶜ).ncard < (K.committee s).ncard) :
    2 * (Hᶜ ∩ AC.voters {v | v ∈ (tr.projAC.state X i₀).pool s}).ncard <
      (AC.voters {v | v ∈ (tr.projAC.state X i₀).pool s}).ncard := by
  sorry

end Consensus.Goldilocks.Compose

end
