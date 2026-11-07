module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.CompatibleSides

public section

/-! # Votes relayed while their writer is honest

The release carries its own honesty witness. A subsequent compromise does not cancel service.
-/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {proposer : Nat → Fin sp.n}

/-- The forwarding side, with sender honesty read at release, not at the recipient's cut. -/
def Relayed (tr : SATrace sp FGP ro) (H : Time → Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (X : Fin sp.n) (s : Nat) (D : Blk sp.n FGP) : Set (Fin sp.n) :=
  {u | ∃ v : Vote sp.n, v.val = u ∧ v.slot = s ∧
    (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
    ∃ k, X ∈ H (tr.time k) ∧ tr.SendOrAdmit X k v ∧
      sp.ts s ≤ tr.time k ∧ tr.time k < sp.ts s + 2 * sp.Δ}

theorem relayed_iff {X : Fin sp.n} {s : Nat} {D : Blk sp.n FGP} {u : Fin sp.n} :
    u ∈ Relayed tr H U X s D ↔
      ∃ v : Vote sp.n, v.val = u ∧ v.slot = s ∧
        (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
        ∃ k, X ∈ H (tr.time k) ∧ tr.SendOrAdmit X k v ∧
          sp.ts s ≤ tr.time k ∧ tr.time k < sp.ts s + 2 * sp.Δ := Iff.rfl

/-- Three quarters of the committee have votes released by the optimistic writer while honest. -/
theorem optimistic_seats (hrun : ACRun proposer tr H U)
    {X : Fin sp.n} {k s : Nat} (hX : X ∈ H (tr.time k))
    {D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : OptimisticLockAt tr X k s D CV) :
    ∃ ℓ A, OptimisticPoint tr X k ℓ A ∧ ℓ.frame.tree ⊆ U ∧
      3 * sp.n ≤ 4 * (optimisticVoters sp A ℓ.frame s D).ncard ∧
      optimisticVoters sp A ℓ.frame s D ⊆ Relayed tr H U X s D := by
  have hm := hrun.localRun.time_mono
  obtain ⟨ℓ, A, hp, hU, hn, hf⟩ := SA.optimistic_side
    (hrun.upTo (hrun.localRun.time_nonneg k)) hX
    ((upTo_optimisticLockAt hm).mpr ⟨le_rfl, hfl⟩)
  refine ⟨ℓ, A, (upTo_optimisticPoint hm).mp hp |>.2, hU, hn, ?_⟩
  intro u hu
  obtain ⟨v, hv, hs, hR, j, hj, h1, h2⟩ := (SA.fwd_iff).mp (hf hu)
  obtain ⟨hjk, hj⟩ := (ACTrace.upTo_sendOrAdmit hm).mp hj
  exact ⟨v, hv, hs, hR, j, hrun.localRun.antitone hjk hX, hj, h1, h2⟩

end Consensus.Goldilocks.SA.Growing

end
