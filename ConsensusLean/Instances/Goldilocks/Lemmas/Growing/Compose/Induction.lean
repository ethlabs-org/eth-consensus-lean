module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Inv
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Induction

public section

/-! # Persistence assembly from the cut induction

The cut step is supplied explicitly while it is proved independently. No assumption about
constant honesty is used: each vote and cache read is checked at its own horizon.
-/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload)

/-- Assemble the persistence contract from the frozen cut-step interface. -/
theorem honest_fast_confirmations_persist_of_cut_step
    (hcut : ∀ {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
      {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}
      {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {proposer : Nat → Fin sp.n}
      {ΔF : Time} {x : Fin sp.n} {i₀ s m : Nat}
      {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)},
      Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr →
      PersistPremises tr H dg ΔF x i₀ s m B CV → ∀ k,
      (∀ j < k, VoteInv tr H s m B j ∧ CutInv tr H s m B j) → CutInv tr H s m B k) :
    HonestFastConfirmationsPersist := by
  intro sp ro dg H tr ΔF x i₀ s m B CV proposer hrun hp s' hs hsm
  have hinv : ∀ k, VoteInv tr H s m B k ∧ CutInv tr H s m B k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih => exact ⟨vote_step hrun hp k ih, hcut hrun hp k ih⟩
  have hts : sp.ts s' ≤ sp.ts m := (SA.ts_le_iff sp).mpr (by exact_mod_cast hsm)
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  refine ⟨fun y => ⟨fun i X hy hacc hi hwin => ?_, fun k hk => ?_,
      fun k X hy hX hk _ => ?_⟩,
    fun y i ℓ e hy hc hsl => ?_, fun y i e hy ⟨ℓ, hc, he⟩ hsl => ?_⟩
  · refine (cutInv_iff.mp (hinv i).2 y hy ⟨_, hacc⟩ hi ?_).2 X hacc
    rcases hwin with h | ⟨h, hX⟩
    · linarith
    · exact (Compose.not_proposesAt_mid hX h).elim
  · rcases hk with ⟨hy, _, hk₀, hk₁⟩ | ⟨hy, hk₀, hk₁⟩
    · exact state_caches hrun hp k (fun j _ => (hinv j).2) y hy hk₀
        fun j hj => by have := hrun.time_mono hj.le; linarith
    · classical
      have hss : sp.ts s ≤ sp.ts s' := (SA.ts_le_iff sp).mpr (by exact_mod_cast hs.le)
      have hex : ∃ j, sp.ts s ≤ tr.time j := ⟨k, by linarith⟩
      have hj₀k : Nat.find hex ≤ k := Nat.find_min' hex (by linarith)
      rcases Compose.state_of_le (tr := tr) (y := y) hj₀k with h | ⟨j, hj, hjk, hc, h⟩
      · rw [h]
        exact hp.clean.caches y _ (hrun.antitone (by linarith) hy)
          ⟨Nat.find_spec hex, fun j hj => not_le.mp (Nat.find_min hex hj)⟩
      · rw [h]
        have htj := hk₁ j hjk
        exact (cutInv_iff.mp (hinv j).2 y (hrun.antitone htj.le hy) hc
          ((Nat.find_spec hex).trans (hrun.time_mono hj)) (by linarith)).1
  · exact (Compose.not_proposesAt_mid hX hk).elim
  · have := (voteInv_iff.mp (hinv i).1 y hy ℓ e hc (hsl ▸ hs) (hsl ▸ hsm)).1
    rwa [hsl] at this
  · exact (voteInv_iff.mp (hinv i).1 y hy ℓ e ⟨hc, he⟩ (hsl ▸ hs) (hsl ▸ hsm)).2

end Consensus.Goldilocks.Compose.Growing

end
