module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Steps
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: the restarts of a joined updater

`update_restarts`: the restarts of an honest node up to its update of slot `s` (joined) are at or
before `t_s`. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (SA.Blk sp.n FGP)} {T : SA.SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

/-- The restarts of an honest node up to its update of slot `s` (joined) are at or before
`t_s`. -/
theorem update_restarts {ini : Fin sp.n → SA.SAState sp.n}
    (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T ini)
    {y : Fin sp.n} (hy : y ∈ H) {k₀ s : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)}
    (hu : SA.UpdateAt T y k₀ s ℓ) : ∀ k ≤ k₀, T.RestartAt y k → T.time k ≤ sp.ts s := by
  obtain ⟨hc, hcall, ht, hj⟩ := hu
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hts₂ : sp.ts (s + 2 : Nat) = sp.ts s + 8 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have he := hr.exec k₀ ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at he
  have hpost : SA.joined sp (T.post k₀) (T.time k₀) := by
    have hp : T.post k₀ =
        ((SA.goldilocksSA sp FGP ro).step y (T.state y k₀) ℓ.frame (T.time k₀) ℓ.call).1 := by
      rw [he]
    unfold SA.joined at hj ⊢
    rw [hp, SA.step_restartTime y _ _ _ _ (by rw [hcall]; simp)]
    exact hj
  have hsl : sp.slot (T.time k₀) = s + 1 :=
    SA.slot_of_mem sp (s + 1) (by rw [ht, hts]; linarith) (by rw [ht, hts₂]; linarith)
  intro k hk hrk
  have := (SA.joined_awakeU sp FGP ro H U T hr.toU y hy k₀ ℓ hc hpost).2 k hk hrk
  rwa [hsl, show ((s + 1 : Nat) : Int) - 1 = s by push_cast; ring] at this

end Consensus.Goldilocks.Compose

end
