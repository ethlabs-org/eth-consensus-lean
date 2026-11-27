module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Persist
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Attest
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Source
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Sync
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Signing provenance retained at the signer's honesty horizon -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {tr : GoldilocksTrace sp} {H : Time → Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {proposer : Nat → Fin sp.n}

/-- An honest signing is at a public time, using honesty only at the signing cut. -/
theorem sign_public {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {a : FG.Att sp.n}
    (hc : tr.CallAt y j (.fg (.attest C (some a)))) :
    sp.toParams.IsPublic (tr.time j) := by
  exact Compose.sign_public (hrun.upTo (hrun.time_nonneg j)) hy
    ((Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩)

/-- Signing follows the same node's source call at the preceding cut and the same time.
Both states are retained at the signing cut, even if the node is compromised later. -/
theorem attest_source {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {a : FG.Att sp.n}
    (hc : tr.CallAt y j (.fg (.attest C (some a)))) :
    ∃ j', j = j' + 1 ∧ ∃ ℓ : ACLabel (goldilocksNode sp),
      tr.CallAt y j' (.ac ℓ) ∧ ℓ.call = .toFG ∧ tr.time j' = tr.time j ∧
      ((goldilocksNode sp).toFG (tr.state y j').ac ℓ.frame (tr.time j')).2 = some C ∧
      (tr.state y j).fg = (tr.state y j').fg := by
  obtain ⟨j', hj, ℓ, hc', hto, ht, hC, hs⟩ :=
    Compose.attest_source (hrun.toLocalRun.upTo (hrun.time_nonneg j)) hy
      ((Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩)
  change tr.time j' = tr.time j at ht
  have hstate := RunTrace.upTo_state_of_le (tr := tr) (y := y)
    hrun.time_mono (le_refl (tr.time j))
  have hstate' := RunTrace.upTo_state_of_le (tr := tr) (y := y) hrun.time_mono ht.le
  rw [hstate'] at hC
  rw [hstate, hstate'] at hs
  exact ⟨j', hj, ℓ, ((Trace.upTo_callAt _).mp hc').2, hto, ht, hC, hs⟩

variable {ΔF : Time} {x : Fin sp.n} {i₀ s m : Nat}
  {B : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}

end Consensus.Goldilocks.Compose.Growing

end
