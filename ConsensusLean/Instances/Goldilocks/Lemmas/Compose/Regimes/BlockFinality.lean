module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.BlockFinality
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety

public section

/-! # Block-level finality accountability -/

namespace Consensus.Goldilocks.BlockFinality

open Compose

private theorem store_eq {P : Params} {A : NodeAC P}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
    {sg : A.Msg → Fin P.n} {tr : RunTrace A} {proposer : Nat → Fin P.n}
    (hrun : Node.LocalRun proposer dg H sg tr) {y : Fin P.n} (hy : y ∈ H) (i : Nat) :
    tr.projFG.store y i = (tr.state y i).fg := by
  change (tr.projFG.state y i).1 = _
  rw [projFG_state hrun hy i]

/-- Conflicting finalized tips convict signers using the two readers' held chains. -/
theorem final_accountable : FinalAccountable := by
  intro P A dg H sg tr proposer hq hg hrun hnc y hy z hz i j hne
  have hr := fg_projection P A dg H sg tr proposer hq hg hrun hnc
  obtain ⟨c₁, σ₁, h₁, hF₁, hU₁, hc₁, -, X₁, hX₁, hb₁⟩ := Store.finalized_chain hr hy i
  obtain ⟨c₂, σ₂, h₂, hF₂, hU₂, hc₂, -, X₂, hX₂, hb₂⟩ := Store.finalized_chain hr hz j
  rw [store_eq hrun hy] at hF₁ hU₁ hc₁ hX₁ hb₁
  rw [store_eq hrun hz] at hF₂ hU₂ hc₂ hX₂ hb₂
  obtain ⟨S, hS, hSv⟩ := FG.accountable_safety P.fg c₁ c₂ σ₁ σ₂ h₁ h₂
    (fun h => hne (hc₂ _ hU₁ (hF₁ ▸ h))) (fun h => hne (hc₁ _ hU₂ (hF₂ ▸ h)).symm)
  have hmem : ∀ a ∈ P.fg.chainAtts c₁ ++ P.fg.chainAtts c₂,
      a ∈ ChainAtts tr y i X₁ ∪ ChainAtts tr z j X₂ := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨Y, hY, hYX, haY⟩ := hb₁ a ha
      exact Or.inl ⟨Y, hY, hYX, haY⟩
    · obtain ⟨Y, hY, hYX, haY⟩ := hb₂ a ha
      exact Or.inr ⟨Y, hY, hYX, haY⟩
  refine ⟨X₁, hX₁, X₂, hX₂, S, hS, fun v hv => ?_⟩
  obtain ⟨a, ha, b, hb, hav, hab⟩ := hSv v hv
  exact ⟨a, hmem a ha, b, hmem b hb, hav, hab⟩

/-- Durable FG clients do not sign slashable pairs, with no collision premise. -/
theorem non_framing : NonFraming := by
  intro P A dg H sg tr proposer hrun v hv k k' a b ha hb
  obtain ⟨inputs, hin, hsign⟩ := Store.signed_run_of_exec (fg_exec hrun) hv (max k k' + 1)
  have conv : ∀ m c, tr.SignAt v m c → tr.projFG.SignAt v m c := fun m c ⟨src, hs⟩ =>
    ⟨src, projFG_callAt.2 hs⟩
  exact FG.client_safety P.fg v inputs hin a
    (hsign k (by omega) a (conv k a ha)) b (hsign k' (by omega) b (conv k' b hb))

/-- Below the accountable fault threshold, honest finalized outputs agree. -/
theorem finalized_safe : FinalizedSafe := by
  intro P A dg H sg tr proposer hq hg hrun hnc hf y hy z hz i j
  have hr := fg_projection P A dg H sg tr proposer hq hg hrun hnc
  have h := Store.finalized_safety P _ _ H _ tr.projFG hr hf y hy z hz i j
  rwa [store_eq hrun hy, store_eq hrun hz] at h

end Consensus.Goldilocks.BlockFinality

end
