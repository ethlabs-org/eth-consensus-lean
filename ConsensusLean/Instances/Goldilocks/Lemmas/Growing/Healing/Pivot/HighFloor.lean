module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.RootSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SourceCover
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.FloorSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Healing.OriginLabel

public section

/-! # Proposal high floors from shared retained and causal suppliers

`high_floor_source_at_proposal_or_covered_at` takes the causal label bound from
`ProposalSources.origin_label_lt_at_proposal_at` and the retained signed floor source from
`ResetPremisesUpTo.high_floor_signed_source_or_covered_before_at`.
-/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
variable {hold : Time}

/-- The proposal floor source with the high-source cover: a high-origin source, or an entry
held by the proposer at or past its floor, covered up to the proposal's slot by a member
written before the proposal. -/
theorem high_floor_source_at_proposal_or_covered_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x p : Fin sp.n} {r l i u : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l B) (hpH : p ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u) (hrb : tr.time r ≤ b) (hib : tr.time i ≤ b)
    (hfloor : ((tr.state x r).fg.σ B.root).h < (tr.state p i).fg.headHeightFloor) :
    (∃ v q m O E, q < i ∧ HighOrigin tr H g v q m O ∧ m < u ∧
      E ∈ (tr.state p i).fg.tree ∧ Anc (tr.HonestBlocksAt H) E O ∧
      Anc (tr.HonestBlocksAt H) B O ∧
      (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ E.root).h) ∨
    (∃ E ∈ (tr.state p i).fg.tree, CoveredBefore tr H g a b (sp.slot (tr.time i)) i E ∧
      (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ E.root).h) := by
  rcases hp.high_floor_signed_source_or_covered_before_at ho (hp.run.time_nonneg i)
      (fun _ hq => hp.run.time_mono hq.le) hpH hib (u := u)
      (fun _ _ _ _ v _ _ _ hdi q m O hqd hO =>
        ProposalSources.origin_label_lt_at_proposal_at hp hpH hci hcall hti hib (by omega) hO)
      (fun _ q _ _ hqi hO _ q' _ _ hqi' hO' => hp.origins_compatible_at hO
        ((hp.run.time_mono hqi.le).trans hib) hO' ((hp.run.time_mono hqi'.le).trans hib))
      (fun _ q _ _ hqi hO => hp.origins_compatible_at ho hrb hO
        ((hp.run.time_mono hqi.le).trans hib)) hfloor with
    ⟨v, q, m, O, E, hqi, hO, hmu, hE, hEO, hBO, hf, -⟩ | ⟨E, hE, hcov, hf, -⟩
  · exact Or.inl ⟨v, q, m, O, E, hqi, hO, hmu, hE, hEO, hBO, hf⟩
  · exact Or.inr ⟨E, hE, hcov, hf⟩

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
