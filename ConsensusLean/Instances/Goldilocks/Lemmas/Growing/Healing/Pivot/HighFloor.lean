module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.RootSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Healing.OriginLabel

public section

/-! # Proposal high floors from shared retained and causal suppliers

The causal label bound and retained floor theorem are explicit inputs owned by other workers.
No duplicate pending declaration is introduced here.
-/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- Specialize the retained signed floor source to an actual proposal's causal label bound. -/
theorem high_floor_source_at_proposal_of_sources_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x p : Fin sp.n} {r l i u : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l B) (hpH : p ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u) (hrb : tr.time r ≤ b) (hib : tr.time i ≤ b)
    (hlabel : p ∈ H (tr.time i) → tr.projAC.CallAt p i ell → ell.call = .proposal →
      tr.time i = sp.ts u → tr.time i ≤ b →
      ∀ v q m O, q < i → HighOrigin tr H g v q m O → m < u)
    (hfloorSource :
      (∀ W ∈ (tr.state p i).fg.tree, ∀ att ∈ W.fgPayload,
        ∀ v d, v ∈ H (tr.time d) → tr.SignAt v d att → d < i → ∀ q m O,
          q < d → HighOrigin tr H g v q m O → m < u) →
      (∀ v q m O, q < i → HighOrigin tr H g v q m O →
        ∀ v' q' m' O', q' < i → HighOrigin tr H g v' q' m' O' →
          Compatible (tr.HonestBlocksAt H) O O') →
      (∀ v q m O, q < i → HighOrigin tr H g v q m O →
        Compatible (tr.HonestBlocksAt H) B O) →
      ((tr.state x r).fg.σ B.root).h < (tr.state p i).fg.headHeightFloor →
      ∃ v q m O E, q < i ∧ HighOrigin tr H g v q m O ∧ m < u ∧
        E ∈ (tr.state p i).fg.tree ∧ Anc (tr.HonestBlocksAt H) E O ∧
        Anc (tr.HonestBlocksAt H) B O ∧
        (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ E.root).h ∧
        ∃ d att, q < d ∧ d < i ∧ v ∈ H (tr.time d) ∧ tr.SignAt v d att ∧ att.T = E.root)
    (hfloor : ((tr.state x r).fg.σ B.root).h < (tr.state p i).fg.headHeightFloor) :
    ∃ v q m O E, q < i ∧ HighOrigin tr H g v q m O ∧ m < u ∧
      E ∈ (tr.state p i).fg.tree ∧ Anc (tr.HonestBlocksAt H) E O ∧
      Anc (tr.HonestBlocksAt H) B O ∧
      (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ E.root).h := by
  obtain ⟨v, q, m, O, E, hqi, hO, hmu, hE, hEO, hBO, hf, _⟩ :=
    hfloorSource (fun _ _ _ _ v _ _ _ hdi q m O hqd hO =>
      hlabel hpH hci hcall hti hib v q m O (by omega) hO)
      (fun _ q _ _ hqi hO _ q' _ _ hqi' hO' => hp.origins_compatible_at hO
        ((hp.run.time_mono hqi.le).trans hib) hO' ((hp.run.time_mono hqi'.le).trans hib))
      (fun _ q _ _ hqi hO => hp.origins_compatible_at ho hrb hO
        ((hp.run.time_mono hqi.le).trans hib)) hfloor
  exact ⟨v, q, m, O, E, hqi, hO, hmu, hE, hEO, hBO, hf⟩

/-- The frozen proposal floor wrapper, with no extra producer premises. -/
theorem high_floor_source_at_proposal_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x p : Fin sp.n} {r l i u : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l B) (hpH : p ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u) (hrb : tr.time r ≤ b) (hib : tr.time i ≤ b)
    (hfloor : ((tr.state x r).fg.σ B.root).h < (tr.state p i).fg.headHeightFloor) :
    ∃ v q m O E, q < i ∧ HighOrigin tr H g v q m O ∧ m < u ∧
      E ∈ (tr.state p i).fg.tree ∧ Anc (tr.HonestBlocksAt H) E O ∧
      Anc (tr.HonestBlocksAt H) B O ∧
      (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ E.root).h := by
  exact high_floor_source_at_proposal_of_sources_at hp ho hpH hci hcall hti hrb hib
    (fun hpH hc hcall hti hib _ _ _ _ hqi hO =>
      ProposalSources.origin_label_lt_at_proposal_at hp hpH hc hcall hti hib hqi hO)
    (hp.high_floor_signed_source_of_row_bound_at ho (hp.run.time_nonneg i)
      (fun _ hq => hp.run.time_mono hq.le) hpH hib) hfloor

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
