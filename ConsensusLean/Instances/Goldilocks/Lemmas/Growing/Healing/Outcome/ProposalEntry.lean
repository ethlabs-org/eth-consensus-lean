module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LeftEntry
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The high left entries of a proposer under growing faults

A high left entry of the store of a proposer honest at its own cut has a crossing attestation
whose high origin was written before the proposal slot (`proposal_entry_below_old_at`): the
crossing supplier of the proposer's fork-choice root and height floor
(`Healing/Outcome/RootFloor`). -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- A high left entry of the proposer's store lies below a bounded pre-slot historical origin: its
crossing attestation's origin label is below the proposal slot. -/
theorem proposal_entry_below_old_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts u)
    (hib : tr.time i ≤ b) {E C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hE : E ∈ (tr.state p i).fg.tree) (hET : ((tr.state p i).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state p i).fg.σ E.root).h) (hEC : (tr.state p i).fg.Anc E C)
    (hlt : ((tr.state p i).fg.σ E.root).h < ((tr.state p i).fg.σ C.root).h) :
    ∃ O, (∃ v r l, HighOrigin tr H g v r l O ∧ tr.time r < sp.ts u ∧ tr.time r ≤ b) ∧
      Anc (tr.HonestBlocksAt H) E O := by
  obtain ⟨_, _, _, _, v, _, k', hki, _, _, r, hrk, l, O, ho, hEO⟩ :=
    hp.left_entry_origin_at (hp.run.time_nonneg i) (fun _ hq => hp.run.time_mono hq.le) hpH hib
      hE hET hEh hEC hlt
  have hlu := hp.origin_label_lt_at_proposal_at hpH hci hcall hti hib (by omega : r < i) ho
  obtain ⟨_, _, _, _, hfl, _⟩ := ho.2.2.1
  have hrt := Outcome.fastLock_time_lt_at hp.run hfl hlu (by
    have := hp.run.time_mono (show r ≤ i by omega)
    rw [hti] at this
    have := sp.toParams.hΔ
    linarith)
  exact ⟨O, ⟨v, r, l, ho, hrt, (hp.run.time_mono (by omega)).trans hib⟩, hEO⟩

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
