module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC

public section

/-! # Goldilocks Healing: the high left entries of a post-drain voter

A high left entry of an honest voter's store has a crossing attestation whose high origin was
written before the vote's slot (`cast_entry_below_old`): the crossing supplier of the voter's
fork-choice root and height floor (`Healing/Outcome/RootFloor`). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- A high left entry of a post-drain voter's store lies below a bounded pre-slot high origin: its
crossing attestation's origin label is below the vote's slot. -/
theorem ResetPremisesUpTo.cast_entry_below_old {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {u : Nat} {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y j ell e)
    (hes : e.msg.slot = u) (hjb : tr.time j ≤ b) {E C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hE : E ∈ (tr.state y j).fg.tree) (hET : ((tr.state y j).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y j).fg.σ E.root).h) (hEC : (tr.state y j).fg.Anc E C)
    (hlt : ((tr.state y j).fg.σ E.root).h < ((tr.state y j).fg.σ C.root).h) :
    ∃ O, (∃ v r l, HighOrigin tr H g v r l O ∧ tr.time r < sp.ts u ∧ tr.time r ≤ b) ∧
      Anc (tr.HonestBlocks H) E O := by
  have hrun := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨W, hW, att, ha, v, hv, d, hdj, hs, _, r, hrd, l, O, ho, hEO⟩ :=
    hp.left_entry_origin hy hE hET hEh hEC hlt
  have hlu : l < u := hes ▸ hp.row_origin_label_lt hy hc hW ha hv hs hdj hrd ho
  obtain ⟨_, D, CV, _, hfl, _⟩ := hp.highOrigin_mem ho
  have hrt := hp.fastLock_time_lt hfl hlu
    ((hp.run.time_mono (by clear * - hdj hrd; omega : r ≤ j)).trans
      (hes ▸ (Compose.cast_head_fcRoot hrun hy hc).2))
  exact ⟨O, ⟨v, r, l, ho, hrt, (hp.run.time_mono (by clear * - hdj hrd; omega)).trans hjb⟩, hEO⟩

end Consensus.Goldilocks.Healing

end
