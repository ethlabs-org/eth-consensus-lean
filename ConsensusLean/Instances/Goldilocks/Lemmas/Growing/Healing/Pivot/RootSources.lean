module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.ProposalReceipt
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC

public section

/-! # Root comparison for independently honest held targets -/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- Compare the actual root without requiring the target's independent read to precede it. -/
theorem held_target_proposal_root_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x p : Fin sp.n} {r i u : Nat} (hx : x ∈ H (tr.time r)) (hpH : p ∈ H (tr.time i))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBx : B ∈ (tr.state x r).fg.tree)
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    (hheld : Anc (tr.HonestBlocksAt H) ell.frame.F B → B ∈ ell.frame.tree)
    (hseed : ∃ v q m S, HighOrigin tr H g v q m S ∧ tr.time q < sp.ts u ∧
      Compatible (tr.HonestBlocksAt H) B S)
    (hcompare : ∀ v q m O, q < i → HighOrigin tr H g v q m O →
      Compatible (tr.HonestBlocksAt H) B O) :
    Compatible (tr.HonestBlocksAt H) ell.frame.fcRoot B := by
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hac.localRun.upTo (hp.run.time_nonneg i)
  have hci' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hci)
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci'
  have hU := hac.localRun.coherent
  have ht := hp.run.time_nonneg i
  have hle : ∀ k < i, tr.time k ≤ tr.time i := fun _ hk => hp.run.time_mono hk.le
  have hfr := Compose.frame_of_projAC (hp.run.upTo ht) hpH
    (show (tr.upTo (tr.time i)).projAC.CallAt p i ell by
      rwa [RunTrace.upTo_projAC])
  rw [RunTrace.upTo_state_of_le hp.run.time_mono le_rfl] at hfr
  have hFF : ell.frame.F = (tr.state p i).fg.F := by rw [hfr]; rfl
  by_cases hlow : (tr.state p i).fg.hj ≤ HZ tr H g
  · obtain ⟨v, q, m, S, hS, hqt, hBS⟩ := hseed
    have hqb : tr.time q ≤ b := hqt.le.trans (hti ▸ hib)
    have hFS := hp.low_finalized_below_origin_at ht hle hpH hib hlow hS hqb
    rw [← hFF] at hFS
    by_cases hBF : Anc (tr.HonestBlocksAt H) B ell.frame.F
    · exact Or.inr (hBF.trans (hPhi.F_anc_fcRoot.mono hPhiU))
    have hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B := by
      rcases hBS with h | h
      · exact (Anc.total hU hFS h).resolve_right hBF
      · exact hFS.trans h
    have hBy := (frame_tree_subset_at hp.run hp.noColl hpH hci).2 (hheld hFB)
    have hSt : S ∈ ell.frame.tree := by
      rcases proposal_holds_old_at hp hpH hci hcall hd hti hib hS hqt with h | h
      · exact h
      · have he := h.antisymm hU hFS
        exact he ▸ hPhi.rooted.1
    exact hp.low_root_of_held_seed_at_call_at hpH hBy hib hpH hib hS hqb hci
      ((frame_tree_subset_at hp.run hp.noColl hpH hci).2 hSt) hlow hBS hheld
  · exact hp.high_J_root_of_held_at_call_before_at hx hBx hpH hib hci (by omega) hcompare

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
