module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Receipt of raw writers without persistent sender honesty -/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- A raw writer's ancestor is held by a later independently honest slot-start reader. -/
theorem raw_writer_held_at_slot_start_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x p : Fin sp.n} {r s i u : Nat} (hx : x ∈ H (tr.time r)) (hpH : p ∈ H (tr.time i))
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hwriter : SA.ResultAt tr.projAC x r s C CV ∨ SA.FastLockAt tr.projAC x r s C CV)
    (hBC : Anc (tr.HonestBlocksAt H) B C) (hs : SA.gbar g + 4 * sp.Δ ≤ sp.ts s)
    (hsu : s < u) {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    (hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B) : B ∈ ell.frame.tree := by
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hac.localRun.upTo (hp.run.time_nonneg i)
  have hci' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hci)
  have hΔ := sp.toParams.hΔ
  have hstep : sp.ts s + 4 * sp.Δ ≤ tr.time i := by
    rw [hti]
    have ht := (SA.ts_le_iff sp).mpr (show (s : Int) + 1 ≤ u by omega)
    simp only [SAParams.ts] at ht ⊢
    linarith
  obtain ⟨v, _, D, hD, hDr, hBD, hg | ⟨q, hxq, hq, hqt⟩⟩ :=
    raw_writer_relay_source_at hac.localRun hx hwriter hBC
  · obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci'
    obtain ⟨G, hG, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hpH _ _ hci'
    have hDG : D = G := hac.localRun.coherent.1 hD hG (hg.trans hGr.symm)
    subst D
    have hGt : G ∈ ell.frame.tree := by
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp (hFB.trans hBD) with he |
          ⟨c, _, hpar⟩
      · exact he ▸ hPhi.rooted.1
      · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
    exact SA.frame_mem_of_between sp hac.localRun.coherent hPhi hPhiU hGt hBD hFB
  · have hpre := hp.run.upTo (hp.run.time_nonneg q)
    have hq' : (tr.upTo (tr.time q)).projAC.AcceptAt x q D := by
      rw [RunTrace.upTo_projAC]
      exact ACTrace.upTo_acceptAt.mpr ⟨le_rfl, hq⟩
    obtain ⟨k, _, hak, hkt⟩ := Healing.fg_accept_before hpre.toLocalRun hxq hq'
    have hak₀ := (RunTrace.upTo_acceptAt tr).mp hak |>.2
    have hkt₀ : tr.time k = tr.time q := hkt
    have hqt₀ : tr.time q < sp.ts s + 2 * sp.Δ := hqt
    have hxk : x ∈ H (tr.time k) := hkt₀ ▸ hxq
    have hjoin : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) ≤ sp.ts s := by
      have hbase := (SA.ts_le_iff_le_slot sp (SA.gbar_nonneg g)
        (sp.slot (SA.gbar g))).mpr (by omega)
      simp only [SAParams.ts] at hbase hs ⊢
      push_cast at hbase hs ⊢
      linarith
    have hDt := Outcome.accept_mem_frame hp hc hxk hpH hak₀ hci hib
      (by linarith) (by linarith) (by rw [hkt₀]; linarith) (hFB.trans hBD)
    obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci'
    exact SA.frame_mem_of_between sp hac.localRun.coherent hPhi hPhiU hDt hBD hFB

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
