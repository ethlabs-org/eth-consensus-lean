module
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesRelay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry

public section

/-! # Early historical witnesses reach later frozen read points -/

namespace Consensus.Goldilocks.Healing.Growing
variable {hold : Time}

open AC (ACParams Payload gbar)

/-- An early frame witness has a pre-freeze stamp at a later honest cast.
The historical holder can already be compromised when the receiver casts. -/
theorem frame_witness_readPoint_stamp_at
    {sp : ACParams}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    {x y : Fin sp.n} {a i s : Nat} (hx : x ∈ H (tr.time a))
    (hy : y ∈ H (tr.time i))
    {ellx ell : ACLabel (goldilocksNode sp)}
    (hcx : tr.projAC.CallAt x a ellx)
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ell e)
    (hes : e.msg.slot = s + 1) (hm : gbar g + 4 * sp.Δ ≤ sp.ts s)
    (ha : tr.time a < sp.ts s + 2 * sp.Δ)
    {Q : AC.Blk sp.n (List (FG.Att sp.n))} (hQ : Q ∈ ellx.frame.tree)
    (hFQ : Anc (tr.HonestBlocksAt H) ell.frame.F Q) :
    Q ∈ (tr.state y i).fg.tree ∧
      e.readPoint.blockStamp Q.root < AC.ETime.of (AC.freeze sp (s + 1)) := by
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have hr := (hac.upTo (hrun.time_nonneg i)).localRun
  have hc' := AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hs : sp.slot (tr.time i) = s + 1 := (AC.castAt_specU hr.toU hy hc').2.1.symm.trans hes
  have hti : sp.ts (s + 1 : Nat) ≤ tr.time i :=
    (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2 (by rw [hs])
  have hts := AC.ts_succ s (sp := sp)
  have hfz : AC.freeze sp (s + 1) = sp.ts s + 3 * sp.Δ := by
    simp only [AC.freeze, show ((s + 1 : Nat) : Int) - 1 = s by omega]
  have hQt := frame_relay_before_at hrun hnc hsvc hcatch hx hy
    (fun r hr' hrs => hnr _ r (hrun.antitone (hrun.time_mono hr') hy) hrs) hcx hc.1 hQ
    (by linarith only [hm, hti, hts, sp.toParams.hΔ])
    (by linarith only [ha, hti, hts, sp.toParams.hΔ]) hFQ
  have hacc : AC.AcceptedBefore (tr.projAC.upTo (tr.time i)) y Q
      (AC.freeze sp (s + 1)) := by
    rcases frame_block_acceptance_at hrun hx hcx hQ with hg | ⟨k, hka, hxk, hk⟩
    · exact Or.inl (congrArg Block.root hg)
    have hkt := (hrun.time_mono hka.le).trans_lt ha
    have hfr : ell.frame.F = (tr.state y i).fg.F := by
      rw [(hrun.cutLaw y i (.ac ell) (Compose.projAC_callAt.mp hc.1) hy).1]
      rfl
    have hp := hrun.upTo (hrun.time_nonneg i)
    have accepted : ∃ q < i, tr.AcceptAt y q Q ∧ tr.time q < AC.freeze sp (s + 1) := by
      by_cases hnew : gbar g ≤ tr.time k
      · have hdl : tr.deadline y i (max (tr.time k) g) sp.Δ ≤ tr.time i := by
          rw [max_eq_left ((AC.le_gbar g).trans hnew), ← Compose.projAC_deadline]
          have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := i)
            (fun r hri hrs => hnr y r (hrun.antitone (hrun.time_mono hri) hy)
              (Compose.projAC_restartAt.mp hrs)) (tr.time k)
          change _ ≤ max (tr.time k) (gbar g) + sp.Δ at h
          rw [max_eq_left hnew] at h
          exact h.trans (by linarith only [hkt, hti, hts, sp.toParams.hΔ])
        obtain ⟨q, hqi, hq, hqd⟩ := hsvc.relay x k Q hxk hk ((AC.le_gbar g).trans hnew)
          y i hy ⟨_, Compose.projAC_callAt.mp hc.1⟩ hdl (hfr ▸ hFQ)
        have hqi' : q < i := by
          refine lt_of_le_of_ne hqi ?_
          rintro rfl
          cases Option.some.inj (hq.2.symm.trans (Compose.projAC_callAt.mp hc.1).2)
        have hdead := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := q)
          (fun r hrq hrs => hnr y r (hrun.antitone (hrun.time_mono (hrq.trans hqi)) hy)
            (Compose.projAC_restartAt.mp hrs)) (tr.time k)
        change _ ≤ max (tr.time k) (gbar g) + sp.Δ at hdead
        rw [max_eq_left hnew, Compose.projAC_deadline] at hdead
        rw [max_eq_left ((AC.le_gbar g).trans hnew)] at hqd
        exact ⟨q, hqi', hq, by rw [hfz]; linarith only [hqd, hdead, hkt]⟩
      · obtain ⟨q, hq, hacc, hqt⟩ := hrun.toLocalRun.fgCatchAt hcatch hxk hk (not_le.mp hnew)
          hy (by linarith only [hm, hti, hts, sp.toParams.hΔ]) (hfr ▸ hFQ)
        exact ⟨q, hq, hacc, by rw [hfz]; linarith only [hqt, hm, sp.toParams.hΔ]⟩
    obtain ⟨q, hqi, hq, hqt⟩ := accepted
    have hq' := (RunTrace.upTo_acceptAt (tr := tr)).mpr ⟨hrun.time_mono hqi.le, hq⟩
    obtain ⟨hqa, htq, _⟩ := Healing.ac_block_after hp.toLocalRun hy hq'
    exact Or.inr ⟨q + 1, by rwa [RunTrace.upTo_projAC] at hqa,
      by change tr.time (q + 1) < _; rw [show tr.time (q + 1) = tr.time q from htq]; exact hqt⟩
  refine ⟨?_, ?_⟩
  · rw [(hrun.cutLaw y i (.ac ell) (Compose.projAC_callAt.mp hc.1) hy).1] at hQt
    exact hQt.1
  · have h := AC.readPoint_blockStamp_lt_of_acceptedBefore hr hrun.vstart hy hc' hQt
      (by simpa only [hes] using hacc)
      (fun k hki hrs => by
        have h := hnr y k (hrun.antitone (hrun.time_mono hki) hy)
          (Compose.projAC_restartAt.mp ((ACTrace.upTo_restartAt).mp hrs).2)
        change tr.time k < _
        rw [hes, hfz]
        linarith only [h, hm, sp.toParams.hΔ])
      (by change AC.freeze sp e.msg.slot ≤ tr.time i; rw [hes, hfz];
          linarith only [hti, hts, sp.toParams.hΔ])
    simpa only [hes] using h

end Consensus.Goldilocks.Healing.Growing

end
