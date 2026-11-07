module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.ServiceCarry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesRelay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Early historical frame witnesses reach the next vote's frozen tree -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)
open Compose.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Joinedness of this cast, rather than a no-restart premise, bounds its relay deadlines. -/
theorem witness_voterBlockTree_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) {s : Nat} (hm : gbar g ≤ sp.ts s)
    {w y : Fin sp.n} {a i : Nat} (hw : w ∈ H (tr.time a)) (hy : y ∈ H (tr.time i))
    {ellw ell : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {Q : SA.Blk sp.n (List (FG.Att sp.n))} (hQw : Q ∈ ellw.frame.tree)
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ell e)
    (hs : e.msg.slot = s + 1) (hFQ : Anc (tr.HonestBlocksAt H) ell.frame.F Q) :
    Q ∈ SA.voterBlockTree sp e.readPoint ell.frame (s + 1) := by
  have ht0 := hrun.time_nonneg i
  have hr := (acRun_upTo hrun hnc ht0).localRun
  have hc' := sa_castAt_upTo.mpr ⟨le_rfl, hc⟩
  have hU := honestBlocksAt_coherent hrun hnc
  have subU := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono ht0
  obtain ⟨hPhi, hPhiU⟩ := frameIn_at hrun hnc hy hc.1
  have hQU := (frameIn_at hrun hnc hw hcw).2 hQw
  have hslot : sp.slot (tr.time i) = s + 1 := (castAt_spec_at hrun hnc hy hc).2.1.symm.trans hs
  have hti : sp.ts (s + 1 : Nat) ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp ht0 _).2 (by rw [hslot])
  have hts := SA.ts_succ s (sp := sp)
  have hΔ := sp.toParams.hΔ
  have hfz : SA.freeze sp (s + 1) = sp.ts s + 3 * sp.Δ := by
    simp only [SA.freeze, show ((s + 1 : Nat) : Int) - 1 = s by omega]
  have hrs : ∀ k ≤ i, tr.projAC.RestartAt y k → tr.time k ≤ sp.ts s := by
    have hjoined := (SA.castAt_spec hr hy hc').2.2.1
    have hj : SA.joined sp ((tr.projAC.upTo (tr.time i)).post i) (tr.time i) := by
      unfold SA.joined
      rw [SA.restartTime_of_castAt hr hy hc']
      exact hjoined
    intro k hk hrestart
    have h := ((SA.joined_awake sp) _ ro (H (tr.time i)) _ _ hr y hy i ell hc'.1 hj).2 k hk
      (ACTrace.upTo_restartAt.mpr ⟨hrun.time_mono hk, hrestart⟩)
    change tr.time k ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1) at h
    simpa only [hslot, show ((s + 1 : Nat) : Int) - 1 = s by omega] using h
  have hdl : ∀ k ≤ i, ∀ t, t < sp.ts s + 2 * sp.Δ →
      tr.projAC.deadline y k t < sp.ts s + 3 * sp.Δ := by
    intro k hk t ht
    have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := k)
      (fun r hr hrestart => hrs r (hr.trans hk) hrestart) t
    have hm' : max t (sp.ts s) < sp.ts s + 2 * sp.Δ := max_lt ht (by linarith only [hΔ])
    change tr.projAC.deadline y k t ≤ max t (sp.ts s) + sp.Δ at h
    linarith only [hm', h]
  have ha : SA.AcceptedBefore (tr.projAC.upTo (tr.time i)) y Q (SA.freeze sp (s + 1)) := by
    rcases frame_block_acceptance_at hrun hw hcw hQw with hg | ⟨k, hka, hwk, hk⟩
    · exact Or.inl (congrArg Block.root hg)
    obtain ⟨hk', htk, -⟩ := Healing.ac_block_after (hrun.upTo (hrun.time_nonneg a)).toLocalRun hw
      ((RunTrace.upTo_acceptAt _).mpr ⟨hrun.time_mono hka.le, hk⟩)
    rw [RunTrace.upTo_projAC] at hk'
    have hacc := (ACTrace.upTo_acceptAt.mp hk').2
    have hwk' : w ∈ H (tr.time (k + 1)) := by
      change tr.time (k + 1) = tr.time k at htk
      rwa [htk]
    have hkt : tr.time (k + 1) < sp.ts s + 2 * sp.Δ := by
      change tr.time (k + 1) = tr.time k at htk
      rw [htk]
      exact (hrun.time_mono hka.le).trans_lt hat
    have hex : ∃ q ≤ i, tr.projAC.AcceptAt y q Q ∧ tr.time q < SA.freeze sp (s + 1) := by
      by_cases hkg : gbar g ≤ tr.time (k + 1)
      · obtain ⟨q, hqi, hq, hqt⟩ :=
          (service_syncACAt hrun hsvc (lo := g) (hi := tr.time (k + 1)) le_rfl).2
            w (k + 1) Q hwk' hacc ((SA.le_gbar g).trans hkg) le_rfl y i ell hy hc.1
            (by have := hdl i le_rfl _ hkt;
                change tr.projAC.deadline y i (tr.time (k + 1)) ≤ tr.time i;
                linarith only [this, hti, hts, hΔ]) hFQ
        exact ⟨q, hqi, hq, by rw [hfz]; exact hqt.trans (hdl q hqi _ hkt)⟩
      · obtain ⟨q, hqi, hq, hqt⟩ := service_catch_at hrun hcatch hwk' hacc
          (lt_of_not_ge hkg) hy hc.1 (by linarith only [hm, hti, hts, hΔ]) hFQ
        exact ⟨q, hqi, hq, by rw [hfz]; linarith only [hqt, hm, hΔ]⟩
    obtain ⟨q, hqi, hq, hqt⟩ := hex
    exact Or.inr ⟨q, ACTrace.upTo_acceptAt.mpr ⟨hrun.time_mono hqi, hq⟩, hqt⟩
  have hQt : Q ∈ ell.frame.tree := by
    rcases ha with hg | ⟨k, hk, hkt⟩
    · obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hy i ell hc'.1
      obtain rfl : Q = G := hU.1 hQU (subU hGU) (hg.trans hGr.symm)
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hFQ with heq | ⟨P, -, hP⟩
      · exact heq ▸ hPhi.rooted.1
      · exact False.elim (Option.some_ne_none _ (hP.2.2.symm.trans hGp))
    · have hki : k ≤ i := by
        by_contra hn
        have ht := hrun.time_mono (show i ≤ k by omega)
        change tr.time k < _ at hkt
        rw [hfz] at hkt
        linarith only [ht, hkt, hti, hts, hΔ]
      obtain ⟨ella, hca, hba⟩ := hk
      have hk : ACTrace.AcceptAt (tr.projAC.upTo (tr.time i)) y k Q := ⟨ella, hca, hba⟩
      have hQp := (SA.frameIn_of_callAt hr hy hca).2 ((SA.accept_new sp hr hy hk).1 _ hca)
      exact SA.mem_tree_of_acceptAt sp hr hy hk hki hc'.1
        (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc ht0 hQp hFQ)
  have hstamp := SA.readPoint_blockStamp_lt_of_acceptedBefore hr hy hc' hQt
    (by simpa only [hs] using ha)
    (fun k hk hrk => by
      have h := hrs k hk (ACTrace.upTo_restartAt.mp hrk).2
      change tr.time k < _
      rw [hs, hfz]
      linarith only [h, hΔ])
    (by change SA.freeze sp e.msg.slot ≤ tr.time i; rw [hs, hfz];
        linarith only [hti, hts, hΔ])
  exact ⟨hQt, Or.inl (by simpa only [hs] using hstamp)⟩

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
