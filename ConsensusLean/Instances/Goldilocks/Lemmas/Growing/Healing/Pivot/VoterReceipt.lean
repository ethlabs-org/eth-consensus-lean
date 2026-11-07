module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.VoteRelay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Raw writer ancestors in a later voter's frozen tree

Each source is read on its writer's own prefix. Old acceptances use growing catch-up,
and newer acceptances use owed relay; neither requires the sender to remain honest.
-/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- An ancestor of a raw write is available at a later honest voter's read point. -/
theorem raw_writer_voterBlockTree_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hcatch : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r s i : Nat} (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time i))
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hwriter : SA.ResultAt tr.projAC x r s C CV ∨ SA.FastLockAt tr.projAC x r s C CV)
    (hBC : Anc (tr.HonestBlocksAt H) B C)
    (hgs : SA.gbar g + 4 * sp.Δ ≤ sp.ts s)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hs : s < e.msg.slot)
    (hF : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    B ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot := by
  have hm := hp.run.time_mono
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := (hac.upTo (hp.run.time_nonneg i)).localRun
  have hc' := SA.upTo_castAt.mpr (And.intro le_rfl hc)
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc'.1
  have hΔ := sp.toParams.hΔ
  obtain ⟨_, hys, hyj, _⟩ := SA.castAt_spec hr hy hc'
  change e.msg.slot = sp.slot (tr.time i) at hys
  have hti : sp.ts e.msg.slot ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg i) _).mpr (by rw [hys])
  have hsm : sp.ts s ≤ sp.ts ((e.msg.slot : Int) - 1) := (SA.ts_le_iff sp).mpr (by omega)
  have hfz : SA.freeze sp e.msg.slot < tr.time i := by
    unfold SA.freeze SAParams.ts at hti ⊢
    linarith
  have hrs : ∀ k ≤ i, ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) y k →
      tr.time k < SA.freeze sp e.msg.slot := by
    have hj' : SA.joined sp ((tr.projAC.upTo (tr.time i)).post i) (tr.time i) := by
      unfold SA.joined
      rw [SA.restartTime_of_castAt hr hy hc']
      exact hyj
    intro k hk hrk
    have ht := ((SA.joined_awake sp) _ ro _ _ _ hr y hy i ell hc'.1 hj').2 k hk hrk
    change tr.time k ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1) at ht
    rw [← hys] at ht
    unfold SA.freeze
    linarith
  obtain ⟨v, _, D, hDU, _, hBD, hsource⟩ :=
    raw_writer_relay_source_at hac.localRun hx hwriter hBC
  have hFD := hF.trans hBD
  have hDt : D ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot := by
    rcases hsource with hgen | ⟨q, hxq, hq, hqt⟩
    · obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hy _ _ hc'.1
      have heq : D = G := hac.localRun.coherent.1 hDU hGU (hgen.trans hGr.symm)
      subst D
      have hGt : G ∈ ell.frame.tree := by
        obtain heq | ⟨c, _, hp⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hFD
        · exact heq ▸ hPhi.rooted.1
        · exact absurd (hp.2.2.symm.trans hGp) (Option.some_ne_none _)
      have hbs := SA.blockStamp_lt_of_acceptedBefore sp hr hy hc'.1 hGt (Or.inl hGr)
        hrs (Or.inl hfz.le)
      have hne : ∀ X, ell.call = .block X → G.root ≠ X.root := by
        intro X hcall heq
        exact SA.accept_ne_genesis sp hr hy ⟨ell, hc'.1, hcall⟩ (heq.symm.trans hGr)
      rw [← SA.readPoint_blockStamp hr hy hc' hne] at hbs
      exact ⟨hGt, Or.inl hbs⟩
    · by_cases hg : g ≤ tr.time q
      · exact KernelProof.relay_mem_voterBlockTree_at hp hxq hq hg hqt hy hc (by omega) hFD
      have hpre := hp.run.upTo (hp.run.time_nonneg q)
      have hq' : (tr.upTo (tr.time q)).projAC.AcceptAt x q D := by
        rw [RunTrace.upTo_projAC]
        exact ACTrace.upTo_acceptAt.mpr ⟨le_rfl, hq⟩
      obtain ⟨q₀, _, hacc, htime⟩ := Healing.fg_accept_before hpre.toLocalRun hxq hq'
      have hacc₀ := (RunTrace.upTo_acceptAt tr).mp hacc |>.2
      have htime₀ : tr.time q₀ = tr.time q := htime
      have hlate : SA.gbar g + 2 * sp.Δ ≤ tr.time i := by
        have ht := (SA.ts_le_iff sp).mpr (show (s : Int) ≤ e.msg.slot by omega)
        linarith
      obtain ⟨j, hj, hji⟩ := Healing.exists_firstCutFrom_le hlate
      have hri := hp.run.upTo (hp.run.time_nonneg i)
      have hfr := Outcome.frame_of_call hp.run hy hc.1
      have hFD' : Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F D := by rwa [hfr] at hFD
      have hprev := Healing.run_F_mono hri.toLocalRun hy hji
      rw [RunTrace.upTo_state_of_le hm (hm hji), RunTrace.upTo_state_of_le hm le_rfl] at hprev
      have hsub := RunTrace.honestBlocks_upTo_subset hm (H := H) (hp.run.time_nonneg i)
      obtain ⟨k, hkj, hak⟩ := hcatch x q₀ D (htime₀ ▸ hxq) hacc₀
        (by rw [htime₀]; exact (not_le.mp hg).trans_le (le_gbar g)) y j
        (hp.run.antitone hlate hy) hj ((hprev.mono hsub).trans hFD')
      have hki : k < i := lt_of_lt_of_le hkj hji
      have hak' := (RunTrace.upTo_acceptAt tr).mpr ⟨hm hki.le, hak⟩
      obtain ⟨hAC, hACt, _⟩ := Healing.ac_block_after hri.toLocalRun hy hak'
      rw [RunTrace.upTo_projAC] at hAC
      have hAC₀ := ACTrace.upTo_acceptAt.mp hAC |>.2
      have hkti : k + 1 ≤ i := by omega
      have hkt : tr.time (k + 1) < SA.freeze sp e.msg.slot := by
        change tr.time (k + 1) = tr.time k at hACt
        rw [hACt]
        have := hj.2 k hkj
        unfold SA.freeze
        linarith
      have hAC' := ACTrace.upTo_acceptAt.mpr (And.intro (hm hkti) hAC₀)
      have hD := SA.mem_tree_of_acceptAt sp hr hy hAC' hkti hc'.1 hFD
      have hbs := SA.blockStamp_lt_of_acceptedBefore sp hr hy hc'.1 hD
        (Or.inr ⟨k + 1, hAC', hkt⟩) hrs (Or.inl hfz.le)
      have hne : ∀ X, ell.call = .block X → D.root ≠ X.root := by
        intro X hcall heq
        have hX := (SA.accept_new sp hr hy ⟨ell, hc'.1, hcall⟩).1 ell hc'.1
        obtain rfl : X = D := hr.coherent.1 (hPhiU hX) (hPhiU hD) heq.symm
        have he := SA.accept_unique sp hr hy hAC' ⟨ell, hc'.1, hcall⟩
        rw [he] at hkt
        linarith
      rw [← SA.readPoint_blockStamp hr hy hc' hne] at hbs
      exact ⟨hD, Or.inl hbs⟩
  have hBt := SA.frame_mem_of_between sp hr.coherent hPhi hPhiU hDt.1 hBD hF
  exact SA.voterBlockTree_anc hr hy hc' D hDt B
    (SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hBt hBD hDt.1)

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
