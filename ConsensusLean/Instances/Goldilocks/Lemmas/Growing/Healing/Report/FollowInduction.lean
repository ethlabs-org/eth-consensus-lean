module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowRelay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowWitnessBoundary
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Later-label propagation from an early historical witness -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

/-- A next-vote base propagates through later labels without retaining a fixed honest cohort. -/
theorem later_heads_of_early_witness_at
    {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s N floor : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts N + sp.Δ ≤ b)
    {kindJ : Prop} {J X Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s) (sp.ts N + sp.Δ) floor kindJ J)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J X)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hbase : ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e →
      e.msg.slot = s + 1 → SA.VoteExtends (tr.HonestBlocksAt H) e.msg X)
    (hstock : sp.committeeSize = sp.n) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e → e.msg.slot = r →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg X) ∧
      (s + 2 ≤ r → ∀ y i ell, y ∈ H (tr.time i) → tr.projAC.CallAt y i ell →
        ell.call = .proposal → tr.time i = sp.ts r → ∀ d pay,
        (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) X d.head) := by
  have hΔ := sp.toParams.hΔ
  have hts {p q : Nat} (hpq : p ≤ q) : sp.ts p ≤ sp.ts q :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast hpq)
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hwa := (hrun.cutLaw w a (.ac ellw) (Compose.projAC_callAt.mp hcw) hw).1
  have hQ : Q ∈ (tr.state w a).fg.tree := by rw [hwa] at hQw; exact hQw.1
  intro r hrlo
  induction r, hrlo using Nat.le_induction with
  | base => exact fun _ => ⟨hbase, fun h => by omega⟩
  | succ m hsm ih =>
    intro hrN
    have ht := hts hrN
    have hms := hts hsm
    have hsstep := SA.ts_succ s (sp := sp)
    have hwarm : gbar g + 4 * sp.Δ ≤ sp.ts m := by linarith only [hm, hms, hsstep]
    have hprior := (ih (show m ≤ N by omega)).1
    have hwin : FrameWindow tr H (sp.ts m) (sp.ts (m + 1 : Nat) + sp.Δ)
        floor kindJ J :=
      ⟨fun y i hy hlo hhi => hframe.floor_eq y i hy ((hts (by omega)).trans hlo)
          (hhi.trans (by linarith only [ht])),
       fun y i hy hlo hhi => hframe.kind_iff y i hy ((hts (by omega)).trans hlo)
          (hhi.trans (by linarith only [ht])),
       fun y i hy hlo hhi => hframe.root_eq y i hy ((hts (by omega)).trans hlo)
          (hhi.trans (by linarith only [ht]))⟩
    have hfinal {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
        (hlo : sp.ts s ≤ tr.time i) (hhi : tr.time i ≤ sp.ts N + sp.Δ) :
        Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F Q := by
      apply hframe.finalized_below_descendant_at hrun hnc hy hw hw
        (sp.toParams.fg.faults_lt_quorum_margin
          (hf _ ((hrun.time_nonneg i).trans (le_max_left _ _))
            (max_le (hhi.trans hmb) (by
              have hmN := hts (show s + 1 ≤ N by omega)
              linarith only [hat, hsstep, hmN, hmb, hΔ]))))
        hlo hhi hQ hh (fun hk => (hJ hk).trans hXQ) hQ .refl
    refine ⟨unanimous_next_votes_of_witness_at hrun hnc hsvc hawake hf hcatch hnr hwarm
      (by linarith only [ht, hmb]) hwin hw hQ hh hJ hXQ ?_ hprior hstock, ?_⟩
    · intro y i e hy hv hes
      obtain ⟨ell, hc⟩ := hv
      have hr := (hac.upTo (hrun.time_nonneg i)).localRun
      have hc' := SA.upTo_castAt.mpr ⟨le_rfl, hc⟩
      have hs : sp.slot (tr.time i) = m + 1 := (SA.castAt_spec hr hy hc').2.1.symm.trans hes
      have hlo : sp.ts s ≤ tr.time i :=
        (SA.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2 (by
          rw [hs]; exact_mod_cast (by omega : s ≤ m + 1))
      have hhi : tr.time i ≤ sp.ts N + sp.Δ := by
        have h := SA.vote_time_le hr hy ⟨ell, hc'⟩
        change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at h
        rw [hs] at h
        linarith only [h, ht]
      have he := (hrun.cutLaw y i (.ac ell) (Compose.projAC_callAt.mp hc.1) hy).1
      exact frame_witness_readPoint_stamp_at hrun hnc hsvc hcatch hnr hw hy hcw hc hes hwarm
        (by linarith only [hat, hms, hsstep, hΔ]) hQw (he ▸ hfinal hy hlo hhi)
    · intro _ y i ell hy hc hcall hti d pay hd
      have hlo : sp.ts s ≤ tr.time i := by rw [hti]; exact hts (by omega)
      have hhi : tr.time i ≤ sp.ts N + sp.Δ := by rw [hti]; linarith only [ht, hΔ]
      have he := (hrun.cutLaw y i (.ac ell) (Compose.projAC_callAt.mp hc) hy).1
      have hQt := frame_relay_before_at hrun hnc hsvc hcatch hnr hw hy hcw hc hQw
        (by rw [hti]; have hmstep := SA.ts_succ m (sp := sp); linarith only [hwarm, hmstep, hΔ])
        (by rw [hti]; have hmstep := SA.ts_succ m (sp := sp)
            linarith only [hat, hms, hsstep, hmstep, hΔ])
        (he ▸ hfinal hy hlo hhi)
      rw [he] at hQt
      exact unanimous_next_proposal_of_witness_at hrun hnc hsvc hawake hf hcatch hnr hwarm
        (by linarith only [ht, hmb]) hwin hw hQ hh hJ hXQ hprior hy hc hcall hti hd hQt.1 hstock

end Consensus.Goldilocks.Healing.Growing

end
