module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ConfirmedPending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.AncestorCandidate
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.UpdateReadPending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ReportCover
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalUnanimous
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Effective
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.OperationalReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepInterval
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LocksWF
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.HeadLock
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyConfirmedSupply
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The read after an operational update, under growing faults (open)

`operational_update_read_after_at`, the growing form of
`Obligations.operational_update_read_after`: the fresh fast lock and the effective record of an
actual honest update of the post-drain operational proposal `P` of slot `u` put `P` under the
confirmed read of the updater at the end of the update time `t_u + 6Δ`. The proposer is honest
through `t_u + Δ`, the updater and reader is honest at the read time (so at its update cut, of the
same time), and ancestry is in the blocks held while honest. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- OPEN. **The read after an actual update** of the operational proposal `P` of slot `u`, by a
node honest at the end of the update time, at the first cut after it. -/
theorem operational_update_read_after_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hhold : p ∈ H (sp.ts u + sp.Δ)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u)
    (hR : drainTime sp a ≤ sp.ts u) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hTb : sp.ts u + 6 * sp.Δ ≤ b) {y : Fin sp.n} (hy : y ∈ H (sp.ts u + 6 * sp.Δ))
    {j : Nat} {ell : ACLabel (goldilocksNode sp ro)} (hup : SA.UpdateAt tr.projAC y j u ell)
    (hlock : ∃ e, u + 2 ≤ e ∧ (⟨P.root, u, true, e⟩ : SA.Lock) ∈ (tr.projAC.post j).locks)
    {J : Nat} (hJ : Regimes.CutAfter tr J (sp.ts u + 6 * sp.Δ)) :
    Anc (tr.HonestBlocksAt H) P (Regimes.readAfter tr y J (sp.ts u + 6 * sp.Δ)) := by
  obtain ⟨ex, hex, hlock⟩ := hlock
  have hrun := hp.run
  have hnc := hp.noColl
  have hΔ := sp.toParams.hΔ
  have hm := hrun.time_mono
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have ht : tr.time j = sp.ts u + 6 * sp.Δ := hup.2.2.1
  have hT0 : 0 ≤ sp.ts u + 6 * sp.Δ := ht ▸ hrun.time_nonneg j
  have hleJ : ∀ q < J, tr.time q ≤ sp.ts u + 6 * sp.Δ := hJ.1
  have hjJ : j < J := by
    by_contra hn
    have := hm (show J ≤ j by omega)
    linarith [hJ.2]
  have hyj : y ∈ H (tr.time j) := ht ▸ hy
  have hle : ∀ e ≤ J, ∀ q < e, tr.time q ≤ sp.ts u + 6 * sp.Δ :=
    fun e he q hq => hleJ q (by omega)
  have htime : ∀ e, j ≤ e → e < J → tr.time e = sp.ts u + 6 * sp.Δ := by
    intro e hje heJ
    exact le_antisymm (hleJ e heJ) (ht ▸ hm hje)
  have hslot : sp.slot (sp.ts u + 6 * sp.Δ) = u + 1 := by
    apply SA.slot_of_mem sp (u + 1)
    · simp only [SA.SAParams.ts]; push_cast; linarith [sp.toParams.hΔ]
    · simp only [SA.SAParams.ts]; push_cast; linarith [sp.toParams.hΔ]
  have hclean : cleanLabel sp a + 2 * sp.k + 1 ≤ u := by
    rw [drainTime_eq] at hR
    have := (SA.ts_le_iff sp).mp hR
    rw [cleanLabel_eq]
    omega
  -- the prefix through the read time, where the reader is honest throughout
  have hrT := hrun.upTo hT0
  have hncT := hnc.upTo (sp.ts u + 6 * sp.Δ)
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hm hT0
  have hst : ∀ e ≤ J, (tr.upTo (sp.ts u + 6 * sp.Δ)).state y e = tr.state y e :=
    fun e he => Trace.upTo_state tr y (hle e he)
  have hstAC : ∀ e ≤ J, tr.projAC.state y e = (tr.state y e).ac := by
    intro e he
    have h := Compose.projAC_state hrT.toLocalRun hy e
    rwa [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC y (hle e he), hst e he] at h
  obtain ⟨hPt, hconf, -, -, -, hrecordEq⟩ :=
    operational_update_selection_at hp hc hhold hdesignated hactual hPs hR hgu hTb hyj hup
  have hRaw : SA.ResultAt tr.projAC y j u P
      (SA.fastCounted sp (tr.projAC.state y j) ell.frame u P) :=
    ⟨ell, hup, hconf, rfl⟩
  have hframes : ∀ e ≤ J, Compatible (tr.HonestBlocksAt H) (tr.state y e).fg.F P :=
    fun e he => hp.finalized_compatible_clean_source_at hc hyj (Or.inl hRaw) hclean
      (ht ▸ hTb) hT0 (hle e he) hy hTb
  -- the effective record after the update
  obtain ⟨hΦj, hΦjU⟩ := Compose.Growing.frameIn_at hrun hnc hyj hup.1
  have heff : Anc (tr.HonestBlocksAt H) P
      ((SA.lookup ell.frame (tr.projAC.post j).latestConfirmed).getD ell.frame.F) := by
    rw [hrecordEq]
    exact (Obligations.effective_record_update_slot_growth (sp := sp) hΦj hPt).1.mono hΦjU
  have hbase := Obligations.Growing.effective_record_after_ac_call_at hrun hyj hup.1 heff
  have hinterval : Obligations.Growing.EffectiveRecordIntervalAt tr H y (j + 1) J P := by
    apply Obligations.Growing.effectiveRecordInterval_of_candidates_before_at hrun hnc hT0
      hleJ hy
    · intro q hjq hqJ D s CV hsource
      have hqt := htime q (by omega) hqJ
      have hyq : y ∈ H (tr.time q) := hqt ▸ hy
      rcases hsource with ⟨ell', hu', hD, -⟩ | ⟨ell', A', -, -, hsel, -⟩
      · have hsu : s = u := by
          have hs : tr.time q = sp.ts s + 6 * sp.Δ := hu'.2.2.1
          have := (SA.ts_le_iff sp).mp (show sp.ts s ≤ sp.ts u by linarith)
          have := (SA.ts_le_iff sp).mp (show sp.ts u ≤ sp.ts s by linarith)
          omega
        subst s
        have hP := (operational_update_selection_at hp hc hhold hdesignated hactual hPs
          hR hgu hTb hyq hu').2.1
        have : D = P := Option.some.inj (hD.symm.trans hP)
        subst D
        exact Or.inl .refl
      · have hlate : sp.ts (sp.slot (tr.time q)) + 2 * sp.Δ ≤ tr.time q := by
          simp only [hqt, hslot]
          simp only [SA.SAParams.ts, Nat.cast_add, Nat.cast_one]
          linarith
        change SA.optimisticSelect sp A' ell'.frame (tr.time q) = some D at hsel
        simp only [SA.optimisticSelect, hlate, or_true, ↓reduceIte] at hsel
        cases hsel
    · intro q _ hqJ
      exact hframes (q + 1) (by omega)
  have hrecord := Obligations.Growing.effective_record_of_interval_at hrun hnc hT0 hleJ hy
    (by omega) hinterval hbase
  -- the frame of the read
  have hΦ : FrameOK (Node.frame (tr.state y J)) := by
    have h := Compose.frameOK_state hrT.toLocalRun hy J
    rwa [hst J le_rfl] at h
  have hΦU : (Node.frame (tr.state y J)).tree ⊆ tr.HonestBlocksAt H :=
    fun X hX => ⟨y, J, _, hT0, hleJ, hy, hX.1⟩
  have hhead : Anc (tr.HonestBlocksAt H) P
      (SA.acHead sp (tr.state y J).ac (Node.frame (tr.state y J)) (sp.ts u + 6 * sp.Δ)) := by
    rcases hframes J le_rfl with hFP | hPF
    · have hF : ∀ e ≤ J, Anc (tr.HonestBlocksAt H) (tr.state y e).fg.F P := by
        intro e he
        have h := Healing.run_F_mono hrT.toLocalRun hy he
        rw [hst e he, hst J le_rfl] at h
        exact (h.mono hsub).trans hFP
      have hPj : P ∈ (Node.frame (tr.state y j)).tree :=
        (Compose.Growing.frame_of_projAC_at hrun hyj hup.1) ▸ hPt
      have hPU : P ∈ tr.HonestBlocksAt H := hΦjU hPt
      have hPe : ∀ e, j ≤ e → e ≤ J → P ∈ (Node.frame (tr.state y e)).tree := by
        intro e hje heJ
        have hheld : P ∈ (tr.state y e).fg.tree := by
          have h := Compose.tree_mono hrT.toLocalRun hy hje
          rw [hst j (by omega), hst e heJ] at h
          exact h hPj.1
        refine ⟨hheld, ?_⟩
        have hPeU : P ∈ (tr.upTo (sp.ts u + 6 * sp.Δ)).HonestBlocks (H (sp.ts u + 6 * sp.Δ)) :=
          ⟨y, hy, e, by rw [hst e heJ]; exact hheld⟩
        have h := Compose.honest_held_anc hrT hncT hy
          (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hT0 hPeU (hF e heJ))
          (by rw [hst e heJ]; exact hheld)
        rwa [hst e heJ] at h
      have hun0 := hp.operational_unanimous_at hc hhold hdesignated hactual hPs hR
        (show sp.ts u ≤ b by linarith only [hTb, hΔ])
      have hun : ∀ z q e, z ∈ H (tr.time q) → SA.VoteAt tr.projAC z q e → tr.time q ≤ b →
          e.msg.slot = u → e.msg.head = P.root :=
        fun z q e hz hv hqb hs => hun0 z q e hz hv hs hqb
      have hRnext := hR.trans ((SA.ts_le_iff sp).mpr
        (show (u : Int) ≤ (u + 1 : Nat) by exact_mod_cast Nat.le_succ u))
      have hu : 0 < u := by
        rw [drainTime_eq] at hR
        have := (SA.ts_le_iff sp).mp hR
        exact (Nat.succ_pos _).trans_le (by exact_mod_cast this)
      obtain ⟨v, r, m, S, hseed, hrb, -, hrt⟩ := hp.reset_seed_before_slot_at hRnext
      have hSP := high_origins_before_next_slot_below_at hp hc hPU hun hgu hRnext
        (by linarith only [hTb, hΔ]) hseed hrt hrb
      have hva : ∀ e, j ≤ e → e ≤ J →
          (Node.frame (tr.state y e)).viableAncestor P = P := by
        intro e hje heJ
        have hΦe : FrameOK (Node.frame (tr.state y e)) := by
          have h := Compose.frameOK_state hrT.toLocalRun hy e
          rwa [hst e heJ] at h
        apply SA.viableAncestor_self hΦe (hPe e hje heJ)
        exact (hp.held_target_ancestor_candidate_at_state_at hT0 (hle e heJ) hy hTb
          (hPe e hje heJ) hseed hrb hSP (fun x q l B hqe ho =>
            (high_origin_compatible_before_update_at hp hc hPU hPs hu hun hgu hRnext hTb ho
              (hle e heJ q hqe)).symm)).symm
      have hlock' : (⟨P.root, u, true, ex⟩ : SA.Lock) ∈ (tr.state y (j + 1)).ac.locks := by
        rw [← hstAC (j + 1) (by omega), tr.projAC.state_succ_of_call hup.1]
        exact hlock
      sorry
    · exact hPF.trans ((hΦ.rooted.2 _ (SA.getHead_mem hΦ
        (fun _ h => h.1) _ _ _ _)).mono hΦU)
  exact (Obligations.exposed_prefix_preserved_of_record_head hU hΦ hΦU).mpr
    ⟨hrecord, hhead⟩

end Consensus.Goldilocks.Healing.Growing

end
