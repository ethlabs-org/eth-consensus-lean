module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # A late delivery follows the receiver's vote

This is receiver-local event ordering; no service invariant or other node's
continued honesty is needed in the retained prefix.
-/

namespace Consensus.Goldilocks.Healing.Growing.Outcome

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {tr : GoldilocksTrace sp ro}

private theorem restart_emits {H : Set (Fin sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {v : Fin sp.n} (hv : v ∈ H) {i : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt v i ell) (hcl : ell.call = .restart) : ell.emits = [] := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have he := hr.exec i ell hc.2 (hc.1 ▸ hv)
  rw [hc.1, hcl] at he
  have h' : ell.emits = (((SA.goldilocksSA sp (List (FG.Att sp.n)) ro).step v
      (tr.projAC.state v i) ell.frame (tr.projAC.time i) .restart)).2 := by rw [he]
  rw [h']
  exact ((SA.restart_state sp) _ ro v (tr.projAC.state v i) ell.frame (tr.projAC.time i)
    (SA.frameIn_of_callAt hr hv hc).1 (hr.time_nonneg i)).1

private theorem vote_before_late_delivery {H : Set (Fin sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y k ell e)
    {i : Nat} {W : SA.Blk sp.n (List (FG.Att sp.n))} (hA : tr.AcceptAt y i W)
    (hik : i < k) (ht : tr.time i = sp.ts e.msg.slot + sp.Δ) : False := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hac.localRun
  have hDelta : (0 : Int) < sp.Δ := sp.toParams.hΔ
  set u := sp.ts e.msg.slot + sp.Δ with hu
  have hm0 : 0 ≤ sp.ts e.msg.slot := by simp only [SAParams.ts]; positivity
  have htk : tr.time k = u :=
    le_antisymm (Compose.cast_head_fcRoot hr hy hc).2 (ht ▸ hrun.time_mono hik.le)
  have hslot : sp.slot u = e.msg.slot := SA.slot_of_mem sp _ (by linarith)
    (by simp only [hu, SAParams.ts]; push_cast; linarith)
  have hpub : sp.toParams.IsPublic u :=
    ⟨4 * (e.msg.slot : Int) + 1, by simp only [hu, SAParams.ts]; ring⟩
  rcases Compose.blockCall_cases hrun.toLocalRun hy hA with hgW | ⟨j, x, -, -, hP, -⟩
  swap
  · obtain ⟨-, hP2, -⟩ := hP
    rw [ht] at hP2
    change u = sp.toParams.slotTime (sp.slot u) at hP2
    rw [hslot, sp.slotTime_eq] at hP2
    have : u = sp.ts e.msg.slot + sp.Δ := hu
    simp only [SAParams.ts] at this
    linarith only [hDelta, hP2, this]
  rw [ht] at hgW
  obtain ⟨jt, x, hgt⟩ := hrun.tick_of_awake y hy u (by linarith only [hDelta, hm0]) hpub
    (htk ▸ hrun.awake_of_call y hy k ⟨_, Compose.projAC_callAt.mp hc.1⟩)
  obtain ⟨hct, htt⟩ := Healing.tick_first_cut hgt
  have hjti : jt < i := by
    rcases lt_trichotomy jt i with h | rfl | h
    · exact h
    · have := hct.2.symm.trans hA.2
      simp [Node.acCall] at this
    · have := hrun.phase_order y hy y hy i jt u (.block W) (.tick x) hgW hgt h
      simp [Node.Event.phase] at this
  have hnrk : ell.call ≠ .restart := fun hcl => by
    have := hc.2
    rw [restart_emits hrun hnc hy hc.1 hcl] at this
    cases this
  have hjk : SA.joined sp (tr.projAC.state y k) u := by
    obtain ⟨-, -, hyj, -⟩ := SA.castAt_spec hr hy hc
    have he := hr.exec k ell hc.1.2 (hc.1.1 ▸ hy)
    rw [hc.1.1] at he
    have h1 : (tr.projAC.post k).restartTime = (tr.projAC.state y k).restartTime := by
      have hpost : tr.projAC.post k = ((SA.goldilocksSA sp (List (FG.Att sp.n)) ro).step y
          (tr.projAC.state y k) ell.frame (tr.projAC.time k) ell.call).1 := by rw [he]
      rw [hpost]
      exact SA.step_restartTime y _ _ _ _ hnrk
    unfold SA.joined at hyj ⊢
    rw [← h1, SA.restartTime_of_castAt hr hy hc, ← htk]
    exact hyj
  have hjp := Compose.joined_projection sp ro dg H tr proposer hrun y hy u
  have hnr_k : ¬ tr.RestartAt y k := fun ⟨ell', hc', hr'⟩ => by
    have h := (Compose.projAC_callAt.mp hc.1).2.symm.trans hc'.2
    simp only [Option.some.injEq, Cut.ac.injEq] at h
    subst h
    exact hnrk hr'
  have hJ : tr.JoinedAt y u := (hjp.2.1 k ⟨_, Compose.projAC_callAt.mp hc.1⟩ hnr_k htk).mpr (by
    rw [← Compose.projAC_state hrun.toLocalRun hy k]
    exact hjk)
  obtain ⟨ellt, hlt, hcall⟩ : ∃ ellt : ACLabel (goldilocksNode sp ro),
      tr.label jt = some (.ac ellt) ∧ ellt.call = .tick := ⟨_, hct.2, rfl⟩
  have hct' : tr.CallAt y jt (.ac ellt) := ⟨hct.1, hlt⟩
  have hpt : tr.projAC.CallAt y jt ellt := Compose.projAC_callAt.mpr hct'
  have hnrt : ¬ tr.RestartAt y jt := fun ⟨ell', hc', hr'⟩ => by
    have h := hlt.symm.trans hc'.2
    simp only [Option.some.injEq, Cut.ac.injEq] at h
    subst h
    rw [hcall] at hr'
    cases hr'
  have hjt : SA.joined sp (tr.projAC.state y jt) u := by
    rw [Compose.projAC_state hrun.toLocalRun hy]
    exact (hjp.2.1 jt ⟨_, hct'⟩ hnrt htt).mp hJ
  have hve : SA.VoteAt tr.projAC y k e := ⟨ell, hc.1, hc.2⟩
  by_cases hvs : (tr.projAC.state y jt).votedSlot = (e.msg.slot : Int)
  · obtain ⟨j', hj', e', hve', hes⟩ := SA.cast_of_votedSlot hr hy jt e.msg.slot hvs
    have := ((SA.one_vote_per_slot sp) _ ro H _ tr.projAC hr y hy j' k e' e hve' hve hes).1
    omega
  · have hexec := hr.exec jt ellt hpt.2 (hpt.1 ▸ hy)
    rw [hpt.1, hcall] at hexec
    have hne := Compose.acOnTick_votes (ro' := ro) y _ ellt.frame hjt
      (by rw [hslot]; exact hvs) (by rw [hslot])
    rw [show tr.projAC.time jt = u from htt] at hexec
    rw [hexec] at hne
    obtain ⟨e', he'⟩ := List.exists_mem_of_ne_nil _ hne
    have hsl' := (SA.castAt_spec hr hy ⟨hpt, he'⟩).2.1
    have := ((SA.one_vote_per_slot sp) _ ro H _ tr.projAC hr y hy jt k e' e ⟨ellt, hpt, he'⟩ hve
      (by rw [hsl']; change sp.slot (tr.time jt) = _; rw [htt, hslot])).1
    omega

/-- An honest voter has not yet accepted a delivery at the late-vote tick. -/
theorem vote_before_late_delivery_at {H : Time → Set (Fin sp.n)}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k i : Nat}
    (hy : y ∈ H (tr.time k)) {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y k ell e)
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hA : tr.AcceptAt y i W)
    (hik : i < k) (ht : tr.time i = sp.ts e.msg.slot + sp.Δ) : False := by
  have hc' : (tr.upTo (tr.time k)).projAC.CallAt y k ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc.1⟩
  exact vote_before_late_delivery (hrun.upTo (hrun.time_nonneg k)) (hnc.upTo _) hy
    ⟨hc', hc.2⟩ ((RunTrace.upTo_acceptAt tr).mpr ⟨hrun.time_mono hik.le, hA⟩) hik ht

end Consensus.Goldilocks.Healing.Growing.Outcome

end
