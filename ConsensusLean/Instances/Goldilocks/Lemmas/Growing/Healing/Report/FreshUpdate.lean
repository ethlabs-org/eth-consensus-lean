module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshUnlock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase

public section

/-! # Fresh fast locks and their adjacent report reads

The update and report are consecutive actual calls. Local execution is retained only
through their common timestamp; no later honesty of the original proposer is required.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Explicit joinedness, rather than a stronger GST margin, supplies actual votes
by the slot deadline from the healthy base on that deadline's prefix. -/
theorem honest_votes_of_joined_before_at
    {g : Time} {u : Nat}
    (hS : SA.HealthyBaseUpTo (tr.projAC.upTo (sp.ts u + sp.Δ))
      (H (sp.ts u + sp.Δ)) ((tr.upTo (sp.ts u + sp.Δ)).HonestBlocks (H (sp.ts u + sp.Δ)))
      proposer g (sp.ts u + sp.Δ))
    (hgu : gbar g ≤ sp.ts u)
    (hjoin : ∀ x, x ∈ H (sp.ts u + sp.Δ) →
      SA.JoinedAt tr.projAC x (sp.ts u + sp.Δ)) :
    ∀ x, x ∈ H (sp.ts u + sp.Δ) →
      ∃ j e, SA.VoteAt tr.projAC x j e ∧ e.msg.slot = u ∧
        tr.time j ≤ sp.ts u + sp.Δ := by
  intro x hx
  obtain ⟨j, e, hv, hs, ht⟩ := SA.honest_votes_of_joined_before hS hgu le_rfl
    (fun x hx r hrs hrt => by
      obtain ⟨ell, hc, hrestart⟩ := hrs
      exact hjoin x hx r
        ⟨ell, ((Trace.upTo_callAt _).mp hc).2, hrestart⟩ hrt) x hx
  obtain ⟨ell, hc, he⟩ := hv
  exact ⟨j, e, ⟨ell, ((Trace.upTo_callAt _).mp hc).2, he⟩, hs, ht⟩

/-- A vote by a validator still honest at the read has its strict early message
stamp in the receiver's pool. Only the receiving prefix is used. -/
theorem honest_vote_early_pool_before_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {u : Nat} (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y j ell)
    (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j) (hjb : tr.time j ≤ b)
    {x : Fin sp.n} (hx : x ∈ H (tr.time j)) {i : Nat}
    {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.VoteAt tr.projAC x i e) (hes : e.msg.slot = u)
    (hit : tr.time i ≤ tr.time j) :
    e.msg ∈ (tr.projAC.state y j).pool u ∧
      (tr.projAC.state y j).voteStamp e.msg < SA.ETime.of (sp.ts u + 2 * sp.Δ) := by
  have hS := healthy_base_of_service_catch_before_at hrun hnc hsvc hawake hf hcatch
    (hrun.time_nonneg j) hjb
  have hs := Trace.upTo_state tr.projAC y (i := j)
    (fun q hq => hrun.time_mono hq.le)
  have hc' : (tr.projAC.upTo (tr.time j)).CallAt y j ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  have hv' : SA.VoteAt (tr.projAC.upTo (tr.time j)) x i e := by
    obtain ⟨ellx, hcx, he⟩ := hv
    exact ⟨ellx, (Trace.upTo_callAt _).mpr ⟨hit, hcx⟩, he⟩
  have hrst : ∀ k ≤ j, ACTrace.RestartAt (tr.projAC.upTo (tr.time j)) y k →
      tr.time k < sp.ts u := by
    intro k _ ⟨ellk, hck, hk⟩
    have hkt := ((Trace.upTo_callAt _).mp hck).1
    have hbound := hnr y k (hrun.antitone hkt hy)
      (Compose.projAC_restartAt.mp ⟨ellk, ((Trace.upTo_callAt _).mp hck).2, hk⟩)
    linarith [sp.toParams.hΔ]
  have hp := SA.honest_vote_early_pool_before hS hy hc'
    (by linarith [sp.toParams.hΔ]) ht le_rfl
    (fun k hkj t _ => Compose.ac_deadline_le_of_restarts
      (fun r hr hrs => (hrst r (hr.trans hkj) hrs).le) t)
    hrst hx hv' hes j (Or.inl rfl)
  simpa only [hs] using hp

/-- Wakefulness and the receiver's restart cutoff produce the actual adjacent calls. -/
theorem update_toFG_calls_of_awake_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {g b : Time}
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hnr : NoRestartAfter tr H (gbar g)) {u : Nat}
    (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H (sp.ts (u + 1 : Nat) + 2 * sp.Δ)) :
    ∃ k ell ell', SA.UpdateAt tr.projAC y k u ell ∧
      tr.projAC.CallAt y (k + 1) ell' ∧ ell'.call = .toFG ∧
      tr.time (k + 1) = sp.ts (u + 1 : Nat) + 2 * sp.Δ ∧
      ell'.frame = ell.frame := by
  let T := sp.ts (u + 1 : Nat) + 2 * sp.Δ
  have hT : T = sp.ts u + 6 * sp.Δ := by
    dsimp only [T, SAParams.ts]
    push_cast
    ring
  have hΔ := sp.toParams.hΔ
  have hT0 : 0 ≤ T := by
    rw [hT]
    have hu0 : 0 ≤ sp.ts u := by simp only [SAParams.ts]; positivity
    linarith
  have hr := hrun.upTo hT0
  have hslot : sp.slot T = u + 1 := by
    rw [hT]
    apply SA.slot_of_mem sp (u + 1)
    all_goals simp only [SAParams.ts]; push_cast; linarith
  have hjoin : ∀ i, (tr.upTo T).time i = sp.ts u + 6 * sp.Δ →
      SA.joined sp ((tr.upTo T).projAC.state y i) ((tr.upTo T).time i) := by
    intro i hi
    unfold SA.joined
    have hac := (Compose.goldilocks_ac_projection sp ro dg (H T) (tr.upTo T)
      proposer hr (hnc.upTo T)).localRun
    rcases SA.restartTime_state hac hy i with h | ⟨r, _, hrs, h⟩
    · rw [h]; exact bot_le
    · rw [h]
      apply WithBot.coe_le_coe.mpr
      rw [hi, ← hT, hslot, show ((u + 1 : Nat) : Int) - 1 = u by omega]
      rw [RunTrace.upTo_projAC] at hrs
      have hrt := ((Trace.upTo_callAt _).mp hrs.choose_spec.1).1
      have hrestart : tr.RestartAt y r := Compose.projAC_restartAt.mp
        ⟨hrs.choose, ((Trace.upTo_callAt _).mp hrs.choose_spec.1).2, hrs.choose_spec.2⟩
      have hbound := hnr y r (hrun.antitone hrt hy) hrestart
      change tr.time r ≤ _
      linarith
  obtain ⟨k, ell, ell', hu, hc, hto, ht, hf, _⟩ :=
    Healing.update_toFG_calls_of_awake hr hy
      ⟨hT ▸ hawake y T hy (by rw [hT]; linarith) hTb, hT.symm.le⟩ hjoin
  have hkt : tr.time k ≤ T := by
    have h := hu.2.2.1
    change tr.time k = sp.ts u + 6 * sp.Δ at h
    exact (h.trans hT.symm).le
  rw [RunTrace.upTo_projAC] at hu hc
  have hs := Trace.upTo_state tr.projAC y (i := k)
    (fun q hq => (hrun.time_mono hq.le).trans hkt)
  refine ⟨k, ell, ell', ?_, ((Trace.upTo_callAt _).mp hc).2, hto,
    ht.trans hT.symm, hf⟩
  refine ⟨((Trace.upTo_callAt _).mp hu.1).2, hu.2.1, hu.2.2.1, ?_⟩
  simpa only [hs, Trace.upTo_time] using hu.2.2.2

/-- Once selection and no-veto are known, local execution inserts the fresh fast lock.
The conclusion keeps its two-slot lifetime independently of the service proof. -/
theorem fresh_fast_lock_of_selection_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {k u : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hu : SA.UpdateAt tr.projAC y k u ell) (hPt : P ∈ ell.frame.tree)
    (hconf : SA.getConfirmation sp (tr.projAC.state y k) ell.frame u = some P)
    (hnv : ¬ SA.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) P)
    (hfast : SA.fastSelect sp (tr.projAC.state y k) ell.frame u P = some P)
    (hva : ell.frame.viableAncestor P = P) :
    ∃ e, u + 2 ≤ e ∧
      (⟨P.root, u, true, e⟩ : SA.Lock) ∈ (tr.projAC.post k).locks := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time k))
    (tr.upTo (tr.time k)) proposer (hrun.upTo (hrun.time_nonneg k))
    (hnc.upTo (tr.time k))).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hc : (tr.projAC.upTo (tr.time k)).CallAt y k ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hu.1⟩
  have hs := Trace.upTo_state tr.projAC y (i := k)
    (fun q hq => hrun.time_mono hq.le)
  have he := hr.exec k ell hc.2 (hc.1 ▸ hy)
  rw [hc.1, hu.2.1, hs, Trace.upTo_post, Trace.upTo_time] at he
  have hkt : tr.time k = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hslot : sp.slot (tr.time k) = u + 1 := by
    rw [hkt]
    apply SA.slot_of_mem sp (u + 1)
    all_goals simp only [SAParams.ts]; push_cast; linarith [sp.toParams.hΔ]
  have hpost : tr.projAC.post k =
      SA.updateConfirmation sp (tr.projAC.state y k) ell.frame (tr.time k) u := by
    rw [show tr.projAC.post k =
      (SA.acOnTick sp y (tr.projAC.state y k) ell.frame (tr.time k)).1 from
        (congrArg Prod.fst he).symm]
    unfold SA.acOnTick
    dsimp only
    rw [hslot]
    have ht1 : ¬ tr.time k = sp.ts (u + 1 : Nat) + sp.Δ := by
      rw [hkt]; simp only [SAParams.ts]; push_cast; linarith [sp.toParams.hΔ]
    have ht2 : tr.time k = sp.ts (u + 1 : Nat) + 2 * sp.Δ := by
      rw [hkt]; simp only [SAParams.ts]; push_cast; ring
    have hj : SA.joined sp (tr.projAC.state y k) (tr.time k) := hu.2.2.2
    rw [ite_eq_right (not_not.mpr hj), ite_eq_right ht1,
      ite_eq_left ⟨ht2, Nat.succ_pos u⟩]
    simp only [Nat.add_sub_cancel]
  rw [hpost]
  exact SA.fastLock_mem_updateConfirmation_floor hPt hva hconf hnv hfast
    (by rw [hslot]; have := sp.two_le_k; omega)

end Consensus.Goldilocks.Healing.Growing

end
