module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run

public section

/-! # Finite healing service carries historical votes

The receiver is read on its own honest prefix. A sender need only be honest
at its send or acceptance, not when the receiver later casts.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload Vote gbar)
open Compose.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

private theorem acBlock_prev_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {B : (goldilocksNode sp ro).Blk}
    (hc : tr.CallAt y i (.ac ell)) (hb : ell.call = .block B) :
    ∃ j, i = j + 1 ∧ tr.CallAt y j (.fg (.block B true)) ∧ tr.time j = tr.time i := by
  obtain ⟨j, rfl, hc', ht⟩ := Compose.acBlock_prev
    (hrun.upTo (hrun.time_nonneg i)).toLocalRun hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc) hb
  exact ⟨j, rfl, ((Trace.upTo_callAt _).mp hc').2, ht⟩

private theorem accept_next_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {B : (goldilocksNode sp ro).Blk} (hc : tr.CallAt y i (.fg (.block B true))) :
    ∃ ell : ACLabel (goldilocksNode sp ro), tr.CallAt y (i + 1) (.ac ell) ∧
      ell.call = .block B ∧ tr.time (i + 1) = tr.time i := by
  obtain ⟨ell, hc', hb, ht⟩ := Compose.accept_next
    (hrun.upTo (hrun.time_nonneg i)).toLocalRun hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc)
  exact ⟨ell, ((Trace.upTo_callAt _).mp hc').2, hb, ht⟩

/-- The post-GST portion of finite service, projected to AC. -/
theorem service_syncACAt
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {g ΔF b lo hi : Time} (hsvc : ResetService tr H g ΔF b) (hg : g ≤ lo) :
    SyncACAt (goldilocksNode sp ro) H (tr.HonestBlocksAt H) lo hi tr.projAC := by
  refine ⟨?_, ?_⟩
  · intro x i m hx hsa hai _ y j ell hy hcj hdl
    have hsa' : tr.SendOrAdmitAt x i m := by
      obtain ⟨ell₀, hc₀, hm⟩ := hsa
      refine ⟨ell₀, Compose.projAC_callAt.1 hc₀, ?_⟩
      rwa [projAC_state_at hrun hx] at hm
    have he : max (tr.time i) g = tr.time i := max_eq_left (hg.trans hai)
    rw [Compose.projAC_deadline] at hdl
    obtain ⟨k, hk, h1, h2, h3⟩ := hsvc.message x i m hx hsa' y j hy
      ⟨_, Compose.projAC_callAt.1 hcj⟩ (by rw [he]; exact hdl)
    refine ⟨k, hk, h1, ?_, ?_⟩
    · rcases h2 with ⟨ell', hc', hm'⟩ | ⟨ell', hc', e, he', hem⟩
      · exact ⟨ell', Compose.projAC_callAt.2 hc', Or.inl hm'⟩
      · exact ⟨ell', Compose.projAC_callAt.2 hc', Or.inr ⟨e, he', hem⟩⟩
    · rw [Compose.projAC_deadline]
      change tr.time k < tr.deadline y k (tr.time i) sp.Δ
      simpa only [he] using h3
  · intro x i B hx hacc hai _ y j ell hy hcj hdl hanc
    obtain ⟨ell₀, hc₀, hb⟩ := hacc
    have hc := Compose.projAC_callAt.mp hcj
    obtain ⟨i', rfl, hi', hti⟩ := acBlock_prev_at hrun hx (Compose.projAC_callAt.mp hc₀) hb
    have hfr : ell.frame.F = (tr.state y j).fg.F := by
      rw [(hrun.cutLaw y j _ hc hy).1]
      rfl
    have hgi : g ≤ tr.time i' := hti ▸ hg.trans hai
    have he : max (tr.time i') g = tr.time i' := max_eq_left hgi
    obtain ⟨k, hkj, hk, hlt⟩ := hsvc.relay x i' B (hti ▸ hx) hi' hgi y j hy ⟨_, hc⟩
      (by rw [he, hti, ← Compose.projAC_deadline]; exact hdl) (hfr ▸ hanc)
    obtain ⟨ell', hc', hb', htk⟩ := accept_next_at hrun
      (hrun.antitone (hrun.time_mono hkj) hy) hk
    have hkj' : k + 1 ≤ j := by
      rcases Nat.lt_or_eq_of_le hkj with hlt' | rfl
      · omega
      · cases Option.some.inj (hk.2.symm.trans hc.2)
    have hnr : ¬ tr.RestartAt y (k + 1) := fun ⟨ellr, hcr, hrestart⟩ => by
      cases Option.some.inj (hc'.2.symm.trans hcr.2)
      rw [hb'] at hrestart
      cases hrestart
    refine ⟨k + 1, hkj', ⟨ell', Compose.projAC_callAt.mpr hc', hb'⟩, ?_⟩
    rw [Compose.projAC_deadline]
    change tr.time (k + 1) < tr.deadline y (k + 1) (tr.time (i' + 1)) sp.Δ
    rw [htk, ← hti]
    rw [he] at hlt
    simp only [RunTrace.deadline, RunTrace.lastWake, hnr, ite_false] at hlt ⊢
    exact hlt

private theorem service_catch_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {g : Time} (hcatch : CatchRun tr H g (2 * sp.Δ)) {w : Fin sp.n} {kw : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hw : w ∈ H (tr.time kw))
    (ha : tr.projAC.AcceptAt w kw B) (hkw : tr.time kw < gbar g) {y : Fin sp.n} {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} (hy : y ∈ H (tr.time i))
    (hcy : tr.projAC.CallAt y i ell) (hi : gbar g + 2 * sp.Δ ≤ tr.time i)
    (hanc : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ k ≤ i, tr.projAC.AcceptAt y k B ∧ tr.time k < gbar g + 2 * sp.Δ := by
  classical
  obtain ⟨ell₀, hc₀, hb⟩ := ha
  obtain ⟨kw', rfl, hkw', hti⟩ := acBlock_prev_at hrun hw (Compose.projAC_callAt.mp hc₀) hb
  have hex : ∃ k, gbar g + 2 * sp.Δ ≤ tr.time k := ⟨i, hi⟩
  have hj₀ : tr.FirstCutFrom (Nat.find hex) (gbar g + 2 * sp.Δ) :=
    ⟨Nat.find_spec hex, fun k hk => not_le.1 (Nat.find_min hex hk)⟩
  have hj₀i : Nat.find hex ≤ i := Nat.find_min' hex hi
  have hc := Compose.projAC_callAt.mp hcy
  have hfr : ell.frame.F = (tr.state y i).fg.F := by
    rw [(hrun.cutLaw y i _ hc hy).1]
    rfl
  have hmono := Healing.run_F_mono (hrun.upTo (hrun.time_nonneg i)).toLocalRun hy hj₀i
  rw [RunTrace.upTo_state_of_le hrun.time_mono (hrun.time_mono hj₀i),
    RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at hmono
  have hmono' := hmono.mono (RunTrace.honestBlocks_upTo_subset hrun.time_mono (hrun.time_nonneg i))
  obtain ⟨k, hk, hak⟩ := hcatch w kw' B (hti ▸ hw) hkw' (by rw [hti]; exact hkw) y
    _ (hrun.antitone hi hy) hj₀ (hmono'.trans (hfr ▸ hanc))
  obtain ⟨ell', hc', hb', htk⟩ := accept_next_at hrun
    (hrun.antitone (hrun.time_mono (show k ≤ i by omega)) hy) hak
  exact ⟨k + 1, by omega, ⟨ell', Compose.projAC_callAt.mpr hc', hb'⟩, by
    rw [htk]; exact hj₀.2 k hk⟩

/-- Historical sends after `ḡ` and historical accepted heads reach the next-slot cast. -/
theorem carry_of_service_senders
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) {s : Nat} (hts : gbar g ≤ sp.ts s)
    {y : Fin sp.n} {i : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hcast : SA.CastAt tr.projAC y i ell e) (hs : e.msg.slot = s + 1) {CV : Set (Vote sp.n)}
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ w k, w ∈ H (tr.time k) ∧ tr.projAC.SendOrAdmit w k v ∧ sp.ts s ≤ tr.time k ∧
        tr.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv : SA.Blk sp.n (List (FG.Att sp.n)), Hv.root = v.head ∧
        Anc (tr.HonestBlocksAt H) ell.frame.F Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ w k, w ∈ H (tr.time k) ∧ tr.projAC.AcceptAt w k Hv ∧
          tr.time k < sp.ts s + 2 * sp.Δ)) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV := by
  have hm := hrun.time_mono
  have hΔ := sp.toParams.hΔ
  have hd := hrun.time_nonneg i
  have hr := (acRun_upTo hrun hnc hd).localRun
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hm hd
  have hc' := sa_castAt_upTo.mpr ⟨le_rfl, hcast⟩
  have hsync := service_syncACAt hrun hsvc (lo := g) (hi := sp.ts s + 2 * sp.Δ) le_rfl
  have hgg := le_gbar g
  have hti : sp.ts s + 4 * sp.Δ ≤ tr.time i := by
    have hsl := (castAt_spec_at hrun hnc hy hcast).2.1
    have h := (SA.ts_le_iff_le_slot sp hd ((s + 1 : Nat) : Int)).2 (by rw [← hsl, hs])
    simp only [SAParams.ts] at h ⊢
    push_cast at h
    linarith only [h]
  have hcarry := carryAt_of_delivered hr hy hc' hs (CV := CV) fun v hv => by
    obtain ⟨hvs, ⟨w, k, hwk, hsend, hk1, hk2⟩, Hv, hHvr, hFHv, hacc⟩ := hW v hv
    refine ⟨hvs, ⟨tr.time k, hk1, hk2, fun hdl => ?_⟩, Hv, hHvr, ?_⟩
    · rw [ac_deadline_upTo (trA := tr.projAC) (d := tr.time i) (k := i) hm le_rfl] at hdl
      exact sa_messageServedBefore_upTo hm le_rfl
        ((SA.messageServedBefore_iff _ _ _ _).mpr (Or.inl
          (hsync.1 w k v hwk hsend (hgg.trans (hts.trans hk1)) hk2.le y i ell hy hcast.1 hdl)))
    rcases hacc with hg | ⟨w', kw, hwkw, hkw, hkwt⟩
    · exact Or.inr (Or.inl hg)
    by_cases hgk : g ≤ tr.time kw
    · refine Or.inl ⟨tr.time kw, hkwt, fun hdl => ?_⟩
      rw [ac_deadline_upTo (trA := tr.projAC) (d := tr.time i) (k := i) hm le_rfl] at hdl
      obtain ⟨ky, hky, hacc', hkyt⟩ := hsync.2 w' kw Hv hwkw hkw hgk hkwt.le y i ell
        hy hcast.1 hdl hFHv
      have hkyd : tr.time ky ≤ tr.time i := hm hky
      exact ⟨ky, hky, (ac_acceptAt_upTo _).mpr ⟨hkyd, hacc'⟩,
        by rw [ac_deadline_upTo (trA := tr.projAC) (d := tr.time i) (k := ky) hm hkyd]; exact hkyt⟩
    · obtain ⟨ky, hky, hacc', hkyt⟩ := service_catch_at hrun hcatch hwkw hkw
        (lt_of_lt_of_le (not_le.mp hgk) hgg) hy hcast.1 (by linarith) hFHv
      exact Or.inr (Or.inr ⟨ky, (ac_acceptAt_upTo _).mpr ⟨hm hky, hacc'⟩,
        show tr.time ky < sp.ts s + 3 * sp.Δ by linarith⟩)
  refine ⟨hcarry.awake.1, hcarry.joined, fun v hv => ?_, hcarry.holds⟩
  obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads v hv
  refine ⟨Hv, hsub hHv, hHvr, fun X hX => ?_⟩
  exact (hacc X (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hHv hX)).imp_right
    fun ⟨k, hk, hkt⟩ => ⟨k, ((ac_acceptAt_upTo _).mp hk).2, hkt⟩

/-- A regular result's counted votes reach the next-slot cast even after its writer's compromise. -/
theorem result_carry_service_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) {s : Nat} (hts : gbar g ≤ sp.ts s)
    {x y : Fin sp.n} {c i : Nat} (hx : x ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x c s C CV)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hFC : Anc (tr.HonestBlocksAt H) ell.frame.F C) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV := by
  apply carry_of_service_senders hrun hnc hsvc hcatch hts hy hc hes
  intro v hv
  obtain ⟨hvs, ⟨k, hk, hsend, hlo, hhi⟩, Hv, -, hroot, hanc, hacc⟩ :=
    result_writer_at hrun hnc hx hres v hv
  refine ⟨hvs, ⟨x, k, hk, hsend, hlo, hhi⟩, Hv, hroot, hFC.trans hanc, ?_⟩
  exact hacc.imp_right fun ⟨k', hk', hacc', htime⟩ => ⟨x, k', hk', hacc', htime⟩

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
