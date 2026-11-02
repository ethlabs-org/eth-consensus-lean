module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AnchorPrefix
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FreshLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Source
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.PreAdvanceFacts

public section

/-! # Finite drain reports

The warm FS′ window supplies unanimity and vote joinedness; the shorter
closed P5b window supplies the actual adjacent read. Reports may precede
that read, so following is proved for the actual returned report.
This is not a reset-time or joint coefficient-envelope theorem.
-/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Every honest reader reports above the actual warm proposal, with the
report itself followed by all proposal heads from slot `u+3` onward.
Both frame and service include the last update/ToFG endpoint. -/
theorem FrameWindow.proposal_report_follow
    {g ΔF b : Time} {s₀ s N floor : Nat} {contest kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts N + 2 * sp.Δ)
      floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ s + 1)
    (hN : s + 2 ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H) (hdesignated : z = proposer (s + 1))
    {kP : Nat} (hactual : tr.ProposesAt z kP P) (hPs : P.slot = s + 1)
    {y : Fin sp.n} (hy : y ∈ H) :
    ∃ i ell R, SA.ToFGAt tr.projAC y i ell R ∧
      tr.time i ≤ sp.ts (s + 2 : Nat) + 2 * sp.Δ ∧
      Anc (tr.HonestBlocks H) P R ∧
      ∀ r, s + 4 ≤ r → r ≤ N →
        ∀ w ∈ H, ∀ c ellp, tr.projAC.CallAt w c ellp → ellp.call = .proposal →
          tr.time c = sp.ts r → ∀ d pay,
          (SA.acProposal sp (tr.projAC.state w c) ellp.frame (tr.time c)).2 =
            some (d, pay) → Anc (tr.HonestBlocks H) R d.head := by
  have hΔ := sp.toParams.hΔ
  have hk := sp.two_le_k
  have hts {p q : Nat} (hpq : p ≤ q) : sp.ts p ≤ sp.ts q :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast hpq)
  have hsub {lo hi : Time} (hlo : sp.ts s₀ ≤ lo) (hhi : hi ≤ sp.ts N + 2 * sp.Δ) :
      FrameWindow (tr := tr) (H := H) lo hi floor contest kindJ J :=
    ⟨fun w hw i hl hh => hframe.floor_eq w hw i (hlo.trans hl) (hh.trans hhi),
     fun w hw i hl hh => hframe.contest_iff w hw i (hlo.trans hl) (hh.trans hhi),
     fun w hw i hl hh => hframe.kind_iff w hw i (hlo.trans hl) (hh.trans hhi),
     fun w hw i hl hh => hframe.root_eq w hw i (hlo.trans hl) (hh.trans hhi)⟩
  have hT : sp.ts (s + 2 : Nat) + 2 * sp.Δ ≤ sp.ts N + 2 * sp.Δ := by
    have := hts hN
    linarith
  have hun := (hsub le_rfl (show sp.ts (s + 1 : Nat) + sp.Δ ≤ _ by
      have := hts (by omega : s + 1 ≤ N); linarith)).honest_vote_heads_eq
    hrun hnc hsvc hawake hf hcatch hnr hm (by omega) hwarm
    (by have := hts (by omega : s + 1 ≤ N); linarith) hz hdesignated hactual hPs
  have hshort := hsub (hts (by omega : s₀ ≤ s + 1)) hT
  have hjoin : ∀ w ∈ H, SA.JoinedAt tr.projAC w (sp.ts (s + 1 : Nat) + sp.Δ) :=
    fun w hw => joined_voteTime_of_warm_frame hnr hm (by omega) hw
  have hmargin : gbar g + 2 * sp.Δ ≤ sp.ts (s + 1 : Nat) := by
    have := hts (by omega : s₀ ≤ s + 1)
    linarith
  obtain ⟨k, ell, ell', hu, hc, hto, ht, he, _, _, _, hva, _, hl⟩ :=
    fresh_fast_lock_update_toFG hrun hnc hsvc hawake hf hcatch hnr hmargin hjoin
      (hT.trans hmb) hshort hz hdesignated hactual hPs hun hy
  have hv := (hshort.proposal_viable_after_votes hrun hnc hsvc hawake hf hcatch hnr
    (by linarith) (by omega) hjoin (hT.trans hmb) hz hdesignated hactual hPs hy hc
    (by rw [ht]; simp only [SAParams.ts]; push_cast; linarith)
    (by simpa only [show s + 1 + 1 = s + 2 by omega] using ht.le)).1
  have hPc := fresh_lock_toFG_candidate hv hva hl
    (by simpa only [show s + 1 + 1 = s + 2 by omega] using ht)
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hj : SA.joined sp (tr.projAC.state y (k + 1)) (tr.time (k + 1)) := by
    unfold SA.joined
    rcases SA.restartTime_state hr hy (k + 1) with h | ⟨q, _, hq, h⟩
    · rw [h]; exact bot_le
    · rw [h]
      apply WithBot.coe_le_coe.mpr
      have hslot : sp.slot (tr.time (k + 1)) = s + 2 := by
        rw [ht]
        apply SA.slot_of_mem sp (s + 2)
        all_goals simp only [SAParams.ts]; push_cast; linarith
      rw [hslot]
      have hqg := hnr y hy q (Compose.projAC_restartAt.mp hq)
      change tr.time q ≤ _
      have hcast : ((s + 2 : Nat) : Int) - 1 = s + 1 := by omega
      rw [hcast]
      have hmargin' := hmargin
      push_cast at hmargin'
      linarith
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, a, _, hacc, _⟩ :=
    honestProposalRun_of_proposesAt hrun hnc hz hdesignated hactual hPs
  rw [← hdesignated] at hacc
  have hPg := SA.accept_ne_genesis sp hr hz hacc
  obtain ⟨i, ellr, R, hR, htime, hPR⟩ := report_of_compatible_candidate_of_run
    hrun hnc hy hc hto hj hPg hPc (toFG_candidates_compatible_at_call hrun hnc hy hc hPc)
  refine ⟨i, ellr, R, hR, htime.trans ht.le, hPR, ?_⟩
  intro r hrlo hrN w hw c ellp hcp hcall htc d pay hd
  have hbound : tr.time i ≤ sp.ts N + sp.Δ := by
    have ht' := hts (by omega : s + 3 ≤ N)
    have hstep : sp.ts (s + 3 : Nat) = sp.ts (s + 2 : Nat) + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    linarith
  exact (hsub le_rfl (by linarith)).toFG_later_proposal_head hrun hnc hsvc hawake hf
    hcatch hnr hm hwarm (by linarith) hy hR hPs hPR hbound (htime.trans ht.le)
    (by omega) hrN hw hcp hcall htc hd

/-- Even a suppressing earlier report extending a slot-u proposal cannot
predate that slot: its actual fast-write origin bounds the stored block slot. -/
theorem toFG_time_ge_of_ancestor_slot
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) {y : Fin sp.n} (hy : y ∈ H) {i u : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {P R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : SA.ToFGAt tr.projAC y i ell R) (hPs : P.slot = u)
    (hPR : Anc (tr.HonestBlocks H) P R) : sp.ts u ≤ tr.time i := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  obtain ⟨a, _, j, D, CV, ho, hRD, hj⟩ := toFG_fast_origin hrun hnc hy hR
  have hPD := (Anc.slot_le hac.localRun.coherent (hPR.trans hRD)).1
  have hDj := fast_selection_slot_le hrun hnc hf hy ho
  have hu : u ≤ sp.slot (tr.time i) := by omega
  exact (SA.ts_le_iff_le_slot sp (hac.localRun.time_nonneg i) _).2 (by exact_mod_cast hu)

/-- Step F uses the actual report's adjacent FG attest, not a hypothetical
signature: suppression at the client still supplies the same reset witness. -/
theorem reset_of_high_report {g : Time}
    (hrun : GoldilocksRun proposer dg H tr) (hq : Hᶜ.ncard < sp.toParams.fg.q)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : SA.ToFGAt tr.projAC y i ell R)
    (hh : HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h) :
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time i := by
  obtain ⟨hc, hto, hres⟩ := hR
  rw [Compose.projAC_state hrun.toLocalRun hy] at hres
  obtain ⟨sg, hatt, ht, hfg⟩ := toFG_attest hrun.toLocalRun hy
    (Compose.projAC_callAt.mp hc) hto hres
  have hh' : HZ tr H g + 1 ≤ ((tr.state y (i + 1)).fg.σ R.root).h := by
    rwa [hfg]
  obtain ⟨a, ha, hat⟩ := reset_of_high_source hrun hq hy hatt hh'
  exact ⟨a, ha, hat.trans ht.le⟩

/-- The finite F-step: a high actual warm proposal forces a reset by its
closed update deadline. The height is measured at any honest cut holding P,
then transported to the actual reporter's store by collision freedom. -/
theorem FrameWindow.reset_of_high_proposal
    {g ΔF b : Time} {s₀ s N floor : Nat} {contest kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts N + 2 * sp.Δ)
      floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ s + 1)
    (hN : s + 2 ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H) (hdesignated : z = proposer (s + 1))
    {kP : Nat} (hactual : tr.ProposesAt z kP P) (hPs : P.slot = s + 1)
    {w : Fin sp.n} (hw : w ∈ H) {c : Nat}
    (hP : P ∈ (tr.state w c).fg.tree)
    (hh : HZ tr H g + 1 ≤ ((tr.state w c).fg.σ P.root).h) :
    ∃ a, IsReset tr H g a ∧ a ≤ sp.ts (s + 2 : Nat) + 2 * sp.Δ := by
  obtain ⟨i, ell, R, hR, ht, hPR, _⟩ := hframe.proposal_report_follow
    hrun hnc hsvc hawake hf hcatch hnr hm hwarm hN hmb hz hdesignated hactual hPs hz
  have hRt := toFG_mem_tree hrun hz hR
  have hanc := store_anc_of_honest_anc hrun hnc hz hPR hRt
  have hPt := mem_of_honest_anc hrun hnc hz hPR hRt
  have hh' : HZ tr H g + 1 ≤ ((tr.state z i).fg.σ R.root).h := by
    have he := σ_eq_honest hrun hnc hw hz hP hPt
    rw [he] at hh
    exact hh.trans (σ_h_le_of_anc (Compose.fg_reachable hrun.toLocalRun hz i) hanc)
  have hq : Hᶜ.ncard < sp.toParams.fg.q := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < (2 * sp.n + 2) / 3
    omega
  obtain ⟨a, ha, hat⟩ := reset_of_high_report hrun hq hz hR hh'
  exact ⟨a, ha, hat.trans ht⟩

/-- A floor-height source above the fork-choice root satisfies O1-L's
kind alternative, including Contest and the equal-height kind-J case. -/
theorem report_kind_of_floor
    (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hh : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ R.root).h)
    (hroot : (tr.state y i).fg.Anc (tr.state y i).fg.fcRoot R) :
    (tr.state y i).fg.hj < ((tr.state y i).fg.σ R.root).h ∨
      ((tr.state y i).fg.hj = ((tr.state y i).fg.σ R.root).h ∧
        (tr.state y i).fg.Anc (tr.state y i).fg.J R) := by
  have hj := hj_lt_hmax hrun hy i
  by_cases hc : (tr.state y i).fg.Contest
  · have he := hc.1
    rw [Store.headHeightFloor, ite_eq_left hc] at hh
    exact Or.inl (by omega)
  · rw [Store.headHeightFloor, ite_eq_right hc] at hh
    by_cases he : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1
    · have hr : (tr.state y i).fg.fcRoot = (tr.state y i).fg.J :=
        ite_eq_left ⟨he, hc⟩
      rw [hr] at hroot
      by_cases hlt : (tr.state y i).fg.hj < ((tr.state y i).fg.σ R.root).h
      · exact Or.inl hlt
      · exact Or.inr ⟨by omega, hroot⟩
    · exact Or.inl (by omega)

/-- An actual report's adjacent attest produces an actual matching signature
using the finite O1-L lock alternative at the report's own store cut. -/
theorem row_of_report_of_kind
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {R E : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : SA.ToFGAt tr.projAC y i ell R) {h : Nat}
    (hE : EntryOf (tr.state y i).fg R E h)
    (hh : ((tr.state y i).fg.σ R.root).h = h)
    (hkind : (tr.state y i).fg.hj < h ∨
      ((tr.state y i).fg.hj = h ∧ (tr.state y i).fg.Anc (tr.state y i).fg.J R)) :
    ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ tr.time i ∧
      att.h = h ∧ att.T = E.root := by
  obtain ⟨hc, hto, hres⟩ := hR
  rw [Compose.projAC_state hrun.toLocalRun hy] at hres
  obtain ⟨sg, hatt, ht, hfg⟩ := toFG_attest hrun.toLocalRun hy
    (Compose.projAC_callAt.mp hc) hto hres
  have hE' : EntryOf (tr.state y (i + 1)).fg R E h := by rwa [hfg]
  have hh' : ((tr.state y (i + 1)).fg.σ R.root).h = h := by rwa [hfg]
  have hk' : (tr.state y (i + 1)).fg.hj < h ∨
      ((tr.state y (i + 1)).fg.hj = h ∧
        (tr.state y (i + 1)).fg.Anc (tr.state y (i + 1)).fg.J R) := by rwa [hfg]
  rcases client_signs_of_frame hrun hnc hf hy hatt hE' hh' hk' with
    ⟨att, rfl, hah, haT⟩ | ⟨k, hki, att, hs, hah, haT⟩
  · exact ⟨i + 1, att, ⟨R, hatt⟩, ht.le, hah, haT⟩
  · exact ⟨k, att, hs, (hrun.time_mono hki.le).trans ht.le, hah, haT⟩

/-- The inherited floor bound and the actual report's candidate ancestry
discharge O1-L. R need only have a viable descendant, not be viable itself. -/
theorem row_of_report_of_floor
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {R E : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : SA.ToFGAt tr.projAC y i ell R) {h : Nat}
    (hE : EntryOf (tr.state y i).fg R E h)
    (hh : ((tr.state y i).fg.σ R.root).h = h)
    (hfloor : (tr.state y i).fg.headHeightFloor ≤ h) :
    ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ tr.time i ∧
      att.h = h ∧ att.T = E.root := by
  have hroot : ell.frame.Anc ell.frame.fcRoot R := by
    have h := hR.2.2
    change (SA.acToFG sp (tr.projAC.state y i) ell.frame (tr.time i)).2.1 = some R at h
    unfold SA.acToFG at h
    dsimp only at h
    split_ifs at h
    split at h
    · cases h
    · rename_i C hC
      split_ifs at h
      cases h
      exact (SA.deepest_mem hC).1.1.2.1
  rw [Compose.frame_of_projAC hrun hy hR.1] at hroot
  have hroot' : (tr.state y i).fg.Anc (tr.state y i).fg.fcRoot R :=
    hroot.mono (fun B hB => hB.1)
  exact row_of_report_of_kind hrun hnc hf hy hR hE hh
    (hh ▸ report_kind_of_floor hrun hy (hh ▸ hfloor) hroot')

end Consensus.Goldilocks.Healing

end
