module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Inv
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Attest
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Source
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Sync
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Signing provenance retained at the signer's honesty horizon -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {proposer : Nat → Fin sp.n}

/-- An honest signing is at a public time, using honesty only at the signing cut. -/
theorem sign_public (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {a : FG.Att sp.n}
    (hc : tr.CallAt y j (.fg (.attest C (some a)))) :
    sp.toParams.IsPublic (tr.time j) := by
  exact Compose.sign_public (hrun.upTo (hrun.time_nonneg j)) hy
    ((Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩)

/-- Signing follows the same node's source call at the preceding cut and the same time.
Both states are retained at the signing cut, even if the node is compromised later. -/
theorem attest_source (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {a : FG.Att sp.n}
    (hc : tr.CallAt y j (.fg (.attest C (some a)))) :
    ∃ j', j = j' + 1 ∧ ∃ ℓ : ACLabel (goldilocksNode sp ro),
      tr.CallAt y j' (.ac ℓ) ∧ ℓ.call = .toFG ∧ tr.time j' = tr.time j ∧
      ((goldilocksNode sp ro).toFG (tr.state y j').ac ℓ.frame (tr.time j')).2 = some C ∧
      (tr.state y j).fg = (tr.state y j').fg := by
  obtain ⟨j', hj, ℓ, hc', hto, ht, hC, hs⟩ :=
    Compose.attest_source (hrun.toLocalRun.upTo (hrun.time_nonneg j)) hy
      ((Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩)
  change tr.time j' = tr.time j at ht
  have hstate := RunTrace.upTo_state_of_le (tr := tr) (y := y)
    hrun.time_mono (le_refl (tr.time j))
  have hstate' := RunTrace.upTo_state_of_le (tr := tr) (y := y) hrun.time_mono ht.le
  rw [hstate'] at hC
  rw [hstate, hstate'] at hs
  exact ⟨j', hj, ℓ, ((Trace.upTo_callAt _).mp hc').2, hto, ht, hC, hs⟩

/-- At a common time, honest tick signings precede an honest delivery's cuts. -/
theorem sign_before_delivery
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {v y : Fin sp.n} {j' k j₀ : Nat} (hv : v ∈ H (tr.time j'))
    (hy : y ∈ H (tr.time k)) {C : SA.Blk sp.n (List (FG.Att sp.n))} {a : FG.Att sp.n}
    (hs : tr.CallAt v j' (.fg (.attest C (some a))))
    {e : Node.Event (goldilocksNode sp ro)}
    (hg : tr.GroupAt proposer dg y j₀ (tr.time k) e) (he : e.phase = 2) (hk : j₀ ≤ k)
    (ht : tr.time j' = tr.time k) : j' < k := by
  have hlocal := hrun.toLocalRun.upTo (hrun.time_nonneg k)
  have hv' : v ∈ H (tr.time k) := ht ▸ hv
  have hs' := (Trace.upTo_callAt _).mpr ⟨ht.le, hs⟩
  obtain ⟨j₁, e₁, i₁, hg₁, rfl, hk₁⟩ := call_in_group hlocal hv' hs'
  have hm : Cut.fg (.attest C (some a)) ∈
      (Node.exec proposer dg v ((tr.upTo (tr.time k)).state v j₁)
        (tr.time (j₁ + i₁)) e₁).2 := List.mem_of_getElem? hk₁
  obtain ⟨xt, he₁⟩ := @signed_only_in_ticks sp.toParams (goldilocksNode sp ro) proposer dg v
    ((tr.upTo (tr.time k)).state v j₁) (tr.time (j₁ + i₁)) e₁ C a hm
  subst he₁
  have hg' := (RunTrace.upTo_groupAt hrun.time_mono).mpr ⟨le_rfl, hg⟩
  change (tr.upTo (tr.time k)).GroupAt proposer dg v j₁ (tr.time (j₁ + i₁)) (.tick xt) at hg₁
  rw [ht] at hg₁
  change (Node.exec proposer dg v ((tr.upTo (tr.time k)).state v j₁)
    (tr.time (j₁ + i₁)) (.tick xt)).2[i₁]? = some (.fg (.attest C (some a))) at hk₁
  rw [ht] at hk₁
  have hlen := (List.getElem?_eq_some_iff.1 hk₁).1
  by_contra hjk
  rcases lt_trichotomy j₀ j₁ with hlt | rfl | hgt
  · have h' := hlocal.phase_order y hy v hv' j₀ j₁ _ e (.tick xt) hg' hg₁ hlt
    rw [he] at h'
    simp [Node.Event.phase] at h'
  · have hn : y = v := ((hg'.2.1 0 (List.length_pos_iff.2 hg'.1)).1).symm.trans
      (hg₁.2.1 0 (List.length_pos_iff.2 hg₁.1)).1
    subst hn
    have h' := group_phase hg' hg₁
    rw [he] at h'
    simp [Node.Event.phase] at h'
  · have := group_start hg₁ hg' (le_of_lt hgt) (by omega)
    omega

variable {ΔF : Time} {x : Fin sp.n} {i₀ s m : Nat}
  {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}

/-- A caller honest at its source call either voted in slot `s + 1` or restarted after `t_s`.
The tick and local voting history are retained only at that call's horizon. -/
theorem vote_or_restart (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp ro)}
    {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hto : SA.ToFGAt tr.projAC y i ℓ C) (ht : sp.ts (s + 1 : Nat) + sp.Δ < tr.time i) :
    (∃ j < i, ∃ ℓ' e, SA.CastAt tr.projAC y j ℓ' e ∧ e.msg.slot = s + 1) ∨
      (∃ k < i, tr.projAC.RestartAt y k ∧ sp.ts s < tr.time k) := by
  by_cases hres : ∃ k < i, tr.projAC.RestartAt y k ∧ sp.ts s < tr.time k
  · exact Or.inr hres
  left
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hp.noColl).localRun
  have hri := hr.upTo (hr.time_nonneg i)
  have hlocal := hrun.toLocalRun.upTo (hrun.time_nonneg i)
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  set u := sp.ts (s + 1 : Nat) + sp.Δ with hu
  have hus : sp.ts s < u := by
    have := (SA.ts_lt_iff sp).mpr (show ((s : Nat) : Int) < ((s + 1 : Nat) : Int) by omega)
    linarith
  have hu0 : 0 ≤ u := by simp only [hu, SA.SAParams.ts]; positivity
  have hrestart : ∀ k, (tr.upTo (tr.time i)).RestartAt y k → tr.projAC.RestartAt y k := by
    intro k hk
    exact Compose.projAC_restartAt.mpr ((RunTrace.upTo_restartAt _).mp hk).2
  have hcall := (RunTrace.upTo_isCall _).mpr
    (show tr.time i ≤ tr.time i ∧ tr.IsCall y i from ⟨le_rfl, _, Compose.projAC_callAt.mp hto.1⟩)
  have hawake : (tr.upTo (tr.time i)).awake y u := by
    by_contra hna
    obtain ⟨k, hk, hku, hki⟩ := hlocal.restart_at_wake y hy u (tr.time i) hu0 ht hna
      (hlocal.awake_of_call y hy i hcall)
    change u < tr.time k at hku
    change tr.time k ≤ tr.time i at hki
    rcases lt_trichotomy k i with hlt | rfl | hgt
    · exact hres ⟨k, hlt, hrestart k hk, by linarith⟩
    · obtain ⟨ℓk, hck, hkr⟩ := (RunTrace.upTo_restartAt _).mp hk |>.2
      cases Option.some.inj ((Compose.projAC_callAt.mp hto.1).2.symm.trans hck.2)
      rw [hto.2.1] at hkr
      cases hkr
    · obtain ⟨u', -, hu'k, -, hbefore⟩ := hlocal.sleep_of_restart y hy k hk
      have := hbefore i hgt hcall
      change tr.time i < u' at this
      change u' < tr.time k at hu'k
      linarith
  have hpub : sp.toParams.IsPublic u :=
    ⟨4 * (s + 1 : Nat) + 1, by simp only [hu, SA.SAParams.ts]; ring⟩
  obtain ⟨j₀, xt, hj₀⟩ := hlocal.tick_of_awake y hy u hu0 hpub hawake
  obtain ⟨ℓt, pc, uc, hlt, hcs, -, -⟩ :=
    @tick_order sp.toParams (goldilocksNode sp ro) proposer dg y
      ((tr.upTo (tr.time i)).state y j₀) u xt
  have hlen : 0 <
      (Node.exec proposer dg y ((tr.upTo (tr.time i)).state y j₀) u (.tick xt)).2.length := by
    change 0 < (Node.onTick proposer dg y ((tr.upTo (tr.time i)).state y j₀) u xt).2.length
    rw [hcs]; simp
  obtain ⟨hn₀, ht₀, -, -, hl₀⟩ := hj₀.2.1 0 hlen
  have hct : (tr.upTo (tr.time i)).CallAt y j₀ (.ac ℓt) := by
    refine ⟨hn₀, ?_⟩
    simp only [Nat.add_zero] at hl₀
    rw [hl₀]
    change some (Node.onTick proposer dg y ((tr.upTo (tr.time i)).state y j₀) u xt).2[0] = _
    simp [hcs]
  simp only [Nat.add_zero] at ht₀
  change tr.time j₀ = u at ht₀
  have hj₀i : j₀ < i := by
    by_contra h
    have := hrun.time_mono (not_lt.mp h)
    linarith
  have hpt := Compose.projAC_callAt.mpr hct
  rw [RunTrace.upTo_projAC] at hpt
  have hslot : sp.slot u = s + 1 := SA.slot_of_mem sp (s + 1) (by linarith)
    (by have := (SA.ts_lt_iff sp).mpr
          (show ((s + 1 : Nat) : Int) < ((s + 1 + 1 : Nat) : Int) by omega)
        have h4 : sp.ts ((s + 1 + 1 : Nat) : Int) = sp.ts ((s + 1 : Nat) : Int) + 4 * sp.Δ := by
          simp only [SA.SAParams.ts]; push_cast; ring
        linarith)
  set A := (tr.projAC.upTo (tr.time i)).state y j₀ with hA
  by_cases hvs : A.votedSlot = ((s + 1 : Nat) : Int)
  · obtain ⟨j, hj, e, ⟨ℓ', hc', he'⟩, hes⟩ := SA.cast_of_votedSlot hri hy j₀ (s + 1) hvs
    exact ⟨j, hj.trans hj₀i, ℓ', e, (SA.upTo_castAt.mp ⟨hc', he'⟩).2, hes⟩
  have hjr : (tr.upTo (tr.time i)).JoinedAt y u := by
    intro k hk hku
    change tr.time k ≤ u at hku
    have hki : k < i := by
      by_contra h
      have := hrun.time_mono (not_lt.mp h)
      linarith
    have hks : tr.time k ≤ sp.ts s := by
      by_contra h
      exact hres ⟨k, hki, hrestart k hk, not_le.mp h⟩
    refine ⟨by change 0 < sp.slot u; omega, ?_⟩
    change tr.time k ≤ sp.toParams.slotTime (sp.slot u - 1)
    rw [hslot, Nat.add_sub_cancel, sp.slotTime_eq]
    exact hks
  have hnr : ¬ (tr.upTo (tr.time i)).RestartAt y j₀ := by
    rintro ⟨ℓk, hck, hkr⟩
    cases Option.some.inj (hct.2.symm.trans hck.2)
    rw [hlt] at hkr
    cases hkr
  have hjoined : SA.joined sp A u := by
    rw [hA, ← RunTrace.upTo_projAC, Compose.projAC_state hlocal hy]
    exact ((Compose.joined_projection sp ro dg (H (tr.time i)) (tr.upTo (tr.time i))
      proposer (hrun.upTo (hrun.time_nonneg i)) y hy u).2.1 j₀ ⟨_, hct⟩ hnr ht₀).mp hjr
  have hexec := hri.exec j₀ ℓt hpt.2 (hpt.1 ▸ hy)
  change (SA.goldilocksSA sp _ ro).step ((tr.projAC.upTo (tr.time i)).node j₀)
    ((tr.projAC.upTo (tr.time i)).state ((tr.projAC.upTo (tr.time i)).node j₀) j₀)
    ℓt.frame (tr.time j₀) ℓt.call = _ at hexec
  rw [hpt.1, hlt] at hexec
  have hne := Compose.acOnTick_votes (ro' := ro) y A ℓt.frame hjoined
    (by rw [hslot]; exact hvs) (by rw [hslot])
  change (SA.goldilocksSA sp _ ro).step y A ℓt.frame (tr.time j₀) .tick = _ at hexec
  rw [ht₀] at hexec
  rw [hexec] at hne
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
  have hsl := (SA.castAt_spec hri hy ⟨hpt, he⟩).2.1
  exact ⟨j₀, hj₀i, ℓt, e, (SA.upTo_castAt.mp ⟨hpt, he⟩).2,
    by rw [hsl]; change sp.slot (tr.time j₀) = _; rw [ht₀, hslot]⟩

/-- Honest attestations in the persistence window name no excluded entry. -/
theorem attest_not_excluded (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV) {v : Fin sp.n} {j : Nat}
    (hv : v ∈ H (tr.time j)) {a : FG.Att sp.n} (hs : tr.SignAt v j a)
    (hT₀ : sp.ts (s + 1 : Nat) + sp.Δ < tr.time j)
    (hTm : tr.time j ≤ sp.ts m + sp.Δ)
    (ih : ∀ i < j, VoteInv tr H s m B i ∧ CutInv tr H s m B i) :
    ∀ E ∈ excludedEntries tr H s B, a.T ≠ E.root := by
  obtain ⟨C, hcall⟩ := hs
  obtain ⟨j', rfl, ℓ, hc', hto, htime, hC, hfgeq⟩ := attest_source hrun hv hcall
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hp.noColl
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hv' : v ∈ H (tr.time j') := htime ▸ hv
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hpc := Compose.projAC_callAt.mpr hc'
  have state {k : Nat} (hk : k ≤ j' + 1) : tr.projAC.state v k = (tr.state v k).ac := by
    have h := Compose.projAC_state
      (hrun.toLocalRun.upTo (hrun.time_nonneg (j' + 1))) hv k
    rw [RunTrace.upTo_projAC] at h
    rw [Trace.upTo_state tr.projAC v (i := k)
      (fun l hl => hrun.time_mono (show l ≤ j' + 1 by omega)),
      Trace.upTo_state tr v (i := k)
        (fun l hl => hrun.time_mono (show l ≤ j' + 1 by omega))] at h
    exact h
  have hToFG : SA.ToFGAt tr.projAC v j' ℓ C := ⟨hpc, hto, by rw [state (by omega)]; exact hC⟩
  have ih' : ∀ i < j', VoteInv tr H s m B i ∧ CutInv tr H s m B i := fun i hi => ih i (by omega)
  have hlo : sp.ts (s + 1 : Nat) + sp.Δ < tr.time j' := htime ▸ hT₀
  have hhi : tr.time j' ≤ sp.ts m + sp.Δ := htime ▸ hTm
  have hs1 := (SA.ts_lt_iff sp).mpr (show ((s : Nat) : Int) < ((s + 1 : Nat) : Int) by omega)
  have hsm := (SA.ts_le_iff sp).mpr (Int.ofNat_le.mpr hp.lt)
  have hframe : ∀ k ≤ j', ∀ ℓk, tr.projAC.CallAt v k ℓk → sp.ts s ≤ tr.time k →
      Compatible (tr.HonestBlocksAt H) ℓk.frame.F B := by
    intro k hk ℓk hck hk₀
    have hvk := hrun.antitone (hrun.time_mono hk) hv'
    rw [(hrun.cutLaw v k _ (Compose.projAC_callAt.mp hck) hvk).1]
    exact (state_caches hrun hp k (fun i hi => (ih' i (by omega)).2) v hvk hk₀
      fun i hi => by have := hrun.time_mono (show i ≤ j' by omega); linarith).1
  have hcase : (∃ i < j', ∃ ℓ' e, SA.CastAt tr.projAC v i ℓ' e ∧ e.msg.slot = s + 1 ∧
      Compatible (tr.HonestBlocksAt H) ℓ'.frame.F B) ∨
      (∃ k < j', tr.projAC.RestartAt v k ∧ sp.ts s < tr.time k) := by
    refine (vote_or_restart hrun hp hv' hToFG hlo).imp_left ?_
    rintro ⟨i, hi, ℓ', e, hce, hsl⟩
    have hts : sp.ts e.msg.slot ≤ tr.time i :=
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).mpr
        (by rw [(SA.castAt_spec (hr.upTo (hr.time_nonneg i))
          (hrun.antitone (hrun.time_mono hi.le) hv') (SA.upTo_castAt.mpr ⟨le_rfl, hce⟩)).2.1]; rfl)
    rw [hsl] at hts
    exact ⟨i, hi, ℓ', e, hce, hsl, hframe i hi.le ℓ' hce.1 (by linarith)⟩
  have hsync := sync_projection sp.toParams (goldilocksNode sp ro) dg H
    (fun v => v.val) tr proposer ΔF (sp.ts s) (sp.ts m + sp.Δ) hrun.toLocalRun hp.sync
  obtain ⟨ℓw, D, hcw, hflD, hBD⟩ := hp.fastLock
  have hΦwU : ℓw.frame.tree ⊆ tr.HonestBlocksAt H := by
    rcases hr.frameLaw x i₀ ℓw hp.writer_honest hcw with
      ⟨_, Φ₀, _, _, h⟩ | ⟨j, ℓ', _, _, _, h⟩ <;> exact h.1.2
  have hf : 2 * (H (tr.time j'))ᶜ.ncard < sp.n := by
    have hsub : (H (tr.time j'))ᶜ ⊆ (H (sp.ts m + sp.Δ))ᶜ :=
      Set.compl_subset_compl.mpr (hrun.antitone hhi)
    have := Set.ncard_le_ncard hsub
    linarith [hp.twoFaults]
  have hCB := SA.Growing.source_compatible_stored sp _ ro proposer H _ tr.projAC hrun'
    s m x v i₀ j' B D CV ℓ C hp.writer_honest hflD
    (hBD ▸ Anc.mono hΦwU (SA.anc_viableAncestor ℓw.frame D))
    ⟨fun x i e hx he ha hb => hsync.1 x i e hx he ha (by linarith),
      fun x i X hx hX ha hb => hsync.2 x i X hx hX ha (by linarith)⟩
    hp.carry hf hv' hToFG hlo hhi
    (fun z i hi hz e ⟨ℓz, hcz, hez⟩ h₁ h₂ =>
      (voteInv_iff.mp (ih' i hi).1 z hz ℓz e ⟨hcz, hez⟩ h₁ h₂).2) hcase
  set st := (tr.state v (j' + 1)).fg with hst
  have hsub : st.tree ⊆ tr.HonestBlocksAt H := fun X hX =>
    ⟨v, j' + 1, tr.time (j' + 1), hrun.time_nonneg _,
      (fun k hk => hrun.time_mono hk.le), hv, hX⟩
  have hret := hrun.toLocalRun.upTo (hrun.time_nonneg (j' + 1))
  have hstate := RunTrace.upTo_state_of_le (tr := tr) (y := v) hrun.time_mono
    (le_refl (tr.time (j' + 1)))
  have hreach := Compose.fg_reachable hret hv (j' + 1)
  rw [hstate] at hreach
  have hCt : C ∈ st.tree := by
    have hri := hr.upTo (hr.time_nonneg j')
    have hpc' := (Trace.upTo_callAt _).mpr ⟨le_rfl, hpc⟩
    obtain ⟨Φp, tp, hreachA, htp, hok⟩ := pre_reachable hri hv' hpc'
    have hΦ : ℓ.frame = Φp := by
      have h := hok.2
      rw [hto] at h
      exact h
    have hsrc := ((SA.interface_requirements sp _ ro).2.1 v _ hU _ _ _ hreachA)
      (tr.time j') htp C (by
        rw [Trace.upTo_state tr.projAC v (fun k hk => hr.time_mono hk.le),
          state (by omega), ← hΦ]
        exact hC)
    have hCf : C ∈ ℓ.frame.tree := hΦ ▸ hsrc.1
    rw [(hrun.cutLaw v j' _ hc' hv').1] at hCf
    change C ∈ st.tree
    rw [hfgeq]
    exact hCf.1
  have hcut := (hrun.cutLaw v (j' + 1) _ hcall hv).1
  have hT : a.T = (st.σ (st.σ C.root).Th).Th := Compose.createAtt_T hcut
  obtain ⟨⟨E, hE, hEr, hEC, _, hETh⟩, _, _⟩ :=
    Store.entry_state_of_source sp.toParams (Payload sp.n) _ st hreach C hCt
  have hTE : a.T = E.root := by rw [hT, ← hEr, hETh, hEr]
  intro E' hE' hEq
  obtain ⟨hnc, y, jy, hy, _, hanc, hne⟩ := hE'
  have hE'U := (Anc.mem hanc hne.symm).2
  have hEE : E' = E := hU.1 hE'U (hsub hE) (hEq.symm.trans hTE)
  subst hEE
  apply hnc
  have hEC' := Anc.mono hsub hEC
  rcases hCB with h | h
  · exact Or.inl (hEC'.trans h)
  · exact SA.anc_total hU hEC' h

end Consensus.Goldilocks.Compose.Growing

end
