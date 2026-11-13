module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Inv
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Source
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Persist, part 2: the honest attestations after the cut name no excluded entry

C1.1's attestation step (claims C1.1, "Proof shape"): an honest attestation signed at a time in
`(t_{s+1} + Δ, t_m + Δ]` has a source compatible with `B` (A1.9 at the node's `ac_to_fg` call
right before it, `source_compatible_stored`), so its target names an ancestor of the source
(G0.2 (c), `entry_state_of_source`), which is compatible with `B`: not an excluded entry. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder goldilocksSA Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Set (Fin sp.n)} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {proposer : Nat → Fin sp.n}

/-! ### The attestation's target -/

/-- The target of an attestation that `create_attestation` signs is the entry of its entry
state. -/
theorem createAtt_T {Λ : FG.Record} {v : Fin sp.n} {σe : FG.ChainState sp.n} {a : FG.Att sp.n}
    {Λ' : FG.Record} (h : Λ.createAtt v σe = some (a, Λ')) : a.T = σe.Th := by
  unfold FG.Record.createAtt at h
  cases hp : Λ.heightPair σe.h σe.Th with
  | none => rw [hp] at h; cases h
  | some p =>
    obtain ⟨h', T, τ⟩ := p
    rw [hp] at h
    dsimp only at h
    split_ifs at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    unfold FG.Record.heightPair at hp
    split_ifs at hp <;> simp only [Option.some.injEq, Prod.mk.injEq] at hp <;>
      exact hp.2.1.symm

/-- An honest signing is at a public time (it is a cut of a tick, C0.5 (c)). -/
theorem sign_public (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {a : FG.Att sp.n}
    (hc : tr.CallAt y j (.fg (.attest C (some a)))) : sp.toParams.IsPublic (tr.time j) := by
  obtain ⟨j₀, e, k, hg, -, hk⟩ := call_in_group hrun.toLocalRun hy hc
  have hm : Cut.fg (.attest C (some a)) ∈
      (Node.exec proposer dg y (tr.state y j₀) (tr.time j) e).2 :=
    List.mem_of_getElem? hk
  obtain ⟨xt, he⟩ := @signed_only_in_ticks sp.toParams (goldilocksNode sp ro) proposer dg y
    (tr.state y j₀) (tr.time j) e C a hm
  subst he
  exact hrun.tick_public y hy j₀ (tr.time j) ⟨xt, hg⟩

variable {ΔF : Time} {x : Fin sp.n} {i₀ s m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
  {CV : Set (Vote sp.n)}

/-- `f < n/2` under C1.1's premises: an honest vote of slot `s + 1` exists (half of the
committee votes honestly) and `f < h_t` holds at its time. -/
theorem faulty_lt_half (hrun : GoldilocksRun proposer dg H tr)
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV) : 2 * Hᶜ.ncard < sp.n := by
  have hn : 0 < sp.n := Fin.pos x
  have hhalf := hp.halfCommittee (s + 1) (by omega) hp.lt
  obtain ⟨z, hz, jz, ez, hv, hsl⟩ : ∃ z ∈ H, ∃ jz ez, SA.VoteAt tr.projAC z jz ez ∧
      ez.msg.slot = s + 1 := by
    by_contra hno
    have : {x' | x' ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x' j e' ∧ e'.msg.slot = s + 1} = ∅ :=
      Set.eq_empty_of_forall_notMem fun z ⟨hz, j, e', h, h'⟩ => hno ⟨z, hz, j, e', h, h'⟩
    rw [this, Set.ncard_empty] at hhalf
    omega
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hp.noColl).localRun
  obtain ⟨ℓz, hcz, hez⟩ := hv
  have hle := (cast_head_fcRoot hr hz ⟨hcz, hez⟩).2
  have hts : sp.ts ez.msg.slot ≤ tr.time jz :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg jz) _).mpr
      (by rw [(SA.castAt_spec hr hz ⟨hcz, hez⟩).2.1])
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hle' : tr.time jz ≤ sp.ts ez.msg.slot + sp.Δ := hle
  rw [hsl] at hle' hts
  have h₁ := (SA.ts_lt_iff sp).mpr (show ((s : Nat) : Int) < ((s + 1 : Nat) : Int) by omega)
  have h₂ := (SA.ts_le_iff sp).mpr (Int.ofNat_le.mpr hp.lt)
  have hfb := hp.faultBound z hz jz ez ⟨ℓz, hcz, hez⟩ (by linarith) (by linarith)
  have hH : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have : tr.honestAwakeJoined H (tr.time jz) ≤ H.ncard := Set.ncard_le_ncard fun y hy => hy.1
  unfold RunTrace.FaultBound at hfb
  omega

/-- At `t = t_{slot(t)} + Δ`, `ac_on_tick` of a joined node that has not voted in the slot
casts a vote. -/
theorem acOnTick_votes {FGP : Type} {ro' : ReplayOrder sp FGP} (self : Fin sp.n)
    (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP) {t : Time} (hj : SA.joined sp A t)
    (hv : A.votedSlot ≠ sp.slot t) (hm : A.mayVote (sp.slot t) = true)
    (ht : t = sp.ts (sp.slot t) + sp.Δ) :
    ((goldilocksSA sp FGP ro').step self A Φ t .tick).2 ≠ [] := by
  change (SA.acOnTick sp self A Φ t).2 ≠ []
  unfold SA.acOnTick
  dsimp only
  have hc : (t = sp.ts (sp.slot t) + sp.Δ) = True := eq_true ht
  simp only [hj, not_true_eq_false, hc, ↓reduceIte]
  unfold SA.tryVote
  dsimp only
  simp only [hm, ↓reduceIte]
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  split_ifs with h₁ h₂
  · rcases h₁ with h | h | h
    · exact absurd hj h
    · exact absurd h hv
    · linarith
  · linarith [h₂.1]
  all_goals simp

/-- **An honest vote of slot `s + 1` before an `ac_to_fg` call after `t_{s+1} + Δ`, or a restart
after `t_s`** (claims A1.9's case split, discharged by C0.4: a node that does not restart after
`t_s` is awake and joined at `t_{s+1} + Δ`, ticks there and votes). -/
theorem vote_or_restart (hrun : GoldilocksRun proposer dg H tr)
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hto : SA.ToFGAt tr.projAC y i ℓ C) (ht : sp.ts (s + 1 : Nat) + sp.Δ < tr.time i) :
    (∃ j < i, ∃ ℓ' e, SA.CastAt tr.projAC y j ℓ' e ∧ e.msg.slot = s + 1) ∨
      (∃ k < i, tr.projAC.RestartAt y k ∧ sp.ts s < tr.time k) := by
  by_cases hres : ∃ k < i, tr.projAC.RestartAt y k ∧ sp.ts s < tr.time k
  · exact Or.inr hres
  left
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hp.noColl).localRun
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hlocal := hrun.toLocalRun
  set u := sp.ts (s + 1 : Nat) + sp.Δ with hu
  have hus : sp.ts s < u := by
    have := (SA.ts_lt_iff sp).mpr (show ((s : Nat) : Int) < ((s + 1 : Nat) : Int) by omega)
    linarith
  have hu0 : 0 ≤ u := by simp only [hu, SA.SAParams.ts]; positivity
  -- a run restart is an AC restart of the projection
  have hrestart : ∀ k, tr.RestartAt y k → tr.projAC.RestartAt y k := fun k ⟨ℓk, hck, hk⟩ =>
    ⟨ℓk, ⟨hck.1, by change (tr.label k).bind RunTrace.acLabel = some ℓk; rw [hck.2]; rfl⟩, hk⟩
  have hcall : tr.IsCall y i := ⟨_, projAC_callAt.mp hto.1⟩
  -- awake at `u`: otherwise it woke up by a restart in `(u, time i]`, before cut `i`
  have hawake : tr.awake y u := by
    by_contra hna
    obtain ⟨k, hk, hku, hki⟩ := hlocal.restart_at_wake y hy u (tr.time i) hu0 ht hna
      (hlocal.awake_of_call y hy i hcall)
    rcases lt_trichotomy k i with hlt | rfl | hgt
    · exact hres ⟨k, hlt, hrestart k hk, by linarith⟩
    · obtain ⟨ℓk, hck, hkr⟩ := hk
      have h₁ := hck.2
      rw [(projAC_callAt.mp hto.1).2] at h₁
      cases h₁
      rw [hto.2.1] at hkr
      cases hkr
    · obtain ⟨u', -, hu'k, -, hbefore⟩ := hlocal.sleep_of_restart y hy k hk
      have := hbefore i hgt hcall
      linarith
  have hpub : sp.toParams.IsPublic u :=
    ⟨4 * (s + 1 : Nat) + 1, by simp only [hu, SA.SAParams.ts]; ring⟩
  obtain ⟨j₀, xt, hj₀⟩ := hlocal.tick_of_awake y hy u hu0 hpub hawake
  obtain ⟨ℓt, pc, uc, hlt, hcs, -, -⟩ :=
    @tick_order sp.toParams (goldilocksNode sp ro) proposer dg y (tr.state y j₀) u xt
  have hlen : 0 < (Node.exec proposer dg y (tr.state y j₀) u (.tick xt)).2.length := by
    change 0 < (Node.onTick proposer dg y (tr.state y j₀) u xt).2.length
    rw [hcs]; simp
  obtain ⟨hn₀, ht₀, -, -, hl₀⟩ := hj₀.2.1 0 hlen
  have hct : tr.CallAt y j₀ (.ac ℓt) := by
    refine ⟨hn₀, ?_⟩
    simp only [Nat.add_zero] at hl₀
    rw [hl₀]
    change some (Node.onTick proposer dg y (tr.state y j₀) u xt).2[0] = _
    simp [hcs]
  simp only [Nat.add_zero] at ht₀
  have hj₀i : j₀ < i := by
    by_contra h
    have := hrun.time_mono (not_lt.mp h)
    linarith
  have hpt : tr.projAC.CallAt y j₀ ℓt :=
    ⟨hct.1, by change (tr.label j₀).bind RunTrace.acLabel = some ℓt; rw [hct.2]; rfl⟩
  have hslot : sp.slot u = s + 1 := SA.slot_of_mem sp (s + 1) (by linarith)
    (by have := (SA.ts_lt_iff sp).mpr
          (show ((s + 1 : Nat) : Int) < ((s + 1 + 1 : Nat) : Int) by omega)
        have h4 : sp.ts ((s + 1 + 1 : Nat) : Int) = sp.ts ((s + 1 : Nat) : Int) + 4 * sp.Δ := by
          simp only [SA.SAParams.ts]; push_cast; ring
        linarith)
  set A := tr.projAC.state y j₀ with hA
  by_cases hvs : A.votedSlot = ((s + 1 : Nat) : Int)
  · rcases SA.cast_of_votedSlot hr (fun _ => SA.voteStart_initial _) hy j₀ (s + 1) hvs with
      ⟨j, hj, e, ⟨ℓ', hc', he'⟩, hes⟩ | hmf
    · exact ⟨j, hj.trans hj₀i, ℓ', e, ⟨hc', he'⟩, hes⟩
    · exact absurd (SA.trace_mayVote_stock hr hy j₀ _) (by rw [hmf]; decide)
  -- joined at the tick
  have hjr : tr.JoinedAt y u := by
    intro k hk hku
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
  have hnr : ¬ tr.RestartAt y j₀ := by
    rintro ⟨ℓk, hck, hkr⟩
    have h₁ := hck.2
    rw [hct.2] at h₁
    cases h₁
    rw [hlt] at hkr
    cases hkr
  have hjoined : SA.joined sp A u := by
    rw [hA, projAC_state hlocal hy]
    exact ((joined_projection sp ro dg H tr proposer hrun y hy u).2.1 j₀ ⟨_, hct⟩ hnr ht₀).mp hjr
  have hexec := hr.exec j₀ ℓt hpt.2 (hpt.1 ▸ hy)
  rw [hpt.1, hlt] at hexec
  have hne := acOnTick_votes (ro' := ro) y A ℓt.frame hjoined (by rw [hslot]; exact hvs)
    (SA.trace_mayVote_stock hr hy j₀ _) (by rw [hslot])
  rw [show tr.projAC.time j₀ = u from ht₀] at hexec
  rw [hexec] at hne
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
  have hsl := (SA.castAt_spec hr hy ⟨hpt, he⟩).2.1
  exact ⟨j₀, hj₀i, ℓt, e, ⟨hpt, he⟩, by rw [hsl]; change sp.slot (tr.time j₀) = _; rw [ht₀, hslot]⟩

/-- **C1.1's attestation step.** An honest attestation signed at a time in
`(t_{s+1} + Δ, t_m + Δ]`, with the invariant at every earlier cut, names no excluded entry. -/
theorem attest_not_excluded
    (hrun : GoldilocksRun proposer dg H tr)
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV) {v : Fin sp.n} (hv : v ∈ H) {j : Nat}
    {a : FG.Att sp.n} (hs : tr.SignAt v j a) (hT₀ : sp.ts (s + 1 : Nat) + sp.Δ < tr.time j)
    (hTm : tr.time j ≤ sp.ts m + sp.Δ)
    (ih : ∀ i < j, VoteInv tr H s m B i ∧ CutInv tr H s m B i) :
    ∀ E ∈ excludedEntries tr H s B, a.T ≠ E.root := by
  obtain ⟨C, hcall⟩ := hs
  obtain ⟨j', rfl, ℓ, hc', hto, htime, hC, hfgeq⟩ := attest_source hrun.toLocalRun hv hcall
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hp.noColl
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hpc : tr.projAC.CallAt v j' ℓ := by
    refine ⟨hc'.1, ?_⟩
    change (tr.label j').bind RunTrace.acLabel = some ℓ
    rw [hc'.2]; rfl
  have hToFG : SA.ToFGAt tr.projAC v j' ℓ C :=
    ⟨hpc, hto, by rw [projAC_state hrun.toLocalRun hv]; exact hC⟩
  have ih' : ∀ i < j', VoteInv tr H s m B i ∧ CutInv tr H s m B i := fun i hi => ih i (by omega)
  have hlo : sp.ts (s + 1 : Nat) + sp.Δ < tr.time j' := htime ▸ hT₀
  have hhi : tr.time j' ≤ sp.ts m + sp.Δ := htime ▸ hTm
  have hs1 := (SA.ts_lt_iff sp).mpr (show ((s : Nat) : Int) < ((s + 1 : Nat) : Int) by omega)
  have hsm := (SA.ts_le_iff sp).mpr (Int.ofNat_le.mpr hp.lt)
  -- the caches at a cut of the window
  have hframe : ∀ k ≤ j', ∀ ℓk, tr.projAC.CallAt v k ℓk → sp.ts s ≤ tr.time k →
      Compatible (tr.HonestBlocks H) ℓk.frame.F B := by
    intro k hk ℓk hck hk₀
    rw [frame_of_projAC hrun hv hck]
    exact (state_caches hrun hp k (fun i hi => (ih' i (by omega)).2) v hv hk₀
      fun i hi => by have := hrun.time_mono (show i ≤ j' by omega); linarith).1
  have hcase : (∃ i < j', ∃ ℓ' e, SA.CastAt tr.projAC v i ℓ' e ∧ e.msg.slot = s + 1 ∧
      Compatible (tr.HonestBlocks H) ℓ'.frame.F B) ∨
      (∃ k < j', tr.projAC.RestartAt v k ∧ sp.ts s < tr.time k) := by
    refine (vote_or_restart hrun hp hv hToFG hlo).imp_left ?_
    rintro ⟨i, hi, ℓ', e, hce, hsl⟩
    have hts : sp.ts e.msg.slot ≤ tr.time i :=
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).mpr
        (by rw [(SA.castAt_spec hr hv hce).2.1])
    rw [hsl] at hts
    exact ⟨i, hi, ℓ', e, hce, hsl, hframe i hi.le ℓ' hce.1 (by linarith)⟩
  have hsync := syncAC_mono (sync_projection sp.toParams (goldilocksNode sp ro) dg H
    (fun v => v.val) tr proposer ΔF (sp.ts s) (sp.ts m + sp.Δ) hrun.toLocalRun hp.sync) le_rfl
    (by linarith : sp.ts (s + 1 : Nat) + sp.Δ ≤ sp.ts m + sp.Δ)
  obtain ⟨ℓw, D, hcw, hflD, hBD⟩ := hp.fastLock
  have hΦwU : ℓw.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hr.frameLaw x hp.writer_honest i₀ ℓw hcw with
      ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1.2
  have hCB : Compatible (tr.HonestBlocks H) C B :=
    SA.source_compatible_stored sp _ ro proposer H _ tr.projAC hp.stock hrun' s m x v i₀ j' B D
      CV ℓ C
      hp.writer_honest hflD (hBD ▸ Anc.mono hΦwU (SA.anc_viableAncestor ℓw.frame D)) hsync
      hp.carry (faulty_lt_half hrun hp) hv hToFG
      hlo hhi
      (fun z hz i hi e ⟨ℓz, hcz, hez⟩ h₁ h₂ =>
        (voteInv_iff.mp (ih' i hi).1 z hz ℓz e ⟨hcz, hez⟩ h₁ h₂).2)
      hcase
  -- the target: the entry of the source's chain
  set st := (tr.state v (j' + 1)).fg with hst
  have hsub : st.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨v, hv, j' + 1, hX⟩
  have hreach := fg_reachable hrun.toLocalRun hv (j' + 1)
  have hCt : C ∈ st.tree := by
    obtain ⟨Φp, tp, hreachA, htp, hok⟩ := pre_reachable hr hv hpc
    have hΦ : ℓ.frame = Φp := by
      have h := hok.2
      rw [hto] at h
      exact h
    have hsrc := ((SA.interface_requirements sp _ ro).2.1 v _ hU _ _ _ hreachA) (tr.time j') htp C
      (by rw [projAC_state hrun.toLocalRun hv, ← hΦ]; exact hC)
    have hCf : C ∈ ℓ.frame.tree := hΦ ▸ hsrc.1
    rw [frame_of_projAC hrun hv hpc] at hCf
    change C ∈ st.tree
    rw [hfgeq]
    exact hCf.1
  have hcut := (hrun.cutLaw v hv (j' + 1) _ hcall).1
  have hT : a.T = (st.σ (st.σ C.root).Th).Th := createAtt_T hcut
  obtain ⟨⟨E, hE, hEr, hEC, -, hETh⟩, -, -⟩ :=
    Store.entry_state_of_source sp.toParams (Payload sp.n) _ st hreach C hCt
  have hTE : a.T = E.root := by rw [hT, ← hEr, hETh, hEr]
  intro E' hE' hEq
  obtain ⟨hnc, y, hy, jy, -, hanc, hne⟩ := hE'
  have hE'U := (Anc.mem hanc hne.symm).2
  have hEE : E' = E := hU.1 hE'U (hsub hE) (hEq.symm.trans hTE)
  subst hEE
  apply hnc
  have hEC' : Anc (tr.HonestBlocks H) E' C := Anc.mono hsub hEC
  rcases hCB with h | h
  · exact Or.inl (hEC'.trans h)
  · exact SA.anc_total hU hEC' h

end Consensus.Goldilocks.Compose

end
