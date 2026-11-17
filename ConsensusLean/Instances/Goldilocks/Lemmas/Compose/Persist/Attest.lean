module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Inv
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Source
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
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

/-- An honest signing is at a public time (it is a cut of a tick, C0.5 (c)). -/
theorem sign_public {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : GoldilocksRun proposer dg H tr ini) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
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
  have hle := (cast_head_fcRoot hr (fun _ => SA.voteStart_initial _) hz ⟨hcz, hez⟩).2
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

end Consensus.Goldilocks.Compose

end
