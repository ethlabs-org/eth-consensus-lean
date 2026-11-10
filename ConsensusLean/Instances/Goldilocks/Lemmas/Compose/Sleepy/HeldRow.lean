module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote

public section

/-! # Goldilocks under `Sleepy`: an honest row signed after an optimistic check

The three steps of "no optimistic check of slot `s + 1` before a row held at a slot-`(s+1)` vote"
(R4). Each reads one run with one honest set, so a fault model applies each at the cut it needs:

* `held_row_sign_time`: an honest signing from a time of slot `s + 1` on and by `t_{s+1} + Δ` is
  at `t_{s+1}` or at `t_{s+1} + Δ`, the public times there;
* `held_row_late_absurd`: an honest slot-`(s+1)` voter accepted, before its vote, no block with a
  row signed at `t_{s+1} + Δ` before the acceptance;
* `held_row_early_count`: an honest optimistic check of slot `s + 1` before an honest signing at
  `t_{s+1}` leaves `n = 1` and an honest slot-`(s+1)` vote no later than the check. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- An honest signing is at a public time (a cut of a tick). (As `Persist/Attest`'s
`sign_public`.) -/
private theorem sign_at_public (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {j : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} {a : FG.Att sp.n}
    (hc : tr.CallAt y j (.fg (.attest C (some a)))) : sp.toParams.IsPublic (tr.time j) := by
  obtain ⟨j₀, e, k, hg, -, hk⟩ := call_in_group hrun.toLocalRun hy hc
  obtain ⟨xt, rfl⟩ := @signed_only_in_ticks sp.toParams (goldilocksNode sp ro) proposer dg y
    (tr.state y j₀) (tr.time j) e C a (List.mem_of_getElem? hk)
  exact hrun.tick_public y hy j₀ (tr.time j) ⟨xt, hg⟩

/-- At `t = t_{slot(t)} + Δ`, `ac_on_tick` of a joined node that has not voted in the slot casts
a vote. (As `Persist/Attest`'s `acOnTick_votes`.) -/
private theorem tick_votes (self : Fin sp.n) (A : SA.SAState sp.n)
    (Φ : SA.Frm sp.n (List (FG.Att sp.n))) {t : Time} (hj : SA.joined sp A t)
    (hv : A.votedSlot ≠ sp.slot t) (ht : t = sp.ts (sp.slot t) + sp.Δ) :
    ((SA.goldilocksSA sp (List (FG.Att sp.n)) ro).step self A Φ t .tick).2 ≠ [] := by
  change (SA.acOnTick sp self A Φ t).2 ≠ []
  unfold SA.acOnTick
  dsimp only
  have hc : (t = sp.ts (sp.slot t) + sp.Δ) = True := eq_true ht
  simp only [hj, not_true_eq_false, hc, ↓reduceIte]
  unfold SA.tryVote
  dsimp only
  split_ifs with h₁ h₂
  · rcases h₁ with h | h | h
    · exact absurd hj h
    · exact absurd h hv
    · exact absurd ht (ne_of_gt h)
  · exact absurd ht (ne_of_lt h₂.1)
  all_goals simp

/-- The AC calls of a tick: `ac_on_tick`, `ac_proposal`, `ac_to_fg`, and the own block's
`ac_on_block` when the node proposes. -/
private theorem tick_ac_call {y : Fin sp.n} {st : NodeState (goldilocksNode sp ro)} {t : Time}
    {x : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (h : Cut.ac ℓ ∈ (Node.exec proposer dg y st t (.tick x)).2) :
    ℓ.call = .tick ∨ ℓ.call = .proposal ∨ ℓ.call = .toFG ∨ Node.Proposes proposer y t := by
  obtain ⟨ℓt, pc, uc, hlt, hcs, hpc, ℓu, hlu, huc⟩ :=
    @tick_order sp.toParams (goldilocksNode sp ro) proposer dg y st t x
  have h' : Cut.ac ℓ ∈ (Node.onTick proposer dg y st t x).2 := h
  rw [hcs] at h'
  rcases List.mem_cons.1 h' with h' | h'
  · rw [Cut.ac.inj h']
    exact Or.inl hlt
  rcases List.mem_append.1 h' with h' | h'
  · rcases hpc with ⟨-, rfl⟩ | ⟨hp, -⟩
    · exact absurd h' List.not_mem_nil
    · exact Or.inr (Or.inr (Or.inr hp))
  · right; right; left
    rcases huc with rfl | ⟨C, rfl⟩ | ⟨C, a, rfl⟩ <;> rcases List.mem_cons.1 h' with h' | h'
    all_goals first
      | (rw [Cut.ac.inj h']; exact hlu)
      | (simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_false] at h')

/-- A time of slot `s + 1` is at least `t_{s+1} = t_s + 4Δ`. -/
private theorem slot_start_le {t : Time} (ht : 0 ≤ t) {s : Nat} (hsl : sp.slot t = s + 1) :
    sp.ts s + 4 * sp.Δ ≤ t := by
  have h := (SA.ts_le_iff_le_slot sp ht ((s + 1 : Nat) : Int)).2 (le_of_eq (by rw [hsl]))
  have h' : sp.ts ((s + 1 : Nat) : Int) ≤ t := h
  simp only [SAParams.ts] at h' ⊢
  push_cast at h'
  linarith only [h']

/-- `t_{s+1} + Δ = t_s + 5Δ`. -/
private theorem le_ts_add_five {t : Time} {s : Nat}
    (h : t ≤ sp.ts ((s + 1 : Nat) : Int) + sp.Δ) : t ≤ sp.ts s + 5 * sp.Δ := by
  simp only [SAParams.ts] at h ⊢
  push_cast at h
  linarith only [h]

/-- **The time of an honest signing in slot `s + 1` by `t_{s+1} + Δ`.** An honest signing at
cut `k`, from a time `t` of slot `s + 1` on and by `t_{s+1} + Δ`, is at `t_{s+1}` (then `t` is
`t_{s+1}` too) or at `t_{s+1} + Δ`: it is a cut of a tick, at a public time. -/
theorem held_row_sign_time (hrun : GoldilocksRun proposer dg H tr) {a : FG.Att sp.n}
    (hav : a.val ∈ H) {k : Nat} (hsg : tr.SignAt a.val k a) {s : Nat} {t : Time} (ht : 0 ≤ t)
    (hsl : sp.slot t = s + 1) (htk : t ≤ tr.time k)
    (hk : tr.time k ≤ sp.ts ((s + 1 : Nat) : Int) + sp.Δ) :
    (tr.time k = sp.ts s + 4 * sp.Δ ∧ t = tr.time k) ∨ tr.time k = sp.ts s + 5 * sp.Δ := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  obtain ⟨src, hsgc⟩ := hsg
  obtain ⟨q, hq⟩ := sign_at_public hrun hav hsgc
  have hq' : tr.time k = sp.Δ * q := hq
  have ht4 := slot_start_le ht hsl
  have h4 := ht4.trans htk
  have h5 := le_ts_add_five hk
  simp only [SAParams.ts] at ht4 h4 h5 ⊢
  have hq1 : 4 * (s : Int) + 4 ≤ q := by
    by_contra h
    have : q + 1 ≤ 4 * (s : Int) + 4 := by omega
    linarith only [h4, hq', hΔ, mul_le_mul_of_nonneg_left this hΔ.le]
  have hq2 : q ≤ 4 * (s : Int) + 5 := by
    by_contra h
    have : 4 * (s : Int) + 6 ≤ q := by omega
    linarith only [h5, hq', hΔ, mul_le_mul_of_nonneg_left this hΔ.le]
  rcases (show q = 4 * (s : Int) + 4 ∨ q = 4 * (s : Int) + 5 by omega) with h | h
  · have h4' : tr.time k = 4 * sp.Δ * s + 4 * sp.Δ := by rw [hq', h]; ring
    exact Or.inl ⟨h4', le_antisymm htk (h4'.trans_le ht4)⟩
  · right; rw [hq', h]; ring

/-- **No held row signed at `t_{s+1} + Δ`.** An honest slot-`(s+1)` voter accepted, before its
vote, no block with a row signed at `t_{s+1} + Δ` before the acceptance: the voter's own tick at
`t_{s+1} + Δ` precedes the acceptance and casts a slot-`(s+1)` vote, a second one. -/
theorem held_row_late_absurd (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {s : Nat} {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} {m : Nat} (hm : tr.AcceptAt y m X) (hmi : m < i)
    {k : Nat} (hkm : k < m) (hT : tr.time k = sp.ts s + 5 * sp.Δ) : False := by
  have hr' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hr'.localRun
  have hl := hrun.toLocalRun
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  obtain ⟨hrs, hti⟩ := honest_vote_restarts hrun hnc hy hc hs
  have hti' : tr.time i ≤ sp.ts s + 5 * sp.Δ :=
    le_ts_add_five (by rw [← hs]; exact (cast_head_fcRoot hr hy hc).2)
  have hsi : sp.slot (tr.time i) = s + 1 := ((SA.castAt_spec hr hy hc).2.1.symm.trans hs)
  have hvi : SA.VoteAt tr.projAC y i e := ⟨ℓ, hc.1, hc.2⟩
  have hkm' := hrun.time_mono hkm.le
  have hmi' := hrun.time_mono hmi.le
  have htm : tr.time m = sp.ts s + 5 * sp.Δ := le_antisymm (hmi'.trans hti') (hT ▸ hkm')
  have hti5 : tr.time i = tr.time m := le_antisymm (hti'.trans htm.ge) hmi'
  have hslm : sp.slot (tr.time m) = s + 1 := hti5 ▸ hsi
  rcases blockCall_cases hl hy hm with hgm | ⟨-, -, -, -, hp, -⟩
  swap
  · obtain ⟨-, hpt', -⟩ := hp
    have h1 : sp.toParams.slotOf (tr.time m) = s + 1 := hslm
    rw [h1, sp.slotTime_eq, htm] at hpt'
    simp only [SAParams.ts] at hpt'
    push_cast at hpt'
    linarith only [hpt', hΔ]
  obtain ⟨jt, xt, hgt⟩ := hl.tick_of_awake y hy (tr.time m) (hl.time_nonneg m)
    ⟨4 * (s : Int) + 5, by rw [htm]; simp only [SAParams.ts]; ring⟩
    (hl.awake_of_call y hy m ⟨_, hm⟩)
  have hjm : jt < m := by
    rcases lt_trichotomy jt m with h | rfl | h
    · exact h
    · have := group_phase hgm hgt
      simp [Node.Event.phase] at this
    · have := hl.phase_order y hy y hy m jt _ _ _ hgm hgt h
      simp [Node.Event.phase] at this
  -- the tick's first cut is `ac_on_tick`
  obtain ⟨ℓt, pc, uc, hlt, hcs, -, -⟩ :=
    @tick_order sp.toParams (goldilocksNode sp ro) proposer dg y (tr.state y jt) (tr.time m) xt
  have hlen : 0 < (Node.exec proposer dg y (tr.state y jt) (tr.time m) (.tick xt)).2.length := by
    change 0 < (Node.onTick proposer dg y (tr.state y jt) (tr.time m) xt).2.length
    rw [hcs]; simp
  obtain ⟨hn₀, ht₀, -, -, hl₀⟩ := hgt.2.1 0 hlen
  have hct : tr.CallAt y jt (.ac ℓt) := by
    refine ⟨hn₀, ?_⟩
    simp only [Nat.add_zero] at hl₀
    rw [hl₀]
    change some (Node.onTick proposer dg y (tr.state y jt) (tr.time m) xt).2[0] = _
    simp [hcs]
  simp only [Nat.add_zero] at ht₀
  have hpt0 : tr.projAC.CallAt y jt ℓt := projAC_callAt.2 hct
  by_cases hvs : (tr.projAC.state y jt).votedSlot = ((s + 1 : Nat) : Int)
  · obtain ⟨j, hj, e', hv', hes'⟩ := SA.cast_of_votedSlot hr hy jt (s + 1) hvs
    have := (SA.one_vote_per_slot sp _ ro H _ tr.projAC hr y hy j i e' e hv' hvi
      (hes'.trans hs.symm)).1
    omega
  -- joined at the tick: its restarts are at or before `t_s`
  have hjr : tr.JoinedAt y (tr.time m) := by
    intro k' hk' hk'T
    refine ⟨by change 0 < sp.slot (tr.time m); omega, ?_⟩
    change tr.time k' ≤ sp.toParams.slotTime (sp.slot (tr.time m) - 1)
    rw [hslm, Nat.add_sub_cancel, sp.slotTime_eq]
    rcases le_or_gt k' i with hki | hki
    · have := hrs k' hki (projAC_restartAt.2 hk')
      simp only [SAParams.ts] at this
      exact this
    · obtain ⟨u, -, hu, -, hbefore⟩ := hl.sleep_of_restart y hy k' hk'
      have := hbefore i hki ⟨_, projAC_callAt.1 hc.1⟩
      linarith only [this, hu, hk'T, hti5]
  have hnr : ¬ tr.RestartAt y jt := by
    rintro ⟨ℓk, hck, hkr⟩
    have h₁ := hck.2
    rw [hct.2] at h₁
    cases h₁
    rw [hlt] at hkr
    cases hkr
  have hjoined : SA.joined sp (tr.projAC.state y jt) (tr.time m) := by
    rw [projAC_state hl hy]
    exact ((joined_projection sp ro dg H tr proposer hrun y hy (tr.time m)).2.1 jt ⟨_, hct⟩ hnr
      ht₀).mp hjr
  have hexec := hr.exec jt ℓt hpt0.2 (hpt0.1 ▸ hy)
  rw [hpt0.1, hlt] at hexec
  have hne := tick_votes (ro := ro) y (tr.projAC.state y jt) ℓt.frame hjoined
    (by rw [hslm]; exact hvs)
    (by rw [hslm, htm]; simp only [SAParams.ts]; push_cast; ring)
  rw [show tr.projAC.time jt = tr.time m from ht₀] at hexec
  rw [hexec] at hne
  obtain ⟨e₀, he₀⟩ := List.exists_mem_of_ne_nil _ hne
  have hsl₀ : e₀.msg.slot = sp.slot (tr.time m) := (SA.castAt_spec hr hy ⟨hpt0, he₀⟩).2.1.trans
    (by rw [show tr.projAC.time jt = tr.time m from ht₀])
  have := (SA.one_vote_per_slot sp _ ro H _ tr.projAC hr y hy jt i e₀ e ⟨ℓt, hpt0, he₀⟩ hvi
    (hsl₀.trans (hslm.trans hs.symm))).1
  omega

/-- **An optimistic check before an honest signing at `t_{s+1}`.** An honest optimistic check of
slot `s + 1` at a cut before an honest signing at `t_{s+1}` leaves `n = 1`, with an honest
slot-`(s+1)` vote at a cut no later than the check: the check is at `t_{s+1}` too, its honest seats
are the slot's proposer, and three quarters of `n` are at most `f + 1` with `2f < n`. -/
theorem held_row_early_count (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n) {s : Nat}
    {a : FG.Att sp.n} (hav : a.val ∈ H) {k : Nat} (hsg : tr.SignAt a.val k a)
    (hT0 : tr.time k = sp.ts s + 4 * sp.Δ)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat} (hck : c < k) {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hO : SA.OptimisticLockAt tr.projAC z c (s + 1) C CV) :
    sp.n = 1 ∧ ∃ u ∈ H, ∃ j' ≤ c, ∃ e', SA.VoteAt tr.projAC u j' e' ∧ e'.msg.slot = s + 1 := by
  have hr' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hr'.localRun
  have hl := hrun.toLocalRun
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  obtain ⟨ℓO, AO, hpt, hslc, hsel, -⟩ := hO
  have hc0 : sp.ts s + 4 * sp.Δ ≤ tr.time c := slot_start_le (hr.time_nonneg c) hslc
  have hck' := hrun.time_mono hck.le
  obtain ⟨src, hsgc⟩ := hsg
  have htc : tr.time c = tr.time k := le_antisymm hck' (hT0 ▸ hc0)
  obtain ⟨gx, ex, kx, hgx, hkeq, hkx⟩ := call_in_group hl hav hsgc
  obtain ⟨xt, rfl⟩ := @signed_only_in_ticks sp.toParams (goldilocksNode sp ro) proposer dg a.val
    (tr.state a.val gx) (tr.time k) ex src a (List.mem_of_getElem? hkx)
  have hklen := (List.getElem?_eq_some_iff.1 hkx).1
  unfold SA.optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  have h34 := (SA.deepest_mem hsel).1.2.1
  rw [hslc] at h34
  have hprop : ∀ u ∈ SA.optimisticVoters sp AO ℓO.frame (s + 1) C, u ∈ H →
      u = proposer (sp.toParams.slotOf (tr.time k)) ∧
        ∃ j' ≤ c, ∃ e', SA.VoteAt tr.projAC u j' e' ∧ e'.msg.slot = s + 1 := by
    rintro u ⟨v, hv, hvu, -⟩ huH
    subst hvu
    obtain ⟨hvs, j', hj', e', ⟨ℓ', hc', he'⟩, rfl⟩ :=
      SA.optimisticPoint_pool_vote hr' hz hpt hv huH
    refine ⟨?_, j', hj', e', ⟨ℓ', hc', he'⟩, hvs⟩
    -- the vote is cast at `t_{s+1}`
    have hsl' : sp.slot (tr.time j') = s + 1 :=
      (SA.castAt_spec hr huH ⟨hc', he'⟩).2.1.symm.trans hvs
    have htj : tr.time j' = tr.time k := by
      refine le_antisymm ((hrun.time_mono hj').trans (htc ▸ le_rfl)) ?_
      rw [hT0]; exact slot_start_le (hr.time_nonneg j') hsl'
    -- in a tick or a restart: before the signer's tick, or in it
    obtain ⟨g, eu, k₁, hg, hjeq, hk₁⟩ := call_in_group hl huH (projAC_callAt.1 hc')
    rw [htj] at hg hk₁
    have hph : eu.phase ≤ 1 := by
      rcases lt_trichotomy g gx with h | rfl | h
      · have := hl.phase_order _ huH _ hav g gx (tr.time k) eu _ hg hgx h
        simpa [Node.Event.phase] using this
      · obtain ⟨_, hn₁⟩ := (group_call hg).1
        obtain ⟨_, hn₂⟩ := (group_call hgx).1
        have hnode : (e'.msg).val = a.val := hn₁.1.symm.trans hn₂.1
        rw [hnode] at hg
        rw [group_phase hg hgx]
        simp [Node.Event.phase]
      · exact absurd (group_start hgx hg h.le (by omega)) h.ne'
    have hmem := List.mem_of_getElem? hk₁
    obtain ⟨htick, hnp, hnt, hnr⟩ := honest_vote_call hrun hnc huH ⟨hc', he'⟩
    cases eu with
    | tick xu =>
      rcases tick_ac_call hmem with h | h | h | hp
      · have h5 := htick h
        rw [hsl', htj, hT0] at h5
        simp only [SAParams.ts] at h5
        push_cast at h5
        linarith only [h5, hΔ]
      · exact absurd h hnp
      · exact absurd h hnt
      · exact hp.2.2.symm
    | restart =>
      simp only [Node.exec, Node.restart, Node.acCall, List.mem_singleton, Cut.ac.injEq] at hmem
      exact absurd (by rw [hmem]) hnr
    | _ => simp [Node.Event.phase] at hph
  -- counting: `3n ≤ 4(f + 1)` and `2f < n` leave `n = 1`
  have hsub : SA.optimisticVoters sp AO ℓO.frame (s + 1) C ⊆
      Hᶜ ∪ {proposer (sp.toParams.slotOf (tr.time k))} := fun u hu => by
    by_cases huH : u ∈ H
    · exact Or.inr (hprop u hu huH).1
    · exact Or.inl huH
  have hcard := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
    ((Set.ncard_union_le _ _).trans (by rw [Set.ncard_singleton]))
  have hn1 : sp.n = 1 := by omega
  obtain ⟨u, hu⟩ := Set.nonempty_of_ncard_ne_zero
    (show (SA.optimisticVoters sp AO ℓO.frame (s + 1) C).ncard ≠ 0 by omega)
  have huH : u ∈ H := by
    by_contra h
    have := (Set.ncard_pos (Set.toFinite Hᶜ)).2 ⟨u, h⟩
    omega
  obtain ⟨-, j', hj', e', hv', hs'⟩ := hprop u hu huH
  exact ⟨hn1, u, huH, j', hj', e', hv', hs'⟩

end Consensus.Goldilocks.Compose

end
