module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: source labels and frame viability

Source labels at a vote bound the origins used by the frame argument. `Frame` supplies the
honest-store geometry and `FrameFrozen` supplies the frozen witness; together they establish
full-read and vote-frame viability. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-! ### The source labels at a vote -/

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
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  split_ifs with h₁ h₂
  · rcases h₁ with h | h | h
    · exact absurd hj h
    · exact absurd h hv
    · linarith
  · linarith [h₂.1]
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

/-- `no_optimistic_before_held_row` with `f < n/2`. -/
theorem no_optimistic_before_held_row_of (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n) {s : Nat} {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} {m : Nat} (hm : tr.AcceptAt y m X) (hmi : m < i)
    {a : FG.Att sp.n} (hav : a.val ∈ H) {k : Nat} (hkm : k < m) (hsg : tr.SignAt a.val k a)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat} (hck : c < k) {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hO : SA.OptimisticLockAt tr.projAC z c (s + 1) C CV) : False := by
  have hr' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hr'.localRun
  have hl := hrun.toLocalRun
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  obtain ⟨hrs, hti⟩ := honest_vote_restarts hrun hnc hy hc hs
  have hti' : tr.time i ≤ sp.ts s + 5 * sp.Δ := by
    have h : tr.time i ≤ sp.ts (e.msg.slot : Int) + sp.Δ := (cast_head_fcRoot hr hy hc).2
    rw [hs] at h
    simp only [SAParams.ts] at h ⊢
    push_cast at h
    linarith
  have hsi : sp.slot (tr.time i) = s + 1 := ((SA.castAt_spec hr hy hc).2.1.symm.trans hs)
  have hvi : SA.VoteAt tr.projAC y i e := ⟨ℓ, hc.1, hc.2⟩
  -- the selection is in slot `s + 1`
  obtain ⟨ℓO, AO, hpt, hslc, hsel, -⟩ := hO
  have hc0 : sp.ts s + 4 * sp.Δ ≤ tr.time c := by
    have h := (SA.ts_le_iff_le_slot sp (hr.time_nonneg c) ((s + 1 : Nat) : Int)).2
      (le_of_eq (by rw [hslc]))
    have h' : sp.ts ((s + 1 : Nat) : Int) ≤ tr.time c := h
    simp only [SAParams.ts] at h' ⊢
    push_cast at h'
    linarith
  have hck' := hrun.time_mono hck.le
  have hkm' := hrun.time_mono hkm.le
  have hmi' := hrun.time_mono hmi.le
  -- the attestation is signed at a public time, `t_{s+1}` or `t_{s+1} + Δ`
  obtain ⟨src, hsgc⟩ := hsg
  obtain ⟨q, hq⟩ := sign_at_public hrun hav hsgc
  have hq' : tr.time k = sp.Δ * q := hq
  have hq1 : 4 * (s : Int) + 4 ≤ q := by
    by_contra h
    have : q + 1 ≤ 4 * (s : Int) + 4 := by omega
    simp only [SAParams.ts] at hc0
    linarith [mul_le_mul_of_nonneg_left this hΔ.le]
  have hq2 : q ≤ 4 * (s : Int) + 5 := by
    by_contra h
    have : 4 * (s : Int) + 6 ≤ q := by omega
    simp only [SAParams.ts] at hti'
    linarith [mul_le_mul_of_nonneg_left this hΔ.le]
  rcases (show q = 4 * (s : Int) + 5 ∨ q = 4 * (s : Int) + 4 by omega) with hq5 | hq4
  · -- at `t_{s+1} + Δ`: the voter's tick there votes before the block arrives
    have hT : tr.time k = sp.ts s + 5 * sp.Δ := by
      rw [hq', hq5]; simp only [SAParams.ts]; ring
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
      linarith
    obtain ⟨jt, xt, hgt⟩ := hl.tick_of_awake y hy (tr.time m) (hl.time_nonneg m)
      ⟨q, by rw [htm, ← hT, hq']⟩ (hl.awake_of_call y hy m ⟨_, hm⟩)
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
        linarith
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
  · -- at `t_{s+1}`: the honest optimistic voters are the slot's proposer
    have hT0 : tr.time k = sp.ts s + 4 * sp.Δ := by
      rw [hq', hq4]; simp only [SAParams.ts]; ring
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
        have h := (SA.ts_le_iff_le_slot sp (hr.time_nonneg j') ((s + 1 : Nat) : Int)).2
          (le_of_eq (congrArg (Nat.cast : Nat → Int) hsl'.symm))
        have h' : sp.ts ((s + 1 : Nat) : Int) ≤ tr.time j' := h
        simp only [SAParams.ts] at h'
        push_cast at h'
        rw [hT0]; simp only [SAParams.ts]; linarith
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
          linarith
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
    obtain rfl : u = y := Fin.ext (by have := u.isLt; have := y.isLt; omega)
    have := (SA.one_vote_per_slot sp _ ro H _ tr.projAC hr u huH j' i e' e hv' hvi
      (hs'.trans hs.symm)).1
    omega

/-- **Sources at a vote have labels at most `s`** (workbench#11 §3, R4; §4 "Extend the vote
frontier"): at an honest slot-`(s+1)` vote, every honest attestation on a block the voter holds has
a source below an origin of label at most `s`. A regular origin of label `l` is written at
`t_l + 6Δ`, after the vote unless `l < s`; an optimistic one of label `l ≥ s + 2` after
`t_{s+2}`; label `s + 1` is `no_optimistic_before_held_row`. -/
private theorem vote_row_source (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {s : Nat} {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y i).fg.tree)
    {a : FG.Att sp.n} (ha : a ∈ X.fgPayload) (hav : a.val ∈ H) :
    ∃ D ∈ tr.HonestBlocks H, IsHonestSource tr H D a.T ∧
      ∃ C j, OriginBefore tr H C j i ∧ j ≤ s ∧ Anc (tr.HonestBlocks H) D C := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨m, hmi, hm, k, hkm, hsg⟩ := honest_row_signed_before hrun hnc hy hX ha hav
  obtain ⟨D, hDU, hDs, C, l, hC, hDC⟩ := attestation_source hrun hnc hav hsg
  obtain ⟨z, hz, c, hck, CV, hRO⟩ := originBefore_iff.1 hC
  refine ⟨D, hDU, hDs, C, l, originBefore_iff.2 ⟨z, hz, c, by omega, CV, hRO⟩, ?_, hDC⟩
  -- the vote is cast by `t_{s+1} + Δ`, after the origin's event
  have hti : tr.time i ≤ sp.ts s + 5 * sp.Δ := by
    have h : tr.time i ≤ sp.ts (e.msg.slot : Int) + sp.Δ := (cast_head_fcRoot hr hy hc).2
    rw [hs] at h
    simp only [SAParams.ts] at h ⊢
    push_cast at h
    linarith
  have hci : tr.time c ≤ tr.time i := hrun.time_mono (by omega)
  by_contra hl
  have hl' : (s : Int) + 1 ≤ (l : Int) := by exact_mod_cast Nat.lt_of_not_le hl
  rcases hRO with ⟨ℓR, ⟨-, -, htR, -⟩, -⟩ | hO
  · -- a regular origin of label `l > s` is written at `t_l + 6Δ ≥ t_{s+1} + 6Δ`
    have htR' : tr.time c = sp.ts (l : Int) + 6 * sp.Δ := htR
    simp only [SAParams.ts] at htR' hti
    linarith [mul_le_mul_of_nonneg_left hl' hΔ.le]
  · rcases Nat.lt_or_ge l (s + 2) with hl2 | hl2
    · obtain rfl : l = s + 1 := by omega
      exact no_optimistic_before_held_row_of hrun hnc hf hy hc hs hm hmi hav hkm hsg hz hck hO
    · -- an optimistic origin of label `l ≥ s + 2` is selected from `t_l ≥ t_s + 8Δ` on
      obtain ⟨ℓO, A, -, hslot, -⟩ := hO
      have h := (SA.ts_le_iff_le_slot sp (hr.time_nonneg c) (l : Int)).2
        (le_of_eq (by rw [hslot]))
      have h' : sp.ts (l : Int) ≤ tr.time c := h
      have hl2' : (s : Int) + 2 ≤ (l : Int) := by exact_mod_cast hl2
      simp only [SAParams.ts] at h' hti
      linarith [mul_le_mul_of_nonneg_left hl2' hΔ.le]

/-- **S3 at full reads, over sources `G`**: with `f < n/2`, the honest attestations at heights
`≥ h_j` sourced by `G`, the sources pairwise compatible and compatible with `B`, a held block `B` is
at or below `fc_root` or in the full viable tree. -/
private theorem held_viable_of (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  have hU := (projFG_localRun hrun hnc).coherent
  -- the frame
  have hΦ : FrameOK (Node.frame (tr.state y i)) :=
    (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).1
  have hΦU : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, i, hX.1⟩
  have hΦs : (Node.frame (tr.state y i)).tree ⊆ (tr.state y i).fg.tree := fun X hX => hX.1
  have hsU := fg_tree_subset_honest (tr := tr) hy i
  -- `fc_root` (`Σ.J` or `Σ.F`) is compatible with `B`
  have hfc : Compatible (tr.HonestBlocks H) (Node.frame (tr.state y i)).fcRoot B := by
    change Compatible _ (tr.state y i).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs
    · exact J_compatible hrun hnc hf hy hsrc hGB (hsU hBt.1)
    · exact Or.inl (hBt.2.mono hsU)
  rcases hfc with hfB | hBf
  swap
  · exact Or.inl (SA.anc_tree_of_anc_U hU hΦ hΦU hBt hBf hΦ.fcRoot_mem)
  have hΦfB := SA.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfB hBt
  right
  rcases floor_or_crossing_of hrun hnc hf hy hsrc hGG hGB hBt.1 with hle | ⟨-, E, X, -, -, -, hBE,
    -, hX, hEX, hXv⟩
  · exact ⟨hBt, hΦfB, B, hBt, ⟨hBt.1, hBt.2, Anc.mono hΦs hΦfB, hle⟩, .refl⟩
  · have hBX := hBE.trans hEX
    have hXΦ : X ∈ (Node.frame (tr.state y i)).tree := ⟨hX, hBt.2.trans hBX⟩
    exact ⟨hBt, hΦfB, X, hXΦ, ⟨hX, hXΦ.2, (Anc.mono hΦs hΦfB).trans hBX, hXv⟩,
      SA.anc_tree_of_anc_U hU hΦ hΦU hBt (Anc.mono hsU hBX) hXΦ⟩

/-- Sources below pairwise compatible tips (`Q`) are pairwise compatible, and compatible with a
block compatible with every tip. -/
private theorem below_tips_compatible (hU : Coherent (tr.HonestBlocks H))
    {Q : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hQQ : ∀ C C', Q C → Q C' → Compatible (tr.HonestBlocks H) C C')
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hQB : ∀ C, Q C → Compatible (tr.HonestBlocks H) B C) :
    (∀ D D', (∃ C, Q C ∧ Anc (tr.HonestBlocks H) D C) → (∃ C, Q C ∧ Anc (tr.HonestBlocks H) D' C) →
      Compatible (tr.HonestBlocks H) D D') ∧
    ∀ D, (∃ C, Q C ∧ Anc (tr.HonestBlocks H) D C) → Compatible (tr.HonestBlocks H) D B := by
  refine ⟨?_, ?_⟩
  · rintro D D' ⟨C, hC, hDC⟩ ⟨C', hC', hDC'⟩
    rcases hQQ C C' hC hC' with h | h
    · exact Anc.total hU (hDC.trans h) hDC'
    · exact Anc.total hU hDC (hDC'.trans h)
  · rintro D ⟨C, hC, hDC⟩
    rcases hQB C hC with h | h
    · exact Anc.total hU hDC h
    · exact Or.inl (hDC.trans h)

/-- `held_origin_viable` with `f < n/2` and the origins whose event precedes the cut pairwise
compatible. -/
private theorem held_origin_viable_of (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    (hP : ∀ C s C' s', OriginBefore tr H C s i → OriginBefore tr H C' s' i →
      Compatible (tr.HonestBlocks H) C C')
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C s, OriginBefore tr H C s i → Compatible (tr.HonestBlocks H) B C)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  have hU := (projFG_localRun hrun hnc).coherent
  have hsrc : HonestRowsSourced tr H (fun D => ∃ C, (∃ l, OriginBefore tr H C l i) ∧
      Anc (tr.HonestBlocks H) D C) y i := by
    rw [honestRowsSourced_iff]
    intro X hX a ha hav
    obtain ⟨m, hm, -, k, hk, hsg⟩ := honest_row_signed_before hrun hnc hy hX ha hav
    obtain ⟨D, -, hDs, C, l, hC, hDC⟩ := attestation_source hrun hnc hav hsg
    obtain ⟨z, hz, k', hk', CV, h⟩ := originBefore_iff.1 hC
    exact ⟨D, ⟨C, ⟨l, originBefore_iff.2 ⟨z, hz, k', by omega, CV, h⟩⟩, hDC⟩, hDs⟩
  obtain ⟨hGG, hGB⟩ := below_tips_compatible hU (Q := fun C => ∃ l, OriginBefore tr H C l i)
    (fun C C' ⟨l, hC⟩ ⟨l', hC'⟩ => hP C l C' l' hC hC') (fun C ⟨l, hC⟩ => hBc C l hC)
  exact held_viable_of hrun hnc hf hy i (hsrc.above _) hGG hGB hBt

/-- **S3 at full reads**: once all origins compare, a block `B` that an honest node holds before
cut `i` and that is compatible with every origin whose event precedes the cut (an origin itself;
a protected proposal before its update, workbench#12 §4 S3P) is at or below its `fc_root` or in
its full viable tree. -/
theorem held_origin_viable (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) (hP : ∀ s, OriginsBelow tr H s) {y : Fin sp.n} (hy : y ∈ H)
    (i : Nat) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C s, OriginBefore tr H C s i → Compatible (tr.HonestBlocks H) B C)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree :=
  held_origin_viable_of hrun hnc (two_faults_lt_of_sleepy hsl) hy i
    (fun C l C' l' hC hC' => originsBelow_iff.1 (hP (l + l' + 1)) C l C' l' (by omega)
      (by omega) hC.origin hC'.origin) hBc hBt

/-- **S3 at full reads up to `b`**: at a cut within `b`, once the origins within `b` compare, a
block `B` that an honest node holds before the cut and that is compatible with every origin whose
event precedes the cut is at or below its `fc_root` or in its full viable tree. -/
theorem held_origin_viable_upTo {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) (hP : ∀ s, OriginsBelowUpTo tr H s b) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) (hi : ∀ k < i, tr.time k ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C s, OriginBefore tr H C s i → Compatible (tr.HonestBlocks H) B C)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree :=
  held_origin_viable_of hrun hnc (two_faults_lt_of_prefix hpre) hy i
    (fun C l C' l' hC hC' => originsBelowUpTo_iff.1 (hP (l + l' + 1)) C l C' l' (by omega)
      (by omega) (hC.within hi) (hC'.within hi)) hBc hBt

/-- Full-read viability uses the finite frontier and fault bound, with no service premise. -/
theorem held_origin_viable_before {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n)
    (hP : ∀ s, OriginsBelowUpTo tr H s b) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) (hi : ∀ k < i, tr.time k ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C s, OriginBefore tr H C s i → Compatible (tr.HonestBlocks H) B C)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree :=
  held_origin_viable_of hrun hnc hf hy i
    (fun C l C' l' hC hC' => originsBelowUpTo_iff.1 (hP (l + l' + 1)) C l C' l' (by omega)
      (by omega) (hC.within hi) (hC'.within hi)) hBc hBt

/-- **S3 at votes, over sources `G`, on a window**: at an honest slot-`(s+1)` vote at a time
`≤ b`, with the honest attestations at heights `≥ h_j` sourced by `G` (sources pairwise compatible,
compatible with `B`, each extended by an honest vote of a slot `≤ s`) and the heads accepted
before `t_{s₀}` caught up (`hold`), a block `B` that an honest slot-`s` vote extends is in the
viable tree of the voter block tree, or at or below `fc_root`. -/
private theorem vote_frame_of {s₀ : Nat} {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hservice : SleepyWindow tr H ΔF s₀ b ∨ SleepyServiceBefore tr H ΔF b)
    (hf : 2 * Hᶜ.ncard < sp.n) {s : Nat} {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    (hold : ∀ x ∈ H, ∀ m B, tr.AcceptAt x m B → tr.time m < sp.ts s₀ →
      Anc (tr.HonestBlocks H) ℓ.frame.F B → SA.AcceptedBefore tr.projAC y B (sp.ts s + 3 * sp.Δ))
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    (hGW : ∀ D, G D → ∃ x ∈ H, ∃ k e', SA.VoteAt tr.projAC x k e' ∧ e'.msg.slot ≤ s ∧
      SA.VoteExtends (tr.HonestBlocks H) e'.msg D)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocks H)
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hw : ∃ x ∈ H, ∃ k e', SA.VoteAt tr.projAC x k e' ∧ e'.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  have hU := (projFG_localRun hrun hnc).coherent
  have hfr := frame_of_projAC hrun hy hc.1
  have hΦ : FrameOK ℓ.frame := by
    rw [hfr]; exact (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).1
  have hΦU : ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rw [hfr]; exact fun X hX => ⟨y, hy, i, hX.1⟩
  have hsU := fg_tree_subset_honest (tr := tr) hy i
  -- `Σ.J`, `Σ.F` and `fc_root` are compatible with `B`
  have hJ := J_compatible hrun hnc hf hy hsrc hGB hB
  have hF : Compatible (tr.HonestBlocks H) (tr.state y i).fg.F B := by
    have hFJ := ((Store.cache_invariants _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).2.2.1).mono
      hsU
    rcases hJ with h | h
    · exact Or.inl (hFJ.trans h)
    · exact Anc.total hU hFJ h
  have hfc : Compatible (tr.HonestBlocks H) ℓ.frame.fcRoot B := by
    rw [hfr]
    change Compatible _ (tr.state y i).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs
    · exact hJ
    · exact hF
  have hv := vote_viable hrun hnc hy hc (B := B) ⟨hF, hJ⟩
  rw [hs] at hv
  apply hv
  rcases hfc with hfB | hBf
  swap
  · exact Or.inr hBf
  left
  have hFB : Anc (tr.HonestBlocks H) ℓ.frame.F B := (Anc.mono hΦU hΦ.F_anc_fcRoot).trans hfB
  -- the relayed honest slot-`s` head extending `B`
  obtain ⟨x, hx, k, e', hve, hs', hext⟩ := hw
  obtain ⟨W, hW, hBW⟩ :=
    honest_head_frozen hrun hnc hservice hy hc hs hib hold hx hve hs'.le hext hFB
  have hWt : W ∈ (tr.state y i).fg.tree := by
    have := hW.1; rw [hfr] at this; exact this.1
  have hBW' := honest_held_anc hrun hnc hy hBW hWt
  have hBt := anc_mem hBW' hWt
  rcases floor_or_crossing_of hrun hnc hf hy hsrc hGG hGB hBt with hle | ⟨D, E, X, hD, hDs, hE,
    hBE, hEh, -⟩
  · exact ⟨W, hW, hBW, hle.trans (honest_held_height hrun hnc hy hBW').1⟩
  · -- the honest head of a vote extending the crossing source
    obtain ⟨x', hx', k', e'', hve', hs'', hext'⟩ := hGW D hD
    obtain ⟨x₀, hx₀, k₀, -, -, hED, -, -⟩ := honest_source_entry hrun hnc hDs ⟨y, hy, i, hE⟩ rfl
    have hEDU : Anc (tr.HonestBlocks H) E D := hED.mono (fg_tree_subset_honest hx₀ k₀)
    have hFD : Anc (tr.HonestBlocks H) ℓ.frame.F D := hFB.trans ((hBE.mono hsU).trans hEDU)
    obtain ⟨W', hW', hDW'⟩ := honest_head_frozen hrun hnc hservice hy hc hs hib hold hx' hve' hs''
      hext' hFD
    have hW't : W' ∈ (tr.state y i).fg.tree := by
      have := hW'.1; rw [hfr] at this; exact this.1
    have hEW' := honest_held_anc hrun hnc hy (hEDU.trans hDW') hW't
    refine ⟨W', hW', (hBE.mono hsU).trans (hEDU.trans hDW'), ?_⟩
    change (tr.state y i).fg.headHeightFloor ≤ _
    rw [← hEh]
    exact (honest_held_height hrun hnc hy hEW').1

/-- **S3 at votes up to `b` (the frozen witness)**: at an honest slot-`(s+1)` vote at a time
`≤ b`, a block `B` of the honest blocks that is compatible with every origin within `b` of label
at most `s` and that some honest slot-`s` vote extends is in the viable tree of the voter block
tree, or at or below `fc_root` (inside the honest blocks). -/
theorem vote_frame_upTo {b : Time} (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H)
    (hBc : ∀ C j, OriginWithin tr H C j b → j ≤ s → Compatible (tr.HonestBlocks H) B C)
    (hw : ∃ x ∈ H, ∃ k e', SA.VoteAt tr.projAC x k e' ∧ e'.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  have hU := (projFG_localRun hrun hnc).coherent
  have hf := two_faults_lt_of_prefix hpre
  have hib' : ∀ k < i, tr.time k ≤ b := fun k hk => (hrun.time_mono hk.le).trans hib
  have hsrc : HonestRowsSourced tr H (fun D => ∃ C, (∃ j, OriginWithin tr H C j b ∧ j ≤ s) ∧
      Anc (tr.HonestBlocks H) D C) y i := by
    rw [honestRowsSourced_iff]
    intro X hX a ha hav
    obtain ⟨D, -, hDs, C, j, hC, hj, hDC⟩ := vote_row_source hrun hnc hf hy hc hs hX ha hav
    exact ⟨D, ⟨C, ⟨j, hC.within hib', hj⟩, hDC⟩, hDs⟩
  obtain ⟨hGG, hGB⟩ := below_tips_compatible hU
    (Q := fun C => ∃ j, OriginWithin tr H C j b ∧ j ≤ s)
    (fun C C' ⟨j, hC, hj⟩ ⟨j', hC', hj'⟩ =>
      originsBelowUpTo_iff.1 hP C j C' j' (by omega) (by omega) hC hC')
    (fun C ⟨j, hC, hj⟩ => hBc C j hC hj)
  refine vote_frame_of hrun hnc (Or.inl hpre.window) hf hy hc hs hib
    (fun _ _ m _ _ hm _ => absurd hm (by rw [ts_natCast_zero]; exact not_lt.2 (hrun.time_nonneg m)))
    (hsrc.above _) hGG (fun D ⟨C, ⟨j, hC, hj⟩, hDC⟩ => ?_) hB hGB
    (let ⟨x, hx, k, e', hv, hs', hext⟩ := hw; ⟨x, hx, k, e', hv, hs', hext⟩)
  obtain ⟨x', hx', k', e'', hve', -, hs'', Hd, hHd, hHdr, hCHd⟩ :=
    honest_supporter_upTo hrun hnc hpre hC
  exact ⟨x', hx', k', e'', hve', hs''.trans_le hj, Hd, hHd, hHdr, hDC.trans hCHd⟩

/-- The frozen witness at a vote needs only recipient service within its finite horizon. -/
theorem vote_frame_before {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H)
    (hBc : ∀ C j, OriginWithin tr H C j b → j ≤ s → Compatible (tr.HonestBlocks H) B C)
    (hw : ∃ x ∈ H, ∃ k e', SA.VoteAt tr.projAC x k e' ∧ e'.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  have hU := (projFG_localRun hrun hnc).coherent
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have h := hfb 0 0 (by simp) (by simpa [SAParams.ts] using hb)
    change Hᶜ.ncard < tr.honestAwakeJoined H (sp.ts 0 + 0) at h
    have hle : tr.honestAwakeJoined H (sp.ts 0 + 0) ≤ H.ncard :=
      Set.ncard_le_ncard fun x hx => hx.1
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hib' : ∀ k < i, tr.time k ≤ b := fun k hk => (hrun.time_mono hk.le).trans hib
  have hsrc : HonestRowsSourced tr H (fun D => ∃ C, (∃ j, OriginWithin tr H C j b ∧ j ≤ s) ∧
      Anc (tr.HonestBlocks H) D C) y i := by
    rw [honestRowsSourced_iff]
    intro X hX a ha hav
    obtain ⟨D, -, hDs, C, j, hC, hj, hDC⟩ := vote_row_source hrun hnc hf hy hc hs hX ha hav
    exact ⟨D, ⟨C, ⟨j, hC.within hib', hj⟩, hDC⟩, hDs⟩
  obtain ⟨hGG, hGB⟩ := below_tips_compatible hU
    (Q := fun C => ∃ j, OriginWithin tr H C j b ∧ j ≤ s)
    (fun C C' ⟨j, hC, hj⟩ ⟨j', hC', hj'⟩ =>
      originsBelowUpTo_iff.1 hP C j C' j' (by omega) (by omega) hC hC')
    (fun C ⟨j, hC, hj⟩ => hBc C j hC hj)
  refine vote_frame_of (s₀ := 0) hrun hnc (Or.inr hsync) hf hy hc hs hib
    (fun _ _ m _ _ hm _ => absurd hm (by rw [ts_natCast_zero]; exact not_lt.2 (hrun.time_nonneg m)))
    (hsrc.above _) hGG (fun D ⟨C, ⟨j, hC, hj⟩, hDC⟩ => ?_) hB hGB hw
  obtain ⟨x', hx', k', e'', hve', -, hs'', Hd, hHd, hHdr, hCHd⟩ :=
    honest_supporter_before hrun hnc hb hsync hfb hC
  exact ⟨x', hx', k', e'', hve', hs''.trans_le hj, Hd, hHd, hHdr, hDC.trans hCHd⟩

end Consensus.Goldilocks.Compose

end
