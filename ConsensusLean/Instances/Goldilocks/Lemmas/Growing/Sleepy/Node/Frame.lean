module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.LiftFrame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Groups
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy` with growing faults: honest rows and their sources

`HonestRowsSourcedAt tr H G y i`: every attestation of a block in the tree of `y` before cut `i`
whose signer is honest at `tr.time i` has a source satisfying `G`, held by a node honest at
`tr.time i` at a cut `k ≤ i` (the signers and the source holder are classified at the reading cut,
Lemma G). The frame lemmas of `Compose/Sleepy/Frame` lift at the cut's time `d = tr.time i`, with
`2 f_d < n`; their honest sources are held while honest at `d` (`IsHonestSourceAt`). -/

/-! ### Static pieces of `no_optimistic_before_held_row_of` (copied, private) -/

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


/-- The `t_{s+1} + Δ` case of `no_optimistic_before_held_row_of`: an honest slot-`(s+1)` voter
accepted, before its vote, no block whose honest row was signed at `t_{s+1} + Δ`. -/
private theorem held_row_late_absurd (hrun : GoldilocksRun proposer dg H tr)
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
  have hti' : tr.time i ≤ sp.ts s + 5 * sp.Δ := by
    have h : tr.time i ≤ sp.ts (e.msg.slot : Int) + sp.Δ := (cast_head_fcRoot hr hy hc).2
    rw [hs] at h
    simp only [SAParams.ts] at h ⊢
    push_cast at h
    linarith only [h]
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

/-- The `t_{s+1}` case of `no_optimistic_before_held_row_of`: an honest optimistic check of slot
`s + 1` before an honest signing at `t_{s+1}` leaves `n = 1`, with an honest slot-`(s+1)` voter at
a cut no later than the check. -/
private theorem held_row_early_count (hrun : GoldilocksRun proposer dg H tr)
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
  have hc0 : sp.ts s + 4 * sp.Δ ≤ tr.time c := by
    have h := (SA.ts_le_iff_le_slot sp (hr.time_nonneg c) ((s + 1 : Nat) : Int)).2
      (le_of_eq (by rw [hslc]))
    have h' : sp.ts ((s + 1 : Nat) : Int) ≤ tr.time c := h
    simp only [SAParams.ts] at h' ⊢
    push_cast at h'
    linarith only [h']
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
      have h := (SA.ts_le_iff_le_slot sp (hr.time_nonneg j') ((s + 1 : Nat) : Int)).2
        (le_of_eq (congrArg (Nat.cast : Nat → Int) hsl'.symm))
      have h' : sp.ts ((s + 1 : Nat) : Int) ≤ tr.time j' := h
      simp only [SAParams.ts] at h'
      push_cast at h'
      rw [hT0]; simp only [SAParams.ts]; linarith only [h']
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

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- The honest rows of `y`'s tree before cut `i` are sourced in `G`, classified at `tr.time i`. -/
def HonestRowsSourcedAt (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop) (y : Fin sp.n) (i : Nat) : Prop :=
  ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H (tr.time i) →
    ∃ D, G D ∧ ∃ x k, x ∈ H (tr.time i) ∧ k ≤ i ∧ D ∈ (tr.state x k).fg.tree ∧
      ((tr.state x k).fg.σ D.root).Th = a.T

theorem honestRowsSourcedAt_iff {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} {y : Fin sp.n} {i : Nat} :
    HonestRowsSourcedAt tr H G y i ↔
      ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H (tr.time i) →
        ∃ D, G D ∧ ∃ x k, x ∈ H (tr.time i) ∧ k ≤ i ∧ D ∈ (tr.state x k).fg.tree ∧
          ((tr.state x k).fg.σ D.root).Th = a.T :=
  Iff.rfl

/-- `D` is the source of target `T` held, while honest at `d`, by a node before a cut whose earlier
cuts are at times `≤ d`. -/
def IsHonestSourceAt (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (D : SA.Blk sp.n (List (FG.Att sp.n))) (T : Nat) (d : Time) : Prop :=
  ∃ x k, x ∈ H d ∧ (∀ k' < k, tr.time k' ≤ d) ∧ D ∈ (tr.state x k).fg.tree ∧
    ((tr.state x k).fg.σ D.root).Th = T

theorem isHonestSourceAt_iff {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {T : Nat} {d : Time} :
    IsHonestSourceAt tr H D T d ↔ ∃ x k, x ∈ H d ∧ (∀ k' < k, tr.time k' ≤ d) ∧
      D ∈ (tr.state x k).fg.tree ∧ ((tr.state x k).fg.σ D.root).Th = T :=
  Iff.rfl

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- An honest source of the prefix through `d` is an honest source held while honest at `d`. -/
theorem isHonestSourceAt_of_upTo (hrun : Growing.GoldilocksRun proposer dg H tr) {d : Time}
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {T : Nat}
    (h : Compose.IsHonestSource (tr.upTo d) (H d) D T) : IsHonestSourceAt tr H D T d := by
  obtain ⟨x, hx, k, hDt, hT⟩ := Compose.isHonestSource_iff.1 h
  obtain ⟨i₀, -, hb, hs⟩ := Trace.upTo_state_exists tr hrun.time_mono x k
  rw [hs] at hDt hT
  exact ⟨x, i₀, hx, hb, hDt, hT⟩

/-- The honest rows sourced at cut `i` are the honest rows of the prefix through `tr.time i`. -/
theorem HonestRowsSourcedAt.upTo (hrun : Growing.GoldilocksRun proposer dg H tr)
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} {y : Fin sp.n} {i : Nat}
    (h : HonestRowsSourcedAt tr H G y i) :
    Compose.HonestRowsSourced (tr.upTo (tr.time i)) (H (tr.time i)) G y i := by
  have hm := hrun.time_mono
  refine Compose.honestRowsSourced_iff.2 fun X hX a ha hav => ?_
  rw [Trace.upTo_state tr y fun _ hk => hm hk.le] at hX
  obtain ⟨D, hD, x, k, hx, hki, hDt, hT⟩ := h X hX a ha hav
  have hst : (tr.upTo (tr.time i)).state x k = tr.state x k :=
    Trace.upTo_state tr x fun _ hk' => hm (hk'.le.trans hki)
  exact ⟨D, hD, Compose.isHonestSource_iff.2 ⟨x, hx, k, by rw [hst]; exact hDt,
    by rw [hst]; exact hT⟩⟩

/-- **An honest row was signed while honest** (`honest_row_signed_before` at `d = tr.time i`): an
attestation of a block in the tree of a node honest at cut `i`, whose signer is honest at `i`, was
signed at an earlier cut, at which its signer was honest, before the block's acceptance. -/
theorem honest_row_signed_before_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y i).fg.tree)
    {a : FG.Att sp.n} (ha : a ∈ X.fgPayload) (hav : a.val ∈ H (tr.time i)) :
    ∃ m < i, tr.AcceptAt y m X ∧ ∃ k < m, tr.SignAt a.val k a ∧ a.val ∈ H (tr.time k) := by
  have hm := hrun.time_mono
  obtain ⟨m, hmi, hA, k, hkm, hS⟩ := honest_row_signed_before
    (hrun.upTo (hrun.time_nonneg i)) (hnc.upTo _) hy
    (by rw [Trace.upTo_state tr y fun _ hk => hm hk.le]; exact hX) ha hav
  obtain ⟨-, hA⟩ := (RunTrace.upTo_acceptAt tr).mp hA
  obtain ⟨hkd, hS⟩ := (RunTrace.upTo_signAt tr).mp hS
  exact ⟨m, hmi, hA, k, hkm, hS, hrun.antitone hkd hav⟩

/-- **The justification has an honest source** (`justified_honest_source_before` at the cut's time
`d`, with `2 f_d < n`): at `h_j ≥ 1`, `Σ.J` of a node honest at cut `i` is an entry block of height
`h_j`, and its target has a source satisfying `G`, held while honest at `d`. -/
theorem justified_honest_source_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n) {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : HonestRowsSourcedAt tr H G y i) (hj : 1 ≤ (tr.state y i).fg.hj) :
    ((tr.state y i).fg.σ (tr.state y i).fg.J.root).h = (tr.state y i).fg.hj ∧
      ((tr.state y i).fg.σ (tr.state y i).fg.J.root).Th = (tr.state y i).fg.J.root ∧
      ∃ D, G D ∧ IsHonestSourceAt tr H D (tr.state y i).fg.J.root (tr.time i) := by
  have hst := Trace.upTo_state tr y (d := tr.time i) fun _ hk => hrun.time_mono hk.le
  have h := justified_honest_source_before (hrun.upTo (hrun.time_nonneg i)) (hnc.upTo _) hf hy
    (hsrc.upTo hrun) (by rw [hst]; exact hj)
  rw [hst] at h
  obtain ⟨h1, h2, D, hD, hDs⟩ := h
  exact ⟨h1, h2, D, hD, isHonestSourceAt_of_upTo hrun hDs⟩

/-- **A crossing of a held block has an honest source** (`frame_crossing_source_before` at the
cut's time `d`, with `2 f_d < n`). -/
theorem frame_crossing_source_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n) {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : HonestRowsSourcedAt tr H G y i)
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hW : W ∈ (tr.state y i).fg.tree) {j : Nat}
    (hj1 : 1 ≤ j) (hj2 : j < ((tr.state y i).fg.σ W.root).h) :
    ∃ E ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc E W ∧
      ((tr.state y i).fg.σ E.root).h = j ∧ ((tr.state y i).fg.σ E.root).Th = E.root ∧
      ∃ D, G D ∧ IsHonestSourceAt tr H D E.root (tr.time i) := by
  have hst := Trace.upTo_state tr y (d := tr.time i) fun _ hk => hrun.time_mono hk.le
  have h := frame_crossing_source_before (hrun.upTo (hrun.time_nonneg i)) (hnc.upTo _) hf hy
    (hsrc.upTo hrun) (W := W) (by rw [hst]; exact hW) hj1 (by rw [hst]; exact hj2)
  rw [hst] at h
  obtain ⟨E, hE, hEW, hEh, hET, D, hD, hDs⟩ := h
  exact ⟨E, hE, hEW, hEh, hET, D, hD, isHonestSourceAt_of_upTo hrun hDs⟩

/-- **No optimistic check before a held row** under growing faults (R, the count at the check's
cut `c`): at a slot-`(s+1)` vote of a node honest at its cut `i`, no block accepted at `m < i` holds
an attestation, by a signer honest at `m`, signed at `k < m` after an optimistic check of slot
`s + 1` at `c < k` by a node honest at `c`, when `2 f_{t_c} < n`. The signing is at `t_{s+1}` or
`t_{s+1} + Δ`. At `t_{s+1} + Δ` the voter's own tick votes before the block arrives (on the prefix
through `tr.time i`); at `t_{s+1}` the check's honest seats are the slot's proposer, so `n = 1`
(on the prefix through `tr.time c`), and the voter has a second slot-`(s+1)` vote. -/
theorem no_optimistic_before_held_row_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} {s : Nat} (hy : y ∈ H (tr.time i))
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) {m : Nat}
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hacc : tr.AcceptAt y m X) (hmi : m < i)
    {a : FG.Att sp.n} (hav : a.val ∈ H (tr.time m)) {k : Nat} (hkm : k < m)
    (hsign : tr.SignAt a.val k a) {z : Fin sp.n} {c : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)} (hz : z ∈ H (tr.time c))
    (hck : c < k) (hO : SA.OptimisticLockAt tr.projAC z c (s + 1) C CV)
    (hf : 2 * (H (tr.time c))ᶜ.ncard < sp.n) : False := by
  have hm := hrun.time_mono
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hti' : tr.time i ≤ sp.ts s + 5 * sp.Δ := by
    have h : tr.time i ≤ sp.ts (e.msg.slot : Int) + sp.Δ := (cast_head_fcRoot_at hrun hnc hy hc).2
    rw [hs] at h
    simp only [SAParams.ts] at h ⊢
    push_cast at h
    linarith only [h]
  obtain ⟨ℓO, AO, -, hslc, -⟩ := id hO
  change sp.slot (tr.time c) = s + 1 at hslc
  have hc0 : sp.ts s + 4 * sp.Δ ≤ tr.time c := by
    have h := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg c) ((s + 1 : Nat) : Int)).2
      (le_of_eq (by rw [hslc]))
    have h' : sp.ts ((s + 1 : Nat) : Int) ≤ tr.time c := h
    simp only [SAParams.ts] at h' ⊢
    push_cast at h'
    linarith only [h']
  have hck' := hm hck.le
  have hkm' := hm hkm.le
  have hmi' := hm hmi.le
  obtain ⟨src, hsgc⟩ := id hsign
  obtain ⟨q, hq⟩ := Compose.sign_at_public (hrun.upTo (hrun.time_nonneg k)) (hrun.antitone hkm' hav)
    ((Trace.upTo_callAt_of_le tr le_rfl).mpr hsgc)
  have hq' : tr.time k = sp.Δ * q := hq
  have hq1 : 4 * (s : Int) + 4 ≤ q := by
    by_contra h
    have : q + 1 ≤ 4 * (s : Int) + 4 := by omega
    simp only [SAParams.ts] at hc0
    linarith only [hc0, hck', hq', hΔ, mul_le_mul_of_nonneg_left this hΔ.le]
  have hq2 : q ≤ 4 * (s : Int) + 5 := by
    by_contra h
    have : 4 * (s : Int) + 6 ≤ q := by omega
    simp only [SAParams.ts] at hti'
    linarith only [hti', hkm', hmi', hq', hΔ, mul_le_mul_of_nonneg_left this hΔ.le]
  rcases (show q = 4 * (s : Int) + 5 ∨ q = 4 * (s : Int) + 4 by omega) with hq5 | hq4
  · have hT : tr.time k = sp.ts s + 5 * sp.Δ := by
      rw [hq', hq5]; simp only [SAParams.ts]; ring
    exact Compose.held_row_late_absurd (hrun.upTo (hrun.time_nonneg i)) (hnc.upTo _) hy
      (by rw [RunTrace.upTo_projAC]; exact sa_castAt_upTo.mpr ⟨le_rfl, hc⟩) hs
      ((RunTrace.upTo_acceptAt tr).mpr ⟨hmi', hacc⟩) hmi hkm hT
  · have hT0 : tr.time k = sp.ts s + 4 * sp.Δ := by
      rw [hq', hq4]; simp only [SAParams.ts]; ring
    obtain ⟨hn1, u, hu, j', hj', e', hv', hs'⟩ := Compose.held_row_early_count
      (hrun.upTo (hrun.time_nonneg c)) (hnc.upTo _) hf (hrun.antitone (hck'.trans hkm') hav)
      ((RunTrace.upTo_signAt tr).mpr ⟨hT0.trans_le hc0, hsign⟩) hT0 hz hck
      (by rw [RunTrace.upTo_projAC]; exact (sa_optimisticLockAt_upTo hm).mpr ⟨le_rfl, hO⟩)
    rw [RunTrace.upTo_projAC] at hv'
    obtain ⟨hjd, hv'⟩ := sa_voteAt_upTo.mp hv'
    obtain rfl : u = y := Fin.ext (by have := u.isLt; have := y.isLt; omega)
    have := (one_vote_per_slot_at hrun hnc (hVoteAt_iff.2 ⟨hrun.antitone hjd hu, hv'⟩)
      (hVoteAt_iff.2 ⟨hy, ℓ, hc.1, hc.2⟩) (hs'.trans hs.symm)).1
    omega

end Consensus.Goldilocks.Compose.Growing

end
