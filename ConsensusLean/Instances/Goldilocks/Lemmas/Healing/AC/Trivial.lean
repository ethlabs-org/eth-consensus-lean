module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ETimeOrder
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: held-vote stamps and the honest batch

Over the healthy setting, with `r = r_AC(ḡ)` (a slot `j` is `≥ r` exactly when `ḡ + 4Δ ≤ t_j`):

* **stamps of held votes** (`stamp_lt_of_held_of_runU`, `heldBefore_readPointU`);
* **the honest batch** (`honest_voters_halfU`): in a slot `≥ r` every honest node votes;
* **a fast lock's honest vote** (`fastLock_honest_voteU`). -/

namespace Consensus.Goldilocks.AC

variable {wm : AC.WriteMode}

variable {FGP : Type} {sp : ACParams} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP} {g : Time} {proposer : Nat → Fin sp.n}

/-! ## Helpers -/

private theorem lastWake_cases (y : Fin sp.n) : ∀ c, tr.lastWake y c = ⊥ ∨
    ∃ k ≤ c, tr.RestartAt y k ∧ tr.lastWake y c = (tr.time k : WithBot Time)
  | 0 => by
    unfold ACTrace.lastWake
    split_ifs with h
    · exact Or.inr ⟨0, le_rfl, h, rfl⟩
    · exact Or.inl rfl
  | c + 1 => by
    unfold ACTrace.lastWake
    split_ifs with h
    · exact Or.inr ⟨c + 1, le_rfl, h, rfl⟩
    · rcases lastWake_cases y c with h' | ⟨k, hk, hrk, h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨k, hk.trans (Nat.le_succ c), hrk, h'⟩

/-! ## Trivial frames: viability and `Carry` -/

/-! ## Trivial frames: blocks, stamps, relay and held votes -/

theorem ts_succ (s : Nat) : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
  simp only [ACParams.ts]; push_cast; ring

/-- A vote an honest node holds at cut `a` is held at every later cut `b` with no restart in
between, with a stamp before `T` when every cut before `a`, every own vote of its slot and every
restart are before `T`. With the unlock given. -/
theorem stamp_lt_of_held_of_runU
    {u : Nat → Set Lock} {ini} (hr : ACLocalRunU wm u H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y)) {y : Fin sp.n} (hy : y ∈ H)
    {a b : Nat} (hab : a ≤ b) {w : Vote sp.n} (hw : w ∈ (tr.state y a).pool w.slot) {T : Time}
    (hta : ∀ k < a, tr.time k < T) (hwT : sp.ts w.slot + sp.Δ < T)
    (hrestart : ∀ k < b, tr.RestartAt y k → tr.time k < T)
    (hnr : ∀ k, a ≤ k → k < b → ¬ tr.RestartAt y k) :
    w ∈ (tr.state y b).pool w.slot ∧ (tr.state y b).voteStamp w < ETime.of T := by
  have hmem := pool_monoU hr hy hab hnr w.slot hw
  refine ⟨hmem, ?_⟩
  rcases pool_originU hr hini hy b w hmem with
    ⟨k, hk, hsend, hst, -⟩ | ⟨k, hk, ℓ, hc, hcall, hst, -⟩
  · rw [hst, etime_of_lt_of]
    by_cases hka : k < a
    · exact hta k hka
    obtain ⟨ℓ, hc, ⟨e, he, rfl⟩ | ⟨-, hnh, -⟩⟩ := hsend
    · obtain ⟨-, hsl, -, -⟩ := castAt_specU hr hy ⟨hc, he⟩
      have := vote_time_leU hr hy ⟨ℓ, hc, he⟩
      rw [← hsl] at this
      linarith only [hwT, this]
    · exact absurd (pool_monoU hr hy (not_lt.1 hka) (fun k' h1 h2 => hnr k' h1 (h2.trans hk))
        _ hw) hnh
  · rw [hst, etime_of_lt_of]
    exact hrestart k hk ⟨ℓ, hc, hcall⟩

private theorem admitVote_pool_ne {A : ACState sp.n} {t : Time} {v : Vote sp.n} {σ : Nat}
    (h : v.slot ≠ σ) : (admitVote sp A t v).pool σ = A.pool σ := by
  unfold admitVote
  split_ifs
  · rfl
  · rfl
  · exact Function.update_of_ne (Ne.symm h) _ _

private theorem admitVote_stamp_ne {A : ACState sp.n} {t : Time} {v w : Vote sp.n}
    (h : w ≠ v) : (admitVote sp A t v).voteStamp w = A.voteStamp w := by
  unfold admitVote
  split_ifs
  · rfl
  · rfl
  · exact Function.update_of_ne h _ _

private theorem optimistic_pool_stamp (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).pool = A.pool ∧
      (optimisticConfirmation sp A Φ t).voteStamp = A.voteStamp := by
  unfold optimisticConfirmation updateLatestConfirmed; split
  · exact ⟨rfl, rfl⟩
  · split_ifs <;> exact ⟨rfl, rfl⟩

/-- **A vote of another slot that the state after a vote branch holds, the branch's read point
held**, with its stamp, whether or not the node may vote in the slot. With the unlock given. -/
theorem heldBefore_readPoint_branchU
    {u : Nat → Set Lock} {ini} (hr : ACLocalRunU wm u H U tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksAC sp FGP)}
    {R : ACState sp.n} (hb : VoteBranchAt tr y i ℓ R) {w : Vote sp.n}
    (hne : sp.slot (tr.time i) ≠ w.slot) {T : Time}
    (h : w ∈ (tr.state y (i + 1)).pool w.slot ∧ (tr.state y (i + 1)).voteStamp w < ETime.of T) :
    HeldBefore R w T := by
  have hst : tr.state y (i + 1) = tr.post i := by
    simp [Trace.state, hb.callAt.1, hb.callAt.2]
  rw [hst] at h
  rcases post_of_voteBranchAtU hr hy hb with ⟨-, -, hpost⟩ | ⟨-, e, -, -, -, hsl, hpost⟩
  · rw [hpost] at h
    exact h
  · rw [← hsl] at hne
    rw [hpost, (optimistic_pool_stamp _ _ _).1, (optimistic_pool_stamp _ _ _).2,
      admitVote_pool_ne hne, admitVote_stamp_ne fun h' => hne (by rw [h'])] at h
    exact h

/-- A vote of another slot that the state after an honest cast holds, it held at the read point,
with its stamp. With the unlock given. -/
theorem heldBefore_readPointU
    {u : Nat → Set Lock} {ini} (hr : ACLocalRunU wm u H U tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksAC sp FGP)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) {w : Vote sp.n} (hne : e.msg.slot ≠ w.slot) {T : Time}
    (h : w ∈ (tr.state y (i + 1)).pool w.slot ∧ (tr.state y (i + 1)).voteStamp w < ETime.of T) :
    HeldBefore e.readPoint w T :=
  heldBefore_readPoint_branchU hr hy (voteBranchAt_of_castAtU hr hy hc)
    ((castAt_specU hr hy hc).2.1 ▸ hne) h

/-- Every honest member of the slot's committee has an actual vote by the bounded slot deadline
(the committee start lets it vote there). Restart bounds are required only before that deadline,
at the join threshold for this slot. -/
theorem honest_votes_in_slot_before {K : AC.CommitteeDict sp.n} {b : Time}
    (hS : HealthyBaseUpTo K tr H U proposer g b)
    {m : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) (hmb : sp.ts m + sp.Δ ≤ b)
    (hrestart : ∀ x ∈ H, ∀ r, tr.time r ≤ sp.ts m + sp.Δ → tr.RestartAt x r →
      tr.time r ≤ sp.ts ((m : Int) - 1)) :
    ∀ x ∈ H, x ∈ K.committee m →
      ∃ j e, VoteAt tr x j e ∧ e.msg.slot = m ∧ tr.time j ≤ sp.ts m + sp.Δ := by
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  have hg0 := AC.gbar_nonneg g
  intro x hx hxK
  have hslot : sp.slot (sp.ts m + sp.Δ) = m := by
    apply slot_of_mem sp m (by linarith)
    simp only [ACParams.ts]; push_cast; linarith
  obtain ⟨c, ell, hc, hcall, htc⟩ := hS.driven.tick x hx (sp.ts m + sp.Δ) (by linarith)
    ⟨4 * m + 1, by simp only [ACParams.ts]; ring⟩ (hS.awake x hx _ (by linarith) hmb)
  have hj : joined sp (tr.state x c) (tr.time c) := by
    unfold joined
    rcases restartTime_stateU hr.toU hS.run.vstart hx c with h | ⟨r, hrc, hrs, h⟩
    · rw [h]; exact bot_le
    · rw [h]
      apply WithBot.coe_le_coe.mpr
      rw [htc, hslot]
      exact hrestart x hx r ((hr.time_mono hrc.le).trans htc.le) hrs
  by_cases hv : (tr.state x c).votedSlot = (sp.slot (tr.time c) : Int)
  · obtain ⟨j, hjc, e, he, hes⟩ :=
      (cast_of_votedSlotU hr.toU hS.run.vstart hx c _ hv).resolve_right
        (by rw [(trace_mayVote_iff hr hx c _).2 (by rw [htc, hslot]; exact hxK)]; decide)
    exact ⟨j, e, he, by rw [hes, htc, hslot], (hr.time_mono hjc.le).trans htc.le⟩
  · have hT : tr.time c = sp.ts (sp.slot (tr.time c)) + sp.Δ := by rw [htc, hslot]
    obtain ⟨e, hem, hes⟩ := tryVote_votes x ell.frame hj hv hT
      ((trace_mayVote_iff hr hx c _).2 (by rw [htc, hslot]; exact hxK))
    have he := hr.exec c ell hc.2 (hc.1 ▸ hx)
    rw [hc.1, hcall] at he
    have h2 : (acOnTick sp x (tr.state x c) ell.frame (tr.time c)).2 = ell.emits :=
      congrArg Prod.snd he
    have h3 : (acOnTick sp x (tr.state x c) ell.frame (tr.time c)).2 =
        (tryVote sp x (tr.state x c) ell.frame (tr.time c)).2 := by
      unfold acOnTick
      dsimp only
      split_ifs
      all_goals first | rfl | exact absurd hj ‹_›
    exact ⟨c, e, ⟨ell, hc, h2 ▸ h3 ▸ hem⟩, by rw [hes, htc, hslot], htc.le⟩

/-- The bounded actual honest vote batch occupies at least half the committee size: it holds the
honest members of the slot's committee, fewer than half of which is faulty. -/
theorem honest_voters_half_before {K : AC.CommitteeDict sp.n} {b : Time}
    (hS : HealthyBaseUpTo K tr H U proposer g b)
    {m : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) (hmb : sp.ts m + sp.Δ ≤ b)
    (hrestart : ∀ x ∈ H, ∀ r, tr.time r ≤ sp.ts m + sp.Δ → tr.RestartAt x r →
      tr.time r ≤ sp.ts ((m : Int) - 1)) :
    sp.committeeSize ≤ 2 * {x | x ∈ H ∧ ∃ j e, VoteAt tr x j e ∧ e.msg.slot = m ∧
      tr.time j ≤ sp.ts m + sp.Δ}.ncard := by
  have hall := honest_votes_in_slot_before hS hm hmb hrestart
  have hle := Set.ncard_le_ncard (s := K.committee m ∩ H)
    (t := {x | x ∈ H ∧ ∃ j e, VoteAt tr x j e ∧ e.msg.slot = m ∧
      tr.time j ≤ sp.ts m + sp.Δ}) fun x hx => ⟨hx.2, hall x hx.2 hx.1⟩
  have hsplit : (K.committee m ∩ H).ncard + (K.committee m ∩ Hᶜ).ncard = sp.committeeSize := by
    rw [← hS.hsize m]
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)
  have hΔ := sp.toParams.hΔ
  have hf := hS.cs2 m (by linarith) (by linarith)
  omega

/-- `honest_votes_in_slot` with the unlock given. -/
theorem honest_votes_in_slotU
    {u : Nat → Set Lock} (hS : HealthyBaseU wm u tr H U proposer g) {m : Nat}
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) : ∀ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = m := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hg0 := AC.gbar_nonneg g
  intro x hx
  have hslot : sp.slot (sp.ts m + sp.Δ) = m := by
    refine slot_of_mem sp m (by linarith) ?_
    rw [show sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ by simp only [ACParams.ts]; push_cast; ring]
    linarith
  obtain ⟨c, ℓ, hc, hcall, htc⟩ := hS.driven.tick x hx (sp.ts m + sp.Δ) (by linarith)
    ⟨4 * m + 1, by simp only [ACParams.ts]; ring⟩ (hS.awake hx (by linarith))
  have hj := hS.joined_state hx c (by rw [htc, hslot, ts_sub_one]; linarith)
  by_cases hv : (tr.state x c).votedSlot = (sp.slot (tr.time c) : Int)
  · obtain ⟨j, -, e, he, hes⟩ :=
      (cast_of_votedSlotU hr (fun _ => voteStart_initial _) hx c _ hv).resolve_right
        (by rw [traceWithM_mayVote hr hx c]; decide)
    exact ⟨j, e, he, by rw [hes, htc, hslot]⟩
  · have hT : tr.time c = sp.ts (sp.slot (tr.time c)) + sp.Δ := by rw [htc, hslot]
    obtain ⟨e, hem, hes⟩ := tryVote_votesWith x ℓ.frame hj hv hT (traceWithM_mayVote hr hx c _)
    have he := hr.exec c ℓ hc.2 (hc.1 ▸ hx)
    rw [hc.1, hcall] at he
    have h2 : (acOnTickWithM sp wm x (u c) (tr.state x c) ℓ.frame (tr.time c)).2 = ℓ.emits :=
      congrArg Prod.snd he
    have h3 : (acOnTickWithM sp wm x (u c) (tr.state x c) ℓ.frame (tr.time c)).2 =
        (tryVoteWithM sp wm x (u c) (tr.state x c) ℓ.frame (tr.time c)).2 := by
      unfold acOnTickWithM
      dsimp only
      split_ifs
      all_goals first | rfl | exact absurd hj ‹_›
    exact ⟨c, e, ⟨ℓ, hc, h2 ▸ h3 ▸ hem⟩, by rw [hes, htc, hslot]⟩

/-- **Every honest node votes** in a slot `m ≥ r` (the honest batch): it is awake and
joined at `t_m + Δ`, runs its tick there (`Driven`), and `try_vote` votes unless it voted in slot
`m` already. -/
theorem honest_votes_in_slot (hS : HealthyBase tr H U proposer g) {m : Nat}
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) : ∀ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = m :=
  honest_votes_in_slotU (hS := hS.toU) (m := m) (hm := hm)

/-- **The honest batch** (it has `n − f > n/2` seats): in a slot `m ≥ r` every honest node votes (it
is awake and joined at `t_m + Δ`, runs its tick there (`Driven`), and `try_vote` votes unless it
voted in slot `m` already), so the honest voters of slot `m` are at least half of the committee.
With the unlock given. -/
theorem honest_voters_halfU
    {u : Nat → Set Lock} (hS : HealthyBaseU wm u tr H U proposer g) {m : Nat}
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) :
    sp.n ≤ 2 * {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = m}.ncard := by
  have hall := honest_votes_in_slotU hS hm
  have hle := Set.ncard_le_ncard (s := H)
    (t := {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = m}) fun x hx => ⟨hx, hall x hx⟩
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have := hS.two_faulty_lt
  omega

/-- `fastLock_honest_vote` with the unlock given. -/
theorem fastLock_honest_voteU
    {uL : Nat → Set Lock} {ini} (hrun : ACRunU wm uL proposer tr H U ini) (K : CommitteeDict sp.n)
    (hP : CommitteeP K tr H) {x : Fin sp.n}
    (hx : x ∈ H) {i₀ s : Nat} {B : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hfl : FastLockAt tr x i₀ s B CV)
    (hf : 2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize) :
    ∃ z ∈ H, ∃ j e, VoteAt tr z j e ∧ e.msg.slot = s ∧ VoteExtends U e.msg B := by
  have hr := hrun.localRun
  rcases hfl with ⟨ℓ, C, ⟨hc, -⟩, -, hD, -⟩ | ⟨ℓ, A, hpt, hsl, hsel, -⟩
  · obtain ⟨-, hΦU⟩ := frameIn_of_callAtU hr hx hc
    have hfast := (deepest_mem hD).1.2.2
    unfold FastTest confirmationScore at hfast
    dsimp only at hfast
    have hlt := Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le hf hfast)
    obtain ⟨u, ⟨-, v, ⟨hvp, -⟩, rfl, -, R, hR, hRr, hBR⟩, hu⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard hlt
    -- the supporter is a pool voter, so a committee member, so honest
    have hvH : v.val ∈ H := by
      by_contra h
      exact hu ⟨hP.1 x hx i₀ s v hvp, h⟩
    obtain ⟨j, -, e, hve, rfl⟩ := hrun.honest.pool_vote x hx i₀ s _ hvp hvH
    exact ⟨_, hvH, j, e, hve, state_pool_slotU sp hr hrun.vstart hx i₀ s _ hvp, R, hΦU hR, hRr,
      Anc.mono hΦU hBR⟩
  · obtain ⟨-, hΦU⟩ := frameIn_of_callAtU hr hx hpt.1
    unfold optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    have h34 := (deepest_mem hsel).1.2.1
    rw [hsl] at h34
    have hOK : optimisticVoters sp A ℓ.frame s B ⊆ K.committee s :=
      fun _ ⟨v, hv, hvu, _⟩ => hvu ▸ hP.2 x hx i₀ ℓ A hpt s v hv
    have hlt : (K.committee s ∩ Hᶜ).ncard < (optimisticVoters sp A ℓ.frame s B).ncard := by
      omega
    obtain ⟨u, hu, huF⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
    have huH : u ∈ H := by_contra fun h => huF ⟨hOK hu, h⟩
    rw [← hsl] at hu
    obtain ⟨v, hv, rfl, R, hR, hRr, hBR⟩ := hu
    obtain ⟨hvs, j, -, e, hve, rfl⟩ := optimisticPoint_pool_voteU hrun hx hpt hv huH
    exact ⟨_, huH, j, e, hve, hvs.trans hsl, R, hΦU hR, hRr, Anc.mono hΦU hBR⟩

/-- A fast lock of an honest node is extended by an honest vote of its slot: the fast test
counts at least half of the committee size in non-equivocating supporters, an optimistic
confirmation three quarters of it in voters, all committee members (P), and fewer than half of
the slot committee is faulty. -/
theorem fastLock_honest_vote {ini}
    (hrun : ACRun proposer tr H U ini) (K : CommitteeDict sp.n) (hP : CommitteeP K tr H)
    {x : Fin sp.n}
    (hx : x ∈ H) {i₀ s : Nat} {B : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hfl : FastLockAt tr x i₀ s B CV)
    (hf : 2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize) :
    ∃ z ∈ H, ∃ j e, VoteAt tr z j e ∧ e.msg.slot = s ∧ VoteExtends U e.msg B :=
  fastLock_honest_voteU hrun.toU K hP hx hfl hf

/-! ## A fast origin of label `≥ r` transfers -/

end Consensus.Goldilocks.AC

end
