module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Carry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer

public section

/-! # Goldilocks Healing: H.2, `Inv` at a vote, `Carry` for a batch

Under H.2's premises (`InclusionRun`, which extends H.1's `HealthyBase`, so H.1's honest-batch
lemmas apply as they are): `Inv` at a vote not covered by `Φ.F` gives the viability of a
protected block and `Φ.F ⪯ B` (`inv_at_vote`); and `Carry_y` for an honest batch extending `B`
(`h2_carry_votes`, §5's transport: relay after `ḡ`, `Catch(2Δ)` before); every honest node is a
voter at an honest update (`honest_voter_at_update`), so a result has an honest supporter
(`result_honest_supporter`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g t₀ : Time} {proposer : Nat → Fin sp.n}


/-- `Carry_y` for a set of votes is `Carry_y` for each of them (the fields are per vote), at a
vote where `y` is awake and joined. -/
theorem carryAt_of_each {y : Fin sp.n} {i : Nat} {e : Em sp FGP} {s : Nat}
    {CV : Set (Vote sp.n)} (ha : tr.awake y (tr.time i)) (hj : joined sp e.readPoint (tr.time i))
    (h : ∀ v ∈ CV, CarryAt tr U y i e s {v}) : CarryAt tr U y i e s CV :=
  ⟨ha, hj, fun v hv => (h v hv).heads v rfl, fun v hv => (h v hv).holds v rfl⟩

/-- A block between `Φ.F` and a block of a well-formed frame tree (inside a coherent `U`
containing the tree) is in the tree. -/
theorem mem_tree_of_between {Φ : Frm sp.n FGP} (hU : Coherent U) (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {B C : Blk sp.n FGP} (hFB : Anc U Φ.F B) (h : Anc U B C) :
    C ∈ Φ.tree → B ∈ Φ.tree := by
  induction h with
  | refl => exact id
  | @tail c d hBc e ih =>
    intro hd
    by_cases hdF : d = Φ.F
    · subst hdF
      obtain rfl := Anc.antisymm hU (hBc.tail e) hFB
      exact hd
    obtain rfl | ⟨q, -, hq⟩ :=
      (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hΦ.rooted.2 d hd)
    · exact absurd rfl hdF
    have hqc : q = c := hU.1 (hΦU hq.1) e.1 (Option.some_injective _ (hq.2.2.symm.trans e.2.2))
    subst hqc
    exact ih hq.1

/-- **`Inv` at a vote not covered by `Φ.F`**: for a protected `(B, j)` and an honest vote at a
time `≥ t_{j+1}` whose frame's `Φ.F` does not extend `B`, `B` is viable at the vote and
`Φ.F ⪯ B`. -/
theorem inv_at_vote (hI : InclusionRun tr H U proposer g t₀) {B : Blk sp.n FGP} {j : Nat}
    (hB : Protected proposer tr H t₀ B j) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y k ℓ e)
    (ht : sp.ts (j + 1 : Nat) ≤ tr.time k) (hBF : ¬ Anc U B ℓ.frame.F) :
    ViableAtVote ℓ e e.msg.slot B ∧ Anc U ℓ.frame.F B := by
  have hr := hI.run.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc.1
  have hfcU := (hΦ.rooted.2 _ hΦ.fcRoot_mem).mono hΦU
  rcases (hI.inv B j hB y hy k ℓ hc.1 ht).2 e hc.2 with h | h
  · exact ⟨Or.inl h, (hΦ.rooted.2 B h.1.1).mono hΦU⟩
  · have hFB : Anc U ℓ.frame.F B := by
      rcases anc_total hU h hfcU with h' | h'
      · exact absurd h' hBF
      · exact h'
    refine ⟨Or.inr ?_, hFB⟩
    exact anc_tree_of_anc_U hU hΦ hΦU (mem_tree_of_between hU hΦ hΦU hFB h hΦ.fcRoot_mem) h
      hΦ.fcRoot_mem

/-- **`Carry` for an honest batch extending `B`** (§6.1, later labels; §5's transport): at an
honest vote of slot `m + 1` with `Φ.F ⪯ B`, where `t_m ≥ ḡ + 4Δ` and every honest vote of slot `m`
extends `B`, `Carry_y` holds for the honest slot-`m` votes (each sent by its voter by
`t_m + Δ`, its head in the voter's frame, accepted after `ḡ` or caught up by `Catch(2Δ)`). -/
theorem h2_carry_votes (hI : InclusionRun tr H U proposer g t₀) {m : Nat}
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) {B : Blk sp.n FGP}
    (hvB : ∀ x ∈ H, ∀ k e, VoteAt tr x k e → e.msg.slot = m → VoteExtends U e.msg B)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = m + 1) (hFB : Anc U ℓ.frame.F B) :
    CarryAt tr U y i e m {v | ∃ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = m} := by
  have hr := hI.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨-, hsl, hyj, -⟩ := castAt_spec hr hy hc
  have hti : sp.ts (m + 1 : Nat) ≤ tr.time i :=
    (ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by rw [← hsl, hs])
  have hts : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  refine carryAt_of_each (hr.awake_of_call y hy i ℓ hc.1) hyj fun v hv => ?_
  obtain ⟨x, hx, j, e', ⟨ℓ', hc', he'⟩, rfl, hvs⟩ := hv
  obtain ⟨-, hsl', -, -⟩ := castAt_spec hr hx ⟨hc', he'⟩
  have htj := vote_time_le hr hx ⟨ℓ', hc', he'⟩
  rw [← hsl', hvs] at htj
  have hjt : sp.ts m ≤ tr.time j :=
    (ts_le_iff_le_slot sp (hr.time_nonneg j) _).2 (by rw [← hsl', hvs])
  obtain ⟨Hd, hHd, hHdr, hBHd⟩ := hvB x hx j e' ⟨ℓ', hc', he'⟩ hvs
  obtain ⟨Hd', hHd', hHd'r, -⟩ := honest_head_frame hr hx ⟨hc', he'⟩
  obtain rfl : Hd' = Hd :=
    hU.1 ((frameIn_of_callAt hr hx hc').2 hHd') hHd (hHd'r.trans hHdr.symm)
  refine carryAt_of_writer_catch hr (hI.syncAC le_rfl (sp.ts m + 2 * sp.Δ))
    (by linarith) le_rfl hx hy hc hs fun v' hv' => ?_
  rw [Set.mem_singleton_iff] at hv'
  subst hv'
  refine ⟨hvs, ⟨j, ⟨ℓ', hc', Or.inl ⟨e', he', rfl⟩⟩, hjt, by linarith⟩, Hd', hHd, hHdr,
    hFB.trans hBHd, ?_⟩
  rcases Compose.frame_anc_accepted hr hx j ℓ' hc' Hd' hHd' Hd' Relation.ReflTransGen.refl with
    hg | ⟨k, hk, hacc⟩
  · exact Or.inl hg
  have hkt := hr.time_mono hk
  by_cases hkg : gbar g ≤ tr.time k
  · exact Or.inr (Or.inl ⟨k, hacc, hkg, by linarith⟩)
  · obtain ⟨k', hk', hacc', hk't⟩ := hI.catchUp x hx k Hd' hacc (not_le.1 hkg) y hy i ℓ hc.1
      (by linarith) (hFB.trans hBHd)
    exact Or.inr (Or.inr ⟨k', hk', hacc', by linarith⟩)

private theorem optimistic_pool (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).pool = A.pool := by
  unfold optimisticConfirmation updateLatestConfirmed
  split
  · rfl
  · split_ifs <;> rfl

/-- **An honest node is a voter at every honest update** of a slot `l` with `t_l ≥ ḡ + 4Δ`: its
slot-`l` vote (or a pair of its slot-`l` votes) is in the writer's pool at the update, or it
equivocates there. -/
theorem honest_voter_at_update (hI : InclusionRun tr H U proposer g t₀) {X : Fin sp.n} (hX : X ∈ H)
    {i₀ l : Nat} {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ l ℓX)
    (hl : gbar g + 4 * sp.Δ ≤ sp.ts l) {z : Fin sp.n} (hz : z ∈ H) :
    z ∈ voters {v | v ∈ (tr.state X i₀).pool l} := by
  have hrun := hI.run
  have hr := hrun.localRun
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (l + 1 : Nat) = sp.ts l + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  obtain ⟨k, e, ⟨ℓ, hc, he⟩, hes⟩ := honest_votes_in_slot hI.toHealthyBase hl z hz
  obtain ⟨i, e', ⟨ℓ', hc', he'⟩, hes'⟩ :=
    honest_votes_in_slot hI.toHealthyBase (show gbar g + 4 * sp.Δ ≤ sp.ts (l + 1 : Nat) by
      linarith) z hz
  obtain ⟨hval, hsl, -, -⟩ := castAt_spec hr hz ⟨hc, he⟩
  obtain ⟨-, hsl', -, -⟩ := castAt_spec hr hz ⟨hc', he'⟩
  have htk := vote_time_le hr hz ⟨ℓ, hc, he⟩
  rw [← hsl, hes] at htk
  have hti : sp.ts (l + 1 : Nat) ≤ tr.time i :=
    (ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by rw [← hsl', hes'])
  have hki : k ≤ i := by
    by_contra h
    have := hr.time_mono (not_le.1 h).le
    linarith
  -- after its slot-`l` vote, `z` holds that vote or two of its slot-`l` votes
  have hpool : e.msg ∈ (tr.state z (k + 1)).pool l ∨
      z ∈ equivocators {x | x ∈ (tr.state z (k + 1)).pool l} := by
    rw [show tr.state z (k + 1) = tr.post k by simp [Trace.state, hc.1, hc.2],
      post_of_castAt hr hz ⟨hc, he⟩, optimistic_pool, ← hes, ← hval]
    exact admitVote_held _ _ _ (by omega) (by omega)
  have hW := writer_pool hrun hX hupd hz ⟨hc', he'⟩ hes' (hI.syncAC (by linarith) _) hki
  have hvot : ∀ v ∈ (tr.state z (k + 1)).pool l, v.val = z →
      z ∈ voters {v | v ∈ (tr.state X i₀).pool l} := by
    intro v hv hvz
    rcases hW v hv with h | ⟨a, ha, -, -, -, hav, -⟩
    · exact ⟨v, h, hvz⟩
    · exact ⟨a, ha, hav.trans hvz⟩
  rcases hpool with h | ⟨a, ha, -, -, -, hav, -⟩
  · exact hvot _ h hval
  · exact hvot a ha hav

/-- **A result of a slot `l` with `t_l ≥ ḡ + 4Δ` has an honest supporter**: an honest slot-`l`
vote whose head extends it (its counted validators are a strict majority of the writer's
voters, which include every honest node, and `f < n/2`). -/
theorem result_honest_supporter (hI : InclusionRun tr H U proposer g t₀) {X : Fin sp.n} (hX : X ∈ H)
    {i₀ l : Nat} {C : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hR : ResultAt tr X i₀ l C CV)
    (hl : gbar g + 4 * sp.Δ ≤ sp.ts l) :
    ∃ x ∈ H, ∃ j e, VoteAt tr x j e ∧ e.msg.slot = l ∧ VoteExtends U e.msg C := by
  have hrun := hI.run
  have hr := hrun.localRun
  have hmaj := result_majority hR
  obtain ⟨ℓX, hu, -, hCV⟩ := hR
  have hHV : H ⊆ voters {v | v ∈ (tr.state X i₀).pool l} := fun z hz =>
    honest_voter_at_update hI hX hu hl hz
  have hSV : {w | ∃ v ∈ CV, v.val = w} ⊆ voters {v | v ∈ (tr.state X i₀).pool l} := by
    rintro w ⟨v, hv, rfl⟩
    rw [hCV] at hv
    exact ⟨v, hv.1, rfl⟩
  obtain ⟨w, ⟨v, hv, rfl⟩, hwH⟩ : ∃ w ∈ {w | ∃ v ∈ CV, v.val = w}, w ∈ H := by
    by_contra hno'
    have hno : ∀ w ∈ {w | ∃ v ∈ CV, v.val = w}, w ∉ H := fun w hw hwH => hno' ⟨w, hw, hwH⟩
    have hdisj : Disjoint H {w | ∃ v ∈ CV, v.val = w} :=
      Set.disjoint_left.2 fun y hyH hyS => hno y hyS hyH
    have h1 := Set.ncard_union_eq hdisj
    have h2 := Set.ncard_le_ncard (Set.union_subset hHV hSV)
    have h3 : {w | ∃ v ∈ CV, v.val = w}.ncard ≤ Hᶜ.ncard :=
      Set.ncard_le_ncard fun y hy => hno y hy
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    have := hI.two_faulty_lt
    omega
  rw [hCV] at hv
  obtain ⟨hvp, -, -, R, hR, hRr, hCR⟩ := hv
  obtain ⟨j, -, e, hve, rfl⟩ := hrun.honest.pool_vote X hX i₀ l _ hvp hwH
  obtain ⟨-, hΦU⟩ := frameIn_of_callAt hr hX hu.1
  exact ⟨_, hwH, j, e, hve, state_pool_slot sp hr hX i₀ l _ hvp, R, hΦU hR, hRr,
    Anc.mono hΦU hCR⟩

end Consensus.Goldilocks.SA

end
