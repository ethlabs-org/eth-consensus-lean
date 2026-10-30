module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Carry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial

public section

/-! # Goldilocks Healing: H.2, `Inv` at a vote, `Carry` for a batch

Under H.2's premises (`InclusionRun`, which extends H.1's `HealthyBase`, so H.1's honest-batch
lemmas apply as they are): `Inv` at a vote not covered by `Φ.F` gives the viability of a
protected block and `Φ.F ⪯ B` (`inv_at_vote`); and `Carry_y` for an honest batch extending `B`
(`h2_carry_votes`, §5's transport: relay after `ḡ`, `Catch(2Δ)` before). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g t₀ : Time}


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
theorem inv_at_vote (hI : InclusionRun tr H U g t₀) {B : Blk sp.n FGP} {j : Nat}
    (hB : Protected tr H t₀ B j) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
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
theorem h2_carry_votes (hI : InclusionRun tr H U g t₀) {m : Nat}
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

end Consensus.Goldilocks.SA

end
