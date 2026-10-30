module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Carry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock

public section

/-! # Goldilocks Healing: H.2, clean raw origins transfer, the drain, settled locks

workbench `h2-open-items.md`:
* §6.1 (with §§2–3 and §5's root-covered reads): a clean raw origin `(B, j)` is carried by every
  honest vote and honest proposal head of a later slot (`raw_origin_transfer`), by increasing
  duty label: the first slot-`(j+1)` votes from the raw evidence, fast (`raw_fast_first_votes`,
  from A1.2 with `Inv`'s viability and §5's `Carry` above `Φ.F`, `h2_carry_fastLock`: the
  writer's counted heads relay by `Sync[ḡ, ·]` or catch up by `Catch(2Δ)`) or
  slow (`raw_slow_first_votes`, open); the first proposal (§3, `raw_first_proposals`,
  open); later labels from the preceding honest batch (`h2_votes_continue`,
  `h2_proposals_continue`, open);
* §5, drain: a lock live at a slot `σ` with `t_σ ≥ t₀ + 2Θ` sits below a clean raw origin of its
  label (`h2_drain`);
* hence the locks are settled from `t₀ + 2Θ + 4Δ` (`h2_locks_settled`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g t₀ : Time}

/-- A block between `Φ.F` and a block of a well-formed frame tree (inside a coherent `U`
containing the tree) is in the tree. -/
private theorem mem_tree_of_between {Φ : Frm sp.n FGP} (hU : Coherent U) (hΦ : FrameOK Φ)
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

/-- **§5, `Carry` for a fast origin at a read not covered by `Φ.F`** (the counted heads accepted
or resolved before `t_j + 2Δ` relay before `t_j + 3Δ`, pre-recovery heads by `Catch`; rooted
retention keeps them until the read, as `B` is above `Φ.F`): at every honest vote of slot
`j + 1` whose frame's `Φ.F` does not extend `B`, `Carry_y(j, CV, B)`. -/
theorem h2_carry_fastLock (hI : InclusionRun tr H U g t₀) {x : Fin sp.n} (hx : x ∈ H)
    {i j : Nat} {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hjx : JoinedAt tr x (tr.time i))
    (hfl : FastLockAt tr x i j B CV) (hj : t₀ + 4 * sp.Δ ≤ sp.ts j) :
    ∀ y ∈ H, ∀ k ℓ e, CastAt tr y k ℓ e → e.msg.slot = j + 1 → ¬ Anc U B ℓ.frame.F →
      CarryAt tr U y k e j CV := by
  have hr := hI.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hg := hI.le
  have hP1 : Protected tr H t₀ B j := Or.inl ⟨x, hx, i, CV, hjx, hfl, hj⟩
  intro y hy k ℓ e hc hs hBF
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc.1
  obtain ⟨-, hsl, -, -⟩ := castAt_spec hr hy hc
  have htk : sp.ts (j + 1 : Nat) ≤ tr.time k :=
    (ts_le_iff_le_slot sp (hr.time_nonneg k) _).2 (by rw [← hsl, hs])
  have hts : sp.ts (j + 1 : Nat) = sp.ts j + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  -- `Φ.F ⪯ B`: by `Inv`, `B` is in the frame's viable tree or below `fc_root`, and not below `Φ.F`
  have hFB : Anc U ℓ.frame.F B := by
    rcases (hI.inv B j hP1 y hy k ℓ hc.1 htk).1 with h | h
    · rcases anc_total hU h ((hΦ.rooted.2 _ hΦ.fcRoot_mem).mono hΦU) with h' | h'
      · exact absurd h' hBF
      · exact h'
    · exact (hΦ.rooted.2 B h.1).mono hΦU
  refine carryAt_of_writer_catch hr (hI.syncAC le_rfl (sp.ts j + 2 * sp.Δ)) (by linarith) le_rfl
    hx hy hc hs fun v hv => ?_
  obtain ⟨h₁, h₂, Hv, hHv, hHvr, hBHv, h₃⟩ := Healing.fastLock_writer hr hx hfl v hv
  refine ⟨h₁, h₂, Hv, hHv, hHvr, hFB.trans hBHv, ?_⟩
  rcases h₃ with hgen | ⟨kw, hkw, hkwt⟩
  · exact Or.inl hgen
  by_cases hkg : gbar g ≤ tr.time kw
  · exact Or.inr (Or.inl ⟨kw, hkw, hkg, hkwt⟩)
  · -- accepted by the writer before `ḡ`: `Catch(2Δ)` at the vote
    obtain ⟨k', hk', hacc, hk't⟩ := hI.catchUp x hx kw Hv hkw (not_le.1 hkg) y hy k ℓ hc.1
      (by linarith) (hFB.trans hBHv)
    exact Or.inr (Or.inr ⟨k', hk', hacc, by linarith⟩)

/-- **§6.1, first transfer of a fast target** (A1.2 at each slot-`(j+1)` vote, by induction on
cuts: the viability from `Inv` (the pair is P1), `Carry` from §5 at a read above `Φ.F`; a read
with `B ⪯ Φ.F` is root-covered, its head extends `Φ.F`): every honest vote of slot `j + 1`
extends the selected block `B`. -/
theorem raw_fast_first_votes (hI : InclusionRun tr H U g t₀) {x : Fin sp.n} (hx : x ∈ H)
    {i j : Nat} {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hjx : JoinedAt tr x (tr.time i))
    (hfl : FastLockAt tr x i j B CV) (hj : t₀ + 4 * sp.Δ ≤ sp.ts j) :
    ∀ y ∈ H, ∀ k e, VoteAt tr y k e → e.msg.slot = j + 1 → VoteExtends U e.msg B := by
  have hrun := hI.run
  have hr := hrun.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hg := hI.le
  have hP1 : Protected tr H t₀ B j := Or.inl ⟨x, hx, i, CV, hjx, hfl, hj⟩
  have hcarry := h2_carry_fastLock hI hx hjx hfl hj
  suffices h : ∀ k, ∀ y ∈ H, ∀ e, VoteAt tr y k e → e.msg.slot = j + 1 → VoteExtends U e.msg B
    from fun y hy k e hv hs => h k y hy e hv hs
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro y hy e ⟨ℓ, hc, he⟩ hes
    have hca : CastAt tr y k ℓ e := ⟨hc, he⟩
    obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc
    obtain ⟨-, hsl, -, -⟩ := castAt_spec hr hy hca
    have ht0 := hr.time_nonneg k
    have htk : sp.ts (j + 1 : Nat) ≤ tr.time k :=
      (ts_le_iff_le_slot sp ht0 _).2 (by rw [← hsl, hes])
    by_cases hBF : Anc U B ℓ.frame.F
    · -- root-covered: the head extends `Φ.F`
      obtain ⟨Hd, hHd, hHdr, -⟩ := honest_head_frame hr hy hca
      exact ⟨Hd, hΦU hHd, hHdr, hBF.trans ((hΦ.rooted.2 Hd hHd).mono hΦU)⟩
    have hviab : ViableAtVote ℓ e (j + 1) B := by
      rcases (hI.inv B j hP1 y hy k ℓ hc htk).2 e he with h | h
      · exact Or.inl (hes ▸ h)
      · refine Or.inr ?_
        have hfc := hΦ.fcRoot_mem
        have hFB : Anc U ℓ.frame.F B := by
          rcases anc_total hU h ((hΦ.rooted.2 _ hfc).mono hΦU) with h' | h'
          · exact absurd h' hBF
          · exact h'
        exact anc_tree_of_anc_U hU hΦ hΦU (mem_tree_of_between hU hΦ hΦU hFB h hfc) h hfc
    have hT : gbar g ≤ sp.ts ((sp.slot (tr.time k) : Int) - 1) := by
      rw [← hsl, hes, show ((j + 1 : Nat) : Int) - 1 = (j : Int) by push_cast; ring]
      linarith
    exact first_transfer sp FGP ro H U tr hrun j x y i k B CV ℓ e hx hfl hy hca hes
      (hI.syncAC (by linarith) _) (hcarry y hy k ℓ e hca hes hBF) (hI.faultBound ht0 hT)
      hviab (fun z hz k' hk' e' hv' hs' => ih k' hk' z hz e' hv' hs')

/-- **§6.1, first transfer of a slow target** (the writer's saved regular results `C_l ⪰ B` of
the window compare every live older lock by RR/RO; the current result gives §2's participant
majority for `B`): every honest vote of slot `j + 1` extends `B`. -/
theorem raw_slow_first_votes (hI : InclusionRun tr H U g t₀) {x : Fin sp.n} (hx : x ∈ H)
    {i j : Nat} {B : Blk sp.n FGP} (hjx : JoinedAt tr x (tr.time i))
    (hsl : SlowLockAt tr x i j B) (hj : t₀ + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1)) :
    ∀ y ∈ H, ∀ k e, VoteAt tr y k e → e.msg.slot = j + 1 → VoteExtends U e.msg B := by
  sorry

/-- **§3, proposal-boundary transfer**: the head of every honest `ac_proposal` at `t_{j+1}`
extends a clean raw origin `(B, j)` (the full previous-slot pool and viable tree; the regular
writer's participants and counted support relay before the proposal; `3n/4` for an optimistic
origin). -/
theorem raw_first_proposals (hI : InclusionRun tr H U g t₀) {B : Blk sp.n FGP} {j : Nat}
    (hB : CleanOrigin tr H t₀ B j) :
    ∀ x ∈ H, ∀ i (ℓ : ACLabel (goldilocksSA sp FGP ro)) d pay, tr.CallAt x i ℓ →
      ℓ.call = .proposal → tr.time i = sp.ts (j + 1 : Nat) →
      (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay) → Anc U B d.head := by
  sorry

/-- **§6.1, later labels (votes)**: for a protected `(B, j)`, if every honest vote of a slot
`m ≥ j` with `t_m ≥ t₀ + 4Δ` extends `B`, so does every honest vote of a later slot (the
preceding honest batch's `n − f` retained seats release older conflicting locks and dominate
the walk; a label-`(m)` lock has an honest supporter; root-covered reads per §5). -/
theorem h2_votes_continue (hI : InclusionRun tr H U g t₀) {B : Blk sp.n FGP} {j m : Nat}
    (hB : Protected tr H t₀ B j) (hjm : j ≤ m) (hm : t₀ + 4 * sp.Δ ≤ sp.ts m)
    (hv : ∀ x ∈ H, ∀ k e, VoteAt tr x k e → e.msg.slot = m → VoteExtends U e.msg B) :
    VotesExtendAfter tr H U m B := by
  sorry

/-- **§6.1, later labels (proposals)**: for a protected `(B, j)`, if every honest vote of a slot
`m ≥ j` with `t_m ≥ t₀ + 4Δ` extends `B`, the head of every honest `ac_proposal` at `t_{m+1}`
extends `B`. -/
theorem h2_proposals_continue (hI : InclusionRun tr H U g t₀) {B : Blk sp.n FGP} {j m : Nat}
    (hB : Protected tr H t₀ B j) (hjm : j ≤ m) (hm : t₀ + 4 * sp.Δ ≤ sp.ts m)
    (hv : ∀ x ∈ H, ∀ k e, VoteAt tr x k e → e.msg.slot = m → VoteExtends U e.msg B) :
    ∀ x ∈ H, ∀ i (ℓ : ACLabel (goldilocksSA sp FGP ro)) d pay, tr.CallAt x i ℓ →
      ℓ.call = .proposal → tr.time i = sp.ts (m + 1 : Nat) →
      (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay) → Anc U B d.head := by
  sorry

/-- **§6.1, raw-origin transfer**: a clean raw origin `(B, j)` is carried by every honest vote
and every honest proposal head of a slot after `j`. -/
theorem raw_origin_transfer (hI : InclusionRun tr H U g t₀) {B : Blk sp.n FGP} {j : Nat}
    (hB : CleanOrigin tr H t₀ B j) :
    VotesExtendAfter tr H U j B ∧ ProposalsExtendAfter tr H U j B := by
  have hΔ := sp.toParams.hΔ
  have hk := sp.two_le_k
  -- the first votes, and `t_{j+1} ≥ t₀ + 4Δ`
  obtain ⟨hfirst, hj1⟩ : (∀ y ∈ H, ∀ k e, VoteAt tr y k e → e.msg.slot = j + 1 →
      VoteExtends U e.msg B) ∧ t₀ + 4 * sp.Δ ≤ sp.ts (j + 1 : Nat) := by
    rcases cleanOrigin_iff.1 hB with ⟨x, hx, i, CV, hjx, hfl, hj⟩ | ⟨x, hx, i, hjx, hsl, hj⟩
    · exact ⟨raw_fast_first_votes hI hx hjx hfl hj, hj.trans ((ts_le_iff sp).2 (by omega))⟩
    · exact ⟨raw_slow_first_votes hI hx hjx hsl hj, hj.trans ((ts_le_iff sp).2 (by omega))⟩
  have hcont := h2_votes_continue hI hB.protected (Nat.le_succ j) hj1 hfirst
  have hvotes : VotesExtendAfter tr H U j B := votesExtendAfter_iff.2 fun y hy k e hv hlt => by
    rcases Nat.lt_or_ge (j + 1) e.msg.slot with h | h
    · exact votesExtendAfter_iff.1 hcont y hy k e hv h
    · exact hfirst y hy k e hv (by omega)
  refine ⟨hvotes, proposalsExtendAfter_iff.2 fun x hx i ℓ m d pay hc hcall ht hjm hd => ?_⟩
  rcases Nat.lt_or_ge (j + 1) m with h | h
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact h2_proposals_continue hI hB.protected (by omega)
      (hj1.trans ((ts_le_iff sp).2 (by omega)))
      (fun y hy k e hv hs => votesExtendAfter_iff.1 hvotes y hy k e hv (by omega))
      x hx i ℓ d pay hc hcall ht hd
  · obtain rfl : m = j + 1 := by omega
    exact raw_first_proposals hI hB x hx i ℓ d pay hc hcall ht hd

/-- A node is joined at a time `T ≥ t_s` when `t_s ≥ ḡ + 4Δ`. -/
private theorem joined_of_ge (hI : InclusionRun tr H U g t₀) {y : Fin sp.n} (hy : y ∈ H)
    {T : Time} (hT0 : 0 ≤ T) {s : Nat} (hsT : sp.ts s ≤ T) (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) :
    JoinedAt tr y T := by
  refine hI.joinedAt hy ?_
  have h1 : (s : Int) ≤ sp.slot T := (ts_le_iff_le_slot sp hT0 s).1 hsT
  have h2 : sp.ts ((s : Int) - 1) ≤ sp.ts ((sp.slot T : Int) - 1) := (ts_le_iff sp).2 (by omega)
  rw [ts_sub_one] at h2
  linarith

/-- The time of a fast lock write of slot `s` is at least `t_s`. -/
private theorem fastLock_time (hI : InclusionRun tr H U g t₀) {x : Fin sp.n} {i s : Nat}
    {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : FastLockAt tr x i s B CV) :
    sp.ts s ≤ tr.time i := by
  have hΔ := sp.toParams.hΔ
  rcases hfl with ⟨ℓ, C, ⟨-, -, ht, -⟩, -⟩ | ⟨ℓ, A, -, hsl, -⟩
  · rw [ht]; linarith
  · exact (ts_le_iff_le_slot sp (hI.run.localRun.time_nonneg i) s).2 (by omega)

/-- **§5, drain**: a lock stored at an honest node and live at a slot `σ` with `t_σ ≥ t₀ + 2Θ`
(`σ ≤ j + k` for its label `j`) sits below a clean raw origin of its label. -/
theorem h2_drain (hI : InclusionRun tr H U g t₀) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {l : Lock} (hl : l ∈ (tr.state y i).locks) {σ : Nat} (hσ : σ ≤ l.slot + sp.k)
    (hT : t₀ + 2 * Θ sp ≤ sp.ts σ) :
    ∃ B, (∃ L ∈ U, L.root = l.block ∧ Anc U L B) ∧ CleanOrigin tr H t₀ B l.slot := by
  have hr := hI.run.localRun
  have hΔ := sp.toParams.hΔ
  have hg := hI.le
  have hk := sp.two_le_k
  have hσ' : sp.ts σ ≤ sp.ts (l.slot + sp.k : Nat) := (ts_le_iff sp).2 (by exact_mod_cast hσ)
  unfold Θ at hT
  have hlk : sp.ts (l.slot + sp.k : Nat) = sp.ts l.slot + 4 * sp.Δ * sp.k := by
    simp only [SAParams.ts]; push_cast; ring
  have hkΔ : 0 ≤ 4 * sp.Δ * (sp.k : Int) := by positivity
  cases hf : l.fast
  · obtain ⟨j, -, B, hsl, hLB⟩ := slow_lock_provenance hr hy i l hl hf
    have hw : sp.ts ((l.slot : Int) - sp.k + 1) = sp.ts l.slot - 4 * sp.Δ * (sp.k - 1) := by
      simp only [SAParams.ts]; ring
    have hwin : t₀ + 4 * sp.Δ ≤ sp.ts ((l.slot : Int) - sp.k + 1) := by
      rw [hw]; nlinarith
    have htj : sp.ts l.slot ≤ tr.time j := by
      obtain ⟨ℓ, C, ⟨-, -, ht, -⟩, -⟩ := hsl
      rw [ht]; linarith
    exact ⟨B, hLB, cleanOrigin_iff.2 (Or.inr ⟨y, hy, j,
      joined_of_ge hI hy (hr.time_nonneg j) htj (by nlinarith), hsl, hwin⟩)⟩
  · obtain ⟨j, -, B, CV, hfl, hLB⟩ := fast_lock_provenance hr hy i l hl hf
    have hj : t₀ + 4 * sp.Δ ≤ sp.ts l.slot := by nlinarith
    exact ⟨B, hLB, cleanOrigin_iff.2 (Or.inl ⟨y, hy, j, CV,
      joined_of_ge hI hy (hr.time_nonneg j) (fastLock_time hI hfl) (by linarith), hfl, hj⟩)⟩

/-- **Settled locks**: from `t₀ + 2Θ + 4Δ` on, every lock live at an honest node is carried by
every later honest duty. -/
theorem h2_locks_settled (hI : InclusionRun tr H U g t₀) :
    LocksSettled tr H U (t₀ + 2 * Θ sp + 4 * sp.Δ) := by
  have hr := hI.run.localRun
  rw [locksSettled_iff]
  intro y hy i hi l hl hlive L hL hLr
  have ht0 := hr.time_nonneg i
  have hσ : t₀ + 2 * Θ sp ≤ sp.ts (sp.slot (tr.time i)) := by
    have h1 : ¬ sp.ts ((sp.slot (tr.time i) : Nat) + 1 : Int) ≤ tr.time i := by
      rw [ts_le_iff_le_slot sp ht0]; omega
    have h2 : sp.ts ((sp.slot (tr.time i) : Nat) + 1 : Int) =
        sp.ts (sp.slot (tr.time i)) + 4 * sp.Δ := by
      simp only [SAParams.ts]; ring
    linarith [not_le.1 h1]
  obtain ⟨B, ⟨L', hL', hL'r, hLB⟩, hclean⟩ := h2_drain hI hy hl hlive hσ
  obtain rfl : L' = L := hr.coherent.1 hL' hL (hL'r.trans hLr.symm)
  obtain ⟨hv, hp⟩ := raw_origin_transfer hI hclean
  refine ⟨votesExtendAfter_iff.2 fun x hx j e he hs => ?_, proposalsExtendAfter_iff.2
    fun x hx j ℓ m d pay hc hcall ht hm hd =>
      hLB.trans (proposalsExtendAfter_iff.1 hp x hx j ℓ m d pay hc hcall ht hm hd)⟩
  obtain ⟨Hd, hHd, hHdr, hBHd⟩ := votesExtendAfter_iff.1 hv x hx j e he hs
  exact ⟨Hd, hHd, hHdr, hLB.trans hBHd⟩

end Consensus.Goldilocks.SA

end
