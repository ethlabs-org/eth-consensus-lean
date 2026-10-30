module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock

public section

/-! # Goldilocks Healing: H.2, clean raw origins transfer, the drain, settled locks

workbench `h2-open-items.md`:
* §6.1 (with §§2–3 and §5's root-covered reads): a clean raw origin `(B, j)` is carried by every
  honest vote and honest proposal head of a later slot (`raw_origin_transfer`), by increasing
  duty label: the first slot-`(j+1)` votes from the raw evidence, fast (`raw_fast_first_votes`,
  open) or slow (`raw_slow_first_votes`, open); the first proposal (§3, `raw_first_proposals`,
  open); later labels from the preceding honest batch (`h2_votes_continue`,
  `h2_proposals_continue`, open);
* §5, drain: a lock live at a slot `σ` with `t_σ ≥ t₀ + 2Θ` sits below a clean raw origin of its
  label (`h2_drain`);
* hence the locks are settled from `t₀ + 2Θ + 4Δ` (`h2_locks_settled`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g t₀ : Time}

/-- **§6.1, first transfer of a fast target** (§2 for the regular arm with its actual result,
§3's `3n/4` score for the optimistic arm; the counted seats oppose every conflicting lock of a
smaller label, locks of label `j` compare by RR/RO/OO, a current-label optimistic lock needs an
earlier bad honest vote): every honest vote of slot `j + 1` extends the selected block `B`. -/
theorem raw_fast_first_votes (hI : InclusionRun tr H U g t₀) {x : Fin sp.n} (hx : x ∈ H)
    {i j : Nat} {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hjx : JoinedAt tr x (tr.time i))
    (hfl : FastLockAt tr x i j B CV) (hj : t₀ + 4 * sp.Δ ≤ sp.ts j) :
    ∀ y ∈ H, ∀ k e, VoteAt tr y k e → e.msg.slot = j + 1 → VoteExtends U e.msg B := by
  sorry

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
`m > j` with `t_m ≥ t₀ + 4Δ` extends `B`, so does every honest vote of a later slot (the
preceding honest batch's `n − f` retained seats release older conflicting locks and dominate
the walk; a label-`(m)` lock has an honest supporter; root-covered reads per §5). -/
theorem h2_votes_continue (hI : InclusionRun tr H U g t₀) {B : Blk sp.n FGP} {j m : Nat}
    (hB : Protected tr H t₀ B j) (hjm : j < m) (hm : t₀ + 4 * sp.Δ ≤ sp.ts m)
    (hv : ∀ x ∈ H, ∀ k e, VoteAt tr x k e → e.msg.slot = m → VoteExtends U e.msg B) :
    VotesExtendAfter tr H U m B := by
  sorry

/-- **§6.1, later labels (proposals)**: for a protected `(B, j)`, if every honest vote of a slot
`m > j` with `t_m ≥ t₀ + 4Δ` extends `B`, the head of every honest `ac_proposal` at `t_{m+1}`
extends `B`. -/
theorem h2_proposals_continue (hI : InclusionRun tr H U g t₀) {B : Blk sp.n FGP} {j m : Nat}
    (hB : Protected tr H t₀ B j) (hjm : j < m) (hm : t₀ + 4 * sp.Δ ≤ sp.ts m)
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
  have hcont := h2_votes_continue hI hB.protected (Nat.lt_succ_self j) hj1 hfirst
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
