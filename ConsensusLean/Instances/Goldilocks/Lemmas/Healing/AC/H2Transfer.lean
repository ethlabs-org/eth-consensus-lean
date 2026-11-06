module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Batch
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ResultAnc
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: H.2, clean raw origins transfer, the drain, settled locks

* raw-origin transfer (with root-covered reads): a clean raw origin `(B, j)` is carried by every
  honest vote and honest proposal head of a later slot (`raw_origin_transfer`), by increasing
  duty label: the first slot-`(j+1)` votes from the raw evidence, fast (`raw_fast_first_votes`,
  from A1.2 with `Inv`'s viability and the `Carry` above `Φ.F`, `h2_carry_fastLock`: the
  writer's counted heads relay by `Sync[ḡ, ·]` or catch up by `Catch(2Δ)`) or
  slow (`raw_slow_first_votes`, open); the first proposal (`raw_first_proposals`,
  open); later labels from the preceding honest batch (`h2_votes_continue`,
  `h2_proposals_continue`, open);
* the drain: a lock live at a slot `σ` with `t_σ ≥ t₀ + 2Θ` sits below a clean raw origin of its
  label (`h2_drain`);
* hence the locks are settled from `t₀ + 2Θ + 4Δ` (`h2_locks_settled`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g t₀ : Time} {proposer : Nat → Fin sp.n}

/-- **`Carry` for a fast origin at a read not covered by `Φ.F`** (the counted heads accepted
or resolved before `t_j + 2Δ` relay before `t_j + 3Δ`, pre-recovery heads by `Catch`; rooted
retention keeps them until the read, as `B` is above `Φ.F`): at every honest vote of slot
`j + 1` whose frame's `Φ.F` does not extend `B`, `Carry_y(j, CV, B)`. -/
theorem h2_carry_fastLock (hI : InclusionRun tr H U proposer g t₀) {x : Fin sp.n} (hx : x ∈ H)
    {i j : Nat} {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hjx : JoinedAt tr x (tr.time i))
    (hfl : FastLockAt tr x i j B CV) (hj : t₀ + 4 * sp.Δ ≤ sp.ts j) :
    ∀ y ∈ H, ∀ k ℓ e, CastAt tr y k ℓ e → e.msg.slot = j + 1 → ¬ Anc U B ℓ.frame.F →
      CarryAt tr U y k e j CV := by
  have hr := hI.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hg := hI.le
  have hP1 : Protected proposer tr H t₀ B j := Or.inl ⟨x, hx, i, CV, hjx, hfl, hj⟩
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
  refine carryAt_of_writer_catch hr (hI.syncAC le_rfl (sp.ts j + 2 * sp.Δ)) (by
      linarith only [hj, hΔ, hg]) le_rfl
    hx hy hc hs fun v hv => ?_
  obtain ⟨h₁, h₂, Hv, hHv, hHvr, hBHv, h₃⟩ := Healing.fastLock_writer hr hx hfl v hv
  refine ⟨h₁, h₂, Hv, hHv, hHvr, hFB.trans hBHv, ?_⟩
  rcases h₃ with hgen | ⟨kw, hkw, hkwt⟩
  · exact Or.inl hgen
  by_cases hkg : gbar g ≤ tr.time kw
  · exact Or.inr (Or.inl ⟨kw, hkw, hkg, hkwt⟩)
  · -- accepted by the writer before `ḡ`: `Catch(2Δ)` at the vote
    obtain ⟨k', hk', hacc, hk't⟩ := hI.catchUp x hx kw Hv hkw (not_le.1 hkg) y hy k ℓ hc.1
      (by linarith only [hj, hΔ, hg, htk, hts]) (hFB.trans hBHv)
    exact Or.inr (Or.inr ⟨k', hk', hacc, by linarith only [hj, hΔ, hg, hk't]⟩)

/-- **First transfer of a fast target** (A1.2 at each slot-`(j+1)` vote, by induction on cuts: the
viability from `Inv` (the pair is P1), `Carry` from `h2_carry_fastLock` at a read above `Φ.F`; a
read with `B ⪯ Φ.F` is root-covered, its head extends `Φ.F`): every honest vote of slot `j + 1`
extends the selected block `B`. -/
theorem raw_fast_first_votes (hI : InclusionRun tr H U proposer g t₀) {x : Fin sp.n} (hx : x ∈ H)
    {i j : Nat} {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hjx : JoinedAt tr x (tr.time i))
    (hfl : FastLockAt tr x i j B CV) (hj : t₀ + 4 * sp.Δ ≤ sp.ts j) :
    ∀ y ∈ H, ∀ k e, VoteAt tr y k e → e.msg.slot = j + 1 → VoteExtends U e.msg B := by
  have hrun := hI.run
  have hr := hrun.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hg := hI.le
  have hP1 : Protected proposer tr H t₀ B j := Or.inl ⟨x, hx, i, CV, hjx, hfl, hj⟩
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
      linarith only [hj, hΔ, hg]
    exact first_transfer sp FGP ro H U tr proposer hrun j x y i k B CV ℓ e hx hfl hy hca hes
      (hI.syncAC (by
          linarith only [hj, hΔ, hg]) _) (hcarry y hy k ℓ e hca hes hBF) (hI.faultBound ht0 hT)
      hviab (fun z hz k' hk' e' hv' hs' => ih k' hk' z hz e' hv' hs')

/-- **First transfer of a slow target** (the writer's saved regular results `C_l ⪰ B` of
the window compare every live older lock by RR/RO; the current result gives the participant
majority for `B`): every honest vote of slot `j + 1` extends `B`. -/
theorem raw_slow_first_votes (hI : InclusionRun tr H U proposer g t₀) {x : Fin sp.n} (hx : x ∈ H)
    {i j : Nat} {B : Blk sp.n FGP} (hjx : JoinedAt tr x (tr.time i))
    (hsl : SlowLockAt tr x i j B) (hj : t₀ + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1)) :
    ∀ y ∈ H, ∀ k e, VoteAt tr y k e → e.msg.slot = j + 1 → VoteExtends U e.msg B := by
  have hrun := hI.run
  have hr := hrun.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hg := hI.le
  have hk := sp.two_le_k
  have hP2 : Protected proposer tr H t₀ B j := Or.inr (Or.inl ⟨x, hx, i, hjx, hsl, hj⟩)
  obtain ⟨ℓX, C, hupd, hconf, hdeep⟩ := id hsl
  have hΦXU := (frameIn_of_callAt hr hx hupd.1).2
  have hDC : Anc U B C := Anc.mono hΦXU (deepest_mem hdeep).1.1.2.2
  have hres : ResultAt tr x i j C (fastCounted sp (tr.state x i) ℓX.frame j C) :=
    ⟨ℓX, hupd, hconf, rfl⟩
  have hjt : t₀ + 4 * sp.Δ ≤ sp.ts j := hj.trans ((ts_le_iff sp).2 (by omega))
  have hwin : gbar g + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1) := by linarith only [hj, hg]
  have hts : sp.ts (j + 1 : Nat) = sp.ts j + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  suffices h : ∀ k, ∀ y ∈ H, ∀ e, VoteAt tr y k e → e.msg.slot = j + 1 → VoteExtends U e.msg B
    from fun y hy k e hv hs => h k y hy e hv hs
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro y hy e ⟨ℓ, hc, he⟩ hes
    have hca : CastAt tr y k ℓ e := ⟨hc, he⟩
    obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc
    obtain ⟨-, hsl', -, -⟩ := castAt_spec hr hy hca
    have ht0 := hr.time_nonneg k
    by_cases hBF : Anc U B ℓ.frame.F
    · obtain ⟨Hd, hHd, hHdr, -⟩ := honest_head_frame hr hy hca
      exact ⟨Hd, hΦU hHd, hHdr, hBF.trans ((hΦ.rooted.2 Hd hHd).mono hΦU)⟩
    have htk : sp.ts (j + 1 : Nat) ≤ tr.time k :=
      (ts_le_iff_le_slot sp ht0 _).2 (by rw [← hsl', hes])
    obtain ⟨hviab, hFB⟩ := inv_at_vote hI hP2 hy hca htk hBF
    -- `Carry` for the result's counted votes: relay after `ḡ`, `Catch(2Δ)` before
    have hCy : CarryAt tr U y k e j (fastCounted sp (tr.state x i) ℓX.frame j C) := by
      refine carryAt_of_writer_catch hr (hI.syncAC le_rfl (sp.ts j + 2 * sp.Δ)) (by
          linarith only [hΔ, hg, hjt])
        le_rfl hx hy hca hes fun v hv => ?_
      obtain ⟨h₁, h₂, Hv, hHv, hHvr, hCHv, h₃⟩ := Compose.result_writer hr hx hres v hv
      have hFHv : Anc U ℓ.frame.F Hv := hFB.trans (hDC.trans hCHv)
      refine ⟨h₁, h₂, Hv, hHv, hHvr, hFHv, ?_⟩
      rcases h₃ with hgen | ⟨kw, hkw, hkwt⟩
      · exact Or.inl hgen
      by_cases hkg : gbar g ≤ tr.time kw
      · exact Or.inr (Or.inl ⟨kw, hkw, hkg, hkwt⟩)
      · obtain ⟨k', hk', hacc, hk't⟩ := hI.catchUp x hx kw Hv hkw (not_le.1 hkg) y hy k ℓ hc
          (by linarith only [hΔ, hg, hjt, hts, htk]) hFHv
        exact Or.inr (Or.inr ⟨k', hk', hacc, by linarith only [hΔ, hg, hjt, hk't]⟩)
    exact result_transfer_anc sp hrun hx hres hDC hy hca hes hCy (hes ▸ hviab)
      (slow_live_locks hI.toHealthyBase hx hsl hwin hy hca hes
        fun z hz k' hk' e' hv' hs' => ih k' hk' z hz e' hv' hs')
      (writer_merged hrun hx hupd hy hca hes (hI.syncAC (by linarith only [hΔ, hg, hjt]) _))

/-- **(P) from a writer, after the GST or by catch-up** (`carryAt_of_writer_catch` at the
proposal duty): a slot-`σ` vote sent or admitted by an honest writer in `[t_σ, t_σ + 2Δ)`, whose
head extends the proposer's `Φ.F` and is genesis, or was accepted by the writer from `a₀` on before
`t_σ + 2Δ`, or by the proposer before `t_σ + 3Δ`, reaches the honest proposer of slot `σ + 1`
(Sync relays the vote and the head before `t_σ + 3Δ`; rooted retention keeps the head). -/
theorem heldAtProposal_of_writer (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {a₀ b : Time} (hsync : SyncAC (goldilocksSA sp FGP ro) H U a₀ b tr) {σ : Nat}
    (ha₀ : a₀ ≤ sp.ts σ) (hb : sp.ts σ + 2 * sp.Δ ≤ b) {w : Fin sp.n} (hw : w ∈ H)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt x i ℓ) (ht : tr.time i = sp.ts (σ + 1 : Nat))
    (hrs : ∀ k ≤ i, tr.RestartAt x k → tr.time k < sp.ts σ) {v : Vote sp.n} (hvs : v.slot = σ)
    (hsend : ∃ k, tr.SendOrAdmit w k v ∧ sp.ts σ ≤ tr.time k ∧ tr.time k < sp.ts σ + 2 * sp.Δ)
    (hhead : ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U ℓ.frame.F Hv ∧
      (Hv.root = sp.genesisRoot ∨
        (∃ k, tr.AcceptAt w k Hv ∧ a₀ ≤ tr.time k ∧ tr.time k < sp.ts σ + 2 * sp.Δ) ∨
        ∃ k ≤ i, tr.AcceptAt x k Hv ∧ tr.time k < sp.ts σ + 3 * sp.Δ)) :
    HeldAtProposal (tr.state x i) ℓ.frame σ v := by
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (σ + 1 : Nat) = sp.ts σ + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc
  have hdl : ∀ k ≤ i, ∀ τ, τ < sp.ts σ + 2 * sp.Δ → tr.deadline x k τ < sp.ts σ + 3 * sp.Δ := by
    intro k hk τ hτ
    have h₁ := Compose.ac_deadline_le_of_restarts
      (fun k' hk' hr' => (hrs k' (hk'.trans hk) hr').le) τ
    have h₂ := max_lt hτ (show sp.ts σ < sp.ts σ + 2 * sp.Δ by linarith only [hΔ])
    change tr.deadline x k τ ≤ max τ (sp.ts σ) + sp.Δ at h₁
    linarith only [h₂, h₁]
  refine heldAtProposal_iff.2 ⟨?_, ?_⟩
  · obtain ⟨k, hsk, hk1, hk2⟩ := hsend
    obtain ⟨k', hk'i, hkk', hp, hk'dl⟩ := hsync.1 w hw k v hsk (ha₀.trans hk1) (by
        linarith only [hb, hk2])
      x hx i ℓ hc (by linarith only [hdl i le_rfl _ hk2, ht, hk1, hk2, hts])
    have hk'lt : tr.time k' < sp.ts σ + 3 * sp.Δ := hk'dl.trans (hdl k' hk'i _ hk2)
    have hk'i' : k' < i := lt_of_le_of_ne hk'i (by rintro rfl; linarith only [hΔ, hts, hk'lt, ht])
    have hnr : ∀ r, k' + 1 ≤ r → r < i → ¬ tr.RestartAt x r := fun r h₁ h₂ hrr => by
      have := hrs r h₂.le hrr
      have := hr.time_mono (show k' ≤ r by omega)
      linarith
    have hsk' : sp.slot (tr.time k') = σ :=
      slot_of_mem sp σ (hk1.trans hkk') (by rw [hts]; linarith only [hk1, hk2, hk'lt])
    have hmono := pool_mono hr hx (show k' + 1 ≤ i by omega) hnr σ
    rcases held_of_processAt hr hx hp (by rw [hvs, hsk']; omega) (by rw [hvs, hsk']) with
      h | ⟨a, ha, c, hc', hac, hav, hcv⟩
    · rw [hvs] at h
      exact Or.inl (hmono h)
    · rw [hvs] at ha hc'
      exact Or.inr ⟨a, hmono ha, c, hmono hc', hac, hav, hcv⟩
  · obtain ⟨Hv, hHv, hHvr, hFHv, hacc⟩ := hhead
    obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_call sp hr hx i ℓ hc
    obtain ⟨hHt, hAB⟩ : Hv ∈ ℓ.frame.tree ∧ AcceptedBefore tr x Hv (sp.ts σ + 3 * sp.Δ) := by
      rcases hacc with hg | ⟨kw, hkw, hkwa, hkwt⟩ | ⟨ky, hky, hacc, hkyt⟩
      · refine ⟨?_, Or.inl hg⟩
        obtain rfl : Hv = G := hU.1 hHv hGU (hg.trans hGr.symm)
        obtain h | ⟨c, -, hcp⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hFHv
        · exact h ▸ hΦ.rooted.1
        · exact absurd (hcp.2.2.symm.trans hGp) (Option.some_ne_none _)
      · obtain ⟨ky, hky, hacc, hkyt⟩ := hsync.2 w hw kw Hv hkw hkwa (by
          linarith only [hb, hkwt]) x hx i ℓ hc
          (by linarith only [hdl i le_rfl _ hkwt, ht, hΔ, hts]) hFHv
        exact ⟨mem_tree_of_acceptAt sp hr hx hacc hky hc hFHv,
          Or.inr ⟨ky, hacc, hkyt.trans (hdl ky hky _ hkwt)⟩⟩
      · exact ⟨mem_tree_of_acceptAt sp hr hx hacc hky hc hFHv, Or.inr ⟨ky, hacc, hkyt⟩⟩
    refine ⟨Hv, hHt, hHvr, ?_⟩
    exact (blockStamp_lt_of_acceptedBefore sp hr hx hc hHt hAB
      (fun k hk hrk => (hrs k hk hrk).trans (by linarith only [hΔ]))
      (Or.inl (by
          rw [ht, hts]; linarith only [hΔ]))).trans (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _))

/-- At a proposal of slot `σ + 1` with `t_σ ≥ ḡ + 4Δ`, under `Inv` for a protected `(B, j)` with
`j ≤ σ` and `B ⋠ Φ.F`, `B` is viable or below `fc_root` in the proposer's tree, above `Φ.F`. -/
private theorem viable_at_proposal (hI : InclusionRun tr H U proposer g t₀)
    {B : Blk sp.n FGP} {j : Nat}
    (hB : Protected proposer tr H t₀ B j) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (ht : sp.ts (j + 1 : Nat) ≤ tr.time i) (hBF : ¬ Anc U B ℓ.frame.F) :
    (B ∈ ℓ.frame.tree ∧ (B ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc B ℓ.frame.fcRoot)) ∧
      Anc U ℓ.frame.F B := by
  have hr := hI.run.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc
  rcases (hI.inv B j hB x hx i ℓ hc ht).1 with h | h
  · have hFB := (anc_total hU h ((hΦ.rooted.2 _ hΦ.fcRoot_mem).mono hΦU)).resolve_left hBF
    have hBt := mem_tree_of_between hU hΦ hΦU hFB h hΦ.fcRoot_mem
    exact ⟨⟨hBt, Or.inr (anc_tree_of_anc_U hU hΦ hΦU hBt h hΦ.fcRoot_mem)⟩, hFB⟩
  · exact ⟨⟨h.1, Or.inl h⟩, (hΦ.rooted.2 B h.1).mono hΦU⟩

/-- (L-high) at a proposal of slot `σ + 1`: a stored lock of slot `> σ` is optimistic over votes
that extend `B`; one of slot `σ` is compatible with `B` by `hsame`. -/
private theorem high_locks (hI : InclusionRun tr H U proposer g t₀) {x : Fin sp.n} (hx : x ∈ H)
    {i σ : Nat} (ht : tr.time i = sp.ts (σ + 1 : Nat)) {B : Blk sp.n FGP}
    (hlater : ∀ z ∈ H, ∀ k e, VoteAt tr z k e → σ < e.msg.slot → VoteExtends U e.msg B)
    (hsame : ∀ k CV O, OptimisticLockAt tr x k σ O CV → Compatible U O B) :
    HighLocksCompatible U (tr.state x i) (tr.time i) σ B := by
  have hrun := hI.run
  have hU := hrun.localRun.coherent
  refine highLocksCompatible_iff.2 fun l hl _ hlσ Y hY hYr => ?_
  obtain ⟨O, hYO, k, CV, hopt⟩ := proposal_high_lock hrun.localRun hx ht hl hlσ hY hYr
  have hO : Compatible U O B := by
    rcases (show l.slot = σ ∨ σ < l.slot by omega) with h | h
    · rw [h] at hopt
      exact hsame k CV O hopt
    · exact optimisticLock_compatible hrun hI.two_faulty_lt hx hopt fun w hw j e hv hs =>
        hlater w hw j e hv (by omega)
  rcases hO with h | h
  · exact Or.inl (hYO.trans h)
  · exact anc_total hU hYO h

/-- **Later labels (votes)**: for a protected `(B, j)`, if every honest vote of a slot
`m ≥ j` with `t_m ≥ t₀ + 4Δ` extends `B`, so does every honest vote of a later slot (the
preceding honest batch's `n − f` retained seats release older conflicting locks and dominate
the walk; a label-`(m)` lock has an honest supporter; a read with `B ⪯ Φ.F` is root-covered). -/
theorem h2_votes_continue (hI : InclusionRun tr H U proposer g t₀) {B : Blk sp.n FGP} {j m : Nat}
    (hB : Protected proposer tr H t₀ B j) (hjm : j ≤ m) (hm : t₀ + 4 * sp.Δ ≤ sp.ts m)
    (hv : ∀ x ∈ H, ∀ k e, VoteAt tr x k e → e.msg.slot = m → VoteExtends U e.msg B) :
    VotesExtendAfter tr H U m B := by
  have hrun := hI.run
  have hr := hrun.localRun
  have hΔ := sp.toParams.hΔ
  have hg := hI.le
  rw [votesExtendAfter_iff]
  suffices h : ∀ d : Nat, ∀ x ∈ H, ∀ k e, VoteAt tr x k e → e.msg.slot = m + d →
      VoteExtends U e.msg B by
    intro x hx k e hve hs
    exact h (e.msg.slot - m) x hx k e hve (by omega)
  intro d
  induction d with
  | zero => exact hv
  | succ d ih =>
    have hmd : gbar g + 4 * sp.Δ ≤ sp.ts (m + d : Nat) :=
      by linarith [(ts_le_iff sp).2 (show ((m : Nat) : Int) ≤ ((m + d : Nat) : Int) by omega)]
    have hhalf := honest_voters_half hI.toHealthyBase hmd
    suffices h : ∀ k, ∀ x ∈ H, ∀ e, VoteAt tr x k e → e.msg.slot = m + (d + 1) →
        VoteExtends U e.msg B from fun x hx k e hve hs => h k x hx e hve hs
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ihk =>
      intro y hy e ⟨ℓ, hc, he⟩ hes
      have hca : CastAt tr y k ℓ e := ⟨hc, he⟩
      obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc
      obtain ⟨-, hsl, -, -⟩ := castAt_spec hr hy hca
      have ht0 := hr.time_nonneg k
      by_cases hBF : Anc U B ℓ.frame.F
      · obtain ⟨Hd, hHd, hHdr, -⟩ := honest_head_frame hr hy hca
        exact ⟨Hd, hΦU hHd, hHdr, hBF.trans ((hΦ.rooted.2 Hd hHd).mono hΦU)⟩
      have htk : sp.ts (j + 1 : Nat) ≤ tr.time k :=
        (ts_le_iff_le_slot sp ht0 _).2 (by rw [← hsl, hes]; push_cast; omega)
      obtain ⟨hviab, hFB⟩ := inv_at_vote hI hB hy hca htk hBF
      have hT : gbar g ≤ sp.ts ((sp.slot (tr.time k) : Int) - 1) := by
        rw [← hsl, hes, show ((m + (d + 1) : Nat) : Int) - 1 = ((m + d : Nat) : Int) by
          push_cast; ring]
        linarith only [hΔ, hmd]
      exact next_transfer sp FGP ro H U tr proposer hrun (m + d) y k B ℓ e hy hca
        (by omega) ih hhalf
        (h2_carry_votes hI hmd ih hy hca (by omega) hFB) (hI.faultBound ht0 hT) (hes ▸ hviab)
        (fun z hz k' hk' e' hv' hs' => ihk k' hk' z hz e' hv' (by omega))

/-- **Later labels (proposals)**: for a protected `(B, j)`, if every honest vote of a slot
`m ≥ j` with `t_m ≥ t₀ + 4Δ` extends `B`, the head of every honest `ac_proposal` at `t_{m+1}`
extends `B`. -/
theorem h2_proposals_continue (hI : InclusionRun tr H U proposer g t₀)
    {B : Blk sp.n FGP} {j m : Nat}
    (hB : Protected proposer tr H t₀ B j) (hjm : j ≤ m) (hm : t₀ + 4 * sp.Δ ≤ sp.ts m)
    (hv : ∀ x ∈ H, ∀ k e, VoteAt tr x k e → e.msg.slot = m → VoteExtends U e.msg B) :
    ∀ x ∈ H, ∀ i (ℓ : ACLabel (goldilocksSA sp FGP ro)) d pay, tr.CallAt x i ℓ →
      ℓ.call = .proposal → tr.time i = sp.ts (m + 1 : Nat) →
      (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay) → Anc U B d.head := by
  have hrun := hI.run
  have hr := hrun.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hg := hI.le
  have hm4 : gbar g + 4 * sp.Δ ≤ sp.ts m := by linarith
  have hcont := h2_votes_continue hI hB hjm hm hv
  intro x hx i ℓ d pay hc hcall ht hprop
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc
  have hts : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  by_cases hBF : Anc U B ℓ.frame.F
  · rw [(acProposal_head hprop).2]
    exact hBF.trans ((hΦ.rooted.2 _ (getHead_mem hΦ (fun _ hX => hX.1) _ _ _ _)).mono hΦU)
  obtain ⟨hV, hFB⟩ := viable_at_proposal hI hB hx hc
    (ht ▸ (ts_le_iff sp).2 (by push_cast; omega)) hBF
  have hlater : ∀ z ∈ H, ∀ k e, VoteAt tr z k e → m < e.msg.slot → VoteExtends U e.msg B :=
    fun z hz k e hve hs => votesExtendAfter_iff.1 hcont z hz k e hve hs
  refine batch_proposal hrun hI.two_faulty_lt (honest_voters_half hI.toHealthyBase hm4) hv hx hc
    (proposal_slot ht) hprop hV (fun z hz k e hve hes => ?_)
    (high_locks hI hx ht hlater fun k CV O hopt => optimisticLock_compatible hrun
      hI.two_faulty_lt hx hopt hv)
  obtain ⟨Hd', hHd', hHd'r, hBHd'⟩ := hv z hz k e hve hes
  obtain ⟨Hd, hHdt, hHdr, -, hh⟩ := late_vote_held_of_frame hI.toHealthyBase hx hc hm4
    (by rw [ht, hts]; linarith only [hΔ]) hz hve hes fun Hd hHd hHdr => by
      rw [hU.1 hHd hHd' (hHdr.trans hHd'r.symm)]
      exact hFB.trans hBHd'
  obtain ⟨hmem, -, hbs⟩ := hh i (Or.inl rfl)
  exact heldAtProposal_iff.2 ⟨Or.inl (hes ▸ hmem), Hd, hHdt, hHdr,
    (hHdr ▸ hbs).trans (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _))⟩

/-- **Raw-origin transfer (votes)**: a clean raw origin `(B, j)` is carried by every honest
vote of a slot after `j`. -/
theorem raw_origin_votes (hI : InclusionRun tr H U proposer g t₀) {B : Blk sp.n FGP} {j : Nat}
    (hB : CleanOrigin tr H t₀ B j) : VotesExtendAfter tr H U j B := by
  have hk := sp.two_le_k
  obtain ⟨hfirst, hj1⟩ : (∀ y ∈ H, ∀ k e, VoteAt tr y k e → e.msg.slot = j + 1 →
      VoteExtends U e.msg B) ∧ t₀ + 4 * sp.Δ ≤ sp.ts (j + 1 : Nat) := by
    rcases cleanOrigin_iff.1 hB with ⟨x, hx, i, CV, hjx, hfl, hj⟩ | ⟨x, hx, i, hjx, hsl, hj⟩
    · exact ⟨raw_fast_first_votes hI hx hjx hfl hj, hj.trans ((ts_le_iff sp).2 (by omega))⟩
    · exact ⟨raw_slow_first_votes hI hx hjx hsl hj, hj.trans ((ts_le_iff sp).2 (by omega))⟩
  have hcont := h2_votes_continue hI hB.protected (Nat.le_succ j) hj1 hfirst
  exact votesExtendAfter_iff.2 fun y hy k e hv hlt => by
    rcases Nat.lt_or_ge (j + 1) e.msg.slot with h | h
    · exact votesExtendAfter_iff.1 hcont y hy k e hv h
    · exact hfirst y hy k e hv (by omega)

/-- **Proposal-boundary transfer**: the head of every honest `ac_proposal` at `t_{j+1}`
extends a clean raw origin `(B, j)`: root-covered when `B ⪯ Φ.F`; otherwise `Inv` gives (V),
the writer's counted votes reach the proposer ((P), Sync and `Catch`), and ProposalCore's
fast-update (A1.2), optimistic (A1.4 (a)) or result (A1.8, with the slow window's
`slow_stored_locks`) transfer applies. -/
theorem raw_first_proposals (hI : InclusionRun tr H U proposer g t₀) {B : Blk sp.n FGP} {j : Nat}
    (hB : CleanOrigin tr H t₀ B j) :
    ∀ x ∈ H, ∀ i (ℓ : ACLabel (goldilocksSA sp FGP ro)) d pay, tr.CallAt x i ℓ →
      ℓ.call = .proposal → tr.time i = sp.ts (j + 1 : Nat) →
      (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay) → Anc U B d.head := by
  have hrun := hI.run
  have hr := hrun.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hg := hI.le
  have hk := sp.two_le_k
  have hvotes := raw_origin_votes hI hB
  intro x hx i ℓ d pay hc hcall ht hprop
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc
  have hslot := proposal_slot ht
  have hts : sp.ts (j + 1 : Nat) = sp.ts j + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  by_cases hBF : Anc U B ℓ.frame.F
  · rw [(acProposal_head hprop).2]
    exact hBF.trans ((hΦ.rooted.2 _ (getHead_mem hΦ (fun _ hX => hX.1) _ _ _ _)).mono hΦU)
  obtain ⟨hV, hFB⟩ := viable_at_proposal hI hB.protected hx hc ht.ge hBF
  have hjt : t₀ + 4 * sp.Δ ≤ sp.ts j := by
    rcases cleanOrigin_iff.1 hB with ⟨-, -, -, -, -, -, h⟩ | ⟨-, -, -, -, -, h⟩
    · exact h
    · exact h.trans ((ts_le_iff sp).2 (by omega))
  have hrs : ∀ {z}, z ∈ H → ∀ k, tr.RestartAt z k → tr.time k < sp.ts j := fun hz k hrk =>
    lt_of_le_of_lt (hI.restart_le hz hrk) (by linarith only [hΔ, hg, hjt])
  have hlater : ∀ z ∈ H, ∀ k e, VoteAt tr z k e → j < e.msg.slot → VoteExtends U e.msg B :=
    fun z hz k e hv hs => votesExtendAfter_iff.1 hvotes z hz k e hv hs
  -- (P) for the votes counted by an honest writer, given its writer facts
  have hP : ∀ {X}, X ∈ H → ∀ {D : Blk sp.n FGP}, Anc U B D → ∀ v, v.slot = j →
      (∃ k, tr.SendOrAdmit X k v ∧ sp.ts j ≤ tr.time k ∧ tr.time k < sp.ts j + 2 * sp.Δ) →
      (∃ Hv ∈ U, Hv.root = v.head ∧ Anc U D Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, tr.AcceptAt X k Hv ∧ tr.time k < sp.ts j + 2 * sp.Δ)) →
      HeldAtProposal (tr.state x i) ℓ.frame j v := by
    intro X hX D hBD v hvs hsend ⟨Hv, hHv, hHvr, hDHv, hacc⟩
    have hFHv := hFB.trans (hBD.trans hDHv)
    refine heldAtProposal_of_writer hr (hI.syncAC le_rfl (sp.ts j + 2 * sp.Δ)) (by
        linarith only [hΔ, hg, hjt])
      le_rfl hX hx hc ht (fun k _ hrk => hrs hx k hrk) hvs hsend ⟨Hv, hHv, hHvr, hFHv, ?_⟩
    rcases hacc with hgen | ⟨kw, hkw, hkwt⟩
    · exact Or.inl hgen
    by_cases hkg : gbar g ≤ tr.time kw
    · exact Or.inr (Or.inl ⟨kw, hkw, hkg, hkwt⟩)
    · obtain ⟨k', hk', hacc', hk't⟩ := hI.catchUp X hX kw Hv hkw (not_le.1 hkg) x hx i ℓ hc
        (by linarith only [hΔ, hg, ht, hts, hjt]) hFHv
      exact Or.inr (Or.inr ⟨k', hk', hacc', by linarith only [hΔ, hg, hjt, hk't]⟩)
  have hW : ∀ {X i₀ ℓX}, X ∈ H → UpdateAt tr X i₀ j ℓX → ∀ v ∈ (tr.state x i).pool j,
      v ∈ (tr.state X i₀).pool j ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool j} :=
    fun hX hupd => writer_pool_proposal hr hX hupd hx ht (hI.syncAC (by
        linarith only [hΔ, hg, hjt]) _)
      (fun k _ hrk => (hrs hX k hrk).le) (fun k _ hrk => hrs hx k hrk)
  rcases cleanOrigin_iff.1 hB with ⟨X, hX, i₀, CV, -, hfl, -⟩ | ⟨X, hX, i₀, -, hsl, hj⟩
  · have hsame : ∀ k CV' O, OptimisticLockAt tr x k j O CV' → Compatible U O B :=
      fun k CV' O hopt => fastLock_fastLock_compatible hI.toHealthyBase hx (Or.inr hopt) hX hfl
        (by linarith only [hΔ, hg, hjt])
    have hPCV : ∀ v ∈ CV, HeldAtProposal (tr.state x i) ℓ.frame j v := fun v hv => by
      obtain ⟨h₁, h₂, h₃⟩ := Healing.fastLock_writer hr hX hfl v hv
      exact hP hX Relation.ReflTransGen.refl v h₁ h₂ h₃
    rcases hfl with hfu | hopt
    · exact update_first_proposal hrun hX hfu hx hc hslot hprop hV hPCV
        (hW hX hfu.choose_spec.choose_spec.1) (high_locks hI hx ht hlater hsame)
    · exact optimistic_first_proposal hrun hI.two_faulty_lt hX hopt hx hc hslot hprop hV hPCV
        (high_locks hI hx ht hlater hsame)
  · obtain ⟨ℓX, C, hupd, hconf, hdeep⟩ := id hsl
    have hres : ResultAt tr X i₀ j C (fastCounted sp (tr.state X i₀) ℓX.frame j C) :=
      ⟨ℓX, hupd, hconf, rfl⟩
    have hBC : Anc U B C :=
      Anc.mono (frameIn_of_callAt hr hX hupd.1).2 (deepest_mem hdeep).1.1.2.2
    have hwin : gbar g + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1) := by linarith only [hg, hj]
    have hall : ∀ l ∈ (tr.state x i).locks, sp.slot (tr.time i) ≤ l.slot + sp.k → ∀ Y ∈ U,
        Y.root = l.block → Compatible U Y B := by
      intro l hl hlive Y hY hYr
      rcases le_or_gt l.slot j with hle | hlt
      · exact slow_stored_locks hI.toHealthyBase hX hsl hwin hx (by rw [hslot]) l hl hlive hle
          Y hY hYr
      · obtain ⟨O, hYO, k, CV', hopt⟩ := proposal_high_lock hr hx ht hl hlt.le hY hYr
        rcases optimisticLock_compatible hrun hI.two_faulty_lt hx hopt fun w hw j' e hv hs =>
            hlater w hw j' e hv (by omega) with h | h
        · exact Or.inl (hYO.trans h)
        · exact anc_total hU hYO h
    exact result_first_proposal hrun hX hres hBC hx hc hslot hprop hV
      (fun v hv => by
        obtain ⟨h₁, h₂, h₃⟩ := Compose.result_writer hr hX hres v hv
        exact hP hX hBC v h₁ h₂ h₃)
      (hW hX hupd) (lowLocksCompatible_iff.2 fun l hl hlive _ => hall l hl hlive)
      (highLocksCompatible_iff.2 fun l hl hlive _ => hall l hl hlive)

/-- **Raw-origin transfer**: a clean raw origin `(B, j)` is carried by every honest vote
and every honest proposal head of a slot after `j`. -/
theorem raw_origin_transfer (hI : InclusionRun tr H U proposer g t₀) {B : Blk sp.n FGP} {j : Nat}
    (hB : CleanOrigin tr H t₀ B j) :
    VotesExtendAfter tr H U j B ∧ ProposalsExtendAfter tr H U j B := by
  have hΔ := sp.toParams.hΔ
  have hk := sp.two_le_k
  have hj1 : t₀ + 4 * sp.Δ ≤ sp.ts (j + 1 : Nat) := by
    rcases cleanOrigin_iff.1 hB with ⟨-, -, -, -, -, -, hj⟩ | ⟨-, -, -, -, -, hj⟩
    · exact hj.trans ((ts_le_iff sp).2 (by omega))
    · exact hj.trans ((ts_le_iff sp).2 (by omega))
  have hvotes := raw_origin_votes hI hB
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
private theorem joined_of_ge (hI : InclusionRun tr H U proposer g t₀) {y : Fin sp.n} (hy : y ∈ H)
    {T : Time} (hT0 : 0 ≤ T) {s : Nat} (hsT : sp.ts s ≤ T) (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) :
    JoinedAt tr y T := by
  refine hI.joinedAt hy ?_
  have h1 : (s : Int) ≤ sp.slot T := (ts_le_iff_le_slot sp hT0 s).1 hsT
  have h2 : sp.ts ((s : Int) - 1) ≤ sp.ts ((sp.slot T : Int) - 1) := (ts_le_iff sp).2 (by omega)
  rw [ts_sub_one] at h2
  linarith

/-- The time of a fast lock write of slot `s` is at least `t_s`. -/
private theorem fastLock_time (hI : InclusionRun tr H U proposer g t₀) {x : Fin sp.n} {i s : Nat}
    {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : FastLockAt tr x i s B CV) :
    sp.ts s ≤ tr.time i := by
  have hΔ := sp.toParams.hΔ
  rcases hfl with ⟨ℓ, C, ⟨-, -, ht, -⟩, -⟩ | ⟨ℓ, A, -, hsl, -⟩
  · rw [ht]; linarith
  · exact (ts_le_iff_le_slot sp (hI.run.localRun.time_nonneg i) s).2 (by omega)

/-- **Drain**: a lock stored at an honest node and live at a slot `σ` with `t_σ ≥ t₀ + 2Θ`
(`σ ≤ j + k` for its label `j`) sits below a clean raw origin of its label. -/
theorem h2_drain (hI : InclusionRun tr H U proposer g t₀) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
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
      rw [hw]; linarith only [hT, hΔ, hσ', hlk]
    have htj : sp.ts l.slot ≤ tr.time j := by
      obtain ⟨ℓ, C, ⟨-, -, ht, -⟩, -⟩ := hsl
      rw [ht]; linarith only [hΔ]
    exact ⟨B, hLB, cleanOrigin_iff.2 (Or.inr ⟨y, hy, j,
      joined_of_ge hI hy (hr.time_nonneg j) htj (by
          linarith only [hT, hg, hσ', hlk, hkΔ, hw, hwin]), hsl, hwin⟩)⟩
  · obtain ⟨j, -, B, CV, hfl, hLB⟩ := fast_lock_provenance hr hy i l hl hf
    have hj : t₀ + 4 * sp.Δ ≤ sp.ts l.slot := by linarith only [hT, hΔ, hσ', hlk, hkΔ]
    exact ⟨B, hLB, cleanOrigin_iff.2 (Or.inl ⟨y, hy, j, CV,
      joined_of_ge hI hy (hr.time_nonneg j) (fastLock_time hI hfl) (by
          linarith only [hg, hj]), hfl, hj⟩)⟩

/-- **Settled locks**: from `t₀ + 2Θ + 4Δ` on, every lock live at an honest node is carried by
every later honest duty. -/
theorem h2_locks_settled (hI : InclusionRun tr H U proposer g t₀) :
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

/-- Current-cut result-prefix transfer. Service and viability are current inputs;
stored older locks and earlier same-label votes account for the live read-point locks. -/
theorem result_prefix_vote_extends_of_stored (hrun : ACRun proposer tr H U)
    (hf : 2 * Hᶜ.ncard < sp.n) {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H)
    {r s i : Nat} {B C : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hres : ResultAt tr x r s C CV) (hBC : Anc U B C)
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hcarry : CarryAt tr U y i e s CV) (hviab : ViableAtVote ℓ e (s + 1) B)
    (hstored : ∀ l ∈ (tr.state y i).locks,
      sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
      ∀ Y ∈ U, Y.root = l.block → Compatible U Y B)
    (hE : EarlierVotesExtend tr H U i (s + 1) B)
    (hmerged : ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state x r).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state x r).pool s}) :
    VoteExtends U e.msg B :=
  result_transfer_anc sp hrun hx hres hBC hy hc hs hcarry hviab
    (live_locks_of_stored_before hrun hf hy hc hs hstored hE) hmerged

/-- Later transfer needs extension only at earlier cuts, for the predecessor and
current labels. Slot monotonicity places every predecessor vote before this cast. The `Sync`
argument is no longer needed (A1.3 dropped it); it stays for the callers' interface. -/
theorem next_vote_extends_before (hrun : ACRun proposer tr H U)
    {m i : Nat} {y : Fin sp.n} {B : Blk sp.n FGP}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hy : y ∈ H) (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = m + 1)
    (hprior : ∀ z ∈ H, ∀ q < i, ∀ e', VoteAt tr z q e' →
      (e'.msg.slot = m ∨ e'.msg.slot = m + 1) → VoteExtends U e'.msg B)
    (hhalf : sp.n ≤ 2 * {z | z ∈ H ∧ ∃ q e', VoteAt tr z q e' ∧ e'.msg.slot = m}.ncard)
    (hcarry : CarryAt tr U y i e m
      {v | ∃ z ∈ H, ∃ q e', VoteAt tr z q e' ∧ e'.msg = v ∧ v.slot = m})
    (hfault : FaultBound tr H (tr.time i))
    (_hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts m) (tr.time i) tr)
    (hviab : ViableAtVote ℓ e (m + 1) B) : VoteExtends U e.msg B := by
  refine next_transfer sp FGP ro H U tr proposer hrun m y i B ℓ e hy hc hs ?_
    hhalf hcarry hfault hviab (fun z hz q hq e' hv he =>
      hprior z hz q hq e' hv (Or.inr he))
  intro z hz q e' hv he
  have hqi : q < i := by
    by_contra hn
    obtain ⟨ell, hcast⟩ := hv
    have hq := (castAt_spec hrun.localRun hz hcast).2.1
    have hi := (castAt_spec hrun.localRun hy hc).2.1
    have hmono := slot_mono sp (hrun.localRun.time_nonneg i)
      (hrun.localRun.time_mono (Nat.le_of_not_gt hn))
    omega
  exact hprior z hz q hqi e' hv (Or.inl he)

end Consensus.Goldilocks.SA

end
