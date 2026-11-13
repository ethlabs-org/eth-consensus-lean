module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.LiveVotes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Later
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.TransferLater
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameSources
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The adoption of a proposal after a hand-over

For the proposal `P` of a slot `s` after a hand-over whose honest slot-`s` votes are all `P`:

* `seeded_member_anc_proposal`: every member of the healed family of a label `≤ s` is below `P`
  (S2 at slot `s`, or the honest supporter of the member's origin of label `s`);
* `seeded_votes_succ_extend`: every honest slot-`(s+1)` vote extends `P`, for `s ≥ σ + 1`
  (`later_transfer_step_at`, with the frozen witness `seeded_vote_frame_of`);
* `seeded_updater_F_anc`: at an update of slot `s` at `t_s + 6Δ ≥ t₁`, the updater's `Σ.F` is below
  `P` (low updater: below the reset seed, a member of a label `< r`; high updater: `Σ.J` is below a
  source of a high row, below a member of a label `≤ s + 1`, compatible with `P`);
* `seeded_result_not_vetoed`: a result of an update at a time in `[t₁, b]` that is a member of the
  healed family is not vetoed (the live lock blocks are on the healed chain);
* `seeded_adopt_result`: for `s ≥ σ + 1` and `t_s ≥ t₁`, every honest update of slot `s` returns
  `P`, not vetoed. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF : Time}
  {T : Time} {r σ : Nat} {t₁ b : Time} {s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}

/-- **Every member of a label `≤ s` is below `P`** when every honest slot-`s` vote is `P`, through
`b ≥ t_s + Δ`: a member of a label `< s` is extended by the vote of a slot-`s` voter awake and
joined at `t_s + Δ` (S2); a member of label `s` is below its origin of label `s`, whose honest
supporter votes `P`. -/
theorem seeded_member_anc_proposal (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b)
    (hrs : r ≤ s) (hPU : P ∈ tr.HonestBlocksAt H) (hsb : sp.ts s + sp.Δ ≤ b)
    (hall : ∀ x j e, HVoteAt tr H x j e → e.msg.slot = s → e.msg.head = P.root)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {l : Nat}
    (hC : HealedOrigin tr H g r (r + sp.k - 1) C l b) (hl : l ≤ s) :
    Anc (tr.HonestBlocksAt H) C P := by
  have hΔ := sp.toParams.hΔ
  have hU := honestBlocksAt_coherent hS.run hS.noColl
  rcases hl.lt_or_eq with hlt | rfl
  · have hcount := hS.bounds.slot s (sp.ts s + sp.Δ) hrs le_rfl hsb (by linarith)
    obtain ⟨x, hx, hw, hjx⟩ := Set.nonempty_of_ncard_ne_zero (Nat.zero_lt_of_lt hcount).ne'
    obtain ⟨k, e, hv, hes, hkt⟩ := vote_of_awake_joined_at hS.run hS.noColl hx
      (mayVote_stock_at hS.run hS.noColl (ts_add_delta_nonneg _) hx) hw hjx
    obtain ⟨Hd, hHd, hHdr, hCH⟩ :=
      hS.inv.vote_extends C l hC x k e hv (hkt.trans hsb) (by omega)
    rwa [hU.1 hHd hPU (hHdr.trans (hall x k e hv hes))] at hCH
  · obtain ⟨O, hO, hCO⟩ := hC.below_origin hS.run hS.noColl
    obtain ⟨x, k, e, hv, hkb, hes, Hd, hHd, hHdr, hOHd⟩ := honest_supporter_at hS.run (fun _
        _ => rfl) hS.noColl
      hS.sync hS.bounds hrs (by linarith [hS.gbar_le hrs]) hO
    rw [hU.1 hHd hPU (hHdr.trans (hall x k e hv hes))] at hOHd
    exact hCO.trans hOHd

/-- **Every honest slot-`(s+1)` vote extends `P`**, for `s ≥ σ + 1`, when every honest slot-`s`
vote is `P`, through `b ≥ t_s + Δ`: by induction on the vote's cut, `later_transfer_step_at` for
the block `P`, compatible with every member of a label `≤ s` (`seeded_member_anc_proposal`), with
the live locks of the vote of labels `≥ r` (`handover_live_lock_label_at`) and the frozen witness
`seeded_vote_frame_of`. -/
theorem seeded_votes_succ_extend (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b)
    (hs : σ + 1 ≤ s) (hPU : P ∈ tr.HonestBlocksAt H) (hsb : sp.ts s + sp.Δ ≤ b)
    (hall : ∀ x j e, HVoteAt tr H x j e → e.msg.slot = s → e.msg.head = P.root) :
    ∀ x j e, HVoteAt tr H x j e → e.msg.slot = s + 1 → tr.time j ≤ b →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨-, hrs, hga, -⟩ := hS.slot_timing hs
  have hrs' : r ≤ s := by have := sp.two_le_k; omega
  have hBc : ∀ C j, HealedOrigin tr H g r (r + sp.k - 1) C j b → j ≤ s →
      Compatible (tr.HonestBlocksAt H) P C := fun C j hC hj =>
    Or.inr (seeded_member_anc_proposal hS hrs' hPU hsb hall hC hj)
  have hPb : HealedOriginsBelow tr H g r (r + sp.k - 1) (s + 1) b :=
    healedOriginsBelow_iff.2 fun C j C' j' _ _ hC hC' => hS.inv.origins_compatible C j C' j' hC hC'
  have hsa : SA.gbar g + 2 * sp.Δ ≤ sp.ts s := by
    have := hS.gbar_le hrs'
    linarith
  intro x j
  induction j using Nat.strong_induction_on generalizing x with
  | _ j ih =>
    intro e hv hes hjb
    obtain ⟨hx, ℓ, hc, he⟩ := hVoteAt_iff.1 hv
    exact later_transfer_step_at hS.run (fun _ _ => rfl) hS.noColl hS.sync hS.bounds (g := g)
        (rL := r)
      (rO := r + sp.k - 1) hrs' hsa hx ⟨hc, he⟩ hes hjb
      (fun l hl _ => handover_live_lock_label_at hS.seed hx ⟨hc, he⟩ (by omega) l hl) hBc
      (fun hw => seeded_vote_frame_of hS.run hS.noColl hS.seed hS.horizon hS.service hS.bounds
        hS.conv hs hPb hx ⟨hc, he⟩ hes hjb (fun C l hC hl => hBc C l hC hl) hw)
      (fun x k e' hv hs => ⟨P, hPU, (hall x k e' hv hs).symm, .refl⟩)
      (fun z j' hj' hz e' hv' hs' => ih j' hj' z e' (hVoteAt_iff.2 ⟨hz, hv'⟩) hs'
        ((hS.run.time_mono hj'.le).trans hjb))

/-- **The updater's `Σ.F` is below `P`** at an update of slot `s ≥ σ + 1` at `t_s + 6Δ ∈ [t₁, b]`,
when every honest slot-`s` vote is `P` and every honest slot-`(s+1)` vote extends it: `Σ.F` is
compatible with `P` (`updater_F_anc_of_compatible`). A low updater's `Σ.F` is below the reset
seed, a member of a label `< r`, below `P`. A high updater's `Σ.J` is below the source of a high
row, below a member written before the update, of a label `≤ s + 1`: below `P` for a label `≤ s`,
and below an optimistic origin of label `s + 1` whose honest supporter extends `P`. -/
theorem seeded_updater_F_anc (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b)
    (hs : σ + 1 ≤ s) (hPU : P ∈ tr.HonestBlocksAt H) (hPs : P.slot = s)
    (hall : ∀ x j e, HVoteAt tr H x j e → e.msg.slot = s → e.msg.head = P.root)
    {y : Fin sp.n} {k₀ : Nat} (hy : y ∈ H (tr.time k₀)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) (ht₁ : t₁ ≤ tr.time k₀) (hb : tr.time k₀ ≤ b) :
    Anc (tr.HonestBlocksAt H) (tr.state y k₀).fg.F P := by
  have hΔ := sp.toParams.hΔ
  have hk := sp.two_le_k
  have hrun := hS.run
  have hnc := hS.noColl
  have hU := honestBlocksAt_coherent hrun hnc
  obtain ⟨-, hrs, -, -⟩ := hS.slot_timing hs
  have hrs' : r ≤ s := by omega
  have ht : tr.time k₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have hsb : sp.ts s + sp.Δ ≤ b := by linarith
  have hmem := fun {C} {l} (hC : HealedOrigin tr H g r (r + sp.k - 1) C l b) (hl : l ≤ s) =>
    seeded_member_anc_proposal hS hrs' hPU hsb hall hC hl
  have hsucc := seeded_votes_succ_extend hS hs hPU hsb hall
  have hd := hrun.time_nonneg k₀
  have hi : ∀ q < k₀, tr.time q ≤ tr.time k₀ := fun _ h => hrun.time_mono h.le
  have hdt : sp.ts (r + sp.k : Nat) ≤ tr.time k₀ := hS.drain.trans ht₁
  have hcall := hS.called hy hdt le_rfl
  have hf := hS.bounds.two _ hd hb
  set R : SA.Blk sp.n (List (FG.Att sp.n)) → Prop := fun D => Compatible (tr.HonestBlocksAt H) D P
  have hRc : ∀ A B, Anc (tr.HonestBlocksAt H) A B → R B → R A := by
    rintro A B hAB (hBP | hPB)
    · exact Or.inl (hAB.trans hBP)
    · exact Anc.total hU hAB hPB
  refine updater_F_anc_of_compatible hrun hnc hPU hPs hy hu ?_
  have hreach := Healing.Growing.fg_reachable_at hrun hd hi hy
  obtain ⟨-, hJm, hFJ, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hreach
  have hFJ' := Healing.Growing.honest_anc_of_store_anc_at hd hi hy hFJ
  by_cases hlow : (tr.state y k₀).fg.hj ≤ Healing.Growing.HZ tr H g
  · obtain ⟨x, q, l, S, hS', hqT, hl, hFS, -, -⟩ :=
      low_seed_held hrun hnc hS.conv hS.seed hd hi hy hcall hlow
    exact Or.inl (hFS.trans (hmem (.of_high (hqT.trans hS.horizon) hS') (by omega)))
  -- the high rows, sourced below members compatible with `P`
  have hst := Trace.upTo_state tr y hi
  have hrun' := hrun.upTo hd
  have hnc' := hnc.upTo (tr.time k₀)
  have hsub := upTo_subset hrun hd
  have hsl₀ : sp.slot (tr.time k₀) = s + 1 := by
    have h6 : sp.ts s + 6 * sp.Δ = sp.ts ((s + 1 : Nat) : Int) + 2 * sp.Δ :=
      (SA.slot_arithmetic sp s).2.2
    rw [ht, h6]
    simpa using (SA.slot_arithmetic sp (s + 1)).1 2 (by omega)
  have hsrc := rowsAbove_of hrun hnc hS.seed hd hi hy (Q := fun C _ => R C)
    fun m hm X hX a ha hav k hkm hsg c hck C l O OV hC hO => by
      have hck₀ : tr.time c ≤ tr.time k₀ := hrun.time_mono (by omega)
      have hCb := hC.mono (hck₀.trans hb)
      rcases hO with hR | hOp
      · obtain ⟨ℓ', hu', _⟩ := hR
        have ht' : tr.time c = sp.ts l + 6 * sp.Δ := hu'.2.2.1
        have hl : l ≤ s := by
          have : sp.ts (l : Int) ≤ sp.ts (s : Int) := by linarith
          exact_mod_cast (SA.ts_le_iff sp).1 this
        exact Or.inl (hmem hCb hl)
      obtain ⟨ℓ', A, -, hslc, -⟩ := id hOp
      change sp.slot (tr.time c) = l at hslc
      have hl : l ≤ s + 1 := by
        rw [← hslc, ← hsl₀]
        exact SA.slot_mono sp (hrun.time_nonneg c) hck₀
      rcases Nat.lt_or_ge l (s + 1) with hls | hls
      · exact Or.inl (hmem hCb (by omega))
      obtain rfl : l = s + 1 := le_antisymm hl hls
      obtain ⟨O', hO', hCO'⟩ := hC.below_origin hrun hnc
      obtain ⟨z, j, e, hv, hjb, hes, Hd, hHd, hHdr, hOH⟩ := honest_supporter_at hrun (fun _
          _ => rfl) hnc
        hS.sync hS.bounds (by omega) (by linarith [hS.gbar_le (show r ≤ s + 1 by omega)])
        (hO'.mono (hck₀.trans hb))
      obtain ⟨Hd', hHd', hHd'r, hPH⟩ := hsucc z j e hv hes (hjb.trans le_rfl)
      obtain rfl : Hd' = Hd := hU.1 hHd' hHd (hHd'r.trans hHdr.symm)
      exact Anc.total hU (hCO'.trans hOH) hPH
  have hsrc' := rowsAbove_height_mono hsrc
    (show Healing.Growing.HZ tr H g + 1 ≤ ((tr.upTo (tr.time k₀)).state y k₀).fg.hj by
      rw [hst]; omega)
  obtain ⟨-, -, D, ⟨C, l, hCR, -, hDC⟩, hDs⟩ := Compose.justified_honest_source_of hrun' hnc' hf
    hy hsrc' (by rw [hst]; omega)
  rw [hst] at hDs
  have hJP : (tr.state y k₀).fg.J ∈ (tr.upTo (tr.time k₀)).HonestBlocks (H (tr.time k₀)) :=
    ⟨y, hy, k₀, by rw [hst]; exact hJm⟩
  obtain ⟨x', hx', k', -, -, hJD, -, -⟩ := Compose.honest_source_entry hrun' hnc' hDs hJP rfl
  have hJR : R (tr.state y k₀).fg.J := hRc _ _
    ((Anc.mono (fun Z hZ => hsub ⟨x', hx', k', hZ⟩) hJD).trans (hDC.mono hsub)) hCR
  exact hRc _ _ hFJ' hJR

/-- **A result of an update at a time in `[t₁, b]` that is a member of the healed family is not
vetoed**: every live lock block of the updater is on the healed chain (`seeded_locks_at`), so
compatible with the member. -/
theorem seeded_result_not_vetoed (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b)
    {y : Fin sp.n} {k₀ m : Nat} (hy : y ∈ H (tr.time k₀)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ m ℓ) (ht₁ : t₁ ≤ tr.time k₀) (hb : tr.time k₀ ≤ b)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {l : Nat}
    (hC : HealedOrigin tr H g r (r + sp.k - 1) C l b) (hCt : C ∈ ℓ.frame.tree) :
    ¬ SA.conflictsWithLock sp (tr.state y k₀).ac.locks ℓ.frame (tr.time k₀) C := by
  have hrun := hS.run
  have hnc := hS.noColl
  have hU := honestBlocksAt_coherent hrun hnc
  obtain ⟨hΦ, hHB⟩ := frameIn_at hrun hnc hy hu.1
  have hfr := frame_of_projAC_at hrun hy hu.1
  rintro ⟨V, hV, hconf⟩
  have hVc := seeded_locks_at hrun hnc hS.seed (hS.drain.trans ht₁)
    (fun q hq => hrun.time_mono hq.le) hb hy V (by rw [← hfr]; exact hV)
  have hcomp := OnHealedChain.compatible hrun hnc hS.inv.origins_compatible hVc hC
  apply hconf
  rcases hcomp with h | h
  · exact Or.inr (SA.anc_tree_of_anc_U hU hΦ hHB hV.1 h hCt)
  · exact Or.inl (SA.anc_tree_of_anc_U hU hΦ hHB hCt h hV.1)

/-- **Every honest update of a slot `s ≥ σ + 1` returns the proposal `P`, not vetoed**, for the
proposal of slot `s` at `t_s ≥ t₁` by a proposer honest at `t_s + Δ`, through `b ≥ t_s + 6Δ`: every
honest slot-`s` vote is `P` (`seeded_votes_eq_proposal`), the updater's `Σ.F` is below `P`
(`seeded_updater_F_anc`), so `P` is held above it with a strict majority
(`proposal_held_at_update_from`, `proposal_majority_at_update_from`, `adopt_result_of`); the
result is an origin of label `s ≥ r + k − 1`, a member, so not vetoed. -/
theorem seeded_adopt_result (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b)
    (hs : σ + 1 ≤ s) {p : Fin sp.n} {k : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) (ht₁ : t₁ ≤ sp.ts s)
    {y : Fin sp.n} {k₀ : Nat} (hy : y ∈ H (tr.time k₀)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) (hb : tr.time k₀ ≤ b) :
    SA.getConfirmation sp (tr.state y k₀).ac ℓ.frame s = some P ∧
      ¬ SA.conflictsWithLock sp (tr.state y k₀).ac.locks ℓ.frame (tr.time k₀) P := by
  have hΔ := sp.toParams.hΔ
  have hrun := hS.run
  have hnc := hS.noColl
  have ht : tr.time k₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  obtain ⟨-, hrs, -, -⟩ := hS.slot_timing hs
  have hrs' : r ≤ s := by have := sp.two_le_k; omega
  have hga : SA.gbar g + 2 * sp.Δ ≤ sp.ts s := by linarith [hS.gbar_le hrs']
  have hkt : tr.time k = sp.ts s := by rw [hP.2.2, sp.slotTime_eq, hPs]; rfl
  have hPU := proposal_honest_at hrun hnc (hrun.antitone (by rw [hkt]; linarith) hp) hP
  have hall := seeded_votes_eq_proposal hS hs hp hP hPs ht₁ (by linarith)
  have hF := seeded_updater_F_anc hS hs hPU hPs hall hy hu (by linarith) hb
  obtain ⟨hPt, hFP⟩ := proposal_held_at_update_from hrun hnc hS.sync hp hP hPs (by linarith) hy
    hu hb hF
  have hmaj := proposal_majority_at_update_from hrun hnc hS.sync hS.bounds hrs' (by linarith)
    (by linarith) hy hu hb hPt hall
  have hC := adopt_result_of hrun hnc hPs hy hu hPt hFP hmaj
  refine ⟨hC, seeded_result_not_vetoed hS hy hu (by linarith) hb (l := s)
    (.of_origin (by omega) (originWithin_iff.2 ⟨y, k₀, _, hy, hb,
      Or.inl ⟨ℓ, hu, by rw [projAC_state_at hrun hy]; exact hC, rfl⟩⟩)) hPt⟩

end Consensus.Goldilocks.Compose.Growing

end
