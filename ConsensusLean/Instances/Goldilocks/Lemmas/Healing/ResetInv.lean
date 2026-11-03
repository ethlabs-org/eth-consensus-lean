module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Bridge
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.AtCall
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.RawAtCall
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyEffective

public section

/-! # Goldilocks Healing: H.3 (c), the `Inv` half after the reset

The retention premise `Inv(a_z + T_b)` on the AC projection (claims H.3 (c1)/(c2)), with the
parameter-only offset `T_b = (8k + 20)Δ` (`resetInvOffset`). The offset puts the label of every
protected target after the drain `R = t_{slot(a_z) + 2k + 5}`, so every live lock at its votes is
clean (workbench `healing_bundles_route.md` §4).

The proof works one protected target `(B, j)` at a time:

* `protected_clean_source` (route L1): every target has an honest fast-lock or slow-lock source
  of its label, after the drain (a unanimous proposal through `unanimous_target_fast_update`);
* `protected_votes_extend`: every honest vote of a slot `> j` extends `B`, by the landed
  clean-source transfer `clean_source_votes_before` (route L3–L6 need no new lemma);
* `protected_vote_domain`: at those votes `B` is in the viable voter block tree or at or below
  `fc_root`, by the landed `result_prefix_vote_domain_before` (fast-update, slow and unanimous
  targets) and `optimistic_target_vote_domain` (route L2);
* `protected_call_viable`: at every honest call from `t_{j+1}` on, `B` is at or below `fc_root`
  or in the viable tree of the whole frame tree (route L7–L9).

-/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- The offset `T_b = (8k + 20)Δ` of H.3 (c), a function of the parameters `k` and `Δ` only
(`Δ` is clamped at `0` so that the offset is nonnegative for every argument, as H.3 asks; for
the positive `Δ` of `SAParams` it is `(8k + 20)Δ`, `resetInvOffset_eq`). -/
def resetInvOffset (k : Nat) (Δ : Time) : Time := (8 * (k : Time) + 20) * max Δ 0

theorem resetInvOffset_nonneg (k : Nat) (Δ : Time) : 0 ≤ resetInvOffset k Δ := by
  unfold resetInvOffset
  have : (0 : Time) ≤ k := Int.natCast_nonneg k
  have : (0 : Time) ≤ max Δ 0 := le_max_right _ _
  nlinarith

theorem resetInvOffset_eq (k : Nat) {Δ : Time} (hΔ : 0 ≤ Δ) :
    resetInvOffset k Δ = (8 * (k : Time) + 20) * Δ := by
  rw [resetInvOffset, max_eq_left hΔ]

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- **The label of a protected target is after the drain** (route L1, label part): every
`(B, j) ∈ 𝒫(a + T_b)` has `j ≥ slot(a) + 2k + 6`, so `t_j > R = t_{slot(a) + 2k + 5}`. The
stronger window bound `slot(a) + 2k + 6 ≤ j − k + 1` holds in the (P2) case only (a pair can be
protected through (P1) or (P3) while some other node writes a slow lock of label `j`), so the
slow-lock step takes it from the (P2) witness, not from the pair. -/
theorem protected_label_after_drain (hp : ResetPremises tr H proposer dg g ΔF a)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat}
    (hB : SA.Protected proposer tr.projAC H (a + resetInvOffset sp.k sp.Δ) B j) :
    sp.slot a + 2 * sp.k + 6 ≤ j := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hΔ := sp.toParams.hΔ
  have hk := sp.two_le_k
  obtain ⟨y, -, k, att, hk', -, hka⟩ := hp.reset.1
  have ha0 : 0 ≤ a := hka ▸ hp.run.time_nonneg k
  have hsa : sp.ts (sp.slot a : Int) ≤ a := (SA.ts_le_iff_le_slot sp ha0 _).mpr le_rfl
  rw [resetInvOffset_eq sp.k hΔ.le] at hB
  -- `t₀ + 4Δ ≤ t_m` puts `m` after the drain
  have hlab : ∀ m : Int, a + (8 * (sp.k : Time) + 20) * sp.Δ + 4 * sp.Δ ≤ sp.ts m →
      ((sp.slot a + 2 * sp.k + 6 : Nat) : Int) ≤ m := by
    intro m hm
    apply (SA.ts_le_iff sp).mp
    simp only [SAParams.ts] at hsa hm ⊢
    push_cast
    nlinarith
  have hΘ : 0 ≤ 2 * SA.Θ sp + 4 * sp.Δ := by
    unfold SA.Θ
    have : (0 : Time) ≤ sp.k := Int.natCast_nonneg _
    nlinarith
  rcases hB with ⟨-, -, -, -, -, -, hs⟩ | ⟨x, hx, i, hj, hl, hs⟩ | ⟨-, -, hs, -⟩
  · exact_mod_cast hlab j hs
  · have h := hlab _ hs
    omega
  · exact_mod_cast hlab j (by linarith)

/-- **The classes of a protected target** (route L1): a protected `(B, j)` after the reset is
(a) a fast-test selection, below the result of its writer's update; (b) an optimistic selection;
(c) a slow-lock block, below the result of its writer's update, with its whole window after the
drain; or (d) a unanimous honest proposal. Every label is after the drain. -/
theorem protected_target_cases (hp : ResetPremises tr H proposer dg g ΔF a)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat}
    (hB : SA.Protected proposer tr.projAC H (a + resetInvOffset sp.k sp.Δ) B j) :
    sp.slot a + 2 * sp.k + 6 ≤ j ∧
      ((∃ x ∈ H, ∃ i CV, SA.JoinedAt tr.projAC x (tr.time i) ∧
          SA.FastUpdateAt tr.projAC x i j B CV ∧
          ∃ C CV', SA.ResultAt tr.projAC x i j C CV' ∧ Anc (tr.HonestBlocks H) B C) ∨
        (∃ x ∈ H, ∃ i CV, SA.JoinedAt tr.projAC x (tr.time i) ∧
          SA.OptimisticLockAt tr.projAC x i j B CV) ∨
        (∃ x ∈ H, ∃ i, SA.JoinedAt tr.projAC x (tr.time i) ∧ SA.SlowLockAt tr.projAC x i j B ∧
          ((sp.slot a + 2 * sp.k + 6 : Nat) : Int) ≤ (j : Int) - sp.k + 1 ∧
          ∃ C CV', SA.ResultAt tr.projAC x i j C CV' ∧ Anc (tr.HonestBlocks H) B C) ∨
        (proposer j ∈ H ∧ SA.HonestProposal tr.projAC (proposer j) j B ∧
          ∀ x ∈ H, ∀ k e, SA.VoteAt tr.projAC x k e → e.msg.slot = j → e.msg.head = B.root)) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hΔ := sp.toParams.hΔ
  obtain ⟨y, -, k, att, -, -, hka⟩ := hp.reset.1
  have ha0 : 0 ≤ a := hka ▸ hp.run.time_nonneg k
  have hsa : sp.ts (sp.slot a : Int) ≤ a := (SA.ts_le_iff_le_slot sp ha0 _).mpr le_rfl
  have hlab : ∀ m : Int, a + resetInvOffset sp.k sp.Δ + 4 * sp.Δ ≤ sp.ts m →
      ((sp.slot a + 2 * sp.k + 6 : Nat) : Int) ≤ m := by
    intro m hm
    rw [resetInvOffset_eq sp.k hΔ.le] at hm
    apply (SA.ts_le_iff sp).mp
    simp only [SAParams.ts] at hsa hm ⊢
    push_cast
    nlinarith
  refine ⟨protected_label_after_drain hp hB, ?_⟩
  rcases hB with ⟨x, hx, i, CV, hj, hfl, -⟩ | ⟨x, hx, i, hj, hsl, hs⟩ | ⟨hp', hP, -, hun⟩
  · rcases hfl with hfu | hop
    · refine Or.inl ⟨x, hx, i, CV, hj, hfu, ?_⟩
      obtain ⟨ℓ, C, hupd, hconf, hfast, -⟩ := id hfu
      have hBC := (SA.deepest_mem hfast).1.1.2.2
      exact ⟨C, _, ⟨ℓ, hupd, hconf, rfl⟩,
        Anc.mono (SA.frameIn_of_callAt hr hx hupd.1).2 hBC⟩
    · exact Or.inr (Or.inl ⟨x, hx, i, CV, hj, hop⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨x, hx, i, hj, hsl, hlab _ hs, ?_⟩))
    obtain ⟨ℓ, C, hupd, hconf, hdeep⟩ := id hsl
    have hBC := (SA.deepest_mem hdeep).1.1.2.2
    exact ⟨C, _, ⟨ℓ, hupd, hconf, rfl⟩,
      Anc.mono (SA.frameIn_of_callAt hr hx hupd.1).2 hBC⟩
  · exact Or.inr (Or.inr (Or.inr ⟨hp', hP, hun⟩))

/-- A deepest block of `T` lying in `S ⊆ T` is the deepest block of `S`. -/
private theorem deepest_of_subset {FGP : Type} {Φ : SA.Frm sp.n FGP}
    {S T : Set (SA.Blk sp.n FGP)} {D : SA.Blk sp.n FGP} (hT : SA.deepest Φ T = some D)
    (hST : S ⊆ T) (hD : D ∈ S) : SA.deepest Φ S = some D := by
  have h : SA.IsDeepest Φ S D := ⟨hD, fun C hC hne => (SA.deepest_mem hT).2 C (hST hC) hne⟩
  cases hd : SA.deepest Φ S with
  | none =>
    unfold SA.deepest at hd
    simp only [show ∃ B, SA.IsDeepest Φ S B from ⟨D, h⟩, ↓reduceDIte, reduceCtorEq] at hd
  | some D' =>
    have h' := SA.deepest_mem hd
    by_contra hne
    have hne' : D' ≠ D := fun h => hne (congrArg some h)
    rcases h.2 D' h'.1 hne' with h₁ | ⟨h₁, h₂⟩ <;>
      rcases h'.2 D h.1 (Ne.symm hne') with h₃ | ⟨h₃, h₄⟩ <;> omega

/-- An honest proposal is the proposer's own block at its slot start (as
`Refinement.proposesAt_of_honestProposalRun`). -/
private theorem proposesAt_of_honestProposal (hrun : GoldilocksRun proposer dg H tr) {s : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hpH : proposer s ∈ H)
    (hP : SA.HonestProposal tr.projAC (proposer s) s P) :
    ∃ k, tr.ProposesAt (proposer s) k P := by
  have hl := hrun.toLocalRun
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hPp, -, j, -, hacc, -⟩ := hP
  obtain ⟨j₀, -, ha, -⟩ := fg_accept_before hl hpH hacc
  obtain ⟨j', -, ⟨acc, hc⟩, hpos⟩ := hl.block_unforgeable _ hpH j₀ P ⟨true, ha⟩ (hPp ▸ hpH)
  rw [hPp] at hc
  rcases Compose.blockCall_cases hl hpH hc with hg | ⟨j₁, x, rfl, -, hpr, d', pay', -, hB, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  · have hs : P.slot = sp.toParams.slotOf (tr.time (j₁ + 2)) := by rw [hB]; rfl
    exact ⟨j₁ + 2, ⟨⟨acc, hc⟩, hpos⟩, hPp, hs ▸ hpr.2.1⟩

/-- **A unanimous protected proposal is an honest fast-update selection** (route L5′): an honest
proposal of a post-drain slot `j` is the result and the fast selection of its own proposer's
slot-`j` update (`Refinement.UpTo.operational_update_selection`, the one Refinement theorem this
module imports; reviewed exception in `scripts/boundaries.toml`). -/
theorem unanimous_target_fast_update (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat} (hj : sp.slot a + 2 * sp.k + 6 ≤ j)
    (hpj : proposer j ∈ H) (hP : SA.HonestProposal tr.projAC (proposer j) j B) :
    ∃ x ∈ H, ∃ i CV, SA.FastUpdateAt tr.projAC x i j B CV ∧
      ∃ CV', SA.ResultAt tr.projAC x i j B CV' := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨k, hactual⟩ := proposesAt_of_honestProposal hp.run hpj hP
  obtain ⟨-, -, -, -, -, -, -, -, -, hPs, -⟩ := hP
  obtain ⟨-, -, kr, -, -, -, hka⟩ := hp.reset.1
  have ha0 : 0 ≤ a := hka ▸ hp.run.time_nonneg kr
  have hlt : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
    have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
    omega
  have hle : sp.ts ((sp.slot a : Int) + 1) ≤ sp.ts j := (SA.ts_le_iff sp).2 (by omega)
  have hca := cutZ_lt_reset hp.run hp.healthy hp.reset
  have hz := lt_cutZ sp g
  have hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts j := by linarith
  have hR : drainTime sp a ≤ sp.ts j := by
    rw [drainTime_eq]; exact (SA.ts_le_iff sp).2 (by push_cast; omega)
  have hab : a ≤ sp.ts j + 6 * sp.Δ := by linarith
  have hp' := hp.toUpTo tr H hab
  have hu : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) ≤ sp.ts j := by
    have h₁ : sp.ts (sp.slot (SA.gbar g) : Int) ≤ SA.gbar g :=
      (SA.ts_le_iff_le_slot sp (SA.gbar_nonneg g) _).mpr le_rfl
    have h₂ : sp.ts ((sp.slot (SA.gbar g) + 1 : Nat) : Int) =
        sp.ts (sp.slot (SA.gbar g) : Int) + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    linarith
  obtain ⟨i, ell, -, hup, -⟩ := hp'.update_toFG_calls hpj hu le_rfl
  obtain ⟨-, hconf, hnv, hsel, -⟩ := Refinement.UpTo.operational_update_selection hp' hc hpj rfl
    hactual hPs hR hgu le_rfl hpj hup
  have hsel' := deepest_of_subset (S := {X | X ∈ SA.confirmationPath sp ell.frame B ∧
      ¬ SA.conflictsWithLock sp (tr.projAC.state (proposer j) i).locks ell.frame (tr.time i) X ∧
      SA.FastTest sp (tr.projAC.state (proposer j) i) ell.frame j X}) hsel
    (fun X hX => ⟨hX.1, hX.2.2⟩)
    ⟨(SA.deepest_mem hsel).1.1, hnv, (SA.deepest_mem hsel).1.2⟩
  exact ⟨proposer j, hpj, i, _, ⟨ell, B, hup, hconf, hsel', rfl⟩, _, ⟨ell, hup, hconf, rfl⟩⟩

/-- **Every protected target has a clean source** (route L1): an honest fast lock or slow lock
of its label, which is after the drain. -/
theorem protected_clean_source (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat}
    (hB : SA.Protected proposer tr.projAC H (a + resetInvOffset sp.k sp.Δ) B j) :
    sp.slot a + 2 * sp.k + 6 ≤ j ∧ ∃ x ∈ H, ∃ r,
      (∃ CV, SA.FastLockAt tr.projAC x r j B CV) ∨ SA.SlowLockAt tr.projAC x r j B := by
  obtain ⟨hj, hcase⟩ := protected_target_cases hp hB
  refine ⟨hj, ?_⟩
  rcases hcase with ⟨x, hx, i, CV, -, hfu, -⟩ | ⟨x, hx, i, CV, -, hop⟩ |
      ⟨x, hx, i, -, hsl, -⟩ | ⟨hpj, hP, hun⟩
  · exact ⟨x, hx, i, Or.inl ⟨CV, Or.inl hfu⟩⟩
  · exact ⟨x, hx, i, Or.inl ⟨CV, Or.inr hop⟩⟩
  · exact ⟨x, hx, i, Or.inr hsl⟩
  · obtain ⟨x, hx, i, CV, hfu, -⟩ := unanimous_target_fast_update hp hc hj hpj hP
    exact ⟨x, hx, i, Or.inl ⟨CV, Or.inl hfu⟩⟩

/-- Every honest vote of a slot `> j` extends a protected target `(B, j)`: the landed
clean-source transfer `clean_source_votes_before`, at a horizon past both the source write and
the vote. -/
theorem protected_votes_extend (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat}
    (hB : SA.Protected proposer tr.projAC H (a + resetInvOffset sp.k sp.Δ) B j) :
    ∀ k, ∀ z ∈ H, ∀ e, SA.VoteAt tr.projAC z k e → j < e.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  rintro k z hz e ⟨ℓ, hcast⟩ hj
  obtain ⟨hlab, x, hx, r, horig⟩ := protected_clean_source hp hc hB
  exact clean_source_votes_before hp hc (max (tr.time r) (tr.time k)) hx horig
    (by rw [cleanLabel_eq]; omega) (le_max_left _ _) k (le_max_right _ _) z hz ℓ e hcast hj

/-- **Vote domain of an optimistic target** (route L2): the optimistic counterpart of
`result_prefix_vote_domain_before`. The writer holds `B`, an honest optimistic voter's vote
extends it, and `held_target_vote_domain_before` gives the domain (heldness by writer relay,
the reset seed, and comparison with older, same-label and later high origins). -/
theorem optimistic_target_vote_domain (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H)
    {r s i : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hop : SA.OptimisticLockAt tr.projAC x r s B CV) (hs : cleanLabel sp a + sp.k + 2 ≤ s)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y i ell e) (hsi : s < e.msg.slot)
    (hprior : ∀ z ∈ H, ∀ q < i, ∀ e', SA.VoteAt tr.projAC z q e' →
      s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B ∧
      ((∃ W ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
        Anc (tr.HonestBlocks H) B W ∧ (tr.state y i).fg.IsViable W) ∨
        Anc (tr.HonestBlocks H) B ell.frame.fcRoot) := by
  have hS := healthy_base_of_reset_catch hp hc
  have hr := hS.run.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have := hp.healthy.2.2
    have := Fin.pos x
    have hn : sp.n = sp.toParams.n := rfl
    omega
  have hfast : SA.FastLockAt tr.projAC x r s B CV := Or.inr hop
  -- the label is after the reset, hence after `ḡ + 4Δ`
  have hgs4 : SA.gbar g + 4 * sp.Δ ≤ sp.ts s := by
    obtain ⟨-, -, k, -, -, -, hka⟩ := hp.reset.1
    have ha0 : 0 ≤ a := hka ▸ hp.run.time_nonneg k
    have hlt : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
      omega
    have hle : sp.ts ((sp.slot a : Int) + 1) ≤ sp.ts s :=
      (SA.ts_le_iff sp).2 (by rw [cleanLabel_eq] at hs; omega)
    have := cutZ_lt_reset hp.run hp.healthy hp.reset
    have := lt_cutZ sp g
    linarith
  have hgs : SA.gbar g ≤ sp.ts s := by linarith
  have evidence : B ∈ (tr.state x r).fg.tree ∧
      ∃ z ∈ H, ∃ q e', SA.VoteAt tr.projAC z q e' ∧ e'.msg.slot = s ∧
        SA.VoteExtends (tr.HonestBlocks H) e'.msg B := by
    obtain ⟨ellX, A, hpt, hslot, hsel, -⟩ := hop
    have hΦU := (SA.frameIn_of_callAt hr hx hpt.1).2
    unfold SA.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    refine ⟨frame_tree_subset hp hx hpt.1 (SA.deepest_mem hsel).1.1, ?_⟩
    have h34 := (SA.deepest_mem hsel).1.2.1
    obtain ⟨z, ⟨v, hv, rfl, R, hR, hRr, hBR⟩, hz⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
        (t := SA.optimisticVoters sp A ellX.frame (sp.slot (tr.projAC.time r)) B) (by omega)
    obtain ⟨hvs, q, _, e', he, rfl⟩ :=
      SA.optimisticPoint_pool_vote hS.run hx hpt hv (not_not.mp hz)
    exact ⟨_, not_not.mp hz, q, e', he, hvs.trans hslot,
      R, hΦU hR, hRr, hBR.mono hΦU⟩
  obtain ⟨hBx, z, hz, q, e', hv, hvs, hVB⟩ := evidence
  refine held_target_vote_domain_before hp hx hy hBx hcast ?_ ?_ ?_
  · intro hF
    have hg := le_gbar g
    exact raw_writer_voterBlockTree_window_before hr (reset_raw_sync_window_before hp (tr.time i))
      (catch_window_of_reset_catch hp hc (tr.time i)) hx hy (Or.inr hfast) .refl hcast
      (by omega) le_rfl
      (by
        have hm := (SA.ts_le_iff sp).mpr (show (s : Int) ≤ e.msg.slot - 1 by omega)
        linarith) hF
  · obtain ⟨v, r₀, m, S, hS', -, hm⟩ := (hp.toUpTo tr H (le_refl a)).reset_seed
    have hms : m < s := by rw [cleanLabel_eq] at hs; omega
    exact ⟨v, r₀, m, S, hS', by omega,
      target_compatible_older_origin hp hS' hz hv hvs hms hVB⟩
  · intro v r₀ m O hri ho
    rcases lt_trichotomy m s with hm | rfl | hm
    · exact target_compatible_older_origin hp ho hz hv hvs hm hVB
    · obtain ⟨CV', hst⟩ := ho.2.2.1
      obtain ⟨_, D, hfl, hOD⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
      rcases SA.fastLock_fastLock_compatible hS hx hfast ho.1 hfl hgs with h | h
      · exact SA.anc_total hr.coherent h hOD
      · exact Or.inr (hOD.trans h)
    · exact target_compatible_later_origin_before hp ho hri hm hprior

/-- **Vote domain of a protected target** (route L1, L2): at an honest vote of a slot `> j`, `B`
is in the viable voter block tree or at or below `fc_root`. -/
theorem protected_vote_domain (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat}
    (hB : SA.Protected proposer tr.projAC H (a + resetInvOffset sp.k sp.Δ) B j)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcast : SA.CastAt tr.projAC y k ℓ e)
    (hj : j < e.msg.slot) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  have hprior : ∀ z ∈ H, ∀ q < k, ∀ e', SA.VoteAt tr.projAC z q e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B :=
    fun z hz q _ e' hv hj' => protected_votes_extend hp hc hB q z hz e' hv hj'
  obtain ⟨hlab, hcase⟩ := protected_target_cases hp hB
  have hclean : cleanLabel sp a + sp.k + 2 ≤ j := by rw [cleanLabel_eq]; omega
  have hdom : Compatible (tr.HonestBlocks H) ℓ.frame.fcRoot B ∧
      ((∃ W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
        Anc (tr.HonestBlocks H) B W ∧ (tr.state y k).fg.IsViable W) ∨
        Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) := by
    rcases hcase with ⟨x, hx, i, -, -, -, C, CV', hres, hBC⟩ | ⟨x, hx, i, CV, -, hop⟩ |
        ⟨x, hx, i, -, -, -, C, CV', hres, hBC⟩ | ⟨hpj, hP, hun⟩
    · exact result_prefix_vote_domain_before hp hc (tr.time k) hx hy hres hBC hclean hcast hj
        le_rfl hprior
    · exact optimistic_target_vote_domain hp hc hx hy hop hclean hcast hj hprior
    · exact result_prefix_vote_domain_before hp hc (tr.time k) hx hy hres hBC hclean hcast hj
        le_rfl hprior
    · obtain ⟨x, hx, i, -, -, CV', hres⟩ := unanimous_target_fast_update hp hc hlab hpj hP
      exact result_prefix_vote_domain_before hp hc (tr.time k) hx hy hres .refl hclean hcast hj
        le_rfl hprior
  exact vote_viable_of_root hp.run hp.noColl hy hcast hdom.1 hdom.2

/-- A label after the drain is after `ḡ + 4Δ`. -/
private theorem gbar_add_le_ts_of_label (hp : ResetPremises tr H proposer dg g ΔF a) {j : Nat}
    (hj : sp.slot a + 2 * sp.k + 6 ≤ j) : SA.gbar g + 4 * sp.Δ ≤ sp.ts j := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨-, -, kr, -, -, -, hka⟩ := hp.reset.1
  have ha0 : 0 ≤ a := hka ▸ hp.run.time_nonneg kr
  have hlt : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
    have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
    omega
  have hle : sp.ts ((sp.slot a : Int) + 1) ≤ sp.ts j := (SA.ts_le_iff sp).2 (by omega)
  have := cutZ_lt_reset hp.run hp.healthy hp.reset
  have := lt_cutZ sp g
  linarith

/-- The writer of a protected target, its heldness at the writer, and an honest supporter. -/
private theorem protected_writer (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) {B : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat}
    (hB : SA.Protected proposer tr.projAC H (a + resetInvOffset sp.k sp.Δ) B j) :
    sp.slot a + 2 * sp.k + 6 ≤ j ∧ ∃ x ∈ H, ∃ r C CV,
      (SA.ResultAt tr.projAC x r j C CV ∨ SA.FastLockAt tr.projAC x r j C CV) ∧
      Anc (tr.HonestBlocks H) B C ∧ B ∈ (tr.state x r).fg.tree ∧
      ∃ z ∈ H, ∃ q e', SA.VoteAt tr.projAC z q e' ∧ e'.msg.slot = j ∧
        SA.VoteExtends (tr.HonestBlocks H) e'.msg B := by
  have hS := healthy_base_of_reset_catch hp hc
  have hr := hS.run.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hj, hcase⟩ := protected_target_cases hp hB
  have hgs4 := gbar_add_le_ts_of_label hp hj
  have hres_ev : ∀ {x r C CV}, x ∈ H → SA.ResultAt tr.projAC x r j C CV →
      Anc (tr.HonestBlocks H) B C → B ∈ (tr.state x r).fg.tree ∧
        ∃ z ∈ H, ∃ q e', SA.VoteAt tr.projAC z q e' ∧ e'.msg.slot = j ∧
          SA.VoteExtends (tr.HonestBlocks H) e'.msg B := by
    intro x r C CV hx hres hBC
    obtain ⟨ell, hupd, hconf, -⟩ := id hres
    have hCx := frame_tree_subset hp hx hupd.1 (SA.deepest_mem hconf).1.1
    refine ⟨mem_tree_of_anc hp hx hBC hCx, ?_⟩
    obtain ⟨z, hz, q, e', hv, hvs, D, hD, hDr, hCD⟩ :=
      SA.result_extended hS hgs4 hx hupd.1 (by rw [hupd.2.2.1]; linarith) hconf
    exact ⟨z, hz, q, e', hv, hvs, D, hD, hDr, hBC.trans hCD⟩
  refine ⟨hj, ?_⟩
  rcases hcase with ⟨x, hx, i, -, -, -, C, CV', hres, hBC⟩ | ⟨x, hx, i, CV, -, hop⟩ |
      ⟨x, hx, i, -, -, -, C, CV', hres, hBC⟩ | ⟨hpj, hP, -⟩
  · exact ⟨x, hx, i, C, CV', Or.inl hres, hBC, hres_ev hx hres hBC⟩
  · refine ⟨x, hx, i, B, CV, Or.inr (Or.inr hop), .refl, ?_⟩
    have hf : 2 * Hᶜ.ncard < sp.n := by
      have := hp.healthy.2.2
      have := Fin.pos x
      have hn : sp.n = sp.toParams.n := rfl
      omega
    obtain ⟨ellX, A, hpt, hslot, hsel, -⟩ := hop
    have hΦU := (SA.frameIn_of_callAt hr hx hpt.1).2
    unfold SA.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    refine ⟨frame_tree_subset hp hx hpt.1 (SA.deepest_mem hsel).1.1, ?_⟩
    have h34 := (SA.deepest_mem hsel).1.2.1
    obtain ⟨z, ⟨v, hv, rfl, R, hR, hRr, hBR⟩, hz⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
        (t := SA.optimisticVoters sp A ellX.frame (sp.slot (tr.projAC.time i)) B) (by omega)
    obtain ⟨hvs, q, _, e', he, rfl⟩ :=
      SA.optimisticPoint_pool_vote hS.run hx hpt hv (not_not.mp hz)
    exact ⟨_, not_not.mp hz, q, e', he, hvs.trans hslot, R, hΦU hR, hRr, hBR.mono hΦU⟩
  · exact ⟨x, hx, i, C, CV', Or.inl hres, hBC, hres_ev hx hres hBC⟩
  · obtain ⟨x, hx, i, -, -, CV', hres⟩ := unanimous_target_fast_update hp hc hj hpj hP
    exact ⟨x, hx, i, B, CV', Or.inl hres, .refl, hres_ev hx hres .refl⟩

/-- A protected target's writer compares with every high origin of its own label. -/
private theorem writer_compatible_same_label (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) {j : Nat} (hj : sp.slot a + 2 * sp.k + 6 ≤ j)
    {x : Fin sp.n} (hx : x ∈ H) {r : Nat} {B C : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)}
    (hw : SA.ResultAt tr.projAC x r j C CV ∨ SA.FastLockAt tr.projAC x r j C CV)
    (hBC : Anc (tr.HonestBlocks H) B C) {v : Fin sp.n} {r₀ : Nat}
    {O : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g v r₀ j O) :
    Compatible (tr.HonestBlocks H) B O := by
  have hS := healthy_base_of_reset_catch hp hc
  have hr := hS.run.localRun
  have hgs4 := gbar_add_le_ts_of_label hp hj
  have hgs : SA.gbar g ≤ sp.ts j := by linarith [sp.toParams.hΔ]
  obtain ⟨CV', hst⟩ := ho.2.2.1
  obtain ⟨_, D, hfl, hOD⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
  have hCD : Compatible (tr.HonestBlocks H) C D := by
    rcases hw with hres | hfw
    · rcases hfl with ⟨ellD, R, huD, hR, hfast, _⟩ | hop
      · have hDR := ((SA.deepest_mem hfast).1.1.2.2).mono
          (SA.frameIn_of_callAt hr ho.1 huD.1).2
        rcases SA.result_result_compatible hS hx hres ho.1 ⟨ellD, huD, hR, rfl⟩ hgs4 with h | h
        · exact SA.anc_total hr.coherent h hDR
        · exact Or.inr (hDR.trans h)
      · exact SA.result_optimistic_compatible hS hx hres ho.1 hop hgs4
    · exact SA.fastLock_fastLock_compatible hS hx hfw ho.1 hfl hgs
  rcases hCD with h | h
  · exact SA.anc_total hr.coherent (hBC.trans h) hOD
  · exact SA.anc_total hr.coherent hBC (hOD.trans h)

/-- **Call clause for a protected target** (route L7): at every honest call from `t_{j+1}` on,
`B` is at or below `fc_root` or in the viable tree of the whole frame tree. The root compares
with `B` (low `J`: the reset seed, `low_root_of_seed_at_call`; high `J`: every earlier high
origin, `high_J_root_of_held_at_call_before`); above the root `B` is held
(`raw_target_held_at_call`), and its viable descendant is the reset seed's (when `B` is below
the seed, `ResetPremisesUpTo.held_high_origin_viable`) or a floor-crossing entry above `B` (when
`B` is high, as in that lemma). -/
theorem protected_call_viable (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat}
    (hB : SA.Protected proposer tr.projAC H (a + resetInvOffset sp.k sp.Δ) B j)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y k ℓ) (ht : sp.ts (j + 1 : Nat) ≤ tr.time k)
    (hprior : ∀ z ∈ H, ∀ q < k, ∀ e', SA.VoteAt tr.projAC z q e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot ∨ B ∈ ℓ.frame.viableTree ℓ.frame.tree := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hU := honest_coherent hp
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hj, x, hx, r, C, CV, hw, hBC, hBx, z, hz, q, e', hv, hvs, hVB⟩ :=
    protected_writer hp hc hB
  have hclean : cleanLabel sp a + sp.k + 2 ≤ j := by rw [cleanLabel_eq]; omega
  obtain ⟨v, r₀, m, S, hS, hra, hm⟩ := (hp.toUpTo tr H (le_refl a)).reset_seed
  have hmj : m < j := by omega
  have hBS : Compatible (tr.HonestBlocks H) B S :=
    target_compatible_older_origin hp hS hz hv hvs hmj hVB
  have htm : sp.ts (m + 1 : Nat) ≤ tr.time k :=
    ((SA.ts_le_iff sp).2 (by push_cast; omega)).trans ht
  have hak : a ≤ tr.time k := by
    obtain ⟨-, -, kr, -, -, -, hka⟩ := hp.reset.1
    have ha0 : 0 ≤ a := hka ▸ hp.run.time_nonneg kr
    have hlt : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
      omega
    have hle : sp.ts ((sp.slot a : Int) + 1) ≤ sp.ts (j + 1 : Nat) :=
      (SA.ts_le_iff sp).2 (by push_cast; omega)
    linarith
  have hcompare : ∀ v r₀ m O, r₀ < k → HighOrigin tr H g v r₀ m O →
      Compatible (tr.HonestBlocks H) B O := by
    intro v r₀ m O hri ho
    rcases lt_trichotomy m j with hm | rfl | hm
    · exact target_compatible_older_origin hp ho hz hv hvs hm hVB
    · exact writer_compatible_same_label hp hc hj hx hw hBC ho
    · exact target_compatible_later_origin_before hp ho hri hm hprior
  have hheld : Anc (tr.HonestBlocks H) ℓ.frame.F B → B ∈ ℓ.frame.tree := fun hF =>
    raw_target_held_at_call hp hc hx hy hw hBC hclean hcall ht hF
  have hroot : Compatible (tr.HonestBlocks H) ℓ.frame.fcRoot B := by
    by_cases hlow : (tr.state y k).fg.hj ≤ HZ tr H g
    · exact low_root_of_seed_at_call hp hnr hx hBx hy hS hcall htm hlow hBS hheld
    · exact high_J_root_of_held_at_call_before hp hx hBx hy hcall (by omega) hcompare
  rcases hroot with hfB | hBf
  swap
  · exact Or.inl hBf
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcall
  have hBt : B ∈ ℓ.frame.tree := hheld ((Anc.mono hΦU hΦ.F_anc_fcRoot).trans hfB)
  have hfB' := SA.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfB hBt
  have hfr := Compose.frame_of_projAC hp.run hy hcall
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, k, hX⟩
  have hBf : B ∈ (Node.frame (tr.state y k)).tree := hfr ▸ hBt
  rcases hBS with hBS | hSB
  · -- below the reset seed: the seed's retention covers `B`
    have hFS : Anc (tr.HonestBlocks H) ℓ.frame.F S :=
      ((Anc.mono hΦU hΦ.F_anc_fcRoot).trans hfB).trans hBS
    have hSy := high_origin_held_at_call hp hnr hS hy hcall htm hFS
    have hFF : ℓ.frame.F = (tr.state y k).fg.F := by rw [hfr]; rfl
    have hSt : S ∈ ℓ.frame.tree := by
      rw [hfr]
      exact ⟨hSy, anc_tree_of_anc hp hy (hFF ▸ hFS) hSy⟩
    rcases (hp.toUpTo tr H hak).held_high_origin_viable hy hcall le_rfl hS
        (hra.trans hak) htm hSt with ⟨-, -, W, hWt, hWv, hSW⟩ | hSf
    · exact Or.inr ⟨hBt, hfB', W, hWt, hWv,
        SA.anc_tree_of_anc_U hU hΦ hΦU hBt (hBS.trans (hSW.mono hΦU)) hWt⟩
    · exact Or.inl (hBS.trans (hSf.mono hΦU))
  -- above the reset seed: `B` is high; a floor above it is crossed above `B`
  have hreach := Compose.fg_reachable hp.run.toLocalRun hy k
  have hBh := high_of_anc hp hS hy hBf.1 hSB
  have hfBs : (tr.state y k).fg.Anc (tr.state y k).fg.fcRoot B := by
    rw [hfr] at hfB'
    exact hfB'.mono (fun _ h => h.1)
  have hdesc : ∃ C ∈ (tr.state y k).fg.tree, (tr.state y k).fg.Anc B C ∧
      (tr.state y k).fg.IsViable C := by
    by_cases hle : (tr.state y k).fg.headHeightFloor ≤ ((tr.state y k).fg.σ B.root).h
    · exact ⟨B, hBf.1, .refl, hle⟩
    have hfloor := lt_of_not_ge hle
    have hcon : ¬ (tr.state y k).fg.Contest := fun h => by
      unfold Store.headHeightFloor at hfloor
      simp only [h, ↓reduceIte] at hfloor
      exact no_high_contest hp hy k ⟨h, by omega⟩
    have hfl : (tr.state y k).fg.headHeightFloor = (tr.state y k).fg.hmax - 1 := by
      unfold Store.headHeightFloor
      simp only [hcon, ↓reduceIte]
    rw [hfl] at hfloor
    obtain ⟨-, -, -, -, -, ⟨C₀, hC₀, hC₀h⟩, -⟩ := Store.cache_invariants _ _ _ _ hreach
    obtain ⟨E, hE, hEC, hEh, hET⟩ :=
      entry_at_height hreach hC₀ (h := (tr.state y k).fg.hmax - 1) (by omega) (by omega)
    obtain ⟨-, -, -, -, v', -, d, hdk, -, -, r', hrd, l, O, hoO, hEO⟩ :=
      left_entry_origin hp hy hE hET (by omega) hEC (by omega)
    have hcmp : Compatible (tr.HonestBlocks H) E B := by
      rcases hcompare v' r' l O (by omega) hoO with h | h
      · exact Anc.total hU hEO h
      · exact Or.inl (hEO.trans h)
    have hBE : Anc (tr.HonestBlocks H) B E := by
      rcases hcmp with h | h
      · have := σ_h_le_of_anc hreach (anc_tree_of_anc hp hy h hBf.1)
        omega
      · exact h
    refine ⟨C₀, hC₀, (anc_tree_of_anc hp hy hBE hE).trans hEC, ?_⟩
    change (tr.state y k).fg.headHeightFloor ≤ _
    omega
  obtain ⟨C', hC', hBC', hvC'⟩ := hdesc
  have hCf : C' ∈ (Node.frame (tr.state y k)).tree := ⟨hC', hBf.2.trans hBC'⟩
  have hCt : C' ∈ ℓ.frame.tree := hfr ▸ hCf
  have hCv : C' ∈ ℓ.frame.viableHeads := by
    rw [hfr]
    exact ⟨hC', hCf.2, hfBs.trans hBC', hvC'⟩
  exact Or.inr ⟨hBt, hfB', C', hCt, hCv,
    SA.anc_tree_of_anc_U hU hΦ hΦU hBt (hBC'.mono hsub) hCt⟩

/-- **H.3 (c1)/(c2), retention after the reset**: `Inv(a_z + T_b)` on the AC projection, for
the parameter-only `T_b = (8k + 20)Δ`. -/
theorem inv_after_reset (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g)) :
    SA.Inv proposer tr.projAC H (tr.HonestBlocks H) (a + resetInvOffset sp.k sp.Δ) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  intro B j hB y hy i ℓ hcall ht
  have hprior : ∀ z ∈ H, ∀ q < i, ∀ e', SA.VoteAt tr.projAC z q e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B :=
    fun z hz q _ e' hv hj => protected_votes_extend hp hc hB q z hz e' hv hj
  refine ⟨protected_call_viable hp hc hnr hB hy hcall ht hprior, fun e he => ?_⟩
  have hcast : SA.CastAt tr.projAC y i ℓ e := ⟨hcall, he⟩
  have hj : j < e.msg.slot := by
    have hs := (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) ((j + 1 : Nat) : Int)).mp ht
    rw [(SA.castAt_spec hr hy hcast).2.1]
    push_cast at hs
    omega
  exact protected_vote_domain hp hc hB hy hcast hj

/-- **H.3 (c1)/(c2)** in the form of the retired `reset_inv`: under the H.3 premises, for every
reset `a`, `Inv(a + T_b)` with `T_b = (8k + 20)Δ`. -/
theorem reset_inv : ∃ Tb : Nat → Time → Time → Nat → Nat → Time,
    (∀ n Δ ΔF k δt, 0 ≤ Tb n Δ ΔF k δt) ∧
    ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
      (proposer : Nat → Fin sp.n)
      (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
      (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time),
      GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF → CatchRun tr H g (2 * sp.Δ) →
      PropPlus tr H proposer g Gp → ∀ a, IsReset tr H g a →
        SA.Inv proposer tr.projAC H (tr.HonestBlocks H)
          (a + Tb sp.n sp.Δ ΔF sp.k sp.toParams.δt) :=
  ⟨fun _ Δ _ k _ => resetInvOffset k Δ, fun _ Δ _ k _ => resetInvOffset_nonneg k Δ,
    fun _ _ _ _ _ _ _ _ _ hrun hs hc _ _ ha =>
      inv_after_reset ⟨hrun, hs.healthy, hs.noColl, ha⟩ hc hs.noRestart⟩

/-- **H.3 (c), the bridge**, from `reset_inv` and `settled_geo`, at `max(T_b, 8Δ)`: the offset
`NonInterference` exposes is `max((8k + 20)·max(Δ, 0), 8Δ)`, which is `(8k + 20)Δ` for `Δ > 0`. -/
theorem bridge : ∃ Tb : Nat → Time → Time → Nat → Nat → Time, (∀ n Δ ΔF k δt, 0 ≤ Tb n Δ ΔF k δt) ∧
    ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
      (proposer : Nat → Fin sp.n)
      (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
      (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time),
      GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF → CatchRun tr H g (2 * sp.Δ) →
      PropPlus tr H proposer g Gp → ∀ a, IsReset tr H g a →
        BridgeAt tr H proposer g a (Tb sp.n sp.Δ ΔF sp.k sp.toParams.δt) := by
  obtain ⟨Tb, hTb, hinv⟩ := reset_inv
  refine ⟨fun n Δ ΔF k δt => max (Tb n Δ ΔF k δt) (8 * Δ), fun n Δ ΔF k δt =>
    (hTb n Δ ΔF k δt).trans (le_max_left _ _),
    fun sp ro proposer dg H tr g ΔF Gp hrun hs hc hp a ha =>
    ⟨(hinv sp ro proposer dg H tr g ΔF Gp hrun hs hc hp a ha).mono
      (add_le_add_right (le_max_left _ _) a),
      fun p P hP htp hph => settled_geo hrun hs hc hp ha (le_max_right _ _) p P hP htp hph⟩⟩

/-- **H.3, FG non-interference after the reset.** -/
theorem non_interference : NonInterference := by
  obtain ⟨Tb, hTb, hb⟩ := bridge
  refine ⟨Tb, hTb, fun sp ro proposer dg H tr g ΔF Gp hrun hs hc hp => ?_⟩
  have hr := reset_existence sp ro proposer dg H tr g ΔF Gp hrun hs hc hp
  obtain ⟨a, ha⟩ := hr.2.2.1
  exact ⟨a, ha, (hr.2.2.2.1 a ha).trans hr.2.2.2.2.1,
    height_scoped_retention sp ro proposer dg H tr g ΔF hrun hs.healthy hs.noColl a ha,
    hb sp ro proposer dg H tr g ΔF Gp hrun hs hc hp a ha⟩

end Consensus.Goldilocks.Healing

end
