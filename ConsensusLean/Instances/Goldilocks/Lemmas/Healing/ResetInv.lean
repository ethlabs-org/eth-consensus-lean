module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Bridge
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation

public section

/-! # Goldilocks Healing: H.3 (c), the `Inv` half after the reset

The retention premise `Inv(a_z + T_b)` on the AC projection (claims H.3 (c1)/(c2)), with the
parameter-only offset `T_b = (8k + 20)Δ` (`resetInvOffset`). The offset puts the label of every
protected target after the drain `R = t_{slot(a_z) + 2k + 5}`, so every live lock at its votes is
clean (workbench `healing_bundles_route.md` §4).

The proof is a strong induction on the cut index for one protected target `(B, j)` at a time:
from "every honest vote of a slot `> j` at an earlier cut extends `B`",

* `protected_vote_domain`: at a vote of a slot `> j`, `B` is in the viable voter block tree or at
  or below `fc_root` (route L1, L2: `result_prefix_vote_domain_before` and its optimistic and
  unanimous counterparts);
* `protected_vote_extends`: that vote extends `B` (route L3–L6: first and next transfer);
* `protected_call_viable`: at every honest call from `t_{j+1}` on, `B` is at or below `fc_root`
  or in the viable tree of the whole frame tree (route L7–L9).

The three step lemmas are OPEN (`sorry`); this file fixes their quantifier order. -/

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
      obtain ⟨ℓ, C, hupd, hconf, -, hfast, -⟩ := id hfu
      have hBC := (SA.deepest_mem hfast).1.1.2.2
      exact ⟨C, _, ⟨ℓ, hupd, hconf, rfl⟩,
        Anc.mono (SA.frameIn_of_callAt hr hx hupd.1).2 hBC⟩
    · exact Or.inr (Or.inl ⟨x, hx, i, CV, hj, hop⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨x, hx, i, hj, hsl, hlab _ hs, ?_⟩))
    obtain ⟨ℓ, C, hupd, hconf, -, hdeep, -⟩ := id hsl
    have hBC := (SA.deepest_mem hdeep).1.1.2.2
    exact ⟨C, _, ⟨ℓ, hupd, hconf, rfl⟩,
      Anc.mono (SA.frameIn_of_callAt hr hx hupd.1).2 hBC⟩
  · exact Or.inr (Or.inr (Or.inr ⟨hp', hP, hun⟩))

/-- **Vote domain of a protected target** (OPEN; route L1, L2): at an honest vote of a slot
`> j`, given that every honest vote of a slot `> j` at an earlier cut extends `B`. -/
theorem protected_vote_domain (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat}
    (hB : SA.Protected proposer tr.projAC H (a + resetInvOffset sp.k sp.Δ) B j)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcast : SA.CastAt tr.projAC y k ℓ e)
    (hj : j < e.msg.slot)
    (hprior : ∀ z ∈ H, ∀ q < k, ∀ e', SA.VoteAt tr.projAC z q e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  sorry

/-- **Vote transfer for a protected target** (OPEN; route L3–L6): the vote of the previous lemma
extends `B`. -/
theorem protected_vote_extends (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat}
    (hB : SA.Protected proposer tr.projAC H (a + resetInvOffset sp.k sp.Δ) B j)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcast : SA.CastAt tr.projAC y k ℓ e)
    (hj : j < e.msg.slot)
    (hviab : B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot)
    (hprior : ∀ z ∈ H, ∀ q < k, ∀ e', SA.VoteAt tr.projAC z q e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  sorry

/-- **Call clause for a protected target** (OPEN; route L7–L9): at every honest call from
`t_{j+1}` on, `B` is at or below `fc_root` or in the viable tree of the whole frame tree. -/
theorem protected_call_viable (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat}
    (hB : SA.Protected proposer tr.projAC H (a + resetInvOffset sp.k sp.Δ) B j)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y k ℓ) (ht : sp.ts (j + 1 : Nat) ≤ tr.time k)
    (hprior : ∀ z ∈ H, ∀ q < k, ∀ e', SA.VoteAt tr.projAC z q e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot ∨ B ∈ ℓ.frame.viableTree ℓ.frame.tree := by
  sorry

/-- Every honest vote of a slot `> j` extends a protected target `(B, j)` (strong induction on
the cut index, from `protected_vote_domain` and `protected_vote_extends`). -/
theorem protected_votes_extend (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat}
    (hB : SA.Protected proposer tr.projAC H (a + resetInvOffset sp.k sp.Δ) B j) :
    ∀ k, ∀ z ∈ H, ∀ e, SA.VoteAt tr.projAC z k e → j < e.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rintro z hz e ⟨ℓ, hcast⟩ hj
    have hprior : ∀ z ∈ H, ∀ q < k, ∀ e', SA.VoteAt tr.projAC z q e' → j < e'.msg.slot →
        SA.VoteExtends (tr.HonestBlocks H) e'.msg B :=
      fun z hz q hq e' hv hj' => ih q hq z hz e' hv hj'
    exact protected_vote_extends hp hc hnr hB hz hcast hj
      (protected_vote_domain hp hc hnr hB hz hcast hj hprior) hprior

/-- **H.3 (c1)/(c2), retention after the reset**: `Inv(a_z + T_b)` on the AC projection, for
the parameter-only `T_b = (8k + 20)Δ`. -/
theorem inv_after_reset (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g)) :
    SA.Inv proposer tr.projAC H (tr.HonestBlocks H) (a + resetInvOffset sp.k sp.Δ) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  intro B j hB y hy i ℓ hcall ht
  have hprior : ∀ z ∈ H, ∀ q < i, ∀ e', SA.VoteAt tr.projAC z q e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B :=
    fun z hz q _ e' hv hj => protected_votes_extend hp hc hnr hB q z hz e' hv hj
  refine ⟨protected_call_viable hp hc hnr hB hy hcall ht hprior, fun e he => ?_⟩
  have hcast : SA.CastAt tr.projAC y i ℓ e := ⟨hcall, he⟩
  have hj : j < e.msg.slot := by
    have hs := (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) ((j + 1 : Nat) : Int)).mp ht
    rw [(SA.castAt_spec hr hy hcast).2.1]
    push_cast at hs
    omega
  exact protected_vote_domain hp hc hnr hB hy hcast hj hprior

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

/-- **H.3 (c), the bridge**, from `reset_inv` and `settled_geo`, at `max(T_b, 8Δ)`. -/
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
