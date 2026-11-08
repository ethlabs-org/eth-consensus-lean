module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Later
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Regimes.Inclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.ServedRead
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Read
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy` with growing faults: finite inclusion and growth

The growing-fault form of `Healing/Regimes/Inclusion` (R.2), finite through `b`, from the finite
service and the count shapes through `b`:

* `ready_record_extends_at`: a reader ready at `t ≥ τ + 6Δ` ran the update of the slot
  `slot(t − 6Δ) ≥ slot(P)` (honest then, as `t_m + 6Δ ≤ t`), which adopts `P`
  (`later_update_adopts_at`); its record and `Σ.F` only extend afterwards;
* `read_extends_of_record_at`: the read after all events at `t` extends `P` when the record or
  `Σ.F` does;
* `ready_proposer_proposes_at`: a proposer ready at its slot start proposes then;
* `include_sleepy_at`, `grow_sleepy_at`: the finite rows, the proposer honest through its hold
  `Δ` and every reader honest at its read time. -/

namespace Consensus.Goldilocks.Regimes.Growing

open SA (SAParams ReplayOrder Payload)
open Compose.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **A proposer ready at its slot start proposes then**, under growing faults: the static
`ready_proposer_proposes` on the prefix through `t_s`. -/
theorem ready_proposer_proposes_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {s : Nat} (hs : 0 < s)
    (hready : ReadyAt tr H (catchUp sp) (proposer s) (sp.ts s)) :
    ∃ k P, tr.ProposesAt (proposer s) k P ∧ tr.time k = sp.ts s := by
  have ht0 : 0 ≤ sp.ts s := Compose.Growing.ts_natCast_nonneg s
  obtain ⟨k, P, hP, hk⟩ := Regimes.ready_proposer_proposes (hrun.upTo ht0) (hnc.upTo _) hs
    ⟨hready.1, fun τ h1 h2 => ⟨hready.2 τ h1 h2, h2⟩⟩
  exact ⟨k, P, ⟨((RunTrace.upTo_ownBlockAt tr).1 hP.1).2, hP.2.1, hP.2.2⟩, hk⟩

/-- A node honest at `t ≥ 0` and awake through the catch-up window before `t` is awake and joined
at `t` (the static `ready_implies_joined` on the prefix through `t`). -/
private theorem ready_joined_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {t c : Time} (hy : y ∈ H t) (ht : 0 ≤ t) (hc : 8 * sp.Δ ≤ c + 1)
    (hawake : ∀ u : Time, max 0 (t - c - 1) ≤ u → u ≤ t → tr.awake y u) :
    tr.awake y t ∧ tr.JoinedAt y t := by
  obtain ⟨hw, hj⟩ := Compose.ready_implies_joined _ _ _ _ _ _ (hrun.upTo ht) y hy t c ht hc
    fun u h1 h2 => ⟨hawake u h1 h2, h2⟩
  exact ⟨hw.1, fun k hk hkt => hj k ((RunTrace.upTo_restartAt tr).2 ⟨hkt, hk⟩) hkt⟩

/-- **A ready reader's record extends a ready proposal** under growing faults: for a proposal `P`
released at `τ` by a proposer ready at `τ` and honest through its hold, and `y` ready at
`t ∈ [τ + 6Δ, b]`, the record of `y` after all events at `t`, or its `Σ.F`, extends `P`. -/
theorem ready_record_extends_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b)
    (hsync : SleepyServiceBefore tr H ΔF b) (hB : SleepyBoundsFrom tr H 0 b)
    (hinv : SleepyInvariantUpTo tr H b) {τ : Time} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposalAt tr H (catchUp sp) τ (hold sp) P) {y : Fin sp.n} {t : Time} {j : Nat}
    (ht : τ + 6 * sp.Δ ≤ t) (hy : ReadyAt tr H (catchUp sp) y t) (hj : CutAfter tr j t)
    (htb : t ≤ b) :
    ∃ E ∈ tr.HonestBlocksAt H, E.root = (tr.state y j).ac.latestConfirmed ∧
      (Anc (tr.HonestBlocksAt H) P E ∨ Anc (tr.HonestBlocksAt H) P (tr.state y j).fg.F) := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨p, kP, hpr, hph, hPa, hkP⟩ := hP
  set s := P.slot
  have hτ : τ = sp.ts s := by rw [← hkP, hPa.2.2, sp.slotTime_eq]; rfl
  have hτ0 : 0 ≤ τ := hkP ▸ hrun.time_nonneg kP
  have hp : p ∈ H (sp.ts s + sp.Δ) := by rw [← hτ]; exact hph
  -- the latest update before `t`: of slot `m = slot(t − 6Δ) ≥ s`, at `u = t_m + 6Δ ≤ t`
  have ht0 : 0 ≤ t - 6 * sp.Δ := by linarith
  set m := sp.slot (t - 6 * sp.Δ)
  have hms : s ≤ m := by
    have := (SA.ts_le_iff_le_slot sp ht0 (s : Int)).1 (by linarith)
    omega
  have hm₁ : sp.ts m ≤ t - 6 * sp.Δ := (SA.ts_le_iff_le_slot sp ht0 (m : Int)).2 le_rfl
  have hm₂ : t - 6 * sp.Δ < sp.ts m + 4 * sp.Δ := by
    by_contra hh
    have := (SA.ts_le_iff_le_slot sp ht0 ((m : Int) + 1)).1 (by
      simp only [SAParams.ts] at hh ⊢; linarith)
    omega
  set u := sp.ts m + 6 * sp.Δ with hu_def
  have hut : u ≤ t := by linarith
  have hcu : catchUp sp = 18 * sp.Δ := rfl
  have hu0 : 0 ≤ u := by simp only [u, SAParams.ts]; positivity
  have hyu : y ∈ H u := hrun.antitone hut hy.1
  have hwin : ∀ v, max 0 (u - (14 * sp.Δ - 1) - 1) ≤ v → v ≤ u → tr.awake y v := by
    intro v h₁ h₂
    exact hy.2 v (le_trans (max_le_max le_rfl (by rw [hcu]; linarith)) h₁) (by linarith)
  have hJ := ready_joined_at hrun hyu hu0 (by linarith) hwin
  obtain ⟨k₁, ℓ₁, hupd⟩ := update_of_awake_joined_at hrun hyu hJ.1 hJ.2
  have hk₁ : tr.time k₁ = u := hupd.2.2.1
  have hyk₁ : y ∈ H (tr.time k₁) := hk₁ ▸ hyu
  obtain ⟨E, hE, hEr, hPE⟩ := later_update_adopts_at hrun hnc hb0 hsync hB hinv hp hPa rfl hyk₁
    hms hupd (by rw [hk₁]; linarith)
  -- the record only extends from the update to `j`
  have hj₁j : k₁ + 1 ≤ j := by
    by_contra hh
    have := hrun.time_mono (show j ≤ k₁ by omega)
    linarith [hj.2]
  have hr := (hrun.upTo (hu0.trans hut)).toLocalRun
  have hyt : y ∈ H t := hy.1
  have key : ∀ i, k₁ + 1 ≤ i → i ≤ j → ∃ E ∈ tr.HonestBlocksAt H,
      E.root = (tr.state y i).ac.latestConfirmed ∧
        (Anc (tr.HonestBlocksAt H) P E ∨ Anc (tr.HonestBlocksAt H) P (tr.state y i).fg.F) := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => exact fun _ => ⟨E, hE, hEr, hPE⟩
    | succ i _ ih =>
      intro hij
      obtain ⟨E₁, hE₁, hE₁r, hPE₁⟩ := ih (by omega)
      have hiy : y ∈ H (tr.time i) := hrun.antitone (hj.1 i (by omega)) hyt
      obtain ⟨E', hE', hE'r, hEE'⟩ := record_step_at hinv hrun hnc hiy
        (fun k hk => (hj.1 k (by omega)).trans htb) E₁ hE₁ hE₁r
      refine ⟨E', hE', hE'r, hPE₁.imp (·.trans hEE') fun h => h.trans ?_⟩
      have hF := Healing.run_F_mono hr hyt (Nat.le_succ i)
      rw [Trace.upTo_state tr y fun k hk => hj.1 k (by omega),
        Trace.upTo_state tr y fun k hk => hj.1 k (by omega)] at hF
      exact hF.mono (upTo_subset hrun (hu0.trans hut))
  exact key j hj₁j le_rfl

/-- **The read after all events at `t` extends `P` when the record or `Σ.F` does**, for a reader
ready at `t ≤ b`. -/
theorem read_extends_of_record_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    (hsync : SleepyServiceBefore tr H ΔF b) (hB : SleepyBoundsFrom tr H 0 b) {y : Fin sp.n}
    {j : Nat} {t : Time} (ht0 : 0 ≤ t) (hj : CutAfter tr j t)
    (hready : ReadyAt tr H (catchUp sp) y t) (htb : t ≤ b) {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hE : ∃ E ∈ tr.HonestBlocksAt H, E.root = (tr.state y j).ac.latestConfirmed ∧
      (Anc (tr.HonestBlocksAt H) P E ∨ Anc (tr.HonestBlocksAt H) P (tr.state y j).fg.F)) :
    Anc (tr.HonestBlocksAt H) P (readAfter tr y j t) := by
  have hcoh := honestBlocksAt_coherent hrun hnc
  have hy : y ∈ H t := hready.1
  have hmem : ∀ {X}, X ∈ (tr.state y j).fg.tree → X ∈ tr.HonestBlocksAt H :=
    fun hX => ⟨y, j, t, ht0, hj.1, hy, hX⟩
  have hst := Trace.upTo_state tr y hj.1
  have hreach := Compose.fg_reachable (hrun.upTo ht0).toLocalRun hy j
  rw [hst] at hreach
  obtain ⟨E, hE, hEr, hPE⟩ := hE
  rcases ready_read_record_at hrun hnc hinv hsync hB ⟨hj.1, hj.2.le⟩ ht0 hready htb with
    ⟨R, hR, hRr, hread⟩ | ⟨hin, hread⟩
  · rw [hread]
    obtain rfl : R = E := hcoh.1 (hmem hR.1) hE (hRr.trans hEr.symm)
    rcases hPE with h | h
    · exact h
    · exact h.trans (Anc.mono (fun X hX => hmem hX) hR.2)
  · rw [hread]
    rcases hPE with hPE | h
    swap
    · exact h
    have hΦ : FrameOK (Node.frame (tr.state y j)) :=
      (Store.frame_realization _ _ _ _ hreach).1
    obtain ⟨C, hC, hCr, hCo⟩ := hinv.record y j t ht0 hj.1 htb hy
    obtain rfl : C = E := hcoh.1 (hmem hC) hE (hCr.trans hEr.symm)
    have hF : (tr.state y j).fg.F ∈ (tr.state y j).fg.tree := hΦ.rooted.1.1
    have hEc : OnOriginChainWithin tr H C b :=
      onOriginChainWithin_iff.2 (hCo.elim Or.inl fun ⟨s, ho⟩ =>
        Or.inr ⟨C, s, ho, Relation.ReflTransGen.refl⟩)
    rcases OnOriginChainWithin.compatible hrun hnc hinv.origins_compatible hE (hmem hF) hEc
      (hinv.caches y j t ht0 hj.1 htb hy).1 with h | h
    · exact hPE.trans h
    -- `Σ.F ⪯ C` inside the blocks held while honest would put `C` in the frame
    obtain ⟨hfin, htc, hgm, hgen⟩ := Store.accepted_tree sp.toParams (Payload sp.n) _ _ hreach
    have hΦg : FrameOK (⟨(tr.state y j).fg.tree, _, _, ∅⟩ :
        Frame sp.n (List (FG.Att sp.n)) (Payload sp.n)) :=
      { finite := hfin, coherent := htc, rooted := ⟨hgm, hgen⟩, fcRoot_mem := hgm
        F_anc_fcRoot := Relation.ReflTransGen.refl, viableHeads_subset := Set.empty_subset _
        fcRoot_anc_viableHeads := fun _ h => h.elim }
    exact (hin ⟨C, ⟨hC, SA.anc_tree_of_anc_U hcoh hΦg (fun X hX => hmem hX) hF h hC⟩,
      hCr⟩).elim

/-- **Finite inclusion under growing faults.** Through `b ≥ 0`, a proposal released at `τ` by a
proposer ready at `τ` and honest through its hold is in the confirmed read of every node ready at
`t ∈ [τ + 6Δ, b]`, after all events at `t`. -/
theorem include_sleepy_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b)
    (hsync : Compose.Growing.SleepyServiceBefore tr H ΔF b)
    (hB : Compose.Growing.SleepyBoundsFrom tr H 0 b) {τ : Time}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposalAt tr H (Regimes.catchUp sp) τ (hold sp) P) {y : Fin sp.n} {t : Time}
    {j : Nat} (hmargin : τ + 6 * sp.Δ ≤ t) (htb : t ≤ b)
    (hy : ReadyAt tr H (Regimes.catchUp sp) y t) (hj : Regimes.CutAfter tr j t) :
    Anc (tr.HonestBlocksAt H) P (Regimes.readAfter tr y j t) := by
  have hinv := sleepy_invariant_at hrun hnc hb0 hsync hB
  have hτ0 : 0 ≤ τ := by
    obtain ⟨p, kP, -, -, -, hkP⟩ := hP
    exact hkP ▸ hrun.time_nonneg kP
  have ht0 : 0 ≤ t := by linarith [sp.toParams.hΔ]
  exact read_extends_of_record_at hrun hnc hinv hsync hB ht0 hj hy htb
    (ready_record_extends_at hrun hnc hb0 hsync hB hinv hP hmargin hy hj htb)

/-- **Finite growth under growing faults.** For `t ≥ 0`, `k ≥ 1` and `t + (4k + 6)Δ ≤ b`, with one
proposer ready at its slot start and honest through its hold in every window of `k` slots up to
`t + (4k + 6)Δ`: some proposal released after `t` by a proposer ready then and honest through its
hold is in every ready read at `t + (4k + 6)Δ`, in no ready read at `t`, and each ready read at `t`
is an ancestor of each ready read at `t + (4k + 6)Δ`. -/
theorem grow_sleepy_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b)
    (hsync : Compose.Growing.SleepyServiceBefore tr H ΔF b)
    (hB : Compose.Growing.SleepyBoundsFrom tr H 0 b) {k : Nat} (hk : 1 ≤ k) {t : Time} (ht : 0 ≤ t)
    (htb : t + (4 * k + 6) * sp.Δ ≤ b)
    (hrec : ProposerRecurrence tr H proposer (Regimes.catchUp sp) k (hold sp) 0
      (t + (4 * k + 6) * sp.Δ)) :
    ∃ τ P, t < τ ∧ ReadyProposalAt tr H (Regimes.catchUp sp) τ (hold sp) P ∧
      (∀ y j, ReadyAt tr H (Regimes.catchUp sp) y (t + (4 * k + 6) * sp.Δ) →
        Regimes.CutAfter tr j (t + (4 * k + 6) * sp.Δ) →
        Anc (tr.HonestBlocksAt H) P (Regimes.readAfter tr y j (t + (4 * k + 6) * sp.Δ))) ∧
      (∀ x jx, ReadyAt tr H (Regimes.catchUp sp) x t → Regimes.CutAfter tr jx t →
        ¬ Anc (tr.HonestBlocksAt H) P (Regimes.readAfter tr x jx t)) ∧
      ∀ x jx y j, ReadyAt tr H (Regimes.catchUp sp) x t → Regimes.CutAfter tr jx t →
        ReadyAt tr H (Regimes.catchUp sp) y (t + (4 * k + 6) * sp.Δ) →
        Regimes.CutAfter tr j (t + (4 * k + 6) * sp.Δ) →
        Anc (tr.HonestBlocksAt H) (Regimes.readAfter tr x jx t)
          (Regimes.readAfter tr y j (t + (4 * k + 6) * sp.Δ)) := by
  have hΔ := sp.toParams.hΔ
  have hcoh := honestBlocksAt_coherent hrun hnc
  set D := (4 * (k : Time) + 6) * sp.Δ with hD
  have hD0 : 0 ≤ t + D := by rw [hD]; positivity
  -- the window `(t, t + 4kΔ]` has a ready proposer, honest through its hold
  set s₀ := sp.slot t + 1
  have hts₀ : t < sp.ts s₀ := by
    by_contra h
    have := (SA.ts_le_iff_le_slot sp ht (s₀ : Int)).1 (not_lt.1 h)
    omega
  have hts₀' : sp.ts s₀ ≤ t + 4 * sp.Δ := by
    have := (SA.ts_le_iff_le_slot sp ht (sp.slot t : Int)).2 le_rfl
    simp only [SAParams.ts] at this ⊢
    push_cast [s₀]
    linarith
  obtain ⟨s, hs₀s, hss, hready, hhold⟩ := hrec s₀ (lt_of_le_of_lt ht hts₀) (by
    simp only [SAParams.ts, hD] at hts₀' ⊢
    have h1k : (1 : Time) ≤ k := by exact_mod_cast hk
    rw [show ((s₀ + k - 1 : Nat) : Time) = (s₀ : Time) + k - 1 by
      rw [Nat.cast_sub (by omega)]; push_cast; ring]
    linarith)
  have hts : t < sp.ts s := lt_of_lt_of_le hts₀ ((SA.ts_le_iff sp).2 (by exact_mod_cast hs₀s))
  have htsD : sp.ts s + 6 * sp.Δ ≤ t + D := by
    have : sp.ts s ≤ sp.ts (s₀ + (k - 1) : Nat) := (SA.ts_le_iff sp).2 (by push_cast; omega)
    simp only [SAParams.ts, hD] at this hts₀' ⊢
    push_cast at this hts₀' ⊢
    rw [show ((k - 1 : Nat) : Time) = k - 1 by rw [Nat.cast_sub hk]; simp] at this
    linarith
  obtain ⟨kP, P, hP, hkP⟩ := ready_proposer_proposes_at hrun hnc (by omega) hready
  have hPslot : P.slot = s := by
    have h := hP.2.2
    rw [hkP, sp.slotTime_eq] at h
    simp only [SAParams.ts] at h
    have := SA.four_delta_pos sp
    exact_mod_cast (mul_left_cancel₀ this.ne' h).symm
  have hRP : ReadyProposalAt tr H (catchUp sp) (sp.ts s) (hold sp) P :=
    ⟨_, kP, hready, hhold, hP, hkP⟩
  have hinc : ∀ y j, ReadyAt tr H (catchUp sp) y (t + D) → CutAfter tr j (t + D) →
      Anc (tr.HonestBlocksAt H) P (readAfter tr y j (t + D)) := fun y j hy hj =>
    include_sleepy_at hrun hnc hb0 hsync hB hRP htsD htb hy hj
  -- `P` is newer than every block of a read at `t`
  have hnot : ∀ x jx, ReadyAt tr H (catchUp sp) x t → CutAfter tr jx t →
      ¬ Anc (tr.HonestBlocksAt H) P (readAfter tr x jx t) := by
    intro x jx hx hjx hPx
    have hst := Trace.upTo_state tr x hjx.1
    have hr := (hrun.upTo ht).toLocalRun
    have hΦ : FrameOK (Node.frame (tr.state x jx)) := by
      rw [← hst]; exact Compose.frameOK_state hr hx.1 jx
    have hmem := (Regimes.sa_tips (A := (tr.state x jx).ac) hΦ t).1
    have hXs : (readAfter tr x jx t).slot ≤ sp.slot t := by
      change (SA.acConfirmed sp (tr.state x jx).ac (Node.frame (tr.state x jx)) t).slot ≤ _
      have hm1 := hmem.1
      rw [← hst] at hm1 ⊢
      rcases Compose.tree_cases hr hx.1 hm1 with hg | ⟨q, hq, hacc⟩
      · rw [hg]; exact Nat.zero_le _
      · exact ((hr.cutLaw x hx.1 q _ hacc).1).trans
          (SA.slot_mono sp (hrun.time_nonneg q) (hjx.1 q hq))
    have := (Anc.slot_le hcoh hPx).1
    have hslt : sp.slot t < s := by
      by_contra h
      have := (SA.ts_le_iff_le_slot sp ht (s : Int)).2 (by omega)
      linarith
    omega
  refine ⟨sp.ts s, P, hts, hRP, hinc, hnot, fun x jx y j hx hjx hy hj => ?_⟩
  have hinv := sleepy_invariant_at hrun hnc hb0 hsync hB
  rcases hinv.read_compatible_at hrun hnc ht hjx.1 (by linarith) hx.1 hD0 hj.1 htb hy.1
      t (t + D) with h | h
  · exact h
  · exact absurd ((hinc y j hy hj).trans h) (hnot x jx hx hjx)

end Consensus.Goldilocks.Regimes.Growing

end
