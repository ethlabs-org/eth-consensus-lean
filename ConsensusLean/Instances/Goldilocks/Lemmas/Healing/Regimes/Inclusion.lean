module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Outputs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Inclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Later
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Read
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Reads
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run

public section

/-! # Goldilocks milestone Regimes: R.2 (inclusion and growth under `Sleepy`)

`IncludeSleepy` and `GrowSleepy` (`Statements/Regimes/Sleepy`) over the run, from

* `later_update_adopts` (`Service/Later`, a generalisation of `update_adopts`): after an honest
  update of any slot `≥ s`, the record or `Σ.F` extends an honest proposal `P` of slot `s` by a
  joined proposer;
* `ready_read_record` (`Sleepy/Read`, A1.6 at a ready read point): the read of a ready node between
  its events is the record's block, or `Σ.F` when the record is not in the frame.

A1.7 (`Compose.inclusion`) is not enough by itself: its reader was awake and joined at
`t_s + 6Δ`, while a ready reader at a later `t` may have slept then and missed the update of slot
`s`. Proved here: a ready reader at `t ≥ τ + 6Δ` ran the update of the slot `slot(t − 6Δ) ≥ s` (its
tick at that public time, joined by F.4), so its record after all events at `t` extends `P`
(`ready_record_extends`, with `record_step`); a proposer ready at its slot start proposes
(`ready_proposer_proposes`: its tick's `ac_proposal` returns a proposal since it is joined, and
C0.3 accepts the own block); the point after all events at `t` is between two events of every
node (`cutAfter_boundary`). Then `include_sleepy` (the read is the record or `Σ.F`, and both
extend `P`, as in A1.7's proof) and `grow_sleepy` (a ready proposer of the window `(t, t + 4kΔ]`
proposes `P`, which every ready read at `t + (4k + 6)Δ` includes; `P` is newer than every block of
a read at `t`, and the agreement half of R.1 orders the reads).

The file is in the Healing layer for the tick facts of `Healing/Projection/Run`. -/

namespace Consensus.Goldilocks.Regimes

open SA (SAParams ReplayOrder Payload)
open Compose

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time}

/-! ## Open steps -/

/-- **A ready reader's record extends a ready proposal**: under `Sleepy`, for an honest
proposal `P` released at `τ` by a proposer ready at `τ`, and `y` ready at `t ≥ τ + 6Δ`, the
record of `y` after all events at `t`, or its `Σ.F`, extends `P`: `y` ran the update of
`slot(t) − 2` or `slot(t) − 1` (a slot `≥ slot(P)`) with no restart since, and that update adopts
`P` (`later_update_adopts`), and the record and `Σ.F` only extend (`record_step`,
`run_F_mono`). -/
theorem ready_record_extends (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {τ : Time} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposalAt tr H (catchUp sp) τ P) {y : Fin sp.n} {t : Time} {j : Nat}
    (ht : τ + 6 * sp.Δ ≤ t) (hy : ReadyAt tr H (catchUp sp) y t) (hj : CutAfter tr j t) :
    ∃ E ∈ tr.HonestBlocks H, E.root = (tr.state y j).ac.latestConfirmed ∧
      (Anc (tr.HonestBlocks H) P E ∨ Anc (tr.HonestBlocks H) P (tr.state y j).fg.F) := by
  have hΔ := sp.toParams.hΔ
  have hc : (8 : Time) * sp.Δ ≤ catchUp sp + 1 := by simp only [catchUp]; linarith
  obtain ⟨p, kP, hpr, hPa, hkP⟩ := hP
  have hp := hpr.1
  have hy' := hy.1
  -- the proposal's slot and the proposer's joining
  set s := P.slot
  have hτ : τ = sp.ts s := by rw [← hkP, hPa.2.2, sp.slotTime_eq]; rfl
  have hτ0 : 0 ≤ τ := hkP ▸ hrun.time_nonneg kP
  have hpj : SA.joined sp (tr.state p kP).ac (tr.time kP) := by
    have hJ := (ready_implies_joined sp ro dg H tr hrun p hp τ (catchUp sp) hτ0 hc hpr.2).2
    obtain ⟨⟨acc, hcall⟩, -⟩ := hPa.1
    refine ((joined_projection sp ro dg H tr hrun p hp _).2.1 kP ⟨_, hcall⟩ ?_ rfl).1
      (hkP ▸ hJ)
    rintro ⟨ℓ, hc', hr⟩
    cases Option.some.inj (hcall.2.symm.trans hc'.2)
  -- the latest update before `t`: of slot `m = slot(t − 6Δ) ≥ s`, at `u = t_m + 6Δ`
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
  have hcu : catchUp sp = 18 * sp.Δ := rfl
  have hu0 : 0 ≤ u := by simp only [u, SAParams.ts]; positivity
  have hpub : sp.toParams.IsPublic u := ⟨4 * m + 6, by simp only [u, SAParams.ts]; ring⟩
  have hwin : ∀ v, max 0 (u - (14 * sp.Δ - 1) - 1) ≤ v → v ≤ u → tr.awake y v := by
    intro v h₁ h₂
    exact hy.2 v (le_trans (max_le_max le_rfl (by rw [hcu]; linarith)) h₁) (by linarith)
  have hyu := hwin u (max_le hu0 (by linarith)) le_rfl
  obtain ⟨j₁, x, hg⟩ := hrun.tick_of_awake y hy' u hu0 hpub hyu
  obtain ⟨hc₁, ht₁⟩ := Healing.tick_first_cut hg
  have hJ := (ready_implies_joined sp ro dg H tr hrun y hy' u (14 * sp.Δ - 1) hu0
    (by linarith) hwin).2
  have hj₁ : SA.joined sp (tr.state y j₁).ac u :=
    ((joined_projection sp ro dg H tr hrun y hy' u).2.1 j₁ ⟨_, hc₁⟩
      (fun ⟨ℓ, hc', hr⟩ => by
        have := Option.some.inj (hc₁.2.symm.trans hc'.2)
        simp only [Node.acCall, Cut.ac.injEq] at this
        rw [← this] at hr
        cases hr) ht₁).1 hJ
  obtain ⟨ℓ₁, hupd⟩ : ∃ ℓ₁, SA.UpdateAt tr.projAC y j₁ m ℓ₁ := by
    refine ⟨_, projAC_callAt.2 hc₁, rfl, ht₁.trans hu_def, ?_⟩
    change SA.joined sp (tr.projAC.state y j₁) (tr.time j₁)
    rw [projAC_state hrun.toLocalRun hy' j₁, ht₁]
    exact hj₁
  obtain ⟨E, hE, hEr, hPE⟩ := later_update_adopts hrun hnc hsl hp hPa rfl hpj hy' hms hupd
  -- the record only extends from the update to `j`
  have hj₁j : j₁ + 1 ≤ j := by
    by_contra hh
    have := hrun.time_mono (show j ≤ j₁ by omega)
    linarith [hj.2]
  have hinv := sleepy_invariant hrun hnc hsl
  have key : ∀ i, j₁ + 1 ≤ i → ∃ E ∈ tr.HonestBlocks H,
      E.root = (tr.state y i).ac.latestConfirmed ∧
        (Anc (tr.HonestBlocks H) P E ∨ Anc (tr.HonestBlocks H) P (tr.state y i).fg.F) := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => exact ⟨E, hE, hEr, hPE⟩
    | succ i _ ih =>
      obtain ⟨E₁, hE₁, hE₁r, hPE₁⟩ := ih
      obtain ⟨E', hE', hE'r, hEE'⟩ := record_step hinv hrun hnc hy' i E₁ hE₁ hE₁r
      refine ⟨E', hE', hE'r, hPE₁.imp (·.trans hEE') fun h => h.trans ?_⟩
      exact Healing.run_F_mono hrun.toLocalRun hy' (Nat.le_succ i)
  exact key j hj₁j

/-- **A proposer ready at its slot start proposes** (node-level: its tick at `t_s` runs
the proposal step, `ac_proposal` returns a proposal since it is joined, and C0.3 accepts the own
block). -/
theorem ready_proposer_proposes (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    {s : Nat} (hs : 0 < s) (hready : ReadyAt tr H (catchUp sp) (sp.toParams.proposer s) (sp.ts s)) :
    ∃ k P, tr.ProposesAt (sp.toParams.proposer s) k P ∧ tr.time k = sp.ts s := by
  have hΔ := sp.toParams.hΔ
  set p := sp.toParams.proposer s
  have hp := hready.1
  have ht0 : 0 ≤ sp.ts s := by simp only [SAParams.ts]; positivity
  have hslot : sp.toParams.slotOf (sp.ts s) = s :=
    SA.slot_of_mem sp s le_rfl (by simp only [SAParams.ts]; push_cast; linarith)
  have hpub : sp.toParams.IsPublic (sp.ts s) := ⟨4 * s, by simp only [SAParams.ts]; ring⟩
  have hc : (8 : Time) * sp.Δ ≤ catchUp sp + 1 := by simp only [catchUp]; linarith
  have hJ := ready_implies_joined sp ro dg H tr hrun p hp _ (catchUp sp) ht0 hc hready.2
  obtain ⟨j, x, hg⟩ := hrun.tick_of_awake p hp _ ht0 hpub hJ.1
  have hP : Node.Proposes p (sp.ts s) :=
    ⟨by rw [hslot]; exact hs, by rw [hslot, sp.slotTime_eq]; simp only [SAParams.ts],
      by rw [hslot]⟩
  obtain ⟨hc₀, ht₀⟩ := Healing.tick_first_cut hg
  have hj : SA.joined sp (tr.state p j).ac (sp.ts s) :=
    ((joined_projection sp ro dg H tr hrun p hp _).2.1 j ⟨_, hc₀⟩
      (fun ⟨ℓ, hc', hr⟩ => by
        have := Option.some.inj (hc₀.2.symm.trans hc'.2)
        simp only [Node.acCall, Cut.ac.injEq] at this
        rw [← this] at hr
        cases hr) ht₀).1 hJ.2
  -- `ac_proposal` after the tick's `ac_on_tick` returns a proposal: the tick keeps `restart_time`
  have hj' : SA.joined sp (Node.tickStep dg p (tr.state p j) (sp.ts s) x .acTick).1.ac
      (sp.ts s) := by
    change SA.joined sp ((goldilocksNode sp ro).step p (tr.state p j).ac
      (Node.frame (tr.state p j)) (sp.ts s) .tick).1 (sp.ts s)
    unfold SA.joined at hj ⊢
    rw [SA.step_restartTime p _ _ _ .tick (by simp)]
    exact hj
  obtain ⟨d, pay, hr⟩ : ∃ d pay,
      (Node.acProposal (Node.tickStep dg p (tr.state p j) (sp.ts s) x .acTick).1
        (sp.ts s)).2.2 = some (d, pay) := by
    cases hpr : (Node.acProposal (Node.tickStep dg p (tr.state p j) (sp.ts s) x .acTick).1
        (sp.ts s)).2.2 with
    | none =>
      exfalso
      change (SA.acProposal sp _ _ (sp.ts s)).2 = none at hpr
      unfold SA.acProposal at hpr
      simp [hj'] at hpr
    | some dp => exact ⟨dp.1, dp.2, rfl⟩
  obtain ⟨hacc, ht₂⟩ := Healing.own_block_accepted hrun.toLocalRun
    (goldilocksNode_requirements sp ro) hrun.genesis_root_ok hnc hp hg hP hr
  refine ⟨j + 2, _, ⟨⟨⟨true, hacc⟩, ?_⟩, rfl, ?_⟩, ht₂⟩
  · -- the own block is the third cut of the tick, so not the first of a group
    have hlen : 2 < (Node.exec dg p (tr.state p j) (sp.ts s) (.tick x)).2.length := by
      have h1 : (Node.tickStep dg p (tr.state p j) (sp.ts s) x .acTick).2.length = 1 := rfl
      change 2 < (Node.onTick dg p (tr.state p j) (sp.ts s) x).2.length
      rw [Healing.onTick_eq, Healing.proposal_cuts_some hP hr]
      simp only [List.length_append, List.length_cons, Node.onBlock, Node.mkBlock, lt_irrefl,
        ↓reduceIte]
      split <;> simp <;> omega
    obtain ⟨j₀, e, k, hg₀, hjk, hk⟩ := call_in_group hrun.toLocalRun hp hacc
    intro h0
    have hk' := (List.getElem?_eq_some_iff.1 hk).1
    have hpos := (hg₀.2.1 k hk').2.2.2.1
    rw [← hjk, h0] at hpos
    subst hpos
    simp only [Nat.add_zero] at hjk
    subst hjk
    exact absurd (group_start hg hg₀ (by omega) (by omega)) (by omega)
  · rw [ht₂]
    simp only [Node.mkBlock]
    rw [hslot, sp.slotTime_eq]
    rfl

/-! ## Reads after all events -/

/-- The point after all events at `t` is between two events of every node. -/
theorem cutAfter_boundary (hrun : GoldilocksRun dg H tr) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {t : Time} (hj : CutAfter tr j t) : Boundary tr y j := by
  rintro ⟨c, hc⟩
  obtain ⟨j₀, e, k, hg, rfl, -⟩ := call_in_group hrun.toLocalRun hy hc
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1
  · exfalso
    have h₀ := (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.1
    simp only [Nat.add_zero] at h₀
    have := hj.1 j₀ (by omega)
    linarith [hj.2]

/-- The read after all events at `t` extends `P` when the record or `Σ.F` does (as in A1.7's
proof: the read is the record's block, above `Σ.F`, or `Σ.F`, which the record's block is below
then). -/
private theorem read_extends_of_record (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {t : Time}
    (hj : CutAfter tr j t) (hready : ReadyAt tr H (catchUp sp) y t)
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hE : ∃ E ∈ tr.HonestBlocks H, E.root = (tr.state y j).ac.latestConfirmed ∧
      (Anc (tr.HonestBlocks H) P E ∨ Anc (tr.HonestBlocks H) P (tr.state y j).fg.F)) :
    Anc (tr.HonestBlocks H) P (readAfter tr y j t) := by
  have hinv := sleepy_invariant hrun hnc hsl
  have hcoh := honest_blocks_coherent hrun.toLocalRun hnc
  obtain ⟨E, hE, hEr, hPE⟩ := hE
  rcases ready_read_record hrun hnc hsl ⟨fun k hk => hj.1 k hk, hj.2.le⟩
      (cutAfter_boundary hrun hy hj) hready with ⟨R, hR, hRr, hread⟩ | ⟨hin, hread⟩
  · rw [hread]
    obtain rfl : R = E := hcoh.1 ⟨y, hy, j, hR.1⟩ hE (hRr.trans hEr.symm)
    rcases hPE with h | h
    · exact h
    · exact h.trans (Anc.mono (fun X hX => ⟨y, hy, j, hX⟩) hR.2)
  · rw [hread]
    rcases hPE with hPE | h
    swap
    · exact h
    have hΦ := frameOK_state hrun.toLocalRun hy j
    obtain ⟨C, hC, hCr, hCo⟩ := hinv.record y hy j
    obtain rfl : C = E := hcoh.1 ⟨y, hy, j, hC⟩ hE (hCr.trans hEr.symm)
    have hF : (tr.state y j).fg.F ∈ (tr.state y j).fg.tree := hΦ.rooted.1.1
    have hEc : OnOriginChain tr H C := onOriginChain_iff.2 (hCo.elim Or.inl fun ⟨s, ho⟩ =>
      Or.inr ⟨C, s, ho, Relation.ReflTransGen.refl⟩)
    rcases OnOriginChain.compatible hrun hnc hinv.origins_compatible hE ⟨y, hy, j, hF⟩ hEc
      (hinv.caches y hy j).1 with h | h
    · exact hPE.trans h
    -- `Σ.F ⪯ C` inside the honest blocks would put `C` in the frame
    obtain ⟨hfin, htc, hgm, hgen⟩ := Store.accepted_tree sp.toParams (Payload sp.n) _ _
      (fg_reachable hrun.toLocalRun hy j)
    have hΦg : FrameOK (⟨(tr.state y j).fg.tree, _, _, ∅⟩ :
        Frame sp.n (List (FG.Att sp.n)) (Payload sp.n)) :=
      { finite := hfin, coherent := htc, rooted := ⟨hgm, hgen⟩, fcRoot_mem := hgm
        F_anc_fcRoot := Relation.ReflTransGen.refl, viableHeads_subset := Set.empty_subset _
        fcRoot_anc_viableHeads := fun _ h => h.elim }
    exact (hin ⟨C, ⟨hC, SA.anc_tree_of_anc_U hcoh hΦg (fun X hX => ⟨y, hy, j, hX⟩) hF h hC⟩,
      hCr⟩).elim

/-! ## R.2 -/

/-- **R.2, `includeSleepy`.** -/
theorem include_sleepy : IncludeSleepy := by
  intro sp ro dg H tr ΔF hrun hnc hsl τ P hP y t j ht hy hj
  exact read_extends_of_record hrun hnc hsl hy.1 hj hy
    (ready_record_extends hrun hnc hsl hP ht hy hj)

/-- A block of an honest node's tree before a cut whose earlier cuts are at times `≤ t` has a
slot at most `slot(t)`. -/
private theorem tree_slot_le (hrun : GoldilocksRun dg H tr) {x : Fin sp.n} (hx : x ∈ H)
    {j : Nat} {t : Time} (hj : ∀ k < j, tr.time k ≤ t)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state x j).fg.tree) :
    X.slot ≤ sp.slot t := by
  rcases tree_cases hrun.toLocalRun hx hX with rfl | ⟨k, hk, hacc⟩
  · exact Nat.zero_le _
  · exact ((hrun.cutLaw x hx k _ hacc).1).trans
      (SA.slot_mono sp (hrun.time_nonneg k) (hj k hk))

/-- **R.2, `growSleepy`.** -/
theorem grow_sleepy : GrowSleepy := by
  intro sp ro dg H tr ΔF k hrun hnc hsl hk t ht hrec _
  have hΔ := sp.toParams.hΔ
  have hcoh := honest_blocks_coherent hrun.toLocalRun hnc
  set D := (4 * (k : Time) + 6) * sp.Δ
  -- the window `(t, t + 4kΔ]` has a ready proposer
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
  obtain ⟨s, hs₀s, hss, hready⟩ := hrec s₀ (lt_of_le_of_lt ht hts₀) (by
    simp only [SAParams.ts] at hts₀' ⊢
    have h1k : (1 : Time) ≤ k := by exact_mod_cast hk
    rw [show ((s₀ + k - 1 : Nat) : Time) = (s₀ : Time) + k - 1 by
      rw [Nat.cast_sub (by omega)]; push_cast; ring]
    nlinarith)
  have hts : t < sp.ts s := lt_of_lt_of_le hts₀ ((SA.ts_le_iff sp).2 (by exact_mod_cast hs₀s))
  have htsD : sp.ts s + 6 * sp.Δ ≤ t + D := by
    have : sp.ts s ≤ sp.ts (s₀ + (k - 1) : Nat) := (SA.ts_le_iff sp).2 (by push_cast; omega)
    simp only [SAParams.ts, D] at this hts₀' ⊢
    push_cast at this hts₀' ⊢
    rw [show ((k - 1 : Nat) : Time) = k - 1 by rw [Nat.cast_sub hk]; simp] at this
    nlinarith
  obtain ⟨kP, P, hP, hkP⟩ := ready_proposer_proposes hrun hnc (by omega) hready
  have hPslot : P.slot = s := by
    have h := hP.2.2
    rw [hkP, sp.slotTime_eq] at h
    simp only [SAParams.ts] at h
    have := SA.four_delta_pos sp
    exact_mod_cast (mul_left_cancel₀ this.ne' h).symm
  have hRP : ReadyProposalAt tr H (catchUp sp) (sp.ts s) P := ⟨_, kP, hready, hP, hkP⟩
  have hinc : ∀ y j, ReadyAt tr H (catchUp sp) y (t + D) → CutAfter tr j (t + D) →
      Anc (tr.HonestBlocks H) P (readAfter tr y j (t + D)) := fun y j hy hj =>
    include_sleepy sp ro dg H tr ΔF hrun hnc hsl _ P hRP y _ j htsD hy hj
  -- `P` is newer than every block of a read at `t`
  have hnot : ∀ x jx, ReadyAt tr H (catchUp sp) x t → CutAfter tr jx t →
      ¬ Anc (tr.HonestBlocks H) P (readAfter tr x jx t) := by
    intro x jx hx hjx hPx
    have hΦ := frameOK_state hrun.toLocalRun hx.1 jx
    have hmem := (sa_tips (A := (tr.state x jx).ac) hΦ t).1
    have hXs := tree_slot_le hrun hx.1 hjx.1 hmem.1
    have := (Anc.slot_le hcoh hPx).1
    have hslt : sp.slot t < s := by
      by_contra h
      have := (SA.ts_le_iff_le_slot sp ht (s : Int)).2 (by omega)
      linarith
    change P.slot ≤ (SA.acConfirmed sp (tr.state x jx).ac (Node.frame (tr.state x jx)) t).slot
      at this
    omega
  refine ⟨sp.ts s, P, hts, hRP, hinc, fun x jx hx hjx => ⟨hnot x jx hx hjx, fun y j hy hj => ?_⟩⟩
  rcases sleepy_reads_compatible hrun hnc hsl x hx.1 y hy.1 jx j t (t + D) with h | h
  · exact h
  · exact absurd ((hinc y j hy hj).trans h) (hnot x jx hx hjx)

end Consensus.Goldilocks.Regimes

end
