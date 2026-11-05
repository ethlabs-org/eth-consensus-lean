module
public import ConsensusLeanTest.Goldilocks.Healing.TickRun
@[expose] public section

/-! # A settled effective phase on the tick run, through HS.4 (`CommonPathAcquisition`)

On the one-validator tick run of `Goldilocks/Runs/OneValidator/Premises` (`n = 1`, `f = 0`, `Δ = 1`,
`k = δ_t = 2`, `t_s = 4s`, cut `i` at time `⌊i/8⌋`), with `g = 0`, `Δ_F = 1`, `κ = 2Δ` and `G_p = 4`
(the premises of `GoldilocksHealingWitness.healing_premises`). At `w = 20 = t_5` (cut `i₀ = 160`,
before the slot-`5` block is accepted) the store holds `blk 0, …, blk 4`, `Σ.h_max = 4`, and
`blk 4`'s state justifies `blk 3` at height `3`. Labelled by kind (CONTRIBUTING "Statements"):

* (a) `settledIn_tickRun`: `SettledIn` holds at `w = 20`, `i₀ = 160`, in the effective phase
  `(4, top (blk 3))`: `w ≥ max(ḡ + κ, ḡ + 8Δ) = 8`, the validator is joined (no restart), it holds
  the evidence of every effective phase at every cut (`holdsEvidence_all`: `Σ.h_max` is the state
  height of the tip, and the top-`J` and contest evidence is read at the only honest node), the
  pre-GST catch-up is vacuous (`ḡ = 0`), and the phase at cut `160` is `(4, top (blk 3))` (no block
  of state height `4` but `blk 4`, which extends `blk 3`).
* (a) `acquisition_premises`: every premise of `CommonPathAcquisition` holds together on this
  instance; `acquisition_applies` is `common_path_acquisition`'s conclusion (a) there.
* (b) `acquisition_phase_changes`: the conclusion (a) holds through its first disjunct, read
  directly: at every cut after `w + D_HS = 92` the frontier is at least `23`, so the phase has
  changed.

**Limitation: the acquisition disjunct is unreachable here.** Every slot's own block justifies its
parent and raises `Σ.h_max`, so no effective phase lasts a slot, and the second disjunct of HS.4 (a)
(a proposal of a slot `s ≥ slot(w)` whose votes and reports lie in the phase until `t_s + 6Δ`) has
no instance on the tick run; nor does HS.4 (b) exercise a client step. Witnessing them needs a run
whose frontier stays flat for `D_HS` (for example no justification, `n ≥ 2` with a short quorum),
which the existing fixtures do not give. -/

namespace Consensus.Goldilocks.Witness.One.Settled

open SA Node ChainFrame Healing

/-- The FG part of the projection is the node's FG state. -/
theorem store_eq (y : Fin sp1.n) (j : Nat) :
    (tickRun N1 dg1).projFG.store y j = ((tickRun N1 dg1).state v0 j).fg := by
  rw [eq_v0 rfl y]
  change ((tickRun N1 dg1).projFG.state v0 j).1 = _
  rw [Compose.projFG_state tickRun_goldilocksRun.toLocalRun (Set.mem_univ _)]

/-- `Σ.h_max` is the state height of the tip `blk (stTip j)`, a block of the store. -/
theorem hmax_attained (j : Nat) :
    blk (stTip j) ∈ ((tickRun N1 dg1).state v0 j).fg.tree ∧
      (((tickRun N1 dg1).state v0 j).fg.σ (blk (stTip j)).root).h =
        ((tickRun N1 dg1).state v0 j).fg.hmax := by
  have hg := state_fgGood j
  exact ⟨(mem_tree_iff hg.blocks).2 ⟨_, le_rfl, rfl⟩, by rw [(hg.sigma _ le_rfl).h, hg.hmax]⟩

/-- At every cut, the validator holds the evidence of every effective phase there. -/
theorem holdsEvidence_all (j m : Nat) (c : PhaseCase (SA.Blk sp1.n (List (FG.Att sp1.n))))
    (h : PhaseAt (tickRun N1 dg1).projFG Set.univ j m c) (y : Fin sp1.n) :
    HoldsEvidence ((tickRun N1 dg1).projFG.store y j) m c := by
  have hfront : ∃ B ∈ ((tickRun N1 dg1).projFG.store y j).tree,
      (((tickRun N1 dg1).projFG.store y j).σ B.root).h = m := by
    have hf : FrontierAt (tickRun N1 dg1).projFG Set.univ j m := by cases c <;> exact h.1
    obtain ⟨y', -, hy'⟩ := hf.1
    rw [store_eq] at hy' ⊢
    exact ⟨_, (hmax_attained j).1, (hmax_attained j).2.trans hy'⟩
  cases c with
  | gap => exact hfront
  | top J =>
    obtain ⟨y', -, hJ, B, hB, hBj⟩ := h.2.1
    rw [store_eq] at hJ hB hBj ⊢
    exact ⟨by rw [← store_eq y]; exact hfront, hJ, B, hB, hBj⟩
  | contest J =>
    obtain ⟨y', -, hJ, B, hB, hBj⟩ := h.2.1
    obtain ⟨y'', -, C, hC, hCm, hCJ⟩ := h.2.2
    rw [store_eq] at hJ hB hBj hC hCm hCJ ⊢
    exact ⟨by rw [← store_eq y]; exact hfront, hJ, ⟨B, hB, hBj⟩, C, hC, hCm, hCJ⟩

/-- At cut `160` (time `20 = t_5`, before the slot-`5` block) the store's tip is `blk 4`. -/
theorem stTip_160 : stTip 160 = 4 := by decide

/-- The effective phase at cut `160` is `(4, top (blk 3))`. -/
theorem phaseAt_160 : PhaseAt (tickRun N1 dg1).projFG Set.univ 160 4 (.top (blk 3)) := by
  have hg := state_fgGood 160
  rw [stTip_160] at hg
  have hmax : ((tickRun N1 dg1).state v0 160).fg.hmax = 4 := by rw [hg.hmax]; rfl
  refine ⟨⟨⟨v0, Set.mem_univ _, by rw [store_eq, hmax]⟩, fun y _ => by rw [store_eq, hmax]⟩,
    ⟨v0, Set.mem_univ _, ?_, blk 4, ?_, ?_⟩, ?_⟩
  · rw [store_eq]; exact (mem_tree_iff hg.blocks).2 ⟨3, by omega, rfl⟩
  · rw [store_eq]; exact (mem_tree_iff hg.blocks).2 ⟨4, le_rfl, rfl⟩
  · rw [store_eq, (hg.sigma 4 le_rfl).hj, (hg.sigma 4 le_rfl).J]; exact ⟨rfl, rfl⟩
  · rintro ⟨y, -, B, hB, hBm, hBJ⟩
    rw [store_eq] at hB hBm hBJ
    obtain ⟨k, hk, rfl⟩ := (mem_tree_iff hg.blocks).1 hB
    rw [(hg.sigma k hk).h] at hBm
    have hk4 : k = 4 := by unfold hexp at hBm; split_ifs at hBm <;> omega
    subst hk4
    exact hBJ (anc_blk (by omega) fun k' _ hk' => (mem_tree_iff hg.blocks).2 ⟨k', hk', rfl⟩)

/-- Cut `160` is the first cut at a time `≥ 20`. -/
theorem firstCutFrom_160 : (tickRun N1 dg1).FirstCutFrom 160 20 :=
  ⟨by rw [tickRun_time]; decide, fun k hk => by
    change ((k / 8 : Nat) : Int) < 20; omega⟩

/-- (a) **`SettledIn` on the tick run** at `g = 0`, `w = 20`, `i₀ = 160`, phase
`(4, top (blk 3))`. -/
theorem settledIn_tickRun :
    SettledIn (tickRun N1 dg1) Set.univ 0 20 160 4 (.top (blk 3)) := by
  refine ⟨⟨?_, fun y _ k hk => absurd hk (tickRun_no_restart y k), fun j _ m c h y _ =>
    holdsEvidence_all j m c h y, fun x _ i B _ hi => ?_⟩, firstCutFrom_160, phaseAt_160⟩
  · rw [gbar_zero]; decide
  · exfalso
    change ((i / 8 : Nat) : Int) < gbar 0 at hi
    rw [gbar_zero] at hi
    omega

/-- (a) **The premises of `CommonPathAcquisition` hold together**, with a settled phase. -/
theorem acquisition_premises :
    GoldilocksRun (sp := sp1) (ro := ro1) (fun _ => v0) dg1 Set.univ (tickRun N1 dg1) ∧
      HSShared (tickRun N1 dg1) Set.univ dg1 0 1 ∧
      CatchRun (tickRun N1 dg1) Set.univ 0 (2 * sp1.Δ) ∧
      PropPlus (tickRun N1 dg1) Set.univ (fun _ => v0) 0 4 ∧
      SettledIn (tickRun N1 dg1) Set.univ 0 20 160 4 (.top (blk 3)) :=
  ⟨healing_premises.1, healing_premises.2.1, healing_premises.2.2.1, healing_premises.2.2.2,
    settledIn_tickRun⟩

/-- `D_HS = (8k + 48)Δ + 2G_p = 72` at `G_p = 4`. -/
theorem D_HS_sp1 : D_HS sp1 4 = 72 := by decide

/-- (b) **HS.4 (a) by its first disjunct, read directly**: at every cut after `w + D_HS = 92` the
frontier is `hexp (stTip j') ≥ 23 > 4`, so no phase at cut `160` is the phase there. -/
theorem acquisition_phase_changes :
    ∀ j', FirstCutAfter (tickRun N1 dg1) j' (20 + D_HS sp1 4) →
      PhaseChanged (tickRun N1 dg1).projFG Set.univ 160 j' := by
  intro j' hj' m c h0 h1
  have front : ∀ j, PhaseAt (tickRun N1 dg1).projFG Set.univ j m c →
      hexp (stTip j) = m := fun j h => by
    have hf : FrontierAt (tickRun N1 dg1).projFG Set.univ j m := by cases c <;> exact h.1
    obtain ⟨y, -, hy⟩ := hf.1
    rw [store_eq, hmax_state] at hy
    exact hy
  have e0 := front 160 h0
  have e1 := front j' h1
  rw [stTip_160] at e0
  have ht := hj'.2
  rw [D_HS_sp1, tickRun_time] at ht
  have hle := tip_le_stTip j'
  have ht' : (92 : Int) < ((j' / 8 : Nat) : Int) := ht
  have h93 : 93 ≤ j' / 8 := by omega
  have : 23 ≤ tip (j' / 8) := by unfold tip; omega
  unfold hexp at e0 e1
  split_ifs at e0 e1 <;> omega

/-- **`common_path_acquisition` applied to the settled instance**: its conclusion (a), the bounded
common path or a phase change by `w + D_HS`. -/
theorem acquisition_applies :
    (∀ j', FirstCutAfter (tickRun N1 dg1) j' (20 + D_HS sp1 4) →
        PhaseChanged (tickRun N1 dg1).projFG Set.univ 160 j') ∨
      ∃ (s h : Nat) (E W : SA.Blk sp1.n (List (FG.Att sp1.n))) (kW : Nat),
        (h = phaseFloor 4 (PhaseCase.top (blk 3)) ∨ h = 4) ∧ 1 ≤ h ∧
        (tickRun N1 dg1).ProposesAt v0 kW W ∧ W.slot = s ∧ v0 ∈ (Set.univ : Set (Fin sp1.n)) ∧
        EntryOf ((tickRun N1 dg1).post kW).fg W E h ∧
        (((tickRun N1 dg1).post kW).fg.σ W.root).h = h ∧
        20 ≤ sp1.ts s ∧ rTime sp1 20 ≤ sp1.ts s ∧ sp1.ts s + 6 * sp1.Δ ≤ 20 + D_HS sp1 4 ∧
        (∀ jv, FirstCutAfter (tickRun N1 dg1) jv (sp1.ts s + 6 * sp1.Δ) →
          PhaseOn (tickRun N1 dg1).projFG Set.univ 160 jv 4 (.top (blk 3))) ∧
        (∀ y ∈ (Set.univ : Set (Fin sp1.n)), ∀ k ℓ e, SA.CastAt (tickRun N1 dg1).projAC y k ℓ e →
          e.msg.slot = s → e.msg.head = W.root ∧
          (W ∈ ℓ.frame.viableTree (SA.voterBlockTree sp1 e.readPoint ℓ.frame s) ∨
            Anc ((tickRun N1 dg1).HonestBlocks Set.univ) W ℓ.frame.fcRoot)) ∧
        (∀ y ∈ (Set.univ : Set (Fin sp1.n)), (∃ k ℓ C, SA.ToFGAt (tickRun N1 dg1).projAC y k ℓ C ∧
            sp1.ts s ≤ (tickRun N1 dg1).time k ∧
            (tickRun N1 dg1).time k ≤ sp1.ts s + 6 * sp1.Δ ∧
            ((tickRun N1 dg1).state y k).fg.Anc W C ∧
            EntryOf ((tickRun N1 dg1).state y k).fg C E h ∧
            (((tickRun N1 dg1).state y k).fg.σ C.root).h = h ∧
            EffAllowed ((tickRun N1 dg1).state y k).fg 4 (.top (blk 3)) C) ∨
          ∃ k att, (tickRun N1 dg1).SignAt y k att ∧
            (tickRun N1 dg1).time k ≤ sp1.ts s + 6 * sp1.Δ ∧ att.h = h ∧ att.T = E.root) ∧
        (∀ y ∈ (Set.univ : Set (Fin sp1.n)), ∀ k ℓ e, SA.CastAt (tickRun N1 dg1).projAC y k ℓ e →
          s < e.msg.slot → PhaseOn (tickRun N1 dg1).projFG Set.univ 160 k 4 (.top (blk 3)) →
          SA.VoteExtends ((tickRun N1 dg1).HonestBlocks Set.univ) e.msg W) ∧
        ∀ (s' : Nat) (P' : SA.Blk sp1.n (List (FG.Att sp1.n))) (k' : Nat), s < s' →
          P'.slot = s' → (tickRun N1 dg1).ProposesAt v0 k' P' →
          v0 ∈ (Set.univ : Set (Fin sp1.n)) →
          PhaseOn (tickRun N1 dg1).projFG Set.univ 160 k' 4 (.top (blk 3)) →
          ∃ Pr, P'.parent = some Pr.root ∧ Anc ((tickRun N1 dg1).HonestBlocks Set.univ) W Pr := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := acquisition_premises
  exact (common_path_acquisition sp1 ro1 (fun _ => v0) dg1 Set.univ (tickRun N1 dg1) 0 1 4 20 160 4
    (.top (blk 3)) h₁ h₂ h₃ h₄ h₅).1

end Consensus.Goldilocks.Witness.One.Settled

end
