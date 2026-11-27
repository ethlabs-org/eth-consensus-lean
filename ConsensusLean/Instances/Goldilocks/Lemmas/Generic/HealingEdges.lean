module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Truncation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.RiseWindow
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingRounds
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameWindowCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameKey
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.StatementsBundle
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.FrameWindowExists
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.RiseWindow
import ConsensusLean.Lemmas.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

/-! # Generic healing assembly edges

The assembly edges over any node AC, from the generic healing leaves (`HealingLeaves` and
`HealingRounds`). Every edge is a theorem.

`reset_or_noAdvance` is proved: a high signing before `T` by a signer honest at it and at `c_z`
gives a reset no later (leaf 1, `reset_of_height_advance_at_from`); without one, `NoAdvance` holds
at `T`.

`highCanonical` is proved over any `ACHealing`: by the horizon of a premised reset, honest stores
have no high contest (leaf 13), high signings come from high origins (leaf 12), and self-entries of
equal height below two high origins are equal (leaf 14, `high_entry_eq_at_of_healing`).

`rise_reset_rounds_at_of` proves the rise contract `rise_reset_rounds_at` over any `ACHealing`, by
induction on the remaining rounds: a warm high proposal gives the reset (leaf 10); a lower one is
crossed by the next honest proposal `δt` to `δt + G - 1` slots later (leaf 11), which is one round
closer.

`exists_reset` proves the slot-budget reset over any `ACHealing` on any slot schedule with
`t_{s+1} ≥ t_s + 4Δ`. The schedule has no upper bound on slot lengths, so leaf 3 is run in slot
space (`exists_slotWindow_seq`): the pigeonhole over the slots of honest cuts, with a lag of two
slots, gives a slot window at a constant key `frameKey''`, and the four attempts fit in
`resetSlots`. A
proposal from the gap in that window is at most `riseRounds` rounds below `HZ + 1` (leaf 8), and
the rise resets before the budget's end.

`generic_healing` chains honest proposals after that reset: `exists_reset`, then `highCanonical`
and `ACHealing.heal_after_reset`.

`premises_truncH` assembles the bundled premises on the honest sets truncated after `b` from the
premises for `H` with restarts bounded only up to `b` (`NoRestartUpTo`). With
`ACRun.run_truncH`, `HZ_truncH` and `isReset_truncH_iff` (`HealingLeaves`) it lets a finite-horizon
consumer apply the bundled leaves on the truncation.
-/

namespace Consensus.Goldilocks.Generic

open AC (gbar)
open Healing (cutZ FirstCutAfter riseLen)
open Healing.Growing (HZ IsReset CatchRun)

/-! ## The milestone frame key and window production

The arithmetic of `frameKey''` (twice `h_max`, plus one in a top frame), restriction of a
`FrameWindow`, and the run-independent production: four attempts of the sequential pigeonhole give
a window from a height range, a key lag and `J` agreement. `sum_riseLen_four'`: four attempts fit
the six rise rounds of the five-attempt budget. -/

section FrameWindowKey

variable {P : Params} {A : NodeAC P}

section Key

variable {a b : Store P A.Payload}

/-- Monotone store heights give a monotone key; at fixed `h_max`, top cannot become gap. -/
theorem frameKey''_mono (hm : a.hmax ≤ b.hmax) (hj : a.hj ≤ b.hj) (hb : b.hj < b.hmax) :
    frameKey'' A a ≤ frameKey'' A b := by
  classical
  rw [frameKey''_eq, frameKey''_eq]
  split_ifs <;> omega

/-- The key along an honest node's cuts is monotone. -/
theorem frameKey''_monotone {st : Nat → Store P A.Payload}
    (hm : Monotone fun i => (st i).hmax) (hj : Monotone fun i => (st i).hj)
    (hlt : ∀ i, (st i).hj < (st i).hmax) : Monotone fun i => frameKey'' A (st i) :=
  fun _ _ hij => frameKey''_mono (hm hij) (hj hij) (hlt _)

/-- On two consecutive maximum heights, the key takes one of four consecutive values. -/
theorem frameKey''_bounds {HZ : Nat} (hlo : HZ ≤ a.hmax) (hhi : a.hmax ≤ HZ + 1) :
    2 * HZ ≤ frameKey'' A a ∧ frameKey'' A a ≤ 2 * HZ + 3 := by
  classical
  rw [frameKey''_eq]
  split_ifs <;> omega

/-- Equal keys are exactly equal maximum heights and equal top status. -/
theorem frameKey''_eq_iff : frameKey'' A a = frameKey'' A b ↔
    a.hmax = b.hmax ∧ ((a.hmax = a.hj + 1) ↔ (b.hmax = b.hj + 1)) := by
  classical
  rw [frameKey''_eq, frameKey''_eq]
  split_ifs <;> simp_all <;> omega

end Key

/-- Restricting the interval keeps the pinned data. -/
theorem FrameWindow.mono {tr : RunTrace A} {H : Time → Set (Fin P.n)}
    {lo hi lo' hi' : Time} {M : Nat} {isTop : Prop} {J : A.Blk}
    (h : FrameWindow tr H lo hi M isTop J) (hl : lo ≤ lo') (hh : hi' ≤ hi) :
    FrameWindow tr H lo' hi' M isTop J :=
  ⟨fun y i hy hi₁ hi₂ => h.M_eq y i hy (hl.trans hi₁) (hi₂.trans hh),
    fun y i hy hi₁ hi₂ => h.top_iff y i hy (hl.trans hi₁) (hi₂.trans hh),
    fun y i hy hi₁ hi₂ => h.root_eq y i hy (hl.trans hi₁) (hi₂.trans hh)⟩

open Classical in
/-- The two numerical window fields determine the key. -/
theorem FrameWindow.key_eq {tr : RunTrace A} {H : Time → Set (Fin P.n)}
    {lo hi : Time} {M : Nat} {isTop : Prop} {J : A.Blk}
    (h : FrameWindow tr H lo hi M isTop J) {y : Fin P.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) (hl : lo ≤ tr.time i) (hh : tr.time i ≤ hi) :
    frameKey'' A (tr.state y i).fg = 2 * M + if isTop then 1 else 0 := by
  classical
  rw [frameKey''_eq, h.M_eq y i hy hl hh]
  have ht := h.top_iff y i hy hl hh
  rw [h.M_eq y i hy hl hh] at ht
  simp only [ht]

/-- A constant key gives constant `(M, isTop)`; agreement at equal `h_j` supplies `J`. -/
theorem frameData_of_frameKey''_eq {α : Type*} (mem : α → Nat → Prop)
    (time : Nat → Time) (st : α → Nat → Store P A.Payload) (dflt : A.Blk)
    {lo hi : Time}
    (hK : ∀ y z i m, mem y i → mem z m → lo ≤ time i → time i ≤ hi → lo ≤ time m →
      time m ≤ hi → frameKey'' A (st y i) = frameKey'' A (st z m))
    (hJ : ∀ y z i m, mem y i → mem z m → lo ≤ time i → time i ≤ hi → lo ≤ time m →
      time m ≤ hi → (st y i).hj = (st z m).hj → (st y i).J = (st z m).J) :
    ∃ M isTop J,
      (∀ y i, mem y i → lo ≤ time i → time i ≤ hi → (st y i).hmax = M) ∧
      (∀ y i, mem y i → lo ≤ time i → time i ≤ hi →
        ((st y i).hmax = (st y i).hj + 1 ↔ isTop)) ∧
      (∀ y i, mem y i → lo ≤ time i → time i ≤ hi → isTop → (st y i).J = J) := by
  classical
  by_cases hex : ∃ y i, mem y i ∧ lo ≤ time i ∧ time i ≤ hi
  · obtain ⟨y₀, i₀, hy₀, h₁, h₂⟩ := hex
    have heq := fun y i hy hl hh =>
      frameKey''_eq_iff.mp (hK y y₀ i i₀ hy hy₀ hl hh h₁ h₂)
    refine ⟨_, _, (st y₀ i₀).J, fun y i hy hl hh => (heq y i hy hl hh).1,
      fun y i hy hl hh => (heq y i hy hl hh).2, fun y i hy hl hh ht => ?_⟩
    have h := heq y i hy hl hh
    have ht' := h.2.mpr ht
    apply hJ y y₀ i i₀ hy hy₀ hl hh h₁ h₂
    omega
  · push Not at hex
    exact ⟨0, True, dflt, fun y i hy hl hh => absurd hh (not_le.mpr (hex y i hy hl)),
      fun y i hy hl hh => absurd hh (not_le.mpr (hex y i hy hl)),
      fun y i hy hl hh => absurd hh (not_le.mpr (hex y i hy hl))⟩

/-- **Window production.** Four attempts of the sequential pigeonhole give a frame window, once
the run supplies the height range, the key lag and `J` agreement at equal `h_j`. -/
theorem exists_frameWindow_seq_of_mem {tr : RunTrace A} {H : Time → Set (Fin P.n)}
    {lo lam T : Time} {hz : Nat} (len : Nat → Time)
    (hlen : ∀ v, 0 ≤ len v) (hlam : 0 ≤ lam)
    (hrange : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i < T →
      hz ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ hz + 1)
    (hlag : ∀ x z i k, x ∈ H (tr.time i) → z ∈ H (tr.time k) →
      lo ≤ tr.time i → tr.time i < T → tr.time i + lam ≤ tr.time k → tr.time k < T →
      frameKey'' A (tr.state x i).fg ≤ frameKey'' A (tr.state z k).fg)
    (hJ : ∀ y z i m, y ∈ H (tr.time i) → z ∈ H (tr.time m) → lo ≤ tr.time i →
      tr.time i < T → lo ≤ tr.time m → tr.time m < T →
      (tr.state y i).fg.hj = (tr.state z m).fg.hj →
      (tr.state y i).fg.J = (tr.state z m).fg.J)
    (hT : lo + ∑ j ∈ Finset.range 4, (len (2 * hz + j) + lam) < T) :
    ∃ v, 2 * hz ≤ v ∧ v ≤ 2 * hz + 3 ∧ ∃ a, lo + lam ≤ a ∧
      a + len v ≤ lo + ∑ j ∈ Finset.range (v - 2 * hz + 1), (len (2 * hz + j) + lam) ∧
      (∀ y i, y ∈ H (tr.time i) → a ≤ tr.time i → tr.time i ≤ a + len v →
        frameKey'' A (tr.state y i).fg = v) ∧
      ∃ M isTop J, FrameWindow tr H a (a + len v) M isTop J := by
  obtain ⟨v, hv₁, hv₂, a, ha, hb, hK⟩ := Healing.exists_const_window_seq_of_mem
    (fun y i => y ∈ H (tr.time i)) tr.time (fun y i => frameKey'' A (tr.state y i).fg)
    (2 * hz) 3 len hlen hlam
    (fun y i hy hl hh => frameKey''_bounds (hrange y i hy hl hh).1
      (hrange y i hy hl hh).2) hlag hT
  have hpart : (∑ j ∈ Finset.range (v - 2 * hz + 1), (len (2 * hz + j) + lam)) ≤
      ∑ j ∈ Finset.range 4, (len (2 * hz + j) + lam) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun j _ _ => add_nonneg (hlen _) hlam)
  have hend : a + len v < T := lt_of_le_of_lt (hb.trans (add_le_add_right hpart lo)) hT
  obtain ⟨M, isTop, J, hM, ht, hj⟩ := frameData_of_frameKey''_eq
    (fun y i => y ∈ H (tr.time i)) tr.time (fun y i => (tr.state y i).fg)
    (P.genesisBlock A.genesisPayload)
    (fun y z i m hy hz hi₁ hi₂ hm₁ hm₂ =>
      (hK y i hy hi₁ hi₂).trans (hK z m hz hm₁ hm₂).symm)
    (fun y z i m hy hz hi₁ hi₂ hm₁ hm₂ => hJ y z i m hy hz
      ((le_add_of_nonneg_right hlam).trans (ha.trans hi₁)) (hi₂.trans_lt hend)
      ((le_add_of_nonneg_right hlam).trans (ha.trans hm₁)) (hm₂.trans_lt hend))
  exact ⟨v, hv₁, hv₂, a, ha, hb, hK, M, isTop, J, hM, ht, hj⟩

/-- Four attempts retain the six rise rounds of the five-attempt budget. -/
theorem sum_riseLen_four' (d ρ s lam : Time) (HZ : Nat) :
    ∑ j ∈ Finset.range 4, (Healing.riseLen d ρ s HZ (2 * HZ + j) + lam) =
      4 * (d + s + lam) + 6 * ρ := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Healing.riseLen_eq,
    Healing.riseRounds_eq, Nat.add_sub_cancel_left]
  norm_num
  ring

end FrameWindowKey

/-! ## Four-delay grid timing -/

private theorem grid_span {P : Params} (hgrid : ∀ s : Nat, P.slotTime s = (s : Time) * (4 * P.Δ))
    (s d : Nat) : P.slotTime (s + d) = P.slotTime s + 4 * P.Δ * (d : Time) := by
  rw [hgrid, hgrid]
  push_cast
  ring

/-- On the four-delay grid `t_s = s · 4Δ`, the timeout inequality at every slot is the numerical
bound `6Δ + ΔF ≤ 4Δ · δt`. -/
theorem timeout_grid_equation {P : Params} (ΔF : Time)
    (hgrid : ∀ s : Nat, P.slotTime s = (s : Time) * (4 * P.Δ)) :
    (∀ s, P.slotTime s + 6 * P.Δ + ΔF ≤ P.slotTime (s + P.δt)) ↔
      6 * P.Δ + ΔF ≤ 4 * P.Δ * (P.δt : Time) := by
  constructor
  · intro h
    linarith [h 0, grid_span hgrid 0 P.δt]
  · intro h s
    linarith [grid_span hgrid s P.δt]

/-- On the four-delay grid every slot is `4Δ` long. -/
theorem slotLen_of_grid {P : Params} (hgrid : ∀ s : Nat, P.slotTime s = (s : Time) * (4 * P.Δ)) :
    ∀ s, P.slotTime s + 4 * P.Δ ≤ P.slotTime (s + 1) := fun s => by
  have h := grid_span hgrid s 1
  push_cast at h
  linarith

section Edges

variable {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n} {runs : ACRun A sg}

/-- Reset or no advance: by a horizon of the bundled premises, either a reset happens by `T` or
no signer honest at its signing and at `c_z` signs above `HZ` before `T`. A high signing gives
the reset by leaf 1, with fewer than `q` faulty nodes at `max c_z t_k ≤ b` (`Premises.faults`,
`Premises.snapshot`). -/
theorem reset_or_noAdvance {hold : Time} :
    ∀ {cm βK tr H proposer dg g ΔF b T},
      runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b hold → T ≤ b →
      (∃ a, IsReset tr H g a ∧ a ≤ T) ∨ NoAdvance tr H g T := by
  intro cm βK tr H proposer dg g ΔF b T hrun hP hTb
  by_cases hadv : ∃ v k att, v ∈ H (max (cutZ P g) (tr.time k)) ∧ tr.SignAt v k att ∧
      tr.time k < T ∧ HZ tr H g + 1 ≤ att.h
  · obtain ⟨v, k, att, hv, hs, hk, hh⟩ := hadv
    have hrl := runs.run_local hrun
    obtain ⟨j, hj, hjb⟩ := hP.snapshot
    have hmax : max (cutZ P g) (tr.time k) ≤ b := max_le (hj.2.le.trans hjb) (hk.le.trans hTb)
    obtain ⟨a, ha, hak⟩ := reset_of_height_advance_at_from hrl
      (faults_lt_q hP.faults ((hrl.time_nonneg k).trans (le_max_right _ _)) hmax) hv hs hh
    exact Or.inl ⟨a, ha, hak.trans hk.le⟩
  · refine Or.inr fun v k att hv hs hk => ?_
    by_contra h
    exact hadv ⟨v, k, att, hv, hs, hk, by omega⟩

/-- A reset within the budget is within the origin cap. -/
private theorem originInCap_of_resetInBudget {P : Params} {budget : Option Nat} {drain : Nat}
    {g a : Time} (ha0 : 0 ≤ a) (h : ResetInBudget P budget drain g a) :
    OriginInCap P budget g a := by
  intro m hm
  have hb := h m hm
  have hspec := (slotOfSpec_iff.mp slotOf_spec) P
  exact (hspec a ha0).2.le.trans (P.slotTime_strictMono.monotone (by omega))

/-- A time within the capped horizon is within the horizon and the origin cap. -/
private theorem le_originCapTime {P : Params} {budget : Option Nat} {g b t : Time}
    (h : t ≤ originCapTime P budget g b) : t ≤ b ∧ OriginInCap P budget g t := by
  cases budget with
  | none => exact ⟨h, fun m hm => by cases hm⟩
  | some m =>
    simp only [originCapTime] at h
    exact ⟨h.trans (min_le_left _ _), fun m' hm' => by cases hm'; exact h.trans (min_le_right _ _)⟩

/-- Canonical high entries by the capped horizon of a premised reset within the budget, field by
field from leaves 13, 12 and 14 over the supplier `O`. -/
theorem highCanonical {hold : Time} (O : ACHealing A sg runs hold) :
    ∀ {cm βK tr H proposer dg g ΔF b a}, βK ≤ 1 / 2 →
      runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b hold →
      IsReset tr H g a → a ≤ b → ResetInBudget P O.deepBudget O.drain g a →
      HighCanonical O.Origin tr H g (originCapTime P O.deepBudget g b) := by
  intro cm βK tr H proposer dg g ΔF b a hβ hrun hP hr hab hbudget
  have hacap : OriginInCap P O.deepBudget g a := by
    obtain ⟨y, k, att, -, -, -, hk⟩ := hr.1
    exact originInCap_of_resetInBudget (hk ▸ (runs.run_local hrun).time_nonneg k) hbudget
  refine ⟨fun _ _ hp hib => no_high_contest_at_of_healing O hβ hrun hP hr hab hacap hp
      (le_originCapTime hib).1 (le_originCapTime hib).2,
    fun _ _ _ hy hs hkb hh => ?_, ?_⟩
  · obtain ⟨r, hrk, l, Og, ⟨hyr, hO, hOh⟩, E, hE, hEO, hEr, hEh, hET⟩ :=
      high_row_source_at_of_healing O hβ hrun hP hr hab hy (le_originCapTime hkb).1
        (le_originCapTime hkb).2 hs hh
    exact ⟨r, hrk, l, Og, hO, hyr, hOh, E, hE, hEO, hEr, hEh, hET⟩
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hx hO hib hBh hx' hO' hi'b hB'h h₁ h₂ ht₁ hle₁ hy₁
      ht₂ hle₂ hy₂ hZ₁ hZ₂ hh hT₁ hT₂
    exact high_entry_eq_at_of_healing O hβ hrun hP hr hab hacap ⟨hx, hO, hBh⟩
      (le_originCapTime hib).1 (le_originCapTime hib).2 ⟨hx', hO', hB'h⟩
      (le_originCapTime hi'b).1 (le_originCapTime hi'b).2
      h₁ h₂ ht₁ hle₁ hy₁ ht₂ hle₂ hy₂ hZ₁ hZ₂ hh hT₁ hT₂

/-- The rise contract over the supplier `O`, by induction on the remaining rounds `r`. A warm
proposal at or above `HZ + 1` gives the reset by leaf 10. Otherwise the proposal gap gives an
honest proposal `x` in `[u + δt, u + δt + G - 1]`; leaf 11 puts it one height above the warm
proposal in its proposer's store, which has the warm proposal's replay state
(`proposal_mem_at_from`, `σ_eq_honest_at_from`), and the induction hypothesis applies at `x`.
The spacing gives `δt ≥ 2` with `ΔF > 0`, and every slot time is read from `ProposesAt`. -/
theorem rise_reset_rounds_at_of {hold : Time} (O : ACHealing A sg runs hold) :
    ∀ {cm proposer dg H} {tr : RunTrace A} {βK : ℚ} {g ΔF b T : Time}
      {s₀ N Gp M : Nat} {isTop : Prop} {J : A.Blk},
    βK ≤ 1 / 2 → CommitteeFaultsUpTo βK cm H g b →
    SlotWindowWithin tr H O.reportDelay s₀ N M isTop J →
    runs.Run cm proposer dg H tr → Compose.NoCollRun dg tr → Service tr H g ΔF b hold →
    (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    (∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) →
    CatchRun tr H g (2 * P.Δ) → Healing.Growing.NoRestartAfter tr H (gbar g) →
    (∀ s, P.slotTime s + 4 * P.Δ ≤ P.slotTime (s + 1)) →
    (∀ s, shiftDelay P O.reportDelay (P.slotTime (s + 1) + 2 * P.Δ) + ΔF ≤
      P.slotTime (s + P.δt)) →
    (∃ k, FirstCutAfter tr k (cutZ P g) ∧ tr.time k ≤ b) →
    gbar g + 4 * P.Δ ≤ P.slotTime s₀ → O.follow ≤ P.δt → 1 ≤ Gp →
    (∀ s, P.slotTime s + 6 * P.Δ + ΔF ≤ P.slotTime (s + P.δt)) →
    ProposalGap tr H proposer Gp s₀ N → shiftDelay P O.reportDelay (P.slotTime N + 2 * P.Δ) ≤ b →
    (H b).Nonempty → T ≤ b → NoAdvance tr H g T →
    ∀ (r : Nat) {u : Nat} {z : Fin P.n} {kB : Nat} {B : A.Blk},
      s₀ ≤ u → s₀ + O.warmup ≤ u → u + r * (P.δt + Gp - 1) + 1 ≤ N →
      shiftDelay P O.reportDelay (P.slotTime (u + r * (P.δt + Gp - 1) + 1) + 2 * P.Δ) ≤ T →
      z ∈ H (P.slotTime u + P.Δ) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
      HZ tr H g + 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h + r →
      ∃ a, IsReset tr H g a ∧
        a ≤ shiftDelay P O.reportDelay (P.slotTime (u + r * (P.δt + Gp - 1) + 1) + 2 * P.Δ) := by
  intro cm proposer dg H tr βK g ΔF b T s₀ N G M isTop J hβ hcom hframe hrun hnc hsvc
    hawake hf hcatch hnr hsl hsp hsnap hm hfol hG htd hgp hmb hHb hTb hna r
  have hrl := runs.run_local hrun
  have hΔ := P.hΔ
  have hdF := hsvc.deltaF
  have hmono := P.slotTime_strictMono.monotone
  have hδ2 : 2 ≤ P.δt := by
    by_contra h1
    have h := hsp 0
    have := hmono (show 0 + P.δt ≤ 0 + 1 by omega)
    rw [shiftDelay_eq_add] at h
    have : 0 ≤ (O.reportDelay : Time) * P.Δ := by positivity
    linarith
  induction r with
  | zero =>
    intro u z kB B hs₀u hwarm hN hT hz hdes hB hBs hrise
    simpa only [Nat.zero_mul, Nat.add_zero] using
      reset_of_high_proposal_at_of_healing O hβ hcom hframe hrun hnc hsvc hawake hf hcatch hnr
        hsl htd hsnap hm hs₀u hwarm (by simpa using hN) hmb hHb hz hdes hB hBs
        (by simpa using hrise)
  | succ r ih =>
    intro u z kB B hs₀u hwarm hN hT hz hdes hB hBs hrise
    have hmul : (r + 1) * (P.δt + G - 1) = r * (P.δt + G - 1) + (P.δt + G - 1) :=
      Nat.succ_mul r _
    by_cases hh : HZ tr H g + 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h
    · obtain ⟨a, ha, hat⟩ := reset_of_high_proposal_at_of_healing O hβ hcom hframe hrun hnc hsvc
        hawake hf hcatch hnr hsl htd hsnap hm hs₀u hwarm (by omega) hmb hHb hz hdes hB hBs hh
      exact ⟨a, ha, hat.trans (by
        apply shiftDelay_le
        linarith [hmono (show u + 1 ≤ u + (r + 1) * (P.δt + G - 1) + 1 by omega)])⟩
    obtain ⟨x, hxl, hxr, hpx, kX, X, hX, hXs⟩ := hgp (u + P.δt) (by omega) (by omega)
    have htX : tr.time kX = P.slotTime x := by rw [hX.2.2, hXs]
    have hpx0 : proposer x ∈ H (tr.time kX) := hrl.antitone (by rw [htX]; linarith) hpx
    have hstrict : shiftDelay P O.reportDelay (P.slotTime (u + 1) + 2 * P.Δ) < T := by
      have := P.slotTime_strictMono (show u + 1 < u + (r + 1) * (P.δt + G - 1) + 1 by omega)
      rw [shiftDelay_eq_add] at hT ⊢
      linarith
    obtain ⟨hBp, -, hcross⟩ := round_of_warm_at_of_healing O hβ hcom hframe hrun hnc hsvc
      hawake hf hcatch hnr hsl hsp hsnap hm hs₀u hwarm hfol htd hxl (by omega) hmb hHb hTb hna
      hstrict hz hdes hB hBs hpx0 rfl hX hXs
    have htB : tr.time kB = P.slotTime u := by rw [hB.2.2, hBs]
    have hz0 : z ∈ H (tr.time kB) := hrl.antitone (by rw [htB]; linarith) hz
    have hBm := proposal_mem_at_from hrl (runs.run_requirements hrun) (runs.run_root hrun) hnc
      hz0 hB
    have hσ := σ_eq_honest_at_from hrl hnc (hrl.time_nonneg kB)
      (fun q hq => hrl.time_mono (by omega)) hz0 (hrl.time_nonneg kX)
      (fun q hq => hrl.time_mono (by omega)) hpx0 hBm hBp
    rw [← hσ] at hcross
    have hnext : x + r * (P.δt + G - 1) + 1 ≤ u + (r + 1) * (P.δt + G - 1) + 1 := by omega
    obtain ⟨a, ha, hat⟩ := ih (u := x) (by omega) (by omega) (hnext.trans hN)
      ((shiftDelay_le _ (by linarith [hmono hnext])).trans hT) hpx rfl hX hXs (by omega)
    exact ⟨a, ha, hat.trans (shiftDelay_le _ (by linarith [hmono hnext]))⟩

/-- The milestone key is the stock frame key `3h + c` (`c = 2` contest, `1` clean top, `0`
gap) under `3h + c ↦ 2h + min c 1`: a contest is a top frame. -/
private theorem frameKey''_eq_of_frameKey (st : Store P A.Payload) :
    frameKey'' A st = 2 * (Healing.frameKey st / 3) + min (Healing.frameKey st % 3) 1 := by
  classical
  have hc : st.Contest → st.hmax = st.hj + 1 := fun h => h.1
  rw [frameKey''_eq, Healing.frameKey_def]
  by_cases h₁ : st.Contest
  · have := hc h₁
    simp only [h₁, this, ite_true]
    omega
  · by_cases h₂ : st.hmax = st.hj + 1
    · simp only [h₁, h₂, ite_false, ite_true]
      omega
    · simp only [h₁, h₂, ite_false]
      omega

/-- **The milestone key lag** between independently honest observations: the stock frame-key
lag (`frameKey_lag_obs_from`) read through `frameKey''_eq_of_frameKey`. -/
theorem frameKey''_lag_obs_from {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
    {tr : RunTrace A} {ini : Fin P.n → A.State} {hold : Time}
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * P.fg.q - P.n)
    (hsvc : Service tr H g ΔF b hold) (hcatch : CatchRun tr H g κ)
    {x z : Fin P.n} {i m : Nat} (hx : x ∈ H (tr.time i)) (hz : z ∈ H (tr.time m))
    (him : tr.time i ≤ tr.time m) (hmb : tr.time m ≤ b)
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) P.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) :
    frameKey'' A (tr.state x i).fg ≤ frameKey'' A (tr.state z m).fg := by
  have hk := frameKey_lag_obs_from h hnc hf hsvc hcatch hx hz him hmb hcall hcm
  rw [frameKey''_eq_of_frameKey, frameKey''_eq_of_frameKey]
  omega

/-- A milestone key that is constant over the cuts of `[lo, hi]` of nodes honest at them gives a
`FrameWindow`, when `hi ≤ b`: `J` from agreement at equal `h_j`. -/
theorem frameWindow_of_frameKey''_eq_obs_from {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
    {tr : RunTrace A} {ini : Fin P.n → A.State}
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {b : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * P.fg.q - P.n)
    {lo hi : Time} (hhi : hi ≤ b)
    (hK : ∀ y z i m, y ∈ H (tr.time i) → z ∈ H (tr.time m) → lo ≤ tr.time i →
      tr.time i ≤ hi → lo ≤ tr.time m → tr.time m ≤ hi →
      frameKey'' A (tr.state y i).fg = frameKey'' A (tr.state z m).fg) :
    ∃ M isTop J, FrameWindow tr H lo hi M isTop J := by
  have hle : ∀ i k, k < i → tr.time k ≤ tr.time i := fun _ _ hk => h.time_mono hk.le
  obtain ⟨M, isTop, J, h1, h2, h3⟩ := frameData_of_frameKey''_eq
    (fun y i => y ∈ H (tr.time i)) tr.time (fun y i => (tr.state y i).fg)
    (P.genesisBlock A.genesisPayload) hK
    (fun y z i m hy hz _ hi _ hm he =>
      Healing.Store.J_eq_of_cache_hj_eq_of_safe
        (fg_reachable_at_from h (h.time_nonneg i) (hle i) hy)
        (fg_reachable_at_from h (h.time_nonneg m) (hle m) hz)
        (Compose.Growing.honest_blocks_coherent_local h hnc)
        (fun _ hX => ⟨y, i, tr.time i, h.time_nonneg i, hle i, hy, hX⟩)
        (fun _ hX => ⟨z, m, tr.time m, h.time_nonneg m, hle m, hz, hX⟩)
        (hf _ ((h.time_nonneg i).trans (le_max_left _ _)) (max_le (hi.trans hhi) (hm.trans hhi)))
        (held_atts_safe_at_from h (h.time_nonneg i) (hle i) hy (h.time_nonneg m) (hle m) hz
          (le_max_left _ _) (le_max_right _ _))
        he)
  exact ⟨M, isTop, J, ⟨h1, h2, h3⟩⟩

/-- Leaf 3 in slot space, on any schedule with `t_{s+1} ≥ t_s + 4Δ`: the sequential pigeonhole
(`Healing.Growing.exists_const_window_seq`) run over the slots `slot(t_i)` of the cuts of nodes
honest at them, from slot `s + 1` to `S`, with a lag of two slots and window lengths `len v` in
slots. Before `t_S` there is no advance, so the key `frameKey''` is in `[2HZ, 2HZ + 3]` (leaf 2,
both bounds) and four attempts suffice; two slots apart, a later cut is more than `4Δ` after an
earlier one (relay calls, `frameKey''_lag_obs_from`). A constant slot window `[s₀, s₀ + len v]`
covers the time window
`[t_{s₀}, t_{s₀ + len v} + 2Δ]`, which is a `SlotWindow`. -/
private theorem exists_slotWindow_seq {cm βK tr H proposer dg g ΔF b hold}
    (hrun : runs.Run cm proposer dg H tr) (hP : Premises tr H cm βK proposer dg sg g ΔF b hold)
    {s S : Nat} (hgs : gbar g ≤ P.slotTime s) (hcs : cutZ P g ≤ P.slotTime s)
    (hSb : P.slotTime S ≤ b) (hna : NoAdvance tr H g (P.slotTime S)) (len : Nat → Nat)
    (hS : s + 1 + ∑ j ∈ Finset.range 5, (len (2 * HZ tr H g + j) + 2) < S) :
    ∃ v, 2 * HZ tr H g ≤ v ∧ ∃ s₀, s + 3 ≤ s₀ ∧ s₀ + len v < S ∧
      (∀ y i, y ∈ H (tr.time i) → P.slotTime s₀ ≤ tr.time i →
        tr.time i ≤ P.slotTime (s₀ + len v) + 2 * P.Δ → frameKey'' A (tr.state y i).fg = v) ∧
      ∃ M isTop J, SlotWindow tr H s₀ (s₀ + len v) M isTop J := by
  classical
  have hrl := runs.run_local hrun
  have hΔ : (1 : Time) ≤ P.Δ := P.hΔ
  have hmono := P.slotTime_strictMono.monotone
  have hspec := (slotOfSpec_iff.mp slotOf_spec) P
  have hsl := hP.slotLen
  have hf2 : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * P.fg.q - P.n := fun t h0 htb =>
    P.fg.faults_lt_quorum_margin (hP.faults t h0 htb)
  have hlt : ∀ i, P.slotOf (tr.time i) < S → tr.time i < P.slotTime S := fun i hi =>
    (hspec _ (hrl.time_nonneg i)).2.trans_le (hmono (by omega))
  have hge : ∀ i n, n ≤ P.slotOf (tr.time i) → P.slotTime n ≤ tr.time i := fun i n hn =>
    (hmono hn).trans (hspec _ (hrl.time_nonneg i)).1
  have hs1 := hsl s
  have hcb : cutZ P g ≤ b := hcs.trans ((hmono (show s ≤ S by omega)).trans hSb)
  have hH : (H (cutZ P g)).Nonempty := hP.nonempty.mono (hrl.antitone hcb)
  have hST : ((s + 1 : Nat) : Time) +
      ∑ j ∈ Finset.range 4, ((len (2 * HZ tr H g + j) : Time) + 2) < (S : Time) := by
    rw [Finset.sum_range_succ] at hS
    have h4 : s + 1 + ∑ j ∈ Finset.range 4, (len (2 * HZ tr H g + j) + 2) < S := by omega
    have := (show ((s + 1 + ∑ j ∈ Finset.range 4, (len (2 * HZ tr H g + j) + 2) : Nat) : Time) <
      (S : Time) by exact_mod_cast h4)
    push_cast at this
    exact this
  obtain ⟨v, hv1, hv2, a, ha, hav, hK⟩ := Healing.Growing.exists_const_window_seq
    (fun y i => y ∈ H (tr.time i)) (fun i => (P.slotOf (tr.time i) : Time))
    (fun y i => frameKey'' A (tr.state y i).fg) (2 * HZ tr H g) 3
    (fun v => (len v : Time)) (lo := ((s + 1 : Nat) : Time)) (T := (S : Time))
    (fun _ => Nat.cast_nonneg _) (show (0 : Time) ≤ 2 by norm_num)
    (fun y i hy h1 h2 => by
      have h1' : s + 1 ≤ P.slotOf (tr.time i) := by exact_mod_cast h1
      have h2' : P.slotOf (tr.time i) < S := by exact_mod_cast h2
      have hti := hge i _ h1'
      have hiT := hlt i h2'
      have hib : tr.time i ≤ b := hiT.le.trans hSb
      have hczi : cutZ P g ≤ tr.time i := by linarith
      have hmx : max (cutZ P g) (tr.time i) = tr.time i := max_eq_right hczi
      obtain ⟨hsnap, hcall⟩ := snapshotCall_of_awake_at_from hrl hP.awake hy (by linarith) hib
      exact frameKey''_bounds
        (HZ_le_hmax_at_from hrl hP.noColl hP.sync hP.catchUp hH hsnap hy
          (by rw [hmx]; exact hf2 _ (hrl.time_nonneg i) hib) hcall (by linarith))
        (hmax_le_of_noAdvance_at_from hrl hna hy
          (by rw [hmx]; exact faults_lt_q hP.faults (hrl.time_nonneg i) hib) hiT))
    (fun x z i k hx hz h1 _ hik hk => by
      have h1' : s + 1 ≤ P.slotOf (tr.time i) := by exact_mod_cast h1
      have hik' : P.slotOf (tr.time i) + 2 ≤ P.slotOf (tr.time k) := by exact_mod_cast hik
      have hk' : P.slotOf (tr.time k) < S := by exact_mod_cast hk
      have hti := hge i _ h1'
      have hi1 := (hspec _ (hrl.time_nonneg i)).2
      have hk2 := hge k _ hik'
      have hs2 := hsl (P.slotOf (tr.time i) + 1)
      have hkb : tr.time k ≤ b := (hlt k hk').le.trans hSb
      have him : tr.time i + 2 * P.Δ ≤ tr.time k := by linarith
      exact frameKey''_lag_obs_from hrl hP.noColl hf2 hP.sync hP.catchUp hx hz (by linarith) hkb
        (callLag_of_awake_at_from hrl hP.awake hcs hz (by linarith) him hkb) (by linarith))
    hST
  have ha0 : (0 : Time) ≤ a := by
    have : (0 : Time) ≤ ((s + 1 : Nat) : Time) := Nat.cast_nonneg _
    linarith
  obtain ⟨s₀, rfl⟩ : ∃ s₀ : Nat, a = (s₀ : Time) := ⟨a.toNat, (Int.toNat_of_nonneg ha0).symm⟩
  have hs₀ : s + 3 ≤ s₀ := by
    have : ((s + 3 : Nat) : Time) ≤ (s₀ : Time) := by push_cast at ha ⊢; linarith
    exact_mod_cast this
  have hpart : ∑ j ∈ Finset.range (v - 2 * HZ tr H g + 1), ((len (2 * HZ tr H g + j) : Time) + 2)
      ≤ ∑ j ∈ Finset.range 4, ((len (2 * HZ tr H g + j) : Time) + 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      fun _ _ _ => by positivity
  have hN : s₀ + len v < S := by
    push_cast at hav hST
    have : ((s₀ + len v : Nat) : Time) < (S : Time) := by push_cast; linarith
    exact_mod_cast this
  have hNS := hsl (s₀ + len v)
  have hN1 : P.slotTime (s₀ + len v + 1) ≤ P.slotTime S := hmono (by omega)
  have hhi : P.slotTime (s₀ + len v) + 2 * P.Δ ≤ b := by linarith
  have hKt : ∀ y i, y ∈ H (tr.time i) → P.slotTime s₀ ≤ tr.time i →
      tr.time i ≤ P.slotTime (s₀ + len v) + 2 * P.Δ → frameKey'' A (tr.state y i).fg = v := by
    intro y i hy h1 h2
    have hi0 := hspec _ (hrl.time_nonneg i)
    apply hK y i hy
    · have : s₀ ≤ P.slotOf (tr.time i) := by
        by_contra h
        have := hmono (show P.slotOf (tr.time i) + 1 ≤ s₀ by omega)
        linarith
      exact_mod_cast this
    · have : P.slotOf (tr.time i) ≤ s₀ + len v := by
        by_contra h
        have := hmono (show s₀ + len v + 1 ≤ P.slotOf (tr.time i) by omega)
        linarith
      exact_mod_cast this
  refine ⟨v, hv1, s₀, hs₀, hN, hKt, frameWindow_of_frameKey''_eq_obs_from hrl hP.noColl hf2 hhi ?_⟩
  intro y z i m hy hz hi1 hi2 hm1 hm2
  rw [hKt y i hy hi1 hi2, hKt z m hz hm1 hm2]

private theorem reportDeadline_le_paddedSlot {P : Params}
    (hsl : ∀ s, P.slotTime s + 4 * P.Δ ≤ P.slotTime (s + 1)) (N d : Nat) :
    shiftDelay P d (P.slotTime N + 2 * P.Δ) ≤ P.slotTime (N + (d + 3) / 4) + 2 * P.Δ := by
  have hspan (e : Nat) : P.slotTime N + (4 * (e : Time)) * P.Δ ≤ P.slotTime (N + e) := by
    induction e with
    | zero => simp
    | succ e ih =>
      rw [Nat.add_succ]
      calc
        P.slotTime N + (4 * ((e + 1 : Nat) : Time)) * P.Δ =
            (P.slotTime N + (4 * (e : Time)) * P.Δ) + 4 * P.Δ := by push_cast; ring
        _ ≤ P.slotTime (N + e) + 4 * P.Δ := add_le_add_left ih _
        _ ≤ P.slotTime (N + e + 1) := hsl (N + e)
  have hcast : (d : Time) ≤ 4 * (((d + 3) / 4 : Nat) : Time) := by
    exact_mod_cast (show d ≤ 4 * ((d + 3) / 4) by omega)
  rw [shiftDelay_eq_add]
  linarith only [hspan ((d + 3) / 4), mul_le_mul_of_nonneg_right hcast P.hΔ.le]

/-- The slot-budget reset: within `resetSlots` slots of a slot `s` at or after `ḡ` and `c_z`, a
premised run resets. With no reset by `T = t_{s + resetSlots}`, there is no advance before `T`
(`reset_or_noAdvance`), and the slot-space leaf 3 (`exists_slotWindow_seq`) gives a slot window
`[s₀, N + ⌈d/4⌉]` at a constant key `v = frameKey''`, where `d = O.reportDelay`,
`N = s₀ + W + Gp + r(v)·(δt + Gp - 1)`, `W` is the warmup, and `r(v) = riseRounds HZ v`.
At most four keys occur, so the padded attempts fit in `resetSlots` (budgeted for five). The
proposal gap gives an honest proposal `u` in
`[s₀ + W, s₀ + W + Gp - 1]`, at most `r(v)` rounds below `HZ + 1` (leaf 8). The rise
(`rise_reset_rounds_at_of`) resets by `t_{u + r(v)·(δt + Gp - 1) + 1} + 2Δ + dΔ`,
which is at most `t_N + 2Δ + dΔ ≤ t_{N + ⌈d/4⌉} + 2Δ < T`. -/
theorem exists_reset {hold : Time} (O : ACHealing A sg runs hold) :
    ∀ {cm βK tr H proposer dg g ΔF b Gp s},
      βK ≤ 1 / 2 →
      (∀ u, shiftDelay P O.reportDelay (P.slotTime (u + 1) + 2 * P.Δ) + ΔF ≤
        P.slotTime (u + P.δt)) →
      runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b hold →
      1 ≤ Gp →
      gbar g ≤ P.slotTime s → cutZ P g ≤ P.slotTime s →
      ProposalGap tr H proposer Gp s (s + resetSlots O.warmup Gp P.δt O.reportDelay) →
      P.slotTime (s + resetSlots O.warmup Gp P.δt O.reportDelay) ≤ b →
      ∃ a, IsReset tr H g a ∧ a ≤ P.slotTime (s + resetSlots O.warmup Gp P.δt O.reportDelay) := by
  intro cm βK tr H proposer dg g ΔF b Gp s hβ hsp hrun hP hGp hgs hcs hgp hb
  rcases reset_or_noAdvance hrun hP hb with h | hna
  · exact h
  have hrl := runs.run_local hrun
  have hΔ : (1 : Time) ≤ P.Δ := P.hΔ
  have hmono := P.slotTime_strictMono.monotone
  have hsl := hP.slotLen
  let pad := (O.reportDelay + 3) / 4
  have hS : s + 1 + ∑ j ∈ Finset.range 5,
      (O.warmup + Gp + riseRounds 0 (2 * HZ tr H g + j - 2 * HZ tr H g) * (P.δt + Gp - 1) +
        pad + 2) <
      s + resetSlots O.warmup Gp P.δt O.reportDelay := by
    simp only [resetSlots, windowSlots, riseRounds, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.add_sub_cancel_left, pad]
    omega
  obtain ⟨v, hv, s₀, hs₀, hN, hK, M, isTop, J, hwin⟩ := exists_slotWindow_seq hrun hP hgs hcs
    hb hna (fun v => O.warmup + Gp + riseRounds 0 (v - 2 * HZ tr H g) * (P.δt + Gp - 1) + pad) hS
  have hrr : riseRounds 0 (v - 2 * HZ tr H g) = riseRounds (HZ tr H g) v := by
    simp [riseRounds]
  rw [hrr] at hN hK hwin
  obtain ⟨u, hul, hur, hpu, kB, B, hB, hBs⟩ := hgp (s₀ + O.warmup) (by omega) (by omega)
  set N := s₀ + (O.warmup + Gp + riseRounds (HZ tr H g) v * (P.δt + Gp - 1)) with hNdef
  have hs₀u : s₀ ≤ u := by omega
  have huN : u + riseRounds (HZ tr H g) v * (P.δt + Gp - 1) + 1 ≤ N := by omega
  have hpad := reportDeadline_le_paddedSlot hsl N O.reportDelay
  change _ ≤ P.slotTime (N + pad) + 2 * P.Δ at hpad
  have hNS := hsl (N + pad)
  have hN1 : P.slotTime (N + pad + 1) ≤
      P.slotTime (s + resetSlots O.warmup Gp P.δt O.reportDelay) := hmono (by omega)
  have hmb := hpad.trans (show P.slotTime (N + pad) + 2 * P.Δ ≤ b by linarith)
  have hbase : P.slotTime N + 2 * P.Δ ≤ P.slotTime (N + pad) + 2 * P.Δ := by
    linarith only [hmono (show N ≤ N + pad by omega)]
  rw [← Nat.add_assoc] at hK hwin
  have hwithin : SlotWindowWithin tr H O.reportDelay s₀ N M isTop J :=
    ⟨fun y i hy hlo hhi => hwin.M_eq y i hy hlo (hhi.trans hpad),
      fun y i hy hlo hhi => hwin.top_iff y i hy hlo (hhi.trans hpad),
      fun y i hy hlo hhi => hwin.root_eq y i hy hlo (hhi.trans hpad)⟩
  have hts := hsl s
  have hm : gbar g + 4 * P.Δ ≤ P.slotTime s₀ := by linarith [hmono (show s + 1 ≤ s₀ by omega)]
  have hu0 : 0 ≤ P.slotTime u := by
    have := hmono (Nat.zero_le u)
    rwa [P.slotTime_zero] at this
  have huN' := hmono (show u ≤ N by omega)
  have hwin' : FrameWindow tr H (P.slotTime s₀)
      (P.slotTime s₀ + (P.slotTime N + 2 * P.Δ - P.slotTime s₀)) M isTop J := by
    rw [add_sub_cancel]
    exact ⟨fun y i hy hlo hhi => hwin.M_eq y i hy hlo (hhi.trans hbase),
      fun y i hy hlo hhi => hwin.top_iff y i hy hlo (hhi.trans hbase),
      fun y i hy hlo hhi => hwin.root_eq y i hy hlo (hhi.trans hbase)⟩
  have hrise := rounds_le_warm_proposal_at_of_healing O hrun hP.noColl hwin'
    (fun y i hy h1 h2 => hK y i hy h1 (by linarith)) hv (hmono hs₀u) (by linarith)
    (hrl.antitone (by linarith) hpu) rfl hB hBs
    (P.fg.faults_lt_quorum_margin (hP.faults _ hu0 (by linarith)))
  have hend := shiftDelay_le (P := P) O.reportDelay (add_le_add_left (hmono huN) (2 * P.Δ))
  obtain ⟨a, ha, hat⟩ := rise_reset_rounds_at_of O hβ hP.committee hwithin hrun hP.noColl
    hP.sync hP.awake hP.faults hP.catchUp hP.noRestart hP.slotLen hsp hP.snapshot hm
    (O.follow_le hrun hP) hGp hP.timeoutDelay (fun a h1 h2 => hgp a (by omega) (by omega)) hmb
    hP.nonempty hb hna _ hs₀u hul huN (by linarith) hpu rfl hB hBs hrise
  exact ⟨a, ha, hat.trans (by linarith)⟩

/-- Proposal chaining after the slot-budget reset: `exists_reset` gives the reset `a` by the
budget's end, `highCanonical` the canonical high entries by the horizon, and
`ACHealing.heal_after_reset` chains honest proposals from `slot(a) + drain`. No confirmed-tip
guarantee is asserted. -/
theorem generic_healing {hold : Time} (O : ACHealing A sg runs hold) :
    ∀ {cm βK tr H proposer dg g ΔF b Gp s},
      βK ≤ 1 / 2 →
      (∀ u, shiftDelay P O.reportDelay (P.slotTime (u + 1) + 2 * P.Δ) + ΔF ≤
        P.slotTime (u + P.δt)) →
      runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b hold →
      1 ≤ Gp →
      gbar g ≤ P.slotTime s → cutZ P g ≤ P.slotTime s →
      ProposalGap tr H proposer Gp s (s + resetSlots O.warmup Gp P.δt O.reportDelay) →
      P.slotTime (s + resetSlots O.warmup Gp P.δt O.reportDelay) ≤ b →
      (∀ a, IsReset tr H g a →
        a ≤ P.slotTime (s + resetSlots O.warmup Gp P.δt O.reportDelay) →
        ResetInBudget P O.deepBudget O.drain g a) →
      ∃ a, IsReset tr H g a ∧ a ≤ P.slotTime (s + resetSlots O.warmup Gp P.δt O.reportDelay) ∧
        HealedFrom tr H proposer (P.slotOf a + O.drain) b := by
  intro cm βK tr H proposer dg g ΔF b Gp s hβ hsp hrun hP hGp hgs hcs hgp hb hbudget
  obtain ⟨a, ha, hat⟩ := exists_reset O hβ hsp hrun hP hGp hgs hcs hgp hb
  exact ⟨a, ha, hat, O.heal_after_reset hβ hrun hP ha (hat.trans hb)
    (hbudget a ha hat) (highCanonical O hβ hrun hP ha (hat.trans hb) (hbudget a ha hat))⟩

/-! ## Truncation after the horizon -/

private theorem committeeFaultsUpTo_truncH {βK : ℚ} {cm : Time → Finset (Fin P.n)}
    {H : Time → Set (Fin P.n)} {g b : Time} (hcom : CommitteeFaultsUpTo βK cm H g b) :
    CommitteeFaultsUpTo βK cm (truncH H b) g b :=
  fun t d ht htb hd hdb hne => by rw [truncH_eq_of_le hdb]; exact hcom t d ht htb hd hdb hne

private theorem faults_truncH {H : Time → Set (Fin P.n)} {b : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) :
    ∀ t, 0 ≤ t → t ≤ b → 3 * (truncH H b t)ᶜ.ncard ≤ P.n - 1 :=
  fun t ht htb => by rw [truncH_eq_of_le htb]; exact hf t ht htb

/-- Service is read only at honest cuts, which the truncation projects; relay ancestry over the
truncated honest blocks is ancestry over `H`'s. -/
private theorem service_truncH {tr : RunTrace A} {H : Time → Set (Fin P.n)} {g ΔF b' hold : Time}
    (hs : Service tr H g ΔF b' hold) (b : Time) : Service tr (truncH H b) g ΔF b' hold where
  deltaF := hs.deltaF
  message x i m hx hm y j hy := hs.message x i m hx.1 hm y j hy.1
  block x i B hx hB y j hy := hs.block x i B hx.1 hB y j hy.1
  relay x i B hx hB hg y j hy hj hd hF :=
    hs.relay x i B hx.1 hB hg y j hy.1 hj hd (Anc.mono (honestBlocksAt_truncH_subset b) hF)
  signedRow x i att hx hsg hxh y j hy :=
    hs.signedRow x i att hx.1 hsg (fun k hk hs' ht h0 => (hxh k hk hs' ht h0).1) y j hy.1
  hold_le := hs.hold_le

/-- **The premises on the honest sets truncated after `b`**, with restarts bounded only up to
`b`. Committee faults, faults, service, wakefulness and catch-up read honesty up to `b`, or only
in hypotheses, where the truncation is `H` or a subset of it; a restart honest on the truncation
is at a time `≤ b`, so `NoRestartUpTo` bounds it. The run on the truncation is
`ACRun.run_truncH`. -/
theorem premises_truncH {cm : Time → Finset (Fin P.n)} {βK : ℚ} {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {tr : RunTrace A} {H : Time → Set (Fin P.n)}
    {g ΔF b hold : Time} (hcom : CommitteeFaultsUpTo βK cm H g b) (hnc : Compose.NoCollRun dg tr)
    (hsvc : Service tr H g ΔF b hold) (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) (hcatch : CatchRun tr H g (2 * P.Δ))
    (hnr : NoRestartUpTo A tr H (gbar g) b)
    (htd : ∀ s, P.slotTime s + 6 * P.Δ + ΔF ≤ P.slotTime (s + P.δt))
    (hsl : ∀ s, P.slotTime s + 4 * P.Δ ≤ P.slotTime (s + 1))
    (hsnap : ∃ k, FirstCutAfter tr k (cutZ P g) ∧ tr.time k ≤ b) (hH : (H b).Nonempty) :
    Premises tr (truncH H b) cm βK proposer dg sg g ΔF b hold where
  committee := committeeFaultsUpTo_truncH hcom
  noColl := hnc
  sync := service_truncH hsvc b
  awake y t hy := hawake y t hy.1
  faults := faults_truncH hf
  catchUp := catchRun_truncH hcatch b
  noRestart y k hy hk := hnr y k hy.1 hk hy.2
  timeoutDelay := htd
  slotLen := hsl
  snapshot := hsnap
  nonempty := hH.mono fun _ hy => ⟨hy, le_rfl⟩

/-- The premises at `b` restrict to the honest sets truncated after `b` (`premises_truncH`): every
field reads the truncation where it reads `H` up to `b`, and its restarts are bounded by the
whole-run bound. -/
theorem premises_restrict_truncH {cm : Time → Finset (Fin P.n)} {βK : ℚ}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload} {tr : RunTrace A}
    {H : Time → Set (Fin P.n)} {g ΔF b hold : Time}
    (h : Premises tr H cm βK proposer dg sg g ΔF b hold) :
    Premises tr (truncH H b) cm βK proposer dg sg g ΔF b hold :=
  premises_truncH h.committee h.noColl h.sync h.awake h.faults h.catchUp
    (fun y k hy hk _ => h.noRestart y k hy hk) h.timeoutDelay h.slotLen h.snapshot h.nonempty

end Edges

end Consensus.Goldilocks.Generic

end
