module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Truncation
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingRounds
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
slots, gives a slot window at a constant merged key, and the five attempts fit in `resetSlots`. A
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
theorem reset_or_noAdvance :
    ∀ {cm βK tr H proposer dg g ΔF b T},
      runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b → T ≤ b →
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

/-- Canonical high entries by the horizon of a premised reset, field by field from leaves 13, 12
and 14 over the supplier `O`. -/
theorem highCanonical (O : ACHealing A sg runs) :
    ∀ {cm βK tr H proposer dg g ΔF b a}, βK ≤ 1 / 2 →
      runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b →
      IsReset tr H g a → a ≤ b → HighCanonical O.Origin tr H g b := by
  intro cm βK tr H proposer dg g ΔF b a hβ hrun hP hr hab
  refine ⟨fun _ _ hp hib => no_high_contest_at_of_healing O hβ hrun hP hr hab hp hib,
    fun _ _ _ hy hs hkb hh => ?_, ?_⟩
  · obtain ⟨r, hrk, l, Og, ⟨hyr, hO, hOh⟩, E, hE, hEO, hEr, hEh, hET⟩ :=
      high_row_source_at_of_healing O hβ hrun hP hr hab hy hkb hs hh
    exact ⟨r, hrk, l, Og, hO, hyr, hOh, E, hE, hEO, hEr, hEh, hET⟩
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hx hO hib hBh hx' hO' hi'b hB'h h₁ h₂ ht₁ hle₁ hy₁
      ht₂ hle₂ hy₂ hZ₁ hZ₂ hh hT₁ hT₂
    exact high_entry_eq_at_of_healing O hβ hrun hP hr hab ⟨hx, hO, hBh⟩ hib ⟨hx', hO', hB'h⟩
      hi'b h₁ h₂ ht₁ hle₁ hy₁ ht₂ hle₂ hy₂ hZ₁ hZ₂ hh hT₁ hT₂

/-- The rise contract over the supplier `O`, by induction on the remaining rounds `r`. A warm
proposal at or above `HZ + 1` gives the reset by leaf 10. Otherwise the proposal gap gives an
honest proposal `x` in `[u + δt, u + δt + G - 1]`; leaf 11 puts it one height above the warm
proposal in its proposer's store, which has the warm proposal's replay state
(`proposal_mem_at_from`, `σ_eq_honest_at_from`), and the induction hypothesis applies at `x`.
The spacing gives `δt ≥ 2` with `ΔF > 0`, and every slot time is read from `ProposesAt`. -/
theorem rise_reset_rounds_at_of (O : ACHealing A sg runs) : rise_reset_rounds_at A sg O := by
  intro cm proposer dg H tr βK g ΔF b T s₀ N G floor kindJ J hβ hcom hframe hrun hnc hsvc
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
    obtain ⟨hBp, -, hcross⟩ := round_of_warm_at_of_healing O hβ hcom hframe hrun hnc hsvc hawake
      hf hcatch hnr hsl hsp hsnap hm hs₀u hwarm hfol htd hxl (by omega) hmb hHb hTb hna hstrict
      hz hdes hB hBs hpx0 rfl hX hXs
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

/-- Leaf 3 in slot space, on any schedule with `t_{s+1} ≥ t_s + 4Δ`: the sequential pigeonhole
(`Healing.Growing.exists_const_window_seq`) run over the slots `slot(t_i)` of the cuts of nodes
honest at them, from slot `s + 1` to `S`, with a lag of two slots and window lengths `len v` in
slots. Before `t_S` there is no advance, so the merged key is in `[2HZ, 2HZ + 4]` (leaf 2, both
bounds); two slots apart, a later cut is more than `4Δ` after an earlier one (relay calls,
`frameKey'_lag_obs_from`). A constant slot window `[s₀, s₀ + len v]` covers the time window
`[t_{s₀}, t_{s₀ + len v} + 2Δ]`, which is a `SlotWindow`. -/
private theorem exists_slotWindow_seq {cm βK tr H proposer dg g ΔF b}
    (hrun : runs.Run cm proposer dg H tr) (hP : Premises tr H cm βK proposer dg sg g ΔF b)
    {s S : Nat} (hgs : gbar g ≤ P.slotTime s) (hcs : cutZ P g ≤ P.slotTime s)
    (hSb : P.slotTime S ≤ b) (hna : NoAdvance tr H g (P.slotTime S)) (len : Nat → Nat)
    (hS : s + 1 + ∑ j ∈ Finset.range 5, (len (2 * HZ tr H g + j) + 2) < S) :
    ∃ v, 2 * HZ tr H g ≤ v ∧ ∃ s₀, s + 3 ≤ s₀ ∧ s₀ + len v < S ∧
      (∀ y i, y ∈ H (tr.time i) → P.slotTime s₀ ≤ tr.time i →
        tr.time i ≤ P.slotTime (s₀ + len v) + 2 * P.Δ → frameKey' A (tr.state y i).fg = v) ∧
      ∃ floor kindJ J, SlotWindow tr H s₀ (s₀ + len v) floor kindJ J := by
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
      ∑ j ∈ Finset.range 5, ((len (2 * HZ tr H g + j) : Time) + 2) < (S : Time) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hS ⊢
    exact_mod_cast hS
  obtain ⟨v, hv1, hv2, a, ha, hav, hK⟩ := Healing.Growing.exists_const_window_seq
    (fun y i => y ∈ H (tr.time i)) (fun i => (P.slotOf (tr.time i) : Time))
    (fun y i => Healing.frameKey' (tr.state y i).fg) (2 * HZ tr H g) 4
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
      exact Healing.frameKey'_bounds
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
      exact frameKey'_lag_obs_from hrl hP.noColl hf2 hP.sync hP.catchUp hx hz (by linarith) hkb
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
      ≤ ∑ j ∈ Finset.range 5, ((len (2 * HZ tr H g + j) : Time) + 2) :=
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
      tr.time i ≤ P.slotTime (s₀ + len v) + 2 * P.Δ → Healing.frameKey' (tr.state y i).fg = v := by
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
  refine ⟨v, hv1, s₀, hs₀, hN, fun y i hy h1 h2 => by rw [frameKey'_eq]; exact hKt y i hy h1 h2,
    frameWindow_of_frameKey'_eq_obs_from hrl hP.noColl hf2 hhi ?_⟩
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
`[s₀, N + ⌈d/4⌉]` at a constant merged key `v`, where `d = O.reportDelay`,
`N = s₀ + W + Gp + r(v)·(δt + Gp - 1)`, `W` is the warmup, and `r(v) = riseRounds HZ v`.
The five padded attempts fit in `resetSlots`. The proposal gap gives an honest proposal `u` in
`[s₀ + W, s₀ + W + Gp - 1]`, at most `r(v)` rounds below `HZ + 1` (leaf 8). The rise
(`rise_reset_rounds_at_of`) resets by `t_{u + r(v)·(δt + Gp - 1) + 1} + 2Δ + dΔ`,
which is at most `t_N + 2Δ + dΔ ≤ t_{N + ⌈d/4⌉} + 2Δ < T`. -/
theorem exists_reset (O : ACHealing A sg runs) :
    ∀ {cm βK tr H proposer dg g ΔF b Gp s}, βK ≤ 1 / 2 →
      (∀ u, shiftDelay P O.reportDelay (P.slotTime (u + 1) + 2 * P.Δ) + ΔF ≤
        P.slotTime (u + P.δt)) →
      runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b → 1 ≤ Gp →
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
  obtain ⟨v, hv, s₀, hs₀, hN, hK, floor, kindJ, J, hwin⟩ := exists_slotWindow_seq hrun hP hgs hcs
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
  have hwithin : SlotWindowWithin tr H O.reportDelay s₀ N floor kindJ J :=
    ⟨fun y i hy hlo hhi => hwin.floor_eq y i hy hlo (hhi.trans hpad),
      fun y i hy hlo hhi => hwin.kind_iff y i hy hlo (hhi.trans hpad),
      fun y i hy hlo hhi => hwin.root_eq y i hy hlo (hhi.trans hpad)⟩
  have hts := hsl s
  have hm : gbar g + 4 * P.Δ ≤ P.slotTime s₀ := by linarith [hmono (show s + 1 ≤ s₀ by omega)]
  have hu0 : 0 ≤ P.slotTime u := by
    have := hmono (Nat.zero_le u)
    rwa [P.slotTime_zero] at this
  have huN' := hmono (show u ≤ N by omega)
  have hwin' : FrameWindow tr H (P.slotTime s₀)
      (P.slotTime s₀ + (P.slotTime N + 2 * P.Δ - P.slotTime s₀)) floor kindJ J := by
    rw [add_sub_cancel]
    exact ⟨fun y i hy hlo hhi => hwin.floor_eq y i hy hlo (hhi.trans hbase),
      fun y i hy hlo hhi => hwin.kind_iff y i hy hlo (hhi.trans hbase),
      fun y i hy hlo hhi => hwin.root_eq y i hy hlo (hhi.trans hbase)⟩
  have hrise := rounds_le_warm_proposal_at_of_healing O hrun hP.noColl hwin'
    (fun y i hy h1 h2 => hK y i hy h1 (by linarith)) hv (hmono hs₀u) (by linarith)
    (hrl.antitone (by linarith) hpu) rfl hB hBs
    (P.fg.faults_lt_quorum_margin (hP.faults _ hu0 (by linarith)))
  have hend := shiftDelay_le (P := P) O.reportDelay (add_le_add_left (hmono huN) (2 * P.Δ))
  obtain ⟨a, ha, hat⟩ := rise_reset_rounds_at_of O hβ hP.committee hwithin hrun hP.noColl hP.sync
    hP.awake hP.faults hP.catchUp hP.noRestart hP.slotLen hsp hP.snapshot hm
    (O.follow_le hrun hP) hGp hP.timeoutDelay (fun a h1 h2 => hgp a (by omega) (by omega)) hmb
    hP.nonempty hb hna _ hs₀u hul huN (by linarith) hpu rfl hB hBs hrise
  exact ⟨a, ha, hat.trans (by linarith)⟩

/-- Proposal chaining after the slot-budget reset: `exists_reset` gives the reset `a` by the
budget's end, `highCanonical` the canonical high entries by the horizon, and
`ACHealing.heal_after_reset` chains honest proposals from `slot(a) + drain`. No confirmed-tip
guarantee is asserted. -/
theorem generic_healing (O : ACHealing A sg runs) :
    ∀ {cm βK tr H proposer dg g ΔF b Gp s}, βK ≤ 1 / 2 →
      (∀ u, shiftDelay P O.reportDelay (P.slotTime (u + 1) + 2 * P.Δ) + ΔF ≤
        P.slotTime (u + P.δt)) →
      runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b → 1 ≤ Gp →
      gbar g ≤ P.slotTime s → cutZ P g ≤ P.slotTime s →
      ProposalGap tr H proposer Gp s (s + resetSlots O.warmup Gp P.δt O.reportDelay) →
      P.slotTime (s + resetSlots O.warmup Gp P.δt O.reportDelay) ≤ b →
      ∃ a, IsReset tr H g a ∧ a ≤ P.slotTime (s + resetSlots O.warmup Gp P.δt O.reportDelay) ∧
        HealedFrom tr H proposer (P.slotOf a + O.drain) b := by
  intro cm βK tr H proposer dg g ΔF b Gp s hβ hsp hrun hP hGp hgs hcs hgp hb
  obtain ⟨a, ha, hat⟩ := exists_reset O hβ hsp hrun hP hGp hgs hcs hgp hb
  exact ⟨a, ha, hat, O.heal_after_reset hβ hrun hP ha (hat.trans hb)
    (highCanonical O hβ hrun hP ha (hat.trans hb))⟩

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
private theorem service_truncH {tr : RunTrace A} {H : Time → Set (Fin P.n)} {g ΔF b' : Time}
    (hs : Service tr H g ΔF b') (b : Time) : Service tr (truncH H b) g ΔF b' where
  deltaF := hs.deltaF
  message x i m hx hm y j hy := hs.message x i m hx.1 hm y j hy.1
  block x i B hx hB y j hy := hs.block x i B hx.1 hB y j hy.1
  relay x i B hx hB hg y j hy hj hd hF :=
    hs.relay x i B hx.1 hB hg y j hy.1 hj hd (Anc.mono (honestBlocksAt_truncH_subset b) hF)
  signedRow x i att hx hsg y j hy := hs.signedRow x i att hx.1 hsg y j hy.1

/-- **The premises on the honest sets truncated after `b`**, with restarts bounded only up to
`b`. Committee faults, faults, service, wakefulness and catch-up read honesty up to `b`, or only
in hypotheses, where the truncation is `H` or a subset of it; a restart honest on the truncation
is at a time `≤ b`, so `NoRestartUpTo` bounds it. The run on the truncation is
`ACRun.run_truncH`. -/
theorem premises_truncH {cm : Time → Finset (Fin P.n)} {βK : ℚ} {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {tr : RunTrace A} {H : Time → Set (Fin P.n)}
    {g ΔF b : Time} (hcom : CommitteeFaultsUpTo βK cm H g b) (hnc : Compose.NoCollRun dg tr)
    (hsvc : Service tr H g ΔF b) (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) (hcatch : CatchRun tr H g (2 * P.Δ))
    (hnr : NoRestartUpTo A tr H (gbar g) b)
    (htd : ∀ s, P.slotTime s + 6 * P.Δ + ΔF ≤ P.slotTime (s + P.δt))
    (hsl : ∀ s, P.slotTime s + 4 * P.Δ ≤ P.slotTime (s + 1))
    (hsnap : ∃ k, FirstCutAfter tr k (cutZ P g) ∧ tr.time k ≤ b) (hH : (H b).Nonempty) :
    Premises tr (truncH H b) cm βK proposer dg sg g ΔF b where
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
    {H : Time → Set (Fin P.n)} {g ΔF b : Time}
    (h : Premises tr H cm βK proposer dg sg g ΔF b) :
    Premises tr (truncH H b) cm βK proposer dg sg g ΔF b :=
  premises_truncH h.committee h.noColl h.sync h.awake h.faults h.catchUp
    (fun y k hy hk _ => h.noRestart y k hy hk) h.timeoutDelay h.slotLen h.snapshot h.nonempty

end Edges

end Consensus.Goldilocks.Generic

end
