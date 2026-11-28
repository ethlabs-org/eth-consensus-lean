module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Truncation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.LocalFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingRounds
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameWindowCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.StatementsBundle
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLagCore
import ConsensusLean.Lemmas.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

/-! # Generic healing assembly edges

The assembly edges over any node AC, from the generic healing leaves (`HealingLeaves` and
`HealingRounds`). Every edge is a theorem.

`reset_or_noAdvance` is proved: a high signing before `T` by a signer honest at it and at `c_z`
gives a reset no later (leaf 1, `reset_of_height_advance_at_from`); without one, `NoAdvance` holds
at `T`.

`rise_reset_rounds_within_of` proves the rise under vote latency `D` over any `ACHealing`, by
induction on the remaining rounds: a warm high proposal gives the reset (leaf 10 under latency);
a lower one is crossed by the next honest proposal `δt` to `δt + G - 1` slots later (leaf 11),
which is one round closer. `rise_reset_rounds_at_of`, the rise contract `rise_reset_rounds_at`,
is its latency-`0` case. It runs in the real-time reset `exists_reset_within`.

`premises_truncH` assembles the bundled premises on the honest sets truncated after `b` from the
premises for `H` with restarts bounded only up to `b` (`NoRestartUpTo`). With
`ACRun.run_truncH`, `HZ_truncH` and `isReset_truncH_iff` (`HealingLeaves`) it lets a finite-horizon
consumer apply the bundled leaves on the truncation.

`exists_reset_within`: a premised run whose honest sets are truncated after the horizon `b`
resets by `r + (16 L + 24ρ + 52)Δ + 4(D + GΔ)`, from any real start `r` past `c_z`, under vote
latency `D`, report delay `G = O.reportDelay`, proposal gap `Gp`, drain length `L` with
`W + Gp ≤ L + 1` (`W = O.warmup`) and rise round `ρ = δt + Gp - 1`, on the four-delay slot grid.

Without an advance before the bound there is no high signing (`reset_or_noAdvance`), so honest
`h_max` is in `[HZ, HZ + 1]` from `r + 4Δ` (leaf 2) and the key `frameKey` takes at most four
values. The sequential pigeonhole (`Healing.exists_const_window_seq_of_mem`, lag `2Δ` by the relay
calls) gives a window at a constant key `v` of real length
`len v = 4Δ(L + 2) + r(v)·4Δρ + 2Δ - 1 + D + GΔ`. The first slot `s₀` in the window starts the
proposal gap: a warm proposal `u ≤ s₀ + L` is at most `r(v)` rounds below `HZ + 1` (leaf 8), and
the rise under latency (`rise_reset_rounds_within_of`) resets by
`t_{u + r(v)ρ + 1} + 2Δ + GΔ + D`, which is in the window. The four attempts sum to the bound.
-/

namespace Consensus.Goldilocks.Healing

/-! ## The rise window

The rise round count is the milestone `riseRounds`: from `h_max − 1` a warm proposal needs
`r(v) = 2 − ⌊(v − 2HZ)/2⌋` rounds (`2, 2, 1, 1` on `v = 2HZ + j`). The window length is
`len(v) = d + r(v)·ρ + s` (`riseLen`). The store-level key lag is `Healing.key_le_of_relay`. -/

open Consensus.Goldilocks.Generic (riseRounds)

/-- The window length of key value `v`: the drain `d`, `r(v)` rounds of length `ρ`, slack `s`. -/
def riseLen (d ρ s : Time) (HZ v : Nat) : Time := d + (riseRounds HZ v : Time) * ρ + s

/-- Unfolding equation of `riseLen`. -/
theorem riseLen_eq (d ρ s : Time) (HZ v : Nat) :
    riseLen d ρ s HZ v = d + (riseRounds HZ v : Time) * ρ + s := by
  unfold riseLen
  rfl

theorem riseLen_nonneg {d ρ s : Time} (hd : 0 ≤ d) (hρ : 0 ≤ ρ) (hs : 0 ≤ s) (HZ v : Nat) :
    0 ≤ riseLen d ρ s HZ v := by
  unfold riseLen
  have : (0 : Time) ≤ (riseRounds HZ v : Time) := Nat.cast_nonneg _
  positivity

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Generic

open AC (gbar)
open Healing (cutZ FirstCutAfter riseLen)
open Healing.Growing (HZ IsReset CatchRun)

/-! ## The milestone frame key

The arithmetic of `frameKey` (twice `h_max`, plus one in a top frame), restriction of a
`FrameWindow`, and a frame window from a constant key. -/

section FrameWindowKey

variable {P : Params} {A : NodeAC P}

section Key

variable {a b : Store P A.Payload}

/-- Monotone store heights give a monotone key; at fixed `h_max`, top cannot become gap. -/
theorem frameKey_mono (hm : a.hmax ≤ b.hmax) (hj : a.hj ≤ b.hj) (hb : b.hj < b.hmax) :
    frameKey A a ≤ frameKey A b := by
  classical
  rw [frameKey_eq, frameKey_eq]
  split_ifs <;> omega

/-- The key along an honest node's cuts is monotone. -/
theorem frameKey_monotone {st : Nat → Store P A.Payload}
    (hm : Monotone fun i => (st i).hmax) (hj : Monotone fun i => (st i).hj)
    (hlt : ∀ i, (st i).hj < (st i).hmax) : Monotone fun i => frameKey A (st i) :=
  fun _ _ hij => frameKey_mono (hm hij) (hj hij) (hlt _)

/-- On two consecutive maximum heights, the key takes one of four consecutive values. -/
theorem frameKey_bounds {HZ : Nat} (hlo : HZ ≤ a.hmax) (hhi : a.hmax ≤ HZ + 1) :
    2 * HZ ≤ frameKey A a ∧ frameKey A a ≤ 2 * HZ + 3 := by
  classical
  rw [frameKey_eq]
  split_ifs <;> omega

/-- Equal keys are exactly equal maximum heights and equal top status. -/
theorem frameKey_eq_iff : frameKey A a = frameKey A b ↔
    a.hmax = b.hmax ∧ ((a.hmax = a.hj + 1) ↔ (b.hmax = b.hj + 1)) := by
  classical
  rw [frameKey_eq, frameKey_eq]
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
    frameKey A (tr.state y i).fg = 2 * M + if isTop then 1 else 0 := by
  classical
  rw [frameKey_eq, h.M_eq y i hy hl hh]
  have ht := h.top_iff y i hy hl hh
  rw [h.M_eq y i hy hl hh] at ht
  simp only [ht]

/-- A constant key gives constant `(M, isTop)`; agreement at equal `h_j` supplies `J`. -/
theorem frameData_of_frameKey_eq {α : Type*} (mem : α → Nat → Prop)
    (time : Nat → Time) (st : α → Nat → Store P A.Payload) (dflt : A.Blk)
    {lo hi : Time}
    (hK : ∀ y z i m, mem y i → mem z m → lo ≤ time i → time i ≤ hi → lo ≤ time m →
      time m ≤ hi → frameKey A (st y i) = frameKey A (st z m))
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
      frameKey_eq_iff.mp (hK y y₀ i i₀ hy hy₀ hl hh h₁ h₂)
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

/-- **The rise under vote latency `D`** over the supplier `O`, by induction on the remaining
rounds `r`. A warm proposal at or above `HZ + 1` gives the reset by leaf 10 under latency
(`reset_of_high_proposal_within_of_healing`). Otherwise the proposal gap gives an honest proposal
`x` in `[u + δt, u + δt + G - 1]`; leaf 11 puts it one height above the warm proposal in its
proposer's store, which has the warm proposal's replay state (`proposal_mem_at_from`,
`σ_eq_honest_at_from`), and the induction hypothesis applies at `x`. The spacing gives `δt ≥ 2`
with `ΔF > 0`, and every slot time is read from `ProposesAt`. -/
theorem rise_reset_rounds_within_of {hold : Time} (O : ACHealing A sg runs hold)
    {cm proposer dg H} {tr : RunTrace A} {βK : ℚ} {g ΔF b T D : Time}
    {s₀ N Gp M : Nat} {isTop : Prop} {J : A.Blk}
    (hβ : βK ≤ 1 / 2) (hframe : SlotWindowWithin tr H O.reportDelay s₀ N M isTop J)
    (hrun : runs.Run cm proposer dg H tr) (hP : Premises tr H cm βK proposer dg sg g ΔF b hold)
    (hlat : VoteLatencyAt tr H D) (hD : 0 ≤ D)
    (hsp : ∀ s, shiftDelay P O.reportDelay (P.slotTime (s + 1) + 2 * P.Δ) + ΔF ≤
      P.slotTime (s + P.δt))
    (hm : gbar g + 4 * P.Δ ≤ P.slotTime s₀) (hfol : O.follow ≤ P.δt) (hG : 1 ≤ Gp)
    (hgp : ProposalGap tr H proposer Gp s₀ N)
    (hmb : shiftDelay P O.reportDelay (P.slotTime N + 2 * P.Δ) ≤ b)
    (hTb : T ≤ b) (hna : NoAdvance tr H g T) :
    ∀ (r : Nat) {u : Nat} {z : Fin P.n} {kB : Nat} {B : A.Blk},
      s₀ ≤ u → s₀ + O.warmup ≤ u → u + r * (P.δt + Gp - 1) + 1 ≤ N →
      shiftDelay P O.reportDelay (P.slotTime (u + r * (P.δt + Gp - 1) + 1) + 2 * P.Δ) ≤ T →
      shiftDelay P O.reportDelay (P.slotTime (u + r * (P.δt + Gp - 1) + 1) + 2 * P.Δ) + D ≤ b →
      z ∈ H (P.slotTime u + P.Δ) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
      HZ tr H g + 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h + r →
      ∃ a, IsReset tr H g a ∧
        a ≤ shiftDelay P O.reportDelay (P.slotTime (u + r * (P.δt + Gp - 1) + 1) + 2 * P.Δ) +
          D := by
  intro r
  have hrl := runs.run_local hrun
  have hnc := hP.noColl
  have hΔ := P.hΔ
  have hdF := hP.sync.deltaF
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
    intro u z kB B hs₀u hwarm hN hT hTD hz hdes hB hBs hrise
    simpa only [Nat.zero_mul, Nat.add_zero] using
      reset_of_high_proposal_within_of_healing O hβ hframe hrun hP hlat hD hm hwarm
        (by simpa using hN) hmb (by simpa using hTD) hz hdes hB hBs (by simpa using hrise)
  | succ r ih =>
    intro u z kB B hs₀u hwarm hN hT hTD hz hdes hB hBs hrise
    have hmul : (r + 1) * (P.δt + Gp - 1) = r * (P.δt + Gp - 1) + (P.δt + Gp - 1) :=
      Nat.succ_mul r _
    have hu1 : shiftDelay P O.reportDelay (P.slotTime (u + 1) + 2 * P.Δ) ≤
        shiftDelay P O.reportDelay
          (P.slotTime (u + (r + 1) * (P.δt + Gp - 1) + 1) + 2 * P.Δ) := by
      apply shiftDelay_le
      linarith [hmono (show u + 1 ≤ u + (r + 1) * (P.δt + Gp - 1) + 1 by omega)]
    by_cases hh : HZ tr H g + 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h
    · obtain ⟨a, ha, hat⟩ := reset_of_high_proposal_within_of_healing O hβ hframe hrun hP hlat
        hD hm hwarm (by omega) hmb (by linarith) hz hdes hB hBs hh
      exact ⟨a, ha, by linarith⟩
    obtain ⟨x, hxl, hxr, hpx, kX, X, hX, hXs⟩ := hgp (u + P.δt) (by omega) (by omega)
    have htX : tr.time kX = P.slotTime x := by rw [hX.2.2, hXs]
    have hpx0 : proposer x ∈ H (tr.time kX) := hrl.antitone (by rw [htX]; linarith) hpx
    have hstrict : shiftDelay P O.reportDelay (P.slotTime (u + 1) + 2 * P.Δ) < T := by
      have := P.slotTime_strictMono (show u + 1 < u + (r + 1) * (P.δt + Gp - 1) + 1 by omega)
      rw [shiftDelay_eq_add] at hT ⊢
      linarith
    obtain ⟨hBp, -, hcross⟩ := round_of_warm_at_of_healing O hβ hP.committee hframe hrun hnc
      hP.sync hP.awake hP.faults hP.catchUp hP.noRestart hP.slotLen hsp hP.snapshot hm hs₀u
      hwarm hfol hP.timeoutDelay hxl (by omega) hmb hP.nonempty hTb hna
      hstrict hz hdes hB hBs hpx0 rfl hX hXs
    have htB : tr.time kB = P.slotTime u := by rw [hB.2.2, hBs]
    have hz0 : z ∈ H (tr.time kB) := hrl.antitone (by rw [htB]; linarith) hz
    have hBm := proposal_mem_at_from hrl (runs.run_requirements hrun) (runs.run_root hrun) hnc
      hz0 hB
    have hσ := σ_eq_honest_at_from hrl hnc (hrl.time_nonneg kB)
      (fun q hq => hrl.time_mono (by omega)) hz0 (hrl.time_nonneg kX)
      (fun q hq => hrl.time_mono (by omega)) hpx0 hBm hBp
    rw [← hσ] at hcross
    have hnext : x + r * (P.δt + Gp - 1) + 1 ≤ u + (r + 1) * (P.δt + Gp - 1) + 1 := by omega
    have hsx : shiftDelay P O.reportDelay
          (P.slotTime (x + r * (P.δt + Gp - 1) + 1) + 2 * P.Δ) ≤
        shiftDelay P O.reportDelay
          (P.slotTime (u + (r + 1) * (P.δt + Gp - 1) + 1) + 2 * P.Δ) :=
      shiftDelay_le _ (by linarith [hmono hnext])
    obtain ⟨a, ha, hat⟩ := ih (u := x) (by omega) (by omega) (hnext.trans hN)
      (hsx.trans hT) (by linarith) hpx rfl hX hXs (by omega)
    exact ⟨a, ha, by linarith⟩

/-- The rise contract over the supplier `O`: the latency-`0` case of
`rise_reset_rounds_within_of` (`voteLatency_zero_from`). -/
theorem rise_reset_rounds_at_of {hold : Time} (O : ACHealing A sg runs hold) :
    rise_reset_rounds_at A sg O := by
  intro cm proposer dg H tr βK g ΔF b T s₀ N G M isTop J hβ hcom hframe hrun hnc hsvc
    hawake hf hcatch hnr hsl hsp hsnap hm hfol hG htd hgp hmb hHb hTb hna r u z kB B hs₀u hwarm
    hN hT hz hdes hB hBs hrise
  simpa only [add_zero] using rise_reset_rounds_within_of O hβ hframe hrun
    ⟨hcom, hnc, hsvc, hawake, hf, hcatch, hnr, htd, hsl, hsnap, hHb⟩
    (voteLatency_zero_from (runs.run_local hrun)) le_rfl hsp hm hfol hG hgp hmb hTb hna r
    hs₀u hwarm hN hT (by rw [add_zero]; exact hT.trans hTb) hz hdes hB hBs hrise

/-- **The milestone key lag** between independently honest observations, after a call of `z` at or
after the relay deadline of `i` (`Healing.key_le_of_relay` at the two observations). -/
theorem frameKey_lag_obs_from {proposer : Nat → Fin P.n}
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
    frameKey A (tr.state x i).fg ≤ frameKey A (tr.state z m).fg := by
  have hi0 := h.time_nonneg i
  have hm0 := h.time_nonneg m
  have hxle : ∀ k < i, tr.time k ≤ tr.time i := fun k hk => h.time_mono hk.le
  have hzle : ∀ k < m, tr.time k ≤ tr.time m := fun k hk => h.time_mono hk.le
  have hfmi : (H (max (tr.time i) (tr.time m)))ᶜ.ncard < 2 * P.fg.q - P.n := by
    rw [max_eq_right him]; exact hf _ hm0 hmb
  rw [frameKey_eq, frameKey_eq]
  exact Healing.key_le_of_relay (h.reachable_at hi0 hxle hx)
    (h.reachable_at hm0 hzle hz) (Compose.Growing.honest_blocks_coherent_local h hnc)
    (fun _ hX => ⟨x, i, tr.time i, hi0, hxle, hx, hX⟩)
    (fun _ hX => ⟨z, m, tr.time m, hm0, hzle, hz, hX⟩) (hf _ hm0 hmb)
    (held_atts_safe_at_from h hm0 hzle hz hi0 hxle hx le_rfl him)
    (fun _ _ hBC hC => h.held_anc_at hnc hm0 hzle hz hBC hC)
    (fun _ hB hh => held_of_relay_le_at_from h hnc hsvc hcatch hi0 hx hz hfmi hB hh hxle hcall
      hcm)

/-- A milestone key that is constant over the cuts of `[lo, hi]` of nodes honest at them gives a
`FrameWindow`, when `hi ≤ b`: `J` from agreement at equal `h_j`. -/
theorem frameWindow_of_frameKey_eq_obs_from {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
    {tr : RunTrace A} {ini : Fin P.n → A.State}
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {b : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * P.fg.q - P.n)
    {lo hi : Time} (hhi : hi ≤ b)
    (hK : ∀ y z i m, y ∈ H (tr.time i) → z ∈ H (tr.time m) → lo ≤ tr.time i →
      tr.time i ≤ hi → lo ≤ tr.time m → tr.time m ≤ hi →
      frameKey A (tr.state y i).fg = frameKey A (tr.state z m).fg) :
    ∃ M isTop J, FrameWindow tr H lo hi M isTop J := by
  have hle : ∀ i k, k < i → tr.time k ≤ tr.time i := fun _ _ hk => h.time_mono hk.le
  obtain ⟨M, isTop, J, h1, h2, h3⟩ := frameData_of_frameKey_eq
    (fun y i => y ∈ H (tr.time i)) tr.time (fun y i => (tr.state y i).fg)
    (P.genesisBlock A.genesisPayload) hK
    (fun y z i m hy hz _ hi _ hm he =>
      Healing.Store.J_eq_of_cache_hj_eq_of_safe
        (h.reachable_at (h.time_nonneg i) (hle i) hy)
        (h.reachable_at (h.time_nonneg m) (hle m) hz)
        (Compose.Growing.honest_blocks_coherent_local h hnc)
        (fun _ hX => ⟨y, i, tr.time i, h.time_nonneg i, hle i, hy, hX⟩)
        (fun _ hX => ⟨z, m, tr.time m, h.time_nonneg m, hle m, hz, hX⟩)
        (hf _ ((h.time_nonneg i).trans (le_max_left _ _)) (max_le (hi.trans hhi) (hm.trans hhi)))
        (held_atts_safe_at_from h (h.time_nonneg i) (hle i) hy (h.time_nonneg m) (hle m) hz
          (le_max_left _ _) (le_max_right _ _))
        he)
  exact ⟨M, isTop, J, ⟨h1, h2, h3⟩⟩

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

/-- Vote latency on the honest sets truncated after `b`: the signing source extends the report
in the reporter's store, hence over the truncated honest blocks. -/
private theorem voteLatency_truncH {hold : Time} (O : ACHealing A sg runs hold)
    {cm proposer dg H tr} (hrun : runs.Run cm proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {D : Time} (hlat : VoteLatencyAt tr H D) (b : Time) : VoteLatencyAt tr (truncH H b) D := by
  have hrl := runs.run_local hrun
  refine ⟨fun y i R hR hy => ?_⟩
  obtain ⟨k, hik, hk, C, s, hc, hh, hRC, j, hij, hjk, hC⟩ := hlat.attests y i R hR hy.1
  have htj := (hrl.time_mono hjk).trans hk
  have hyj := hrl.antitone htj hy.1
  have hle : ∀ q < j, tr.time q ≤ tr.time j := fun q hq => hrl.time_mono hq.le
  have hj0 := hrl.time_nonneg j
  have hanc := hrl.held_anc_at hnc hj0 hle hyj hRC
    (O.report_in_frame hrun hyj hC).1
  exact ⟨k, hik, hk, C, s, hc, hh,
    honest_anc_of_store_anc_at_from (H := truncH H b) hj0 hle ⟨hyj, htj.trans hy.2⟩ hanc,
    j, hij, hjk, hC⟩

/-- **The real-time reset** over the supplier `O`, on the honest sets truncated after the horizon
`b` (`premises_truncH` supplies the premises from restarts bounded up to `b`). -/
theorem exists_reset_within {hold : Time} (O : ACHealing A sg runs hold)
    {cm proposer dg H tr} {βK : ℚ} {g ΔF b r D : Time} {Gp L : Nat}
    (hβ : βK ≤ 1 / 2) (hgrid : ∀ s : Nat, P.slotTime s = (s : Time) * (4 * P.Δ))
    (hrun : runs.Run cm proposer dg H tr)
    (hP : Premises tr (truncH H b) cm βK proposer dg sg g ΔF b hold)
    (hlat : VoteLatencyAt tr H D) (hD : 0 ≤ D)
    (hΔF : 6 * P.Δ + (D + (O.reportDelay : Time) * P.Δ) + ΔF ≤ 4 * P.Δ * (P.δt : Time))
    (hG : 1 ≤ Gp) (hL : O.warmup + Gp ≤ L + 1)
    (hgr : gbar g ≤ r) (hcz : cutZ P g + P.Δ + 1 ≤ r + 4 * P.Δ)
    (hgp : ∀ s₀ N : Nat, r + 4 * P.Δ ≤ P.slotTime s₀ →
      P.slotTime N + 2 * P.Δ < r + (16 * (L : Time) + 24 * ((P.δt + Gp - 1 : Nat) : Time) + 52) *
        P.Δ + 4 * (D + (O.reportDelay : Time) * P.Δ) →
      ProposalGap tr H proposer Gp s₀ N)
    (hb : r + (16 * (L : Time) + 24 * ((P.δt + Gp - 1 : Nat) : Time) + 52) * P.Δ +
      4 * (D + (O.reportDelay : Time) * P.Δ) ≤ b) :
    ∃ a, IsReset tr H g a ∧
      a ≤ r + (16 * (L : Time) + 24 * ((P.δt + Gp - 1 : Nat) : Time) + 52) * P.Δ +
        4 * (D + (O.reportDelay : Time) * P.Δ) := by
  classical
  set B := r + (16 * (L : Time) + 24 * ((P.δt + Gp - 1 : Nat) : Time) + 52) * P.Δ +
    4 * (D + (O.reportDelay : Time) * P.Δ) with hBdef
  set H' := truncH H b
  have hrun' := runs.run_truncH hrun b
  have hrl := runs.run_local hrun'
  have hnc := hP.noColl
  have hlat' := voteLatency_truncH O hrun hnc hlat b
  have hΔ : (1 : Time) ≤ P.Δ := P.hΔ
  have hGΔ : (0 : Time) ≤ (O.reportDelay : Time) * P.Δ := by positivity
  set ρ : Nat := P.δt + Gp - 1 with hρ
  have hρ0 : (0 : Time) ≤ (ρ : Time) := Nat.cast_nonneg _
  have hL0 : (0 : Time) ≤ (L : Time) := Nat.cast_nonneg _
  let lo := r + 4 * P.Δ
  have hczlo : cutZ P g ≤ lo := by linarith
  have hB4 : lo + 48 * P.Δ ≤ B := by
    have h1 : (0 : Time) ≤ (L : Time) * P.Δ := by positivity
    have h2 : (0 : Time) ≤ (ρ : Time) * P.Δ := by positivity
    rw [hBdef]
    nlinarith
  have hczb : cutZ P g ≤ b := by linarith
  have hf2 : ∀ t, 0 ≤ t → t ≤ b → (H' t)ᶜ.ncard < 2 * P.fg.q - P.n := fun t h0 htb =>
    P.fg.faults_lt_quorum_margin (hP.faults t h0 htb)
  -- without an advance before `B` there is no high signing
  rcases reset_or_noAdvance hrun' hP hb with ⟨a, ha, hab⟩ | hna
  · exact ⟨a, (isReset_truncH_iff hczb (hab.trans hb)).mp ha, hab⟩
  -- the pigeonhole over the key, four attempts of length `len`
  let slack := 2 * P.Δ - 1 + (D + (O.reportDelay : Time) * P.Δ)
  let len : Nat → Time := fun v =>
    riseLen (4 * P.Δ * ((L : Time) + 2)) (4 * P.Δ * (ρ : Time)) slack (HZ tr H' g) v
  have hlen : ∀ v, 0 ≤ len v := fun v =>
    Healing.riseLen_nonneg (by positivity) (by positivity) (by dsimp [slack]; linarith) _ v
  have hsum : lo + ∑ j ∈ Finset.range 4, (len (2 * HZ tr H' g + j) + 2 * P.Δ) = B - 4 := by
    simp only [len, Finset.sum_range_succ, Finset.sum_range_zero, Healing.riseLen_eq, riseRounds,
      Nat.add_sub_cancel_left]
    norm_num
    dsimp [lo, slack]
    rw [hBdef]
    ring
  obtain ⟨v, hv, hv3, a, ha, hav, hK⟩ := Healing.exists_const_window_seq_of_mem
    (fun y i => y ∈ H' (tr.time i)) tr.time (fun y i => frameKey A (tr.state y i).fg)
    (2 * HZ tr H' g) 3 len hlen (show (0 : Time) ≤ 2 * P.Δ by linarith) (lo := lo) (T := B)
    (fun y i hy hi hiB => by
      have hib : tr.time i ≤ b := hiB.le.trans hb
      have hczi : cutZ P g ≤ tr.time i := hczlo.trans hi
      have hmx : max (cutZ P g) (tr.time i) = tr.time i := max_eq_right hczi
      obtain ⟨hsnap, hcall⟩ := snapshotCall_of_awake_at_from hrl hP.awake hy (by linarith) hib
      exact frameKey_bounds
        (HZ_le_hmax_at_from hrl hnc hP.sync hP.catchUp
          (hP.nonempty.mono (hrl.antitone hczb)) hsnap hy
          (by rw [hmx]; exact hf2 _ (hrl.time_nonneg i) hib) hcall (by linarith))
        (hmax_le_of_noAdvance_at_from hrl hna hy
          (by rw [hmx]; exact faults_lt_q hP.faults (hrl.time_nonneg i) hib) hiB))
    (fun x z i k hx hz hi _ hik hk => by
      have hkb : tr.time k ≤ b := hk.le.trans hb
      exact frameKey_lag_obs_from hrl hnc hf2 hP.sync hP.catchUp hx hz (by linarith) hkb
        (callLag_of_awake_at_from hrl hP.awake hczlo hz hi hik hkb) (by linarith))
    (by rw [hsum]; linarith)
  have hpart : ∑ j ∈ Finset.range (v - 2 * HZ tr H' g + 1), (len (2 * HZ tr H' g + j) + 2 * P.Δ)
      ≤ ∑ j ∈ Finset.range 4, (len (2 * HZ tr H' g + j) + 2 * P.Δ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun j _ _ => add_nonneg (hlen _) (by linarith))
  have hend : a + len v ≤ B - 4 := by linarith
  obtain ⟨M, isTop, J, hwin⟩ := frameWindow_of_frameKey_eq_obs_from hrl hnc hf2
    (show a + len v ≤ b by linarith) (fun y z i m hy hz hi₁ hi₂ hm₁ hm₂ => by
      rw [hK y i hy hi₁ hi₂, hK z m hz hm₁ hm₂])
  -- the first slot in the window starts the proposal gap
  obtain ⟨s₀, hslo, hshi⟩ := exists_slot_align_of_grid (P := P) hgrid a (by
    have : (0 : Time) ≤ lo := by
      have : (0 : Time) ≤ gbar g := le_max_right _ _
      linarith
    linarith)
  have halign := Int.le_sub_one_of_lt hshi
  set rr := riseRounds (HZ tr H' g) v
  set N := s₀ + L + rr * ρ + 1 with hNdef
  have hNt : P.slotTime N + 2 * P.Δ + (D + (O.reportDelay : Time) * P.Δ) ≤ a + len v := by
    have hlv : len v = 4 * P.Δ * ((L : Time) + 2) + (rr : Time) * (4 * P.Δ * (ρ : Time)) +
        slack := Healing.riseLen_eq _ _ _ _ _
    rw [hlv, hgrid N, hNdef]
    dsimp [slack]
    nlinarith only [halign]
  have hmono := P.slotTime_strictMono.monotone
  have hmb : shiftDelay P O.reportDelay (P.slotTime N + 2 * P.Δ) ≤ b := by
    rw [shiftDelay_eq_add]; linarith
  have hgpN : ProposalGap tr H' proposer Gp s₀ N := by
    intro c hc hcN
    obtain ⟨x, hxl, hxr, hx, hQ⟩ := hgp s₀ N (by linarith) (by linarith) c hc hcN
    have hxN : P.slotTime x + P.Δ ≤ P.slotTime N + 2 * P.Δ := by
      linarith [hmono (show x ≤ N by omega)]
    exact ⟨x, hxl, hxr, ⟨hx, by linarith⟩, hQ⟩
  obtain ⟨u, hul, hur, hpu, kB, Bk, hB, hBs⟩ := hgpN (s₀ + O.warmup) (by omega) (by omega)
  have huN : u + rr * ρ + 1 ≤ N := by omega
  have hts₀ : P.slotTime s₀ ≤ P.slotTime u := hmono (by omega)
  have htuN : P.slotTime u ≤ P.slotTime N := hmono (by omega)
  have hu0 : (0 : Time) ≤ P.slotTime u := by rw [hgrid]; positivity
  have hrise := rounds_le_warm_proposal_at_of_healing O hrun' hnc hwin
    (fun y i hy h1 h2 => hK y i hy h1 h2) hv (hslo.trans hts₀) (by linarith)
    (hrl.antitone (by linarith) hpu) rfl hB hBs
    (hf2 _ hu0 (by linarith))
  -- the rise under latency
  have hsp : ∀ s, shiftDelay P O.reportDelay (P.slotTime (s + 1) + 2 * P.Δ) + ΔF ≤
      P.slotTime (s + P.δt) := by
    intro s
    rw [shiftDelay_eq_add, hgrid, hgrid]
    have e1 : ((s + 1 : Nat) : Time) * (4 * P.Δ) = (s : Time) * (4 * P.Δ) + 4 * P.Δ := by
      push_cast; ring
    have e2 : ((s + P.δt : Nat) : Time) * (4 * P.Δ) =
        (s : Time) * (4 * P.Δ) + 4 * P.Δ * (P.δt : Time) := by
      push_cast; ring
    rw [e1, e2]
    linarith
  have hend' : shiftDelay P O.reportDelay
      (P.slotTime (u + rr * (P.δt + Gp - 1) + 1) + 2 * P.Δ) ≤
      P.slotTime N + 2 * P.Δ + (O.reportDelay : Time) * P.Δ := by
    rw [shiftDelay_eq_add]
    linarith [hmono huN]
  obtain ⟨a', ha', hat⟩ := rise_reset_rounds_within_of O hβ
    (hwin.mono hslo (by rw [shiftDelay_eq_add]; linarith)) hrun' hP hlat' hD hsp
    (by linarith) (O.follow_le hrun' hP) hG hgpN hmb hb hna rr (by omega) hul huN
    (by linarith) (by linarith) hpu rfl hB hBs hrise
  have hab : a' ≤ B := by linarith
  exact ⟨a', (isReset_truncH_iff hczb (hab.trans hb)).mp ha', hab⟩

end Edges

end Consensus.Goldilocks.Generic

end
