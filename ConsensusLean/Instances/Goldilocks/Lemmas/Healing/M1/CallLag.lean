module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLag
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.StatementsBundle
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The call-lag premises from public ticks (`λ = 2Δ`)

The premises `hcallZ`, `hcall` and `hsnap` of the frame-window lemmas (`Healing.M1`), produced
from wakefulness on `[ḡ, b]` alone, for any node AC (`Node.LocalRun` from any starts `ini`) and
any slot schedule: the reset cut `c_z = t_{slot(ḡ)+3}` is a slot start, so it is public and
later than `t_{slot(ḡ)+1} > ḡ` (`slotOf_spec`).

* `exists_call_of_public`: an awake honest node ticks at every public time of `[ḡ, b]`, and the
  first cut of the tick is a call at that time.
* `call_before_of_public`: from `c_z` on, a call at a public `q ≥ τ + Δ` meets the relay deadline
  of `τ`: the node's restarts up to `b` are at or before `t_{slot(ḡ)+1} ≤ c_z`.
* `callLag_of_awake` (`hcall`, `λ = 2Δ`): `q = Δ·⌈(τ + Δ)/Δ⌉ < τ + 2Δ ≤ time m`, so the call is
  at a cut `j < m`, also when `time m = τ + 2Δ`. A unit wait is not available: an engine tick
  at a non-public time has no cut.
* `snapshotCall_of_awake` (`hcallZ`): the call at the public `c_z + Δ`, before every cut
  at or after `lo ≥ c_z + Δ + 1`.
* `snapshot_of_awake` (`hsnap`).

Only the NoAdvance premise of the frame-window route stays: it holds for `T ≤ a_z`
and fails after the reset, so this file gives no range after the reset. -/

namespace Consensus.Goldilocks.Healing

open AC (gbar)

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n}
  {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- `ḡ < t_{slot(ḡ)+1} ≤ c_z`: the slot after `ḡ`'s starts after `ḡ`, and not after `c_z`. -/
private theorem gbar_lt_slot_succ_le_cutZ (g : Time) :
    gbar g < P.slotTime (P.slotOf (gbar g) + 1) ∧
      P.slotTime (P.slotOf (gbar g) + 1) ≤ cutZ P g :=
  ⟨((slotOfSpec_iff.mp slotOf_spec) P (gbar g) (gbar_nonneg g)).2,
    P.slotTime_strictMono.monotone (by omega)⟩

/-- An honest node awake at a public time `q ∈ [ḡ, b]` has a call at a cut of time `q`. -/
private theorem exists_call_of_public (hrun : Node.LocalRun proposer dg H sg tr ini) {g b : Time}
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    {z : Fin P.n} (hz : z ∈ H) {q : Time} (hq : P.IsPublic q)
    (hgq : gbar g ≤ q) (hqb : q ≤ b) :
    ∃ j, tr.IsCall z j ∧ tr.time j = q := by
  obtain ⟨j, _, fgDue, hne, hcs, -⟩ :=
    hrun.tick_of_awake z hz q ((gbar_nonneg g).trans hgq) hq (hawake z hz q hgq hqb)
  obtain ⟨hn, ht, -, -, hl⟩ := hcs 0 (List.length_pos_of_ne_nil hne)
  simp only [Nat.add_zero] at hn ht hl
  exact ⟨j, ⟨_, hn, hl⟩, ht⟩

/-- An honest restart up to `b` is at or before `t_{slot(ḡ)+1}` (`restart_le_before` from
wakefulness alone): the node was asleep at some `u` with no call in `[u, restart)`; `u ≥ ḡ`
contradicts wakefulness, and `u < ḡ` the call of the tick at `t_{slot(ḡ)+1}`. -/
private theorem restart_le_of_awake (hrun : Node.LocalRun proposer dg H sg tr ini) {g b : Time}
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    {y : Fin P.n} (hy : y ∈ H) {k : Nat} (hk : tr.RestartAt y k) (hkb : tr.time k ≤ b) :
    tr.time k ≤ P.slotTime (P.slotOf (gbar g) + 1) := by
  by_contra hlt
  obtain ⟨u, -, huk, hu, hprev⟩ := hrun.sleep_of_restart y hy k hk
  have hp₀ := (gbar_lt_slot_succ_le_cutZ (P := P) g).1.le
  by_cases hgu : gbar g ≤ u
  · exact hu (hawake y hy u hgu (huk.le.trans hkb))
  · obtain ⟨j, hj, ht⟩ := exists_call_of_public hrun hawake hy (P.slotTime_public _) hp₀
      ((lt_of_not_ge hlt).le.trans hkb)
    have hjk : j < k := by
      by_contra h
      exact hlt (ht ▸ hrun.time_mono (not_lt.mp h))
    have := hprev j hjk hj
    exact hgu (by linarith)

/-- `c_z + Δ` is public. -/
private theorem cutZ_add_public (g : Time) : P.IsPublic (cutZ P g + P.Δ) :=
  dvd_add (P.slotTime_public _) (dvd_refl _)

/-- **The call for a relay deadline.** From `c_z` on, the call of `z` at a public time
`q ∈ [τ + Δ, b]` is at a cut before every cut `m` later than `q`, and meets the deadline of `τ`. -/
private theorem call_before_of_public (hrun : Node.LocalRun proposer dg H sg tr ini) {g b : Time}
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    {z : Fin P.n} (hz : z ∈ H) {τ q : Time} (hτ : cutZ P g ≤ τ)
    (hq : P.IsPublic q) (hτq : τ + P.Δ ≤ q) (hqb : q ≤ b)
    {m : Nat} (hqm : q < tr.time m) :
    ∃ j < m, tr.IsCall z j ∧ tr.deadline z j τ P.Δ ≤ tr.time j := by
  have hΔ := P.hΔ
  obtain ⟨hg, hr⟩ := gbar_lt_slot_succ_le_cutZ (P := P) g
  obtain ⟨j, hj, hjt⟩ := exists_call_of_public hrun hawake hz hq (by linarith) hqb
  refine ⟨j, ?_, hj, ?_⟩
  · by_contra h
    have := hrun.time_mono (not_lt.mp h)
    linarith
  · have := Compose.deadline_le_of_restarts (tr := tr) (y := z) (c := j)
      (fun k hk hrk => restart_le_of_awake hrun hawake hz hrk
        ((hrun.time_mono hk).trans (hjt ▸ hqb))) τ P.Δ
    rw [max_eq_left (hr.trans hτ)] at this
    linarith

/-- **`hcall` with `λ = 2Δ`.** From `lo ≥ c_z` and before `T ≤ b + 1`, every honest node has a
call before `m` at or after the relay deadline of every cut `i` with `time i + 2Δ ≤ time m`. -/
theorem callLag_of_awake (hrun : Node.LocalRun proposer dg H sg tr ini) {g b : Time}
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    {lo T : Time} (hlo : cutZ P g ≤ lo) (hT : T ≤ b + 1) :
    ∀ z ∈ H, ∀ i m, lo ≤ tr.time i → tr.time i + 2 * P.Δ ≤ tr.time m → tr.time m < T →
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) P.Δ ≤ tr.time j := by
  intro z hz i m hi him hmT
  have hΔ : 0 < P.Δ := P.hΔ
  have hcz := (gbar_lt_slot_succ_le_cutZ (P := P) g)
  have hg := le_gbar g
  rw [max_eq_left (by linarith)]
  -- `q = Δ·⌈(τ + Δ)/Δ⌉`, the first public time at or after `τ + Δ`
  set r := (tr.time i + 2 * P.Δ - 1) / P.Δ with hr
  have h₁ : P.Δ * r ≤ tr.time i + 2 * P.Δ - 1 := Int.mul_ediv_self_le hΔ.ne'
  have h₂ : tr.time i + 2 * P.Δ - 1 < P.Δ * r + P.Δ := by
    have := Int.lt_ediv_add_one_mul_self (tr.time i + 2 * P.Δ - 1) hΔ
    rw [← hr] at this
    linarith [add_one_mul r P.Δ, mul_comm r P.Δ]
  exact call_before_of_public hrun hawake hz (q := P.Δ * r) (hlo.trans hi) (dvd_mul_right _ _)
    (by linarith [Int.add_one_le_iff.mpr h₂]) (by linarith) (by linarith)

/-- **`hcallZ`.** From `lo ≥ c_z + Δ + 1` and before `T ≤ b + 1`, every honest node has a call
before `m` at or after the relay deadline of `c_z` (the call at `c_z + Δ`). -/
theorem snapshotCall_of_awake (hrun : Node.LocalRun proposer dg H sg tr ini) {g b : Time}
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    {lo T : Time} (hlo : cutZ P g + P.Δ + 1 ≤ lo) (hT : T ≤ b + 1) :
    ∀ z ∈ H, ∀ m, lo ≤ tr.time m → tr.time m < T → ∃ j < m, tr.IsCall z j ∧
      tr.deadline z j (max (cutZ P g) g) P.Δ ≤ tr.time j := by
  intro z hz m hm hmT
  have hcz := (gbar_lt_slot_succ_le_cutZ (P := P) g)
  rw [max_eq_left (by linarith [le_gbar g])]
  exact call_before_of_public hrun hawake hz le_rfl (cutZ_add_public g) le_rfl (by linarith)
    (by linarith)

/-- **`hsnap`.** With an honest node awake at `c_z + Δ ≤ b`, a cut follows `c_z` by `b`
(from `H.Nonempty`, not the fault bound). -/
theorem snapshot_of_awake (hrun : Node.LocalRun proposer dg H sg tr ini) {g b : Time}
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t) (hH : H.Nonempty)
    (hb : cutZ P g + P.Δ ≤ b) :
    ∃ j, FirstCutAfter tr j (cutZ P g) ∧ tr.time j ≤ b := by
  classical
  obtain ⟨y, hy⟩ := hH
  have hΔ : 0 < P.Δ := P.hΔ
  have hcz := (gbar_lt_slot_succ_le_cutZ (P := P) g)
  obtain ⟨j, -, hjt⟩ := exists_call_of_public hrun hawake hy (cutZ_add_public g)
    (by linarith) hb
  have hj : cutZ P g < tr.time j := by linarith
  have hex : ∃ k, cutZ P g < tr.time k := ⟨j, hj⟩
  exact ⟨Nat.find hex, ⟨fun k hk => not_lt.1 (Nat.find_min hex hk), Nat.find_spec hex⟩,
    (hrun.time_mono (Nat.find_min' hex hj)).trans (hjt ▸ hb)⟩

end Consensus.Goldilocks.Healing

end
