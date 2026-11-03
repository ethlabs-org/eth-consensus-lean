module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Range
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame

public section

/-! # M1′: the call-lag premises from public ticks (`λ = 2Δ`)

The premises `hcallZ`, `hcall` and `hsnap` of `exists_frameWindow_of_noAdvance` (and `hcall` of
`exists_frameWindow_of_service`), produced from wakefulness on `[ḡ, b]` alone.

* `exists_call_of_public`: an awake honest node ticks at every public time of `[ḡ, b]`, and the
  first cut of the tick is a call at that time.
* `call_before_of_public`: from `c_z` on, a call at a public `q ≥ τ + Δ` meets the relay deadline
  of `τ`: the node's restarts up to `b` are at or before `t_{slot(ḡ)+1} ≤ c_z`.
* `callLag_of_awake` (`hcall`, `λ = 2Δ`): `q = Δ·⌈(τ + Δ)/Δ⌉ < τ + 2Δ ≤ time m`, so the call is
  at a cut `j < m`, also when `time m = τ + 2Δ`. A unit wait is not available: an engine tick
  at a non-public time has no cut.
* `snapshotCall_of_awake` (`hcallZ`): the call at the public `c_z + Δ`, before every cut
  at or after `lo ≥ c_z + Δ + 1`.
* `snapshot_of_awake` (`hsnap`) and `exists_frameWindow_of_awake`, the composition.

Only the NoAdvance premise of `exists_frameWindow_of_noAdvance` stays: it holds for `T ≤ a_z`
and fails after the reset, so this file gives no range after the reset. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- An honest node awake at a public time `q ∈ [ḡ, b]` has a call at a cut of time `q`. -/
theorem exists_call_of_public (hrun : GoldilocksRun proposer dg H tr) {g b : Time}
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    {z : Fin sp.n} (hz : z ∈ H) {q : Time} (hq : sp.toParams.IsPublic q)
    (hgq : gbar g ≤ q) (hqb : q ≤ b) :
    ∃ j, tr.IsCall z j ∧ tr.time j = q := by
  obtain ⟨j, _, hne, hcs, -⟩ :=
    hrun.tick_of_awake z hz q ((gbar_nonneg g).trans hgq) hq (hawake z hz q hgq hqb)
  obtain ⟨hn, ht, -, -, hl⟩ := hcs 0 (List.length_pos_of_ne_nil hne)
  simp only [Nat.add_zero] at hn ht hl
  exact ⟨j, ⟨_, hn, hl⟩, ht⟩

/-- An honest restart up to `b` is at or before `t_{slot(ḡ)+1}` (`restart_le_before` from
wakefulness alone): the node was asleep at some `u` with no call in `[u, restart)`; `u ≥ ḡ`
contradicts wakefulness, and `u < ḡ` the call of the tick at `t_{slot(ḡ)+1}`. -/
private theorem restart_le_of_awake (hrun : GoldilocksRun proposer dg H tr) {g b : Time}
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} (hk : tr.RestartAt y k) (hkb : tr.time k ≤ b) :
    tr.time k ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
  by_contra hlt
  obtain ⟨u, -, huk, hu, hprev⟩ := hrun.sleep_of_restart y hy k hk
  have hp₀ : gbar g ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
    have h := (SA.ts_le_iff_le_slot sp (gbar_nonneg g) ((sp.slot (gbar g) + 1 : Nat) : Int)).not.mpr
      (by push_cast; omega)
    exact (not_le.mp h).le
  by_cases hgu : gbar g ≤ u
  · exact hu (hawake y hy u hgu (huk.le.trans hkb))
  · obtain ⟨j, hj, ht⟩ := exists_call_of_public hrun hawake hy
      ⟨4 * ((sp.slot (gbar g) + 1 : Nat) : Int), by simp only [SAParams.ts]; ring⟩ hp₀
      ((lt_of_not_ge hlt).le.trans hkb)
    have hjk : j < k := by
      by_contra h
      exact hlt (ht ▸ hrun.time_mono (not_lt.mp h))
    have := hprev j hjk hj
    exact hgu (by linarith)

/-- `c_z + Δ` is public. -/
private theorem cutZ_add_public (g : Time) : sp.toParams.IsPublic (cutZ sp.toParams g + sp.Δ) :=
  ⟨4 * ((sp.slot (gbar g) + 3 : Nat) : Int) + 1, by rw [cutZ_eq]; simp only [SAParams.ts]; ring⟩

/-- **The call for a relay deadline.** From `c_z` on, the call of `z` at a public time
`q ∈ [τ + Δ, b]` is at a cut before every cut `m` later than `q`, and meets the deadline of `τ`. -/
theorem call_before_of_public (hrun : GoldilocksRun proposer dg H tr) {g b : Time}
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    {z : Fin sp.n} (hz : z ∈ H) {τ q : Time} (hτ : cutZ sp.toParams g ≤ τ)
    (hq : sp.toParams.IsPublic q) (hτq : τ + sp.Δ ≤ q) (hqb : q ≤ b)
    {m : Nat} (hqm : q < tr.time m) :
    ∃ j < m, tr.IsCall z j ∧ tr.deadline z j τ sp.Δ ≤ tr.time j := by
  have hΔ := sp.toParams.hΔ
  have hcz := lt_cutZ sp g
  have hr : sp.ts (sp.slot (gbar g) + 1 : Nat) ≤ τ := by
    refine le_trans ?_ ((cutZ_eq sp g).symm.le.trans hτ)
    exact (SA.ts_le_iff sp).mpr (by push_cast; omega)
  obtain ⟨j, hj, hjt⟩ := exists_call_of_public hrun hawake hz hq (by linarith) hqb
  refine ⟨j, ?_, hj, ?_⟩
  · by_contra h
    have := hrun.time_mono (not_lt.mp h)
    linarith
  · have := Compose.deadline_le_of_restarts (tr := tr) (y := z) (c := j)
      (fun k hk hrk => restart_le_of_awake hrun hawake hz hrk
        ((hrun.time_mono hk).trans (hjt ▸ hqb))) τ sp.Δ
    rw [max_eq_left hr] at this
    linarith

/-- **`hcall` with `λ = 2Δ`.** From `lo ≥ c_z` and before `T ≤ b + 1`, every honest node has a
call before `m` at or after the relay deadline of every cut `i` with `time i + 2Δ ≤ time m`. -/
theorem callLag_of_awake (hrun : GoldilocksRun proposer dg H tr) {g b : Time}
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    {lo T : Time} (hlo : cutZ sp.toParams g ≤ lo) (hT : T ≤ b + 1) :
    ∀ z ∈ H, ∀ i m, lo ≤ tr.time i → tr.time i + 2 * sp.Δ ≤ tr.time m → tr.time m < T →
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j := by
  intro z hz i m hi him hmT
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hcz := lt_cutZ sp g
  have hg := le_gbar g
  rw [max_eq_left (by linarith)]
  -- `q = Δ·⌈(τ + Δ)/Δ⌉`, the first public time at or after `τ + Δ`
  set r := (tr.time i + 2 * sp.Δ - 1) / sp.Δ with hr
  have h₁ : sp.Δ * r ≤ tr.time i + 2 * sp.Δ - 1 := Int.mul_ediv_self_le hΔ.ne'
  have h₂ : tr.time i + 2 * sp.Δ - 1 < sp.Δ * r + sp.Δ := by
    have := Int.lt_ediv_add_one_mul_self (tr.time i + 2 * sp.Δ - 1) hΔ
    rw [← hr] at this
    linarith [add_one_mul r sp.Δ, mul_comm r sp.Δ]
  exact call_before_of_public hrun hawake hz (q := sp.Δ * r) (hlo.trans hi) (dvd_mul_right _ _)
    (by linarith [Int.add_one_le_iff.mpr h₂]) (by linarith) (by linarith)

/-- **`hcallZ`.** From `lo ≥ c_z + Δ + 1` and before `T ≤ b + 1`, every honest node has a call
before `m` at or after the relay deadline of `c_z` (the call at `c_z + Δ`). -/
theorem snapshotCall_of_awake (hrun : GoldilocksRun proposer dg H tr) {g b : Time}
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    {lo T : Time} (hlo : cutZ sp.toParams g + sp.Δ + 1 ≤ lo) (hT : T ≤ b + 1) :
    ∀ z ∈ H, ∀ m, lo ≤ tr.time m → tr.time m < T → ∃ j < m, tr.IsCall z j ∧
      tr.deadline z j (max (cutZ sp.toParams g) g) sp.Δ ≤ tr.time j := by
  intro z hz m hm hmT
  have hcz := lt_cutZ sp g
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  rw [max_eq_left (by linarith [le_gbar g])]
  exact call_before_of_public hrun hawake hz le_rfl (cutZ_add_public g) le_rfl (by linarith)
    (by linarith)

/-- **`hsnap`.** With an honest node awake at `c_z + Δ ≤ b`, a cut follows `c_z` by `b`
(`cutZ_snapshot_of_awake_before` from `H.Nonempty` instead of the fault bound). -/
theorem snapshot_of_awake (hrun : GoldilocksRun proposer dg H tr) {g b : Time}
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t) (hH : H.Nonempty)
    (hb : cutZ sp.toParams g + sp.Δ ≤ b) :
    ∃ j, FirstCutAfter tr j (cutZ sp.toParams g) ∧ tr.time j ≤ b := by
  classical
  obtain ⟨y, hy⟩ := hH
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨j, -, hjt⟩ := exists_call_of_public hrun hawake hy (cutZ_add_public g)
    (by linarith [lt_cutZ sp g]) hb
  have hj : cutZ sp.toParams g < tr.time j := by linarith
  have hex : ∃ k, cutZ sp.toParams g < tr.time k := ⟨j, hj⟩
  exact ⟨Nat.find hex, ⟨fun k hk => not_lt.1 (Nat.find_min hex hk), Nat.find_spec hex⟩,
    (hrun.time_mono (Nat.find_min' hex hj)).trans (hjt ▸ hb)⟩

end Consensus.Goldilocks.Healing

end
