module
public import ConsensusShape
public import Mathlib.Tactic
@[expose] public section

/-! # Test support (moved from the library; no library proof uses them)

* The act time of each skeleton duty and its characterization of `duties`
  (`Skeleton.duties_spec`, under `0 < Δ`), and that `duties` lists each duty
  once (`Skeleton.duties_nodup`). Execution reads only `duties`.
* The extremal PKI `extremalKey` (key `k` is validator `k`) and
  `active_relay` (an active liveness witness exercises the relay). -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public Key SelSpec Obj Msg pubOf protoOf sysOf)

namespace Skeleton

variable {n : Nat} (sk : Skeleton n)

/-- The act time of each duty. -/
def actTime (Δ : Time) : ShapeDuty sk.Kind → Time
  | .propose s _ => sk.grid.slotTime Δ s
  | .act s k => sk.grid.slotTime Δ s + (sk.phase k : Time) * Δ
  | .pollPropose t => (t : Time)
  | .poll t => (t : Time)

theorem duties_spec {Δ : Time} (hΔ : 0 < Δ) (d : ShapeDuty sk.Kind) (t : Time) :
    d ∈ sk.duties Δ t ↔ sk.actTime Δ d = t := by
  unfold duties
  simp only [List.mem_append]
  cases d with
  | propose s hs =>
    have hA : ShapeDuty.propose s hs ∉ sk.actAt Δ t := by
      simp [actAt]
    have hP : ShapeDuty.propose s hs ∉ sk.pollAt t := by
      unfold pollAt; split <;> simp
    simp only [hA, hP, or_false, actTime]
    rw [← add_zero (sk.grid.slotTime Δ s), ← sk.grid.slotAt?_eq_some hΔ]
    unfold proposeAt
    constructor
    · intro h
      split at h
      · rename_i s' hs'
        split at h
        · simp only [List.mem_singleton, ShapeDuty.propose.injEq] at h
          rw [hs', h]
        · simp at h
      · simp at h
    · intro h
      rw [h]
      simp [hs]
  | act s k =>
    have hA : ShapeDuty.act s k ∉ sk.proposeAt Δ t := by
      unfold proposeAt; split
      · split <;> simp
      · simp
    have hP : ShapeDuty.act s k ∉ sk.pollAt t := by
      unfold pollAt; split <;> simp
    simp only [hA, hP, false_or, or_false, actTime]
    rw [← sk.grid.slotAt?_eq_some hΔ]
    simp only [actAt, List.mem_filterMap, Option.map_eq_some_iff, ShapeDuty.act.injEq]
    constructor
    · rintro ⟨k', -, s', hs', rfl, rfl⟩
      exact hs'
    · intro h
      exact ⟨k, sk.kinds_complete k, s, h, rfl, rfl⟩
  | pollPropose u =>
    have hA : ShapeDuty.pollPropose u ∉ sk.proposeAt Δ t := by
      unfold proposeAt; split
      · split <;> simp
      · simp
    have hB : ShapeDuty.pollPropose u ∉ sk.actAt Δ t := by
      simp [actAt]
    simp only [hA, hB, false_or, actTime, pollAt]
    split
    · rename_i ht
      simp only [List.mem_cons, ShapeDuty.pollPropose.injEq, List.not_mem_nil, or_false]
      constructor
      · rintro (rfl | h)
        · exact Int.toNat_of_nonneg ht
        · cases h
      · intro h
        left
        rw [← h]
        simp
    · rename_i ht
      simp only [List.not_mem_nil, false_iff]
      intro h
      exact ht (h ▸ Int.natCast_nonneg u)
  | poll u =>
    have hA : ShapeDuty.poll u ∉ sk.proposeAt Δ t := by
      unfold proposeAt; split
      · split <;> simp
      · simp
    have hB : ShapeDuty.poll u ∉ sk.actAt Δ t := by
      simp [actAt]
    simp only [hA, hB, false_or, actTime, pollAt]
    split
    · rename_i ht
      simp only [List.mem_cons, ShapeDuty.poll.injEq, List.not_mem_nil, or_false]
      constructor
      · rintro (h | rfl)
        · cases h
        · exact Int.toNat_of_nonneg ht
      · intro h
        right
        rw [← h]
        simp
    · rename_i ht
      simp only [List.not_mem_nil, false_iff]
      intro h
      exact ht (h ▸ Int.natCast_nonneg u)

theorem duties_nodup (Δ t : Time) : (sk.duties Δ t).Nodup := by
  have hP : (sk.proposeAt Δ t).Nodup := by
    unfold proposeAt; split
    · split <;> simp
    · simp
  have hA : (sk.actAt Δ t).Nodup := by
    refine sk.kinds_nodup.filterMap ?_
    intro a a' b hb hb'
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨_, _, h⟩ := Option.map_eq_some_iff.mp hb'
    cases h
    rfl
  have hQ : (sk.pollAt t).Nodup := by
    unfold pollAt; split
    · simp
    · simp
  have mP : ∀ a ∈ sk.proposeAt Δ t, ∃ s h, a = .propose s h := by
    intro a ha
    unfold proposeAt at ha
    split at ha
    · split at ha
      · exact ⟨_, _, List.mem_singleton.mp ha⟩
      · simp at ha
    · simp at ha
  have mA : ∀ a ∈ sk.actAt Δ t, ∃ s k, a = .act s k := by
    intro a ha
    simp only [actAt, List.mem_filterMap, Option.map_eq_some_iff] at ha
    obtain ⟨k, _, s, _, rfl⟩ := ha
    exact ⟨s, k, rfl⟩
  have mQ : ∀ a ∈ sk.pollAt t, (∃ u, a = .pollPropose u) ∨ ∃ u, a = .poll u := by
    intro a ha
    unfold pollAt at ha
    split at ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact Or.inl ⟨_, rfl⟩
      · exact Or.inr ⟨_, rfl⟩
    · simp at ha
  unfold duties
  rw [List.nodup_append, List.nodup_append]
  refine ⟨⟨hP, hA, ?_⟩, hQ, ?_⟩
  · intro a ha b hb hab
    subst hab
    obtain ⟨_, _, rfl⟩ := mP _ ha
    obtain ⟨_, _, h⟩ := mA _ hb
    cases h
  · intro a ha b hb hab
    subst hab
    rcases mQ _ hb with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨_, _, h⟩ := mP _ ha; cases h
    · obtain ⟨_, _, h⟩ := mA _ ha; cases h
    · obtain ⟨_, _, h⟩ := mP _ ha; cases h
    · obtain ⟨_, _, h⟩ := mA _ ha; cases h

end Skeleton

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Encodable Info]

/-- The extremal PKI on `Fin (n + 1)`: key `k` is validator `k`. -/
def extremalKey (n : Nat) : Fin (Fintype.card (Fin (n + 1))) ≃ Fin (n + 1) :=
  finCongr (Fintype.card_fin _)

/-- The relay is exercised: in a run partially synchronous with a GST at or
before `start` where every validator is always awake, an active liveness
witness (`TxLiveActive`) has an honest reader that receives the submitted
transaction by relay, never by its own submission. -/
theorem active_relay {F : ShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (rho : Model.Run (compiled F) E) {gst c start D : Time}
    (hs : CommLog.PSync rho.point rho.log gst) (hgs : gst ≤ start) (hD : 0 ≤ D)
    (hawake : ∀ v t, E.awake v t = true)
    (ha : ((sysOf O (compiled F) V).trace ⟨E, rho⟩).TxLiveActive c start D) :
    ∃ x, ∃ w ∈ rho.honest, (∀ τ, x ∉ rho.submit w τ) ∧ ∃ τ, 0 ≤ τ ∧ x ∈ rho.relay w τ := by
  obtain ⟨x, t, t', u, w, ht0, hu, hua, hx, hw, -, hnw, hdl, hth, -⟩ := ha
  change u ∈ rho.honest at hu
  change w ∈ rho.honest at hw
  change x ∈ rho.submit u t at hx
  change ∀ τ, x ∉ rho.submit w τ at hnw
  change max t start + E.Δ + D ≤ t' at hdl
  change t' ≤ rho.horizon at hth
  have hm : max t gst ≤ max t start := max_le_max le_rfl hgs
  have hd : max t gst + E.Δ ≤ rho.horizon := by linarith
  obtain ⟨τ, hτ, -, hxτ⟩ := hs.txs u hu x t ht0 hua hx w hw t le_rfl hd hd (hawake w _)
  refine ⟨x, w, hw, hnw, τ, hτ, ?_⟩
  rcases List.mem_append.mp hxτ with h | h
  · exact absurd h (hnw τ)
  · exact h

end Consensus.Shape

end
