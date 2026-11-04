module
public import ConsensusLean
public import Solution
public import Mathlib.Tactic
@[expose] public section

/-! # Test support (moved from the library; no library proof uses them)

* The act time and step of each skeleton duty and their characterization of
  `duties` (`Skeleton.duties_spec`: the duty's step is in
  `order` and its act time is `t`), and that `duties` lists each duty once when
  `order` lists each step once (`Skeleton.duties_nodup`). Execution reads only
  `duties`.
* The extremal PKI `extremalKey` (key `k` is validator `k`) and
  `active_relay` (an active liveness witness exercises the relay). -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public Key SelSpec Obj Msg pubOf protoOf sysOf)

namespace Skeleton

variable {n : Nat} (sk : Skeleton n)

/-- The act time of each duty. -/
def actTime : ShapeDuty sk.Kind → Time
  | .propose s _ => sk.grid.slotTime s
  | .act s k => sk.grid.slotTime s + (sk.phase k : Time)
  | .pollPropose t => (t : Time)
  | .poll t => (t : Time)

/-- The step of each duty. -/
def stepOf : ShapeDuty sk.Kind → Step sk.Kind
  | .propose _ _ => .propose
  | .act _ k => .kind k
  | .pollPropose _ => .pollPropose
  | .poll _ => .poll

/-- A step's duties at `t` are the duties of that step whose act time is `t`. -/
theorem mem_stepAt (t : Time) (x : Step sk.Kind)
    (d : ShapeDuty sk.Kind) : d ∈ sk.stepAt t x ↔ sk.stepOf d = x ∧ sk.actTime d = t := by
  cases x with
  | propose =>
    simp only [stepAt, proposeAt]
    cases d with
    | propose s hs =>
      simp only [stepOf, actTime, true_and]
      rw [← add_zero (sk.grid.slotTime s), ← sk.grid.slotAt?_eq_some]
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
      simp only [stepOf, reduceCtorEq, false_and, iff_false]
      split
      · split <;> simp
      · simp
    | pollPropose u =>
      simp only [stepOf, reduceCtorEq, false_and, iff_false]
      split
      · split <;> simp
      · simp
    | poll u =>
      simp only [stepOf, reduceCtorEq, false_and, iff_false]
      split
      · split <;> simp
      · simp
  | kind k =>
    simp only [stepAt, kindAt, Option.mem_toList, Option.map_eq_some_iff]
    cases d with
    | act s k' =>
      simp only [stepOf, Step.kind.injEq, actTime, ShapeDuty.act.injEq]
      constructor
      · rintro ⟨s', hs', rfl, rfl⟩
        exact ⟨rfl, sk.grid.slotAt?_eq_some.mp hs'⟩
      · rintro ⟨rfl, h⟩
        exact ⟨s, sk.grid.slotAt?_eq_some.mpr h, rfl, rfl⟩
    | propose s hs => simp [stepOf]
    | pollPropose u => simp [stepOf]
    | poll u => simp [stepOf]
  | pollPropose =>
    simp only [stepAt]
    cases d with
    | pollPropose u =>
      simp only [stepOf, actTime, true_and]
      split
      · rename_i ht
        simp only [List.mem_singleton, ShapeDuty.pollPropose.injEq]
        constructor
        · rintro rfl
          exact Int.toNat_of_nonneg ht
        · rintro rfl
          simp
      · rename_i ht
        simp only [List.not_mem_nil, false_iff]
        intro h
        exact ht (h ▸ Int.natCast_nonneg u)
    | propose s hs => simp only [stepOf, reduceCtorEq, false_and, iff_false]; split <;> simp
    | act s k => simp only [stepOf, reduceCtorEq, false_and, iff_false]; split <;> simp
    | poll u => simp only [stepOf, reduceCtorEq, false_and, iff_false]; split <;> simp
  | poll =>
    simp only [stepAt]
    cases d with
    | poll u =>
      simp only [stepOf, actTime, true_and]
      split
      · rename_i ht
        simp only [List.mem_singleton, ShapeDuty.poll.injEq]
        constructor
        · rintro rfl
          exact Int.toNat_of_nonneg ht
        · rintro rfl
          simp
      · rename_i ht
        simp only [List.not_mem_nil, false_iff]
        intro h
        exact ht (h ▸ Int.natCast_nonneg u)
    | propose s hs => simp only [stepOf, reduceCtorEq, false_and, iff_false]; split <;> simp
    | act s k => simp only [stepOf, reduceCtorEq, false_and, iff_false]; split <;> simp
    | pollPropose u => simp only [stepOf, reduceCtorEq, false_and, iff_false]; split <;> simp

/-- A duty is due at `t` iff its step is in the skeleton's `order` and its act
time is `t`. -/
theorem duties_spec (d : ShapeDuty sk.Kind) (t : Time) :
    d ∈ sk.duties t ↔ sk.stepOf d ∈ sk.order ∧ sk.actTime d = t := by
  simp only [duties, List.mem_flatMap, sk.mem_stepAt]
  constructor
  · rintro ⟨x, hx, rfl, h⟩
    exact ⟨hx, h⟩
  · rintro ⟨hx, h⟩
    exact ⟨_, hx, rfl, h⟩

/-- With the default `order`, `duties` is the former fixed list: the proposal,
the kinds in `kinds` order, then the two poll duties (at `t ≥ 0`). -/
theorem duties_of_default_order {t : Time}
    (h : sk.order = [.propose] ++ sk.kinds.map .kind ++ [.pollPropose, .poll]) :
    sk.duties t = sk.proposeAt t ++ sk.kinds.flatMap (sk.kindAt t) ++
      (if 0 ≤ t then [.pollPropose t.toNat, .poll t.toNat] else []) := by
  simp only [duties, h, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.flatMap_map, stepAt]
  split <;> simp

/-- With an order that lists each step once, `duties` lists each duty once. -/
theorem duties_nodup (t : Time) (h : sk.order.Nodup) :
    (sk.duties t).Nodup := by
  unfold duties
  refine List.nodup_flatMap.mpr ⟨fun x _ => ?_, h.imp fun {x y} hxy => ?_⟩
  · cases x with
    | propose =>
      simp only [stepAt, proposeAt]
      split
      · split <;> simp
      · simp
    | kind k =>
      simp only [stepAt, kindAt]
      cases sk.grid.slotAt? (sk.phase k) t <;> simp
    | pollPropose => simp only [stepAt]; split <;> simp
    | poll => simp only [stepAt]; split <;> simp
  · intro d hd hd'
    exact hxy (((sk.mem_stepAt t x d).mp hd).1.symm.trans ((sk.mem_stepAt t y d).mp hd').1)

end Skeleton

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

/-- The extremal PKI on `Fin (n + 1)`: key `k` is validator `k`. -/
def extremalKey (n : Nat) : Fin (Fintype.card (Fin (n + 1))) ≃ Fin (n + 1) :=
  finCongr (Fintype.card_fin _)

/-- The relay is exercised: in a run partially synchronous with a GST at or
before `start` where every validator is always awake, an active liveness
witness (`TxLiveActive`) has an honest reader that receives the submitted
transaction by relay, never by its own submission. -/
theorem active_relay {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (rho : Model.Run (compiled F) E) {gst c start D : Time}
    (hs : CommLog.PSync rho.point rho.log gst) (hgs : gst ≤ start) (hD : 0 ≤ D)
    (hawake : ∀ v t, E.awake v t = true)
    (ha : rho.point.TxLiveActive c start D) :
    ∃ x, ∃ w ∈ rho.honest, (∀ τ, x ∉ rho.submit w τ) ∧ ∃ τ, 0 ≤ τ ∧ x ∈ rho.relay w τ := by
  obtain ⟨x, t, t', u, w, ht0, hu, hua, hx, hw, -, hnw, hdl, hth, -⟩ := ha
  change u ∈ rho.honest at hu
  change w ∈ rho.honest at hw
  change x ∈ rho.submit u t at hx
  change ∀ τ, x ∉ rho.submit w τ at hnw
  change max t start + E.Δ + D ≤ t' at hdl
  change t' ≤ rho.horizon at hth
  have hm : max t gst ≤ max t start := max_le_max le_rfl hgs
  have hd : max t gst + E.Δ - 1 ≤ rho.horizon := by linarith
  obtain ⟨τ, hτ, -, hxτ⟩ := hs.txs u hu x t ht0 hua hx w hw t le_rfl hd hd
    (fun u _ _ => hawake w u)
  refine ⟨x, w, hw, hnw, τ, hτ, ?_⟩
  rcases List.mem_append.mp hxτ with h | h
  · exact absurd h (hnw τ)
  · exact h

end Consensus.Shape

end
