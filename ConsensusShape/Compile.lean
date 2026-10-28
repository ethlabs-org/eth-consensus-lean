module
public import ConsensusShape.Shape

@[expose] public section

/-! # Compilation of a chain shape to a model protocol (L2)

`compile S` is the model (L1) protocol of shape `S`. Its state is the shape's
state with the node's cumulative mempool; its roles are `ShapeRole`, its duties
`ShapeDuty`, its items headers. Selections come from the skeleton: the
proposer selection for every slot, the kind's selection for a committee duty,
the poll selection for the poll role.

Duties: the proposal of positive slot `s` at `slotTime s`; committee kind `k`
of slot `s` at `slotTime s + phase k · Δ`; the two poll duties at every unit tick
`t ≥ 0`. The engine writes every proposal's payload (`input := encodeTxs
mempool`) and a slot proposal's position (`pos := s`); a poll proposal's
position is the shape's choice.

Same-tick semantics: all duties of a tick (the proposal, then the kinds in
`kinds` order, then the poll duties) and gossip are built from one post-clock
state; recording an earlier signature of the tick does not affect a later
action of the same tick. Poll duties exist at every unit tick; a shape that
does not poll returns `none` and sets `pollSel := .fixed ∅`. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public Key SelSpec Obj Msg)

variable {Info : Type} [DecidableEq Info] [Encodable Info]

namespace Skeleton

variable {n : Nat} (sk : Skeleton n)

/-- The selection specification of each role. -/
def selSpec : ShapeRole sk.Kind → SelSpec n
  | .proposer _ => sk.proposerSel
  | .duty _ k => sk.kindSel k
  | .poll => sk.pollSel

/-- The signing role of each duty. -/
def role : ShapeDuty sk.Kind → ShapeRole sk.Kind
  | .propose s _ => .proposer s
  | .act s k => .duty s k
  | .pollPropose _ => .poll
  | .poll _ => .poll

/-- The act time of each duty. -/
def actTime (Δ : Time) : ShapeDuty sk.Kind → Time
  | .propose s _ => sk.grid.slotTime Δ s
  | .act s k => sk.grid.slotTime Δ s + (sk.phase k : Time) * Δ
  | .pollPropose t => (t : Time)
  | .poll t => (t : Time)

/-- The positive proposal slot at `t`, if any. -/
def proposeAt (Δ t : Time) : List (ShapeDuty sk.Kind) :=
  match sk.grid.slotAt? Δ 0 t with
  | some s => if h : 0 < s then [.propose s h] else []
  | none => []

/-- The committee duties at `t`, kinds in `kinds` order. -/
def actAt (Δ t : Time) : List (ShapeDuty sk.Kind) :=
  sk.kinds.filterMap fun k => (sk.grid.slotAt? Δ ((sk.phase k : Time) * Δ) t).map fun s => .act s k

/-- The poll duties at `t` (every unit tick `t ≥ 0`). -/
def pollAt (t : Time) : List (ShapeDuty sk.Kind) :=
  if 0 ≤ t then [.pollPropose t.toNat, .poll t.toNat] else []

/-- The duties due at `t`, in signing order. -/
def duties (Δ t : Time) : List (ShapeDuty sk.Kind) :=
  sk.proposeAt Δ t ++ sk.actAt Δ t ++ sk.pollAt t

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

variable {pub : Public} {Out : Type}

/-- The model protocol of a chain shape (see the module docstring). -/
def compile (S : ChainShape pub Out Info) : Model.Protocol pub Out where
  State := S.State × List Tx
  Role := ShapeRole S.skel.Kind
  Duty := ShapeDuty S.skel.Kind
  Item := Header Info
  Body := S.Body
  Durable := S.Durable
  decRole := inferInstance
  decItem := inferInstance
  decBody := inferInstance
  encItem := inferInstance
  selSpec := S.skel.selSpec
  role := S.skel.role
  actTime := S.skel.actTime pub.Δ
  duties := S.skel.duties pub.Δ
  duties_spec := S.skel.duties_spec pub.Δ_pos
  duties_nodup := S.skel.duties_nodup pub.Δ
  init k := (S.init k, [])
  clock st t xs := (S.clock st.1 t, xs)
  act st d := match d with
    | .propose s _ => (S.propose st.1 s).map fun (par, info, cs) =>
        (.item ⟨par, s, encodeTxs st.2, info⟩, cs)
    | .act s k => (S.act st.1 s k).map fun (b, cs) => (.data b, cs)
    | .pollPropose t => (S.pollPropose st.1 (t : Time)).map fun (par, pos, info, cs) =>
        (.item ⟨par, pos, encodeTxs st.2, info⟩, cs)
    | .poll t => (S.poll st.1 (t : Time)).map fun (b, cs) => (.data b, cs)
  gossip st t := S.gossip st.1 t
  process st o hs := (S.process st.1 o hs, st.2)
  recordOwn st o hs := (S.recordOwn st.1 o hs, st.2)
  durable st := S.durable st.1
  restore k d t := (S.restore k d t, [])
  out g st := ledgerOf (S.out g st.1)
  conflicts := S.conflicts

/-- The model family of a shape family. -/
abbrev compiled {O : OutputSchema} (F : ShapeFamily O Info) : Model.Family O :=
  fun pub => compile (F pub)

end Consensus.Shape

end
