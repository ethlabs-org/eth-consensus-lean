module
public import ConsensusLean.Spec.Model.System
public import ConsensusLean.Spec.Shape.Run
public import ConsensusLean.Spec.Shape.Active
public import ConsensusLean.Spec.Model.Served
public import ConsensusLean.Lemmas.Problem.Constant
public import ConsensusLean.Lemmas.Model.View

public section

/-! # Constant-fault reductions of the execution model -/

namespace Consensus.Model.Run

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema}
    {F : ProtocolFamily O} {E : Env V} (rho : Run F E)

omit [DecidableEq V] in
theorem faultyAt_eq_zero (h : rho.point.ConstantFaults) (t : Time) :
    rho.faultyAt t = rho.faultyAt 0 := h t

end Consensus.Model.Run

namespace Consensus.Blocks

variable {V : Type} [Fintype V] {p : EnvPoint V}

/-- Every proposer hold has the static meaning when faults are constant. -/
theorem honestReadyIn_constant_iff (hp : p.ConstantFaults)
    (key : Fin (Fintype.card V) ≃ V) (sel : Slot → Finset (Fin (Fintype.card V)))
    (s : Slot) (c t h : Time) :
    HonestReadyIn p key sel s c t h ↔
      (sel s).Nonempty ∧ ∀ k ∈ sel s, p.Ready c (key k) t := by
  simp only [HonestReadyIn]
  constructor
  · exact fun ⟨hne, h⟩ => ⟨hne, fun k hk => (h k hk).1⟩
  · rintro ⟨hne, h⟩
    refine ⟨hne, fun k hk => ⟨h k hk, ?_⟩⟩
    exact (p.honestAt_iff_zero hp _ _).mpr ((p.honestAt_iff_zero hp _ _).mp (h k hk).1)

/-- On constant faults, recurrence has exactly the original slot-readiness meaning,
independently of its proposer hold. -/
theorem patternRecurrence_constant_iff (hp : p.ConstantFaults)
    (key : Fin (Fintype.card V) ≃ V) (sel : Slot → Finset (Fin (Fintype.card V)))
    (G : TimeGrid) (ρ : Recurrence) (c start stop : Time) :
    PatternRecurrence p key sel G ρ c start stop ↔
      ∀ t, max start 0 ≤ t → t + (ρ.len : Time) * G.slotLen ≤ stop →
        t + (ρ.len : Time) * G.slotLen ≤ p.horizon →
        ∃ s, t < G.slotTime s ∧ G.slotTime s ≤ t + ((ρ.gap : Nat) : Time) * G.slotLen ∧
          ∀ j ∈ ρ.pattern.offsets, (sel (s + j)).Nonempty ∧
            ∀ k ∈ sel (s + j), p.Ready c (key k) (G.slotTime (s + j)) := by
  simp only [PatternRecurrence, honestReadyIn_constant_iff hp]

end Consensus.Blocks
end
