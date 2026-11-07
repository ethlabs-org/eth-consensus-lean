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

theorem unforgeable_constant_iff (h : rho.point.ConstantFaults) :
    rho.Unforgeable ↔
      ∀ i w o t, rho.events[i]? = some (Event.deliver w o t) →
        ∀ o', Obj.Contains o o' → ∀ u, rho.signerOf o' = some u → u ∉ rho.faultyAt 0 →
          ∃ j t', j < i ∧ rho.SendsAt u j t' ∧ o' ∈ rho.releasesAt j := by
  simp only [Unforgeable, rho.faultyAt_eq_zero h]

theorem executionValid_constant_iff (h : rho.point.ConstantFaults) :
    rho.ExecutionValid ↔
      0 ≤ rho.horizon ∧ rho.events.Pairwise Event.keyLe ∧ rho.events.Nodup ∧
      (∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon) ∧
      (∀ e ∈ rho.events, e.node ∉ rho.faultyAt 0) ∧
      (∀ v, v ∉ rho.faultyAt 0 → ∀ t, 0 ≤ t → t ≤ rho.horizon →
        E.awake v t = true → Event.tick v t ∈ rho.events) ∧
      (∀ v t, Event.tick v t ∈ rho.events → E.awake v t = true) ∧
      (∀ v o t, Event.deliver v o t ∈ rho.events → E.awake v t = true) ∧
      (∀ v t, Event.restart v t ∈ rho.events → 0 < t ∧ Wakes E v t) ∧
      (∀ v, v ∉ rho.faultyAt 0 → ∀ t, 0 < t → t ≤ rho.horizon →
        Wakes E v t → Event.restart v t ∈ rho.events) ∧
      rho.Unforgeable ∧ rho.SelValid ∧ rho.Credentials := by
  constructor
  · intro hv
    refine ⟨hv.horizon_nonneg, hv.sorted, hv.nodup, hv.in_horizon, ?_, ?_,
      hv.tick_awake, hv.deliver_awake, hv.restart_at_wake, ?_,
      hv.unforgeable, hv.selValid, hv.credentials⟩
    · simpa only [rho.faultyAt_eq_zero h] using hv.honest_only
    · exact fun v hf t ht hh => hv.tick_total v t ht hh (by
        simpa only [rho.faultyAt_eq_zero h] using hf)
    · exact fun v hf t ht hh => hv.wake_restart v t ht hh (by
        simpa only [rho.faultyAt_eq_zero h] using hf)
  · rintro ⟨hh, hs, hn, hi, ho, ht, ha, hd, hr, hw, hu, hv, hc⟩
    refine ⟨hh, hs, hn, hi, ?_, ?_, ha, hd, hr, ?_, hu, hv, hc⟩
    · simpa only [rho.faultyAt_eq_zero h] using ho
    · intro v t h0 hb hf
      exact ht v (by simpa only [rho.faultyAt_eq_zero h] using hf) t h0 hb
    · intro v t h0 hb hf
      exact hw v (by simpa only [rho.faultyAt_eq_zero h] using hf) t h0 hb

theorem observed_constant_iff (h : rho.point.ConstantFaults) (o : (protoOf F E).Object) :
    o ∈ rho.Observed ↔ ∃ v, v ∉ rho.faultyAt 0 ∧ o ∈ rho.ViewIdx v rho.events.length := by
  constructor
  · rintro ⟨v, i, hi, hv, ho⟩
    exact ⟨v, (rho.point.honestAt_iff_zero h v _).mp hv, rho.viewIdx_mono hi v ho⟩
  · rintro ⟨v, hv, ho⟩
    exact ⟨v, rho.events.length, le_rfl,
      (rho.point.honestAt_iff_zero h v _).mpr hv, ho⟩

theorem held_iff_served_constant (h : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    (o : (protoOf F E).Object) {w : V} {d : Time} (hw : w ∉ rho.faultyAt 0)
    (hd : d ≤ rho.horizon) :
    CommLog.Held rho.point rho.log w o d ↔ rho.Served w o d := by
  constructor
  · rintro ⟨t', ht, hs, hn⟩
    refine ⟨t', ht, hs, ?_⟩
    rintro u hu ⟨h₁, h₂⟩
    exact hn u h₁ h₂ (hv.restart_at_wake w u hu).2
  · rintro ⟨t', ht, hs, hn⟩
    refine ⟨t', ht, hs, ?_⟩
    intro u h₁ h₂ hwk
    have ht0 : 0 ≤ t' := by
      rcases hs with ⟨i, hi | ⟨_, hi⟩, -⟩ | ⟨i, hi⟩ <;>
        exact (hv.in_horizon _ (List.mem_of_getElem? hi)).1
    exact hn u (hv.wake_restart w u (lt_of_le_of_lt ht0 h₁) (h₂.trans hd)
      (by simpa only [rho.faultyAt_eq_zero h] using hw) hwk) ⟨h₁, h₂⟩

end Consensus.Model.Run

namespace Consensus.Shape

open Blocks
open Consensus.Model (pubOf Obj)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V] {E : Env V}

theorem honestProposal_constant_iff (rho : Model.Run (compiled F) E)
    (hc : rho.point.ConstantFaults) (τ : Time) (k : Fin (Fintype.card V)) (h : Header Info) :
    HonestProposal rho τ k h ↔ rho.point.HonestAt (rho.key k) 0 ∧
      ∃ r : ShapeRole (F (pubOf E)).skel.Kind, ∃ cs, ProposalRole h r ∧
        rho.releases (rho.key k) (Obj.mk (.signed k r) (.item h) cs) τ := by
  simp only [HonestProposal, EnvPoint.honestAt_iff_zero hc]

theorem outputValid_constant_iff (rho : Model.Run (compiled F) E)
    (hc : rho.point.ConstantFaults) (g : O.Id) :
    OutputValid rho g ↔ ∀ v, rho.point.HonestAt v 0 → ∀ i, i ≤ rho.events.length →
      Chain.Linked rho.hash ((chainTrace rho).read g v i) ∧
      Chain.PosIncreasing ((chainTrace rho).read g v i) ∧
      Chain.Provenant (rho.ViewIdx v i) ProposalRole ((chainTrace rho).read g v i) := by
  simp only [OutputValid, EnvPoint.honestAt_iff_zero hc]
  constructor
  · exact fun h v hv i hi => h v i hi hv
  · exact fun h v i hi hv => h v hv i hi

omit [DecidableEq V] in
theorem badProposerEvery_constant_iff (rho : Model.Run (compiled F) E)
    (K : Contract ProgressReq) (cap : Capability) (i : K.Idx) :
    BadProposerEvery F K cap i rho ↔
      match K.progress cap i with
      | .recur ρ => ∀ a : Slot, ∃ s, a ≤ s ∧ s < a + (ρ.gap : Nat) ∧
          (rho.sel (ShapeRole.proposer s)).Nonempty ∧
          ∀ k ∈ rho.sel (ShapeRole.proposer s), ¬ rho.point.HonestAt (rho.key k) 0
      | .notReadyAtMost _ => True := by
  classical
  unfold BadProposerEvery
  cases K.progress cap i <;>
    simp only [EnvPoint.HonestAt, Model.Run.point, not_not, iff_self]

end Consensus.Shape

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
