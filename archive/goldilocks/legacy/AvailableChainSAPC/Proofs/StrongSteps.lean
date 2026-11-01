module
public import AvailableChainSAPC.Proofs.StrongBoundary

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- Compatibility passes from a certificate to each of its ancestors. -/
theorem compatible_with_prefix (a b c : Block) (h : Block.Compatible a c)
    (belowPC : Block.Preceq b c) : Block.Compatible a b := by
  rcases Bool.or_eq_true_iff.mp h with below | above
  · exact GridCO.ancestors_compatible a b c below belowPC
  · exact Bool.or_eq_true_iff.mpr (Or.inr (GridCO.prefix_trans b c a belowPC above))

/-- The lease loop cannot create a conflicting mandatory entry while the
live PC contains the protected prefix, even when the raw tip is vetoed. -/
theorem gateWithPC_finite_compatible (p : Params) {n : Nat} (st : GridCO.State n)
    (r : Slot) (c : PC n) (B : Block) (belowPC : Block.Preceq B c.target)
    (old : ∀ b g d, (b, g, d) ∈ st.obligations → Block.Compatible b B) :
    ∀ b g d, (b, g, d) ∈ (gateWithPC p st r (some c)).obligations →
      Block.Compatible b B := by
  intro b g d row
  rcases gateWithPC_row_origin p st r (some c) b g d row with prior | ⟨_, _, _, _, guard, _⟩
  · exact old b g d prior
  · exact compatible_with_prefix b B c.target guard belowPC

/-- Expiry and release only remove entries. The PC-controlled gate keeps
all remaining and newly written entries compatible with the armed target. -/
theorem clock_finite_compatible (p : Params) {n : Nat} (st : State n)
    (t : Time) (c : PC n) (B : Block) (active : capBroken p st = false)
    (selected : st.bestPC = some c) (belowPC : Block.Preceq B c.target)
    (old : ∀ b g d, (b, g, d) ∈ st.base.obligations → Block.Compatible b B) :
    ∀ b g d, (b, g, d) ∈ (clock p st t).base.obligations → Block.Compatible b B := by
  have pre : ∀ b g d, (b, g, d) ∈ (clockPreGate p st t).base.obligations →
      Block.Compatible b B := by
    rw [clockPreGate_base]
    intro b g d row
    exact old b g d (GridCO.clockPreGate_obligations_subset p.engine st.base t _ row)
  rw [clock_eq_gate_prestate]
  dsimp only
  split
  · change ∀ b g d, (b, g, d) ∈ (gateWithPC p (clockPreGate p st t).base _
        (if capBroken p (clockPreGate p st t) then none
         else (clockPreGate p st t).bestPC)).obligations → Block.Compatible b B
    rw [(clockPreGate_pcData p st t).1, (clockPreGate_pcData p st t).2, active, selected]
    exact gateWithPC_finite_compatible p _ _ c B belowPC pre
  · exact pre

/-- A compatible floor cannot displace the protected part of a PC.
A compatible mandatory root then retains that same prefix. -/
theorem choice_covers_of_pc (p : Params) {n : Nat} (st : State n)
    (tree : List Block) (raw support : List (GridCO.Wire n)) (r : Slot)
    (c : PC n) (B : Block) (active : capBroken p st = false)
    (belowPC : Block.Preceq B c.target)
    (floorCompat : Block.Compatible (floor p st tree raw support r) B)
    (rootCompat : Block.Compatible (GridCO.liveRoot st.base) B) :
    Block.Preceq B (choice p st tree raw support r (some c)) := by
  have anchor : Block.Preceq B
      (preliminaryAnchor (floor p st tree raw support r) (some c)) := by
    simp only [preliminaryAnchor]
    split
    · exact belowPC
    · rename_i no
      rcases Bool.or_eq_true_iff.mp floorCompat with below | above
      · exact (no (Bool.or_eq_true_iff.mpr (Or.inr
          (GridCO.prefix_trans _ B c.target below belowPC)))).elim
      · exact above
  have root : Block.Preceq B (mandatoryRoot (GridCO.liveRoot st.base)
      (preliminaryAnchor (floor p st tree raw support r) (some c))) := by
    unfold mandatoryRoot
    split
    · exact anchor
    · rename_i no
      rcases Bool.or_eq_true_iff.mp rootCompat with below | above
      · exact (no (GridCO.prefix_trans _ B _ below anchor)).elim
      · exact above
  exact GridCO.prefix_trans _ _ _ root (by
    simpa only [choice, active, Bool.false_eq_true, ↓reduceIte] using!
      GridCO.ghost_extends (mandatoryRoot (GridCO.liveRoot st.base)
        (preliminaryAnchor (floor p st tree raw support r) (some c))) tree
        (GridCO.goldfishScore st.base.blocks raw support)
        (GridCO.goldfishEligible st.base.blocks raw support r))

/-- All conflicting score seats are faulty if the label's honest HEADs
cover B. The bound includes the equivocator contribution to each score. -/
theorem conflicting_score_le_faults {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hs : ScheduleWellFormed E rho) (st : State p.n)
    (auth : ArchiveAuthenticated p E rho st) (label : Slot)
    (raw support : List (GridCO.Wire p.n)) (sub : support ⊆ raw)
    (archived : ∀ o ∈ raw, ∃ h ∈ st.receivedHeads, baseWire h = o)
    (labels : ∀ o ∈ raw, GridCO.headLabel? o = some label)
    (B : Block) (heads : ∀ v ∈ rho.honest,
      Block.Preceq B (headData p rho label v).target)
    (b : Block) (conflict : Block.compatible b B = false) :
    GridCO.goldfishScore st.base.blocks raw support b ≤ (faulty rho).card := by
  rw [GridCO.goldfishScore_eq_card]
  apply faulty_seats_card_le p rho label
  intro seat member honest
  let view := { st with base := { st.base with votes := raw } }
  have noEquiv : GridCO.equivocates raw seat = false := by
    apply GridCO.equivocates_false_of_unique
    intro x hx y hy
    obtain ⟨hx, xi⟩ := List.mem_filter.mp hx
    obtain ⟨hy, yi⟩ := List.mem_filter.mp hy
    exact base_honest_heads_equal p E rho hs view archived auth x y label seat hx hy
      (labels x hx) (labels y hy) (by simpa using xi) (by simpa using yi) honest
  obtain ⟨o, target, ho, ht, _, _, below⟩ := scoreSeat_witness _ raw support b seat member noEquiv
  obtain ⟨os, oi⟩ := List.mem_filter.mp ho
  have oraw := sub os
  obtain ⟨target', eq⟩ := GridCO.head_wire_shape o label seat (labels o oraw) (by simpa using oi)
  subst o
  have targetEq : target' = target := Option.some.inj ht
  obtain ⟨data, hm, dataEq⟩ := baseArchived_head view archived label seat target' oraw
  obtain ⟨i, tick, emitted⟩ := auth label seat data hm honest
  have act := (emittedAt_seat_action (sapc p) E rho i _ (voteTime p label)
    label seat (.head data) emitted).2
  rw [stateBefore_tick_eq_stateBeforeTime hs tick] at act
  change some (Msg.head (headData p rho label (rho.seatOf label seat))) = some (.head data) at act
  have eq := (congrArg HeadData.target (Msg.head.inj (Option.some.inj act))).trans
    (dataEq.trans targetEq)
  have cover := eq ▸ heads _ honest
  have comp := GridCO.ancestors_compatible b B target below cover
  change Block.compatible b B = true at comp
  rw [conflict] at comp
  contradiction

/-- F4 cannot be the first departure under the cap: a conflicting floor
would need more than f faulty seats at its own label. -/
theorem floor_compatible_of_heads {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hs : ScheduleWellFormed E rho) (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (st : State p.n) (auth : ArchiveAuthenticated p E rho st)
    (tree : List Block) (label r : Slot) (raw support : List (GridCO.Wire p.n))
    (sub : support ⊆ raw)
    (archived : ∀ o ∈ raw, ∃ h ∈ st.receivedHeads, baseWire h = o)
    (labels : ∀ o ∈ raw, GridCO.headLabel? o = some label)
    (B : Block) (heads : ∀ v ∈ rho.honest,
      Block.Preceq B (headData p rho label v).target) :
    Block.Compatible (floor p st tree raw support r) B := by
  by_cases gen : floor p st tree raw support r = .genesis
  · rw [gen]
    exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.genesis_prefix B))
  · cases compatible : Block.compatible (floor p st tree raw support r) B with
    | true => exact compatible
    | false =>
      have bound := conflicting_score_le_faults p E rho hs st auth label raw support
        sub archived labels B heads _ compatible
      have score := (floor_properties p st tree raw support r gen).2.2
      exact (Nat.not_lt_of_ge (bound.trans cap) score).elim

end AvailableChain.SAPC
end
