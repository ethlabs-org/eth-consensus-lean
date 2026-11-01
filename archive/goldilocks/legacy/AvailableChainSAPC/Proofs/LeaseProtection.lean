module
public import AvailableChainSAPC.Proofs.GateAdmission
public import AvailableChainSAPC.Proofs.CleanDelivery
public import AvailableChainSAPC.Proofs.CleanInclusion
public import AvailableChainSAPC.Proofs.BaseReceipts

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- Both PC guards retain existing map keys. The prefix loop uses the
shared unique-key proof, including renewals under a stable-record veto. -/
theorem gateWithPC_unique_keys (p : Params) {n : Nat} (st : GridCO.State n)
    (r : Slot) (cert : Option (PC n)) (h : GridCO.UniqueObligationKeys st) :
    GridCO.UniqueObligationKeys (gateWithPC p st r cert) := by
  cases cert with
  | none => exact @GridCO.gate_unique_keys GridCO.slowLeasePolicy p.engine n st r h
  | some cert =>
    simp only [gateWithPC]
    split
    · exact h
    · split
      · exact h
      · apply GridCO.foldl_unique_keys
        · intro acc b hu
          apply GridCO.foldl_unique_keys
          · intro acc g hu
            exact GridCO.write_unique_keys acc b g _ hu
          · exact hu
        · split <;> exact h

/-- A gate can renew an existing lease but cannot shorten it. No PC
compatibility premise is needed for a row already in the map. -/
theorem gateWithPC_protectsUntil (p : Params) {n : Nat} (st : GridCO.State n)
    (r : Slot) (cert : Option (PC n)) (B : Block) (g : Nat) (d : Time)
    (hu : GridCO.UniqueObligationKeys st) (hp : GridCO.ProtectsUntil st B g d) :
    GridCO.ProtectsUntil (gateWithPC p st r cert) B g d := by
  cases cert with
  | none => exact @GridCO.gate_protectsUntil GridCO.slowLeasePolicy p.engine n st r B g d hu hp
  | some cert =>
    simp only [gateWithPC]
    split
    · exact hp
    · split
      · exact hp
      · apply (GridCO.fold_write_protectsUntil _ _ _ B g d ?_ ?_ ?_).2
        · intro acc b hu hp
          apply GridCO.fold_write_protectsUntil
          · intro acc level hu hp
            exact ⟨GridCO.write_unique_keys acc b level _ hu,
              GridCO.write_protectsUntil acc B b g level d _ hu hp⟩
          · exact hu
          · exact hp
        · split <;> exact hu
        · split <;> exact hp

private theorem compatible_prefix_right (A B C : Block)
    (h : Block.Compatible A C) (hp : Block.Preceq B C) : Block.Compatible A B := by
  rcases Bool.or_eq_true_iff.mp h with ha | ha
  · exact GridCO.ancestors_compatible A B C ha hp
  · exact Bool.or_eq_true_iff.mpr (Or.inr (GridCO.prefix_trans B C A hp ha))

/-- Comparable finite targets are preserved from their raw gate sources.
This statement does not relate a live target to the stable record. -/
theorem gateWithPC_comparable_targets (p : Params) {n : Nat} (st : GridCO.State n)
    (r : Slot) (cert : Option (PC n)) (h : GridCO.ComparableTargets st) :
    GridCO.ComparableTargets (gateWithPC p st r cert) := by
  intro A g d hA B level expiry hB
  have cross (K : Block) (k : Nat) (e : Time) (row : (K, k, e) ∈ st.obligations)
      (C : Block) (raw : SA.confirmation p st r = some C)
      (new : ∃ X g d, (X, g, d) ∈ (gateWithPC p st r cert).obligations ∧
        (X, g, d) ∉ st.obligations) : Block.Compatible K C := by
    have guard : st.obligations.any (fun (a, _, _) => !Block.compatible a C) = false := by
      apply Bool.eq_false_iff.mpr
      intro veto
      obtain ⟨X, g, d, present, absent⟩ := new
      rw [gateWithPC_finite_veto p st r cert C raw veto] at present
      exact absent present
    simpa using! List.any_eq_false.mp guard (K, k, e) row
  by_cases oldA : (A, g, d) ∈ st.obligations
  · by_cases oldB : (B, level, expiry) ∈ st.obligations
    · exact h A g d oldA B level expiry oldB
    · obtain ⟨C, raw, below, _⟩ :=
        (gateWithPC_row_origin p st r cert B level expiry hB).resolve_left oldB
      exact compatible_prefix_right A B C
        (cross A g d oldA C raw ⟨B, level, expiry, hB, oldB⟩) below
  · obtain ⟨C, raw, below, _⟩ :=
      (gateWithPC_row_origin p st r cert A g d hA).resolve_left oldA
    by_cases oldB : (B, level, expiry) ∈ st.obligations
    · have comp := compatible_prefix_right B A C
        (cross B level expiry oldB C raw ⟨A, g, d, hA, oldA⟩) below
      simpa only [Block.Compatible, Block.compatible, Bool.or_comm] using comp
    · obtain ⟨D, rawD, belowD, _⟩ :=
        (gateWithPC_row_origin p st r cert B level expiry hB).resolve_left oldB
      have eq : D = C := Option.some.inj (rawD.symm.trans raw)
      exact GridCO.ancestors_compatible A B C below (eq ▸ belowD)

theorem clock_unique_keys (p : Params) {n : Nat} (st : State n) (t : Time)
    (h : GridCO.UniqueObligationKeys st.base) :
    GridCO.UniqueObligationKeys (clock p st t).base := by
  have pre : GridCO.UniqueObligationKeys (clockPreGate p st t).base := by
    rw [clockPreGate_base]
    intro a ha b hb eq
    exact h a (GridCO.clockPreGate_obligations_subset p.engine st.base t a ha)
      b (GridCO.clockPreGate_obligations_subset p.engine st.base t b hb) eq
  rw [clock_eq_gate_prestate]
  dsimp only
  split
  · exact gateWithPC_unique_keys p _ _ _ pre
  · exact pre

theorem clock_comparable_targets (p : Params) {n : Nat} (st : State n) (t : Time)
    (h : GridCO.ComparableTargets st.base) :
    GridCO.ComparableTargets (clock p st t).base := by
  have pre : GridCO.ComparableTargets (clockPreGate p st t).base := by
    rw [clockPreGate_base]
    intro a g d ha b k e hb
    exact h a g d (GridCO.clockPreGate_obligations_subset p.engine st.base t _ ha)
      b k e (GridCO.clockPreGate_obligations_subset p.engine st.base t _ hb)
  rw [clock_eq_gate_prestate]
  dsimp only
  split
  · exact gateWithPC_comparable_targets p _ _ _ pre
  · exact pre

/-- These two map facts hold on every reachable path, including arbitrary
delivery, mode changes, and leases whose raw tips were PC-vetoed. -/
theorem lease_map_at_fold {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (sapc p).Object)) (v : V) :
    let st := (events.foldl World.step World.init) v
    GridCO.UniqueObligationKeys st.base ∧ GridCO.ComparableTargets st.base := by
  apply fold_invariant p (fun st =>
    GridCO.UniqueObligationKeys st.base ∧ GridCO.ComparableTargets st.base)
  · exact ⟨GridCO.initial_unique_keys p.n, GridCO.initial_comparable_targets p.n⟩
  · intro st t h
    exact ⟨clock_unique_keys p st t h.1, clock_comparable_targets p st t h.2⟩
  · intro st o h
    simpa only [GridCO.UniqueObligationKeys, GridCO.ComparableTargets,
      process_obligations] using h

/-- The shared SA expiry and release proof applies before the PC gate.
The finite guard then retains the prefix, in either mode. -/
theorem clock_preserves_protection (p : Params) {n : Nat} (st : State n) (t : Time)
    (B : Block) (g : Nat) (d : Time) (hs : GridCO.ReceiptStamped st.base)
    (hu : GridCO.UniqueObligationKeys st.base) (hp : GridCO.ProtectsUntil st.base B g d)
    (old : Block.Preceq B st.base.stableRecord) (ht : t < d)
    (hc : ∀ r, t = GridCO.releaseTime p.engine r →
      GridCO.releaseCount p.engine st.base r B < g) :
    GridCO.ProtectsUntil (clock p st t).base B g d ∧
      Block.Preceq B (clock p st t).base.stableRecord := by
  have pre : GridCO.ProtectsUntil (clockPreGate p st t).base B g d := by
    rw [clockPreGate_base]
    exact @GridCO.clockPreGate_protectsUntil GridCO.slowLeasePolicy
      p.engine n st.base t B g d hs hp ht hc
  have order : GridCO.UniqueObligationKeys (clockPreGate p st t).base := by
    rw [clockPreGate_base]
    intro a ha b hb eq
    exact hu a (GridCO.clockPreGate_obligations_subset p.engine st.base t a ha)
      b (GridCO.clockPreGate_obligations_subset p.engine st.base t b hb) eq
  have record : Block.Preceq B (clockPreGate p st t).base.stableRecord := by
    simpa only [clockPreGate_base, GridCO.clockPreGate_stable] using old
  rw [clock_eq_gate_prestate]
  dsimp only
  split
  · exact ⟨gateWithPC_protectsUntil p _ _ _ B g d order pre,
      gateWithPC_preserves_protected_prefix p _ _ _ B g d pre record⟩
  · exact ⟨pre, record⟩

end AvailableChain.SAPC
end
