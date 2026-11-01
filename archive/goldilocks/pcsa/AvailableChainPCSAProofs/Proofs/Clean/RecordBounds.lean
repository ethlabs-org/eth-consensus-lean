module
public import AvailableChainPCSAProofs.Proofs.Clean.RecordEvents
public import AvailableChainPCSAProofs.Proofs.Clean.LockEvents

public section

/-! C6 RecordBounds: concrete receipt and count support. -/
namespace AvailableChain.PCSA
/-- A gate before the next vote has no later label. -/
theorem pcsa_gate_label_before_vote (p : Params) (i j : Slot)
    (ht : SA.gateTime p.toParams i < SA.voteTime p.toParams (j + 1)) : i ≤ j := by
  by_contra hn
  have hi : (j + 1 : Nat) ≤ i := Nat.lt_of_not_ge hn
  have hiz : ((j + 1 : Nat) : Int) ≤ (i : Int) := Int.ofNat_le.mpr hi
  change 4 * p.Δ * (i : Int) + 6 * p.Δ <
    4 * p.Δ * ((j + 1 : Nat) : Int) + p.Δ at ht
  have hp := p.deltaPos
  nlinarith
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- An inclusive honest record read is genesis or a bounded own gate result. -/
theorem pcsa_record_storeAt_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest)
    (t : Time) (j : Slot) (ht : t < SA.voteTime p.toParams (j + 1)) :
    (storeAt p c E rho x t).base.stableRecord = .genesis ∨
      ∃ i X, i ≤ j ∧ gateResultAt p c E rho x i = some (some X) ∧
        (storeAt p c E rho x t).base.stableRecord = X := by
  rw [storeAt_def, V2.D.Engine.readAt_eq_stateBefore h.valid.toScheduleWellFormed]
  rcases pcsa_record_stateBefore_origin E rho h hF
      (rho.events.filter (fun e : V2.Event V (Obj p) => decide (e.time ≤ t))).length x hx with
    hz | ⟨k, hk, i, X, he, hX, hs⟩
  · exact Or.inl hz
  · have htime := (V2.D.Engine.index_lt_read_length_iff h.valid.toScheduleWellFormed t he).mp hk
    exact Or.inr ⟨i, X, pcsa_gate_label_before_vote p i j (htime.trans_lt ht), hX, hs⟩
/-- An inclusive lock read lies below a bounded gate result at the same node. -/
theorem pcsa_lock_storeAt_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (x : V) (t : Time) (j : Slot) (ht : t < SA.voteTime p.toParams (j + 1))
    (row : Block × Nat × Time) (hr : row ∈ (storeAt p c E rho x t).base.obligations) :
    ∃ i X, i ≤ j ∧ gateResultAt p c E rho x i = some (some X) ∧
      Block.Preceq row.1 X ∧ row.2.1 = SA.releaseThreshold p.toParams := by
  rw [storeAt_def, V2.D.Engine.readAt_eq_stateBefore h.valid.toScheduleWellFormed] at hr
  obtain ⟨k, hk, i, X, he, hX, hb, hl⟩ := pcsa_lock_stateBefore_origin E rho h _ x row hr
  have htime := (V2.D.Engine.index_lt_read_length_iff h.valid.toScheduleWellFormed t he).mp hk
  exact ⟨i, X, pcsa_gate_label_before_vote p i j (htime.trans_lt ht), hX, hb, hl⟩
/-- A chain of gate results makes all bounded honest record reads compatible. -/
theorem pcsa_record_storeAt_compatible (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (j : Slot)
    (hchain : ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ i i' X Y,
      i ≤ j → i' ≤ j → gateResultAt p c E rho x i = some (some X) →
      gateResultAt p c E rho y i' = some (some Y) → Block.Compatible X Y)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) (t t' : Time)
    (ht : t < SA.voteTime p.toParams (j + 1))
    (ht' : t' < SA.voteTime p.toParams (j + 1)) :
    Block.Compatible (storeAt p c E rho x t).base.stableRecord
      (storeAt p c E rho y t').base.stableRecord := by
  rcases pcsa_record_storeAt_origin E rho h hF x hx t j ht with hz | ⟨i, X, hi, hX, hs⟩
  · rw [hz]
    exact Bool.or_eq_true_iff.mpr (Or.inl (Gen.Pure.block_genesis_preceq _))
  · rw [hs]
    rcases pcsa_record_storeAt_origin E rho h hF y hy t' j ht' with hz | ⟨i', Y, hi', hY, hs'⟩
    · rw [hz]
      exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_genesis_preceq _))
    · rw [hs']
      exact hchain x hx y hy i i' X Y hi hi' hX hY
end AvailableChain.PCSA.Run

end
