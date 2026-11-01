module
public import AvailableChainPCSAProofs.Proofs.Clean.RecordOrder
public import AvailableChainPCSAProofs.Proofs.Clean.AckDecisions
public import AvailableChainPCSAProofs.Proofs.Clean.RelayPersistence
public import AvailableChainPCSAProofs.Proofs.Clean.ViewRank
public import AvailableChainPCSAProofs.Proofs.Foundations.Output

public section

/-! C6 CutReads: concrete receipt and count support. -/
namespace AvailableChain.PCSA
/-- A selected target has an exact source certificate in the current pool. -/
theorem pcsa_pcTarget_source (st : State n) (B : Block) (hb : pcTarget? st = some B) :
    ∃ C ∈ st.pcs, latestPC st = some C ∧ C.target = B := by
  obtain ⟨C, hC, hB⟩ := Option.map_eq_some_iff.mp hb
  exact ⟨C, bestPC_mem st.pcs C hC, hC, hB⟩
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- An inclusive record is genesis or an own result whose gate has already occurred. -/
theorem pcsa_record_storeAt_timed_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest) (t : Time) :
    (storeAt p c E rho x t).base.stableRecord = .genesis ∨
      ∃ i X, SA.gateTime p.toParams i ≤ t ∧ gateResultAt p c E rho x i = some (some X) ∧
        (storeAt p c E rho x t).base.stableRecord = X := by
  rw [storeAt_def, V2.D.Engine.readAt_eq_stateBefore h.valid.toScheduleWellFormed]
  rcases pcsa_record_stateBefore_origin E rho h hF
      (rho.events.filter (fun e : V2.Event V (Obj p) => decide (e.time ≤ t))).length x hx with
    hz | ⟨k, hk, i, X, he, hX, hs⟩
  · exact Or.inl hz
  · exact Or.inr ⟨i, X,
      (V2.D.Engine.index_lt_read_length_iff h.valid.toScheduleWellFormed t he).mp hk, hX, hs⟩
/-- A PC in an inclusive read has an honest ack no later than the read time. -/
theorem pcsa_pc_storeAt_timed_ack [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFault : FaultsBelowQA p c rho) (x : V) (hx : x ∈ rho.honest) (t : Time)
    (C : PC p.n) (hc : C ∈ (storeAt p c E rho x t).pcs) :
    C.wellFormed = true ∧ ∃ y, HonestAckAt p c E rho y C.slot C.target ∧
      SA.earlyTime p.toParams C.slot ≤ t := by
  obtain ⟨hw, y, ha, ht⟩ := pcsa_pc_honest_ack_storeAt E rho h hFault x hx t (t + 1)
    (Int.lt_add_one_iff.mpr (le_refl _)) C hc
  exact ⟨hw, y, ha, Int.le_of_lt_add_one ht⟩
/-- Held PCs persist between inclusive stage-one reads. -/
theorem pcsa_storeAt_pcs_mono (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest) (t t' : Time) (ht : t ≤ t') :
    (storeAt p c E rho x t).pcs ⊆ (storeAt p c E rho x t').pcs := by
  rw [storeAt_def, storeAt_def, V2.D.Engine.readAt_eq_stateBefore h.valid.toScheduleWellFormed,
    V2.D.Engine.readAt_eq_stateBefore h.valid.toScheduleWellFormed]
  exact pcsa_clean_pc_indices_mono E rho h.noRestart hF x hx _ _
    (V2.D.Engine.read_length_mono t t' ht)
end AvailableChain.PCSA.Run

end
