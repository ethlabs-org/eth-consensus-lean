module
public import AvailableChainPCSAProofs.Proofs.Clean.AckAdmit
public import AvailableChainPCSAClaims.Statements.LaneReads
public import AvailableChainFGSA.Proofs.HeadResolution

public section

/-! CI StepAck: exact N targets and their body scope. -/

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- An honest ack has an exact, held, slot-correct N target in its duty state. -/
theorem pcsa_honestAck_N_source (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (s : Slot) (B : Block)
    (ha : HonestAckAt p c E rho x s B) :
    ∃ nd, pcsa_postClock E rho x (SA.earlyTime p.toParams s) = some nd ∧
      nTarget? p nd.st s = some B ∧ B.slot = s ∧ holdsN p (actView nd.st) s B = true ∧
      B ∈ nd.st.base.blocks := by
  have hh := ha.2.2
  rw [pcsa_ackAt_def] at hh
  obtain ⟨nd, hnd, hB⟩ := Option.map_eq_some_iff.mp hh
  have hn := (Option.filter_eq_some_iff.mp hB).1
  have ht := List.find?_some hn
  have hs : B.slot = s := beq_iff_eq.mp (Bool.and_eq_true_iff.mp ht).1
  have hN := (Bool.and_eq_true_iff.mp ht).2
  obtain ⟨o, _, hres⟩ := List.mem_filterMap.mp (List.mem_of_find?_eq_some hn)
  have hmem := (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hres)).1
  exact ⟨nd, hnd, hn, hs, hN, hmem⟩
/-- The N target of an honest ack is in the run's collision-freedom scope. -/
theorem pcsa_honestAck_body_scope (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (s : Slot) (B : Block)
    (ha : HonestAckAt p c E rho x s B) : RootBlockInRun p c E rho B := by
  obtain ⟨nd, hnd, _, _, _, hmem⟩ := pcsa_honestAck_N_source E rho x s B ha
  rw [pcsa_postClock_def] at hnd
  obtain ⟨before, hb, he⟩ := Option.map_eq_some_iff.mp hnd
  rw [pcsa_preTick_def] at hb
  obtain ⟨k, _, hk⟩ := Option.map_eq_some_iff.mp hb
  subst before
  have hs := pcsa_clock_body_scope p (RootBlockInRun p c E rho)
    (V2.D.Run.stateBefore E rho k x).st (SA.earlyTime p.toParams s)
    (pcsa_body_scope E rho k x ha.1)
  have hst : (clock p (V2.D.Run.stateBefore E rho k x).st
      (SA.earlyTime p.toParams s)) = nd.st := congrArg Node.st he
  exact hs B (hst.symm ▸ hmem)
end AvailableChain.PCSA.Run

end
