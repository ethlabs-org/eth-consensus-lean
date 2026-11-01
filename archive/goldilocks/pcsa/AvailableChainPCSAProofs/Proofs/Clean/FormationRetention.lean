module
public import AvailableChainPCSAProofs.Proofs.Clean.FormationAck
public import AvailableChainPCSAProofs.Proofs.Clean.AckStore
public import AvailableChainPCSAProofs.Proofs.Foundations.SnapshotRun
public import AvailableChainPCSAProofs.Proofs.Foundations.AckPool
public import AvailableChainKitV2.DutyEngineClock

public section

/-! Formation retention facts. The ack pool grows across deliveries and ticks.
NoRestart supplies the run input hAckPoolMono. -/

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- NoRestart closes hAckPoolMono at every node without a frame premise. -/
theorem pcsa_formation_run_ackPool_mono (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hNR : V2.D.NoRestart rho)
    (y : V) (i j : Nat) (hij : i ≤ j) :
    (V2.D.Run.stateBefore E rho i y).st.ackPool ⊆
      (V2.D.Run.stateBefore E rho j y).st.ackPool := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => (V2.D.Run.stateBefore E rho i y).st.ackPool ⊆ nd.st.ackPool)
    hij y ?_ (List.Subset.refl _)
  intro k e _ _ he hn hm
  cases e with
  | restart x t => exact (hNR k x t he).elim
  | tick x t =>
    change x = y at hn
    subst x
    change (V2.D.Run.stateBefore E rho i y).st.ackPool ⊆
      (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.ackPool
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k y) y t
    rw [ht, pcsa_clock_ackPool]
    exact hm
  | deliver x o t =>
    change x = y at hn
    subst x
    change (V2.D.Run.stateBefore E rho i y).st.ackPool ⊆
      (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.ackPool
    rw [Function.update_self]
    exact List.Subset.trans hm (pcsa_process_ackPool_mono p _ (toWire p o))
end AvailableChain.PCSA.Run
end
