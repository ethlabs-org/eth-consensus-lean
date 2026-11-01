module
public import AvailableChainPCSAProofs.Proofs.Recovery.RunInputs
public import AvailableChainPCSAProofs.Proofs.Shared.StageRun

public section

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- C8's strong-output bound also bounds the proposer base in stage one. -/
theorem recovery_base_of_arm (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho)
    (hf : StageOneFrame p c E rho) (cA : Slot) (P : Block)
    (x : V) (hx : x ∈ rho.honest)
    (hs : PCStampedBefore p c E rho x (SA.freezeTime p.toParams cA) cA P)
    (hstrong : ∀ t t' : Time, t ≤ t' →
      (∃ pc ∈ (storeAt p c E rho x t).pcs, pc.slot = cA ∧ pc.target = P) →
      Block.Preceq P (strong (storeAt p c E rho x t')))
    (t : Time)
    (ht : SA.freezeTime p.toParams cA < t)
    (nd : Node p) (hn : pcsa_postClock E rho x t = some nd) :
    Block.Preceq P (walkBase p nd.st (proposerPC p nd.st)) := by
  rw [pcsa_postClock_def] at hn
  obtain ⟨pre, hpre, he⟩ := Option.map_eq_some_iff.mp hn
  rw [pcsa_preTick_def] at hpre
  obtain ⟨k, hk, hpre⟩ := Option.map_eq_some_iff.mp hpre
  subst pre
  subst nd
  have hev := V2.D.Run.tickIdx?_spec hk
  have hnext : (V2.D.Run.stateBefore E rho (k + 1) x).st =
      clock p (V2.D.Run.stateBefore E rho k x).st t := by
    rw [V2.D.Run.stateBefore_succ E rho hev]
    change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st = _
    rw [Function.update_self]
    exact pcsa_tick_st E rho _ x t
  have hframe := hf x hx (k + 1)
  have ho := pcsa_outageStore_stateBefore E rho (k + 1) x hx
  rw [hnext] at hframe ho
  have hactive : (clock p (V2.D.Run.stateBefore E rho k x).st t).pcs.filter
      (frameActive p (clock p (V2.D.Run.stateBefore E rho k x).st t)) =
      (clock p (V2.D.Run.stateBefore E rho k x).st t).pcs := by
    apply List.filter_eq_self.mpr
    intro pc hpc
    exact (pcsa_frameActive_vacuous p _ hframe pc).mpr (ho.lift _ (ho.pcBlocks pc hpc))
  have hread : (V2.D.Run.stateBefore E rho k x).st = storeAt p c E rho x (t - 1) := by
    rw [V2.D.Engine.stateBefore_tick_eq_stateBeforeTime
      h hnr hev, storeAt_def]
    unfold V2.D.Run.stateBeforeTime V2.D.Run.readAt
    simp only [Int.le_sub_one_iff]
  have hbound := hstrong (SA.freezeTime p.toParams cA) (t - 1) (Int.le_sub_one_iff.mpr ht)
    (recovery_stampRead E rho h hnr hf x hx _ cA P hs)
  change Block.Preceq P (walkBase p (clock p (V2.D.Run.stateBefore E rho k x).st t)
    (proposerPC p (clock p (V2.D.Run.stateBefore E rho k x).st t)))
  rw [recovery_proposer_base]
  unfold proposerPC
  rw [hactive, hframe.2.1]
  change Block.Preceq P (strong (clock p (V2.D.Run.stateBefore E rho k x).st t))
  unfold strong pcTarget? latestPC
  rw [clock_pcs_eq, hread]
  exact hbound

end AvailableChain.PCSA.Run
end
