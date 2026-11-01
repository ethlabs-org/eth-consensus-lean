module
public import AvailableChainPCSAProofs.Proofs.Foundations.OutputState
public import AvailableChainPCSAClaims.Statements.Reads
public import AvailableChainGeneric.Proofs.V2.Duty.Induction

public section

/-! Store reachability in the PC-SA engine (proof plan §3; FG-SA Reachable template). -/

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Every indexed run state has a reachable store, also after a restart. -/
theorem pcsa_reachable_stateBefore (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (i : Nat) (v : V) : Reachable p (V2.D.Run.stateBefore E rho i v).st := by
  refine Gen.V2.Duty.invariant_triple (P := pcsaWith m p c)
    (fun nd : Node p => Reachable p nd.st) ?_ ?_ ?_ ?_ ?_ E rho i v
  · exact Reachable.init
  · intro nd t h; exact Reachable.tick t h
  · intro nd o h; exact Reachable.deliver (toWire p o) h
  · intro nd o h; exact h
  · intro nd _; exact Reachable.init

/-- The inclusive time reader has a reachable store without a schedule premise. -/
theorem reachable_storeAt (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (t : Time) (v : V) : Reachable p (storeAt p c E rho v t) := by
  let rho' := { rho with events := rho.events.filter (fun e => decide (e.time ≤ t)) }
  have hs : V2.D.World.step E rho' = V2.D.World.step E rho := by
    funext w e
    cases e <;> rfl
  have h := pcsa_reachable_stateBefore E rho' rho'.events.length v
  change Reachable p ((rho'.events.take rho'.events.length).foldl
    (V2.D.World.step E rho') V2.D.World.init v).st at h
  rw [List.take_length, hs] at h
  exact h

/-- All duties use the store after the clock; recording own rows changes only Λ. -/
theorem pcsa_tick_st (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (nd : Node p) (v : V) (t : Time) :
    (V2.D.tick E rho nd v t).1.st = clock p nd.st t := by
  unfold V2.D.tick
  dsimp only
  apply List.foldlRecOn (motive := fun nd' : Node p => nd'.st = clock p nd.st t)
  · rfl
  · intro nd' h o _
    exact h

/-- The after-ticks reader also has a reachable store. -/
theorem reachable_storeAfterTicks (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (t : Time) (v : V) : Reachable p (storeAfterTicks p c E rho v t) := by
  let rho' := { rho with events := rho.events.filter (cutPred t) }
  have hs : V2.D.World.step E rho' = V2.D.World.step E rho := by
    funext w e
    cases e <;> rfl
  have h := pcsa_reachable_stateBefore E rho' rho'.events.length v
  change Reachable p ((rho'.events.take rho'.events.length).foldl
    (V2.D.World.step E rho') V2.D.World.init v).st at h
  rw [List.take_length, hs] at h
  exact h

end AvailableChain.PCSA.Run
end
