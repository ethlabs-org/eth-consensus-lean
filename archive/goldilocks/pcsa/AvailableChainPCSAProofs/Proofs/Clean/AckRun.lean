module
public import AvailableChainPCSAProofs.Proofs.Clean.AckStore
public import AvailableChainPCSAProofs.Proofs.Foundations.SnapshotRun

public section

/-! C3 cumulative ack pools in runs and held PCs through the freeze tick
(pcsa34-r4.3 §3.6, §5.2.3). -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} {m : FGMode}

/-- In a run without restarts, later event states keep every pooled ack. -/
theorem pcsa_ackPool_stateBefore_mono (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hn : V2.D.NoRestart rho)
    (y : V) {j k : Nat} (hjk : j ≤ k) :
    (V2.D.Run.stateBefore E rho j y).st.ackPool ⊆
      (V2.D.Run.stateBefore E rho k y).st.ackPool := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => (V2.D.Run.stateBefore E rho j y).st.ackPool ⊆ nd.st.ackPool)
    hjk y ?_ (List.Subset.refl _)
  intro l e _ _ he hy h
  cases e with
  | restart x t => exact (hn l x t he).elim
  | tick x t =>
    change x = y at hy
    subst x
    change _ ⊆ (Function.update (V2.D.Run.stateBefore E rho l) y _ y).st.ackPool
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho l y) y t
    rw [ht, pcsa_clock_ackPool]
    exact h
  | deliver x o t =>
    change x = y at hy
    subst x
    change _ ⊆ (Function.update (V2.D.Run.stateBefore E rho l) y _ y).st.ackPool
    rw [Function.update_self]
    exact List.Subset.trans h (pcsa_process_ackPool_mono p _ (toWire p o))

/-- The freeze clock preserves held PCs exactly. Assembly must occur on a
receipt before this clock; it is not part of the freeze tick. -/
theorem pcsa_freeze_pcs (st : State p.n) (s : Slot) :
    (clock p st (SA.freezeTime p.toParams s)).pcs = st.pcs := by
  rw [clock_freeze, clockPre_pcs]

/-- The after-ticks PC set at the freeze is exactly the strict pre-time
PC set. This closes preservation of PCs already assembled before the tick. -/
theorem pcsa_pcs_after_freeze (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c))
    (hv : V2.D.ScheduleWellFormed E rho) (hn : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) (y : V) (hy : y ∈ rho.honest) (s : Slot)
    (hh : SA.freezeTime p.toParams s ≤ rho.horizon) :
    (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)).pcs =
      (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st.pcs := by
  have hpublic : V2.PublicTime E (SA.freezeTime p.toParams s) := by
    refine ⟨4 * s + 3, ?_⟩
    rw [hdelta]
    change 4 * p.Δ * (s : Int) + 3 * p.Δ = ((4 * s + 3 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hz : 0 ≤ SA.freezeTime p.toParams s := by
    have hd := p.deltaPos
    change 0 ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    positivity
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hv.tick_total y hy _ hpublic hz hh)
  change (FGSA.Run.afterTicks E rho (SA.freezeTime p.toParams s) y).st.pcs = _
  rw [FGSA.Run.afterTicks_eq_tick_preTick E rho hv hn hi]
  have ht := pcsa_tick_st E rho
    (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y) y
    (SA.freezeTime p.toParams s)
  rw [ht, pcsa_freeze_pcs]

end AvailableChain.PCSA.Run
end
