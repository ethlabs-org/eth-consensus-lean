module
public import AvailableChainSAPC.Proofs.RunCleanHeads
public import AvailableChainSAPC.Proofs.RunCleanTicks

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- The mode proof is retained at every later event input. No schedule,
participation, or fault-count premise is needed for this local fact. -/
theorem capBroken_before_mono {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) {i j : Nat} (hij : i ≤ j) (reader : V)
    (disabled : capBroken p (Run.stateBefore (sapc p) rho i reader) = true) :
    capBroken p (Run.stateBefore (sapc p) rho j reader) = true :=
  capBroken_mono p _ _ (stateBefore_archive_mono p rho hij reader) disabled

theorem clockPreGate_archive (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clockPreGate p st t).receivedHeads = st.receivedHeads := by
  unfold clockPreGate
  dsimp only
  split_ifs <;> simp only [saveTimely]
  all_goals (try split_ifs) <;> rfl

/-- The complete disabled clock projects to SA, including the raw history
and lease map. It starts from the current base state. -/
theorem clock_base_of_capBroken (p : Params) {n : Nat} (st : State n) (t : Time)
    (disabled : capBroken p st = true) :
    (clock p st t).base = SA.clock p st.base t := by
  have hd : capBroken p (clockPreGate p st t) = true := by
    simpa only [capBroken, archiveEquivocators, clockPreGate_archive] using! disabled
  rw [clock_eq_gate_prestate, SA.clock,
    @GridCO.clock_eq_gate_prestate GridCO.slowLeasePolicy]
  dsimp only
  simp only [show p.engine.Δ = p.Δ from rfl,
    show GridCO.gateTime p.engine = gateTime p from rfl]
  change (if 0 ≤ t - 6 * p.Δ && t == gateTime p ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
    then gate p (clockPreGate p st t) ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
    else clockPreGate p st t).base = _
  split_ifs
  · rw [gate_base_of_capBroken p _ _ hd, clockPreGate_base]
  · exact clockPreGate_base p st t

/-- Once disabled, every later clock at this reader uses the SA clock.
This is a local projection; receipt streams still contain SA-PC objects. -/
theorem clock_base_after_capBroken {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) {i j : Nat} (hij : i ≤ j) (reader : V) (t : Time)
    (disabled : capBroken p (Run.stateBefore (sapc p) rho i reader) = true) :
    (clock p (Run.stateBefore (sapc p) rho j reader) t).base =
      SA.clock p (Run.stateBefore (sapc p) rho j reader).base t :=
  clock_base_of_capBroken p _ t (capBroken_before_mono p rho hij reader disabled)

/-- A receipt that changes mode retains the full input invariant. This
uses the existing uncapped delivery proof, including finite sources. -/
theorem jointClean_mode_change {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (t₀ : Time)
    (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (reader : V) (obj : Wire p.n) (t : Time)
    (he : rho.events[i]? = some (.deliver reader obj t))
    (h : JointCleanInvariant p E rho i)
    (disabled : capBroken p (process p (Run.stateBefore (sapc p) rho i reader) obj) = true) :
    JointCleanInvariant p E rho (i + 1) ∧
      ∀ j, i + 1 ≤ j → capBroken p (Run.stateBefore (sapc p) rho j reader) = true := by
  refine ⟨jointClean_delivery_of_sleepy p E rho t₀ hs i reader obj t he h, ?_⟩
  intro j hj
  apply capBroken_before_mono p rho hj reader
  rw [stateBefore_succ_event he]
  simpa only [World.step, sapc, Function.update_self] using disabled

/-- A disabled tick between duties, including a proposal, adds no PC
authority. The current source path and all historical facts survive. -/
theorem jointClean_tick_between_duties_disabled {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (i : Nat) (reader : V) (t : Time)
    (he : rho.events[i]? = some (.tick reader t))
    (hne : ∀ r, t ≠ earlyTime p r) (hnh : ∀ r, t ≠ voteTime p r)
    (hng : ∀ r, t ≠ gateTime p r) (h : JointCleanInvariant p E rho i)
    (disabled : capBroken p (Run.stateBefore (sapc p) rho i reader) = true) :
    JointCleanInvariant p E rho (i + 1) := by
  set_option backward.isDefEq.respectTransparency false in
  apply jointClean_tick_between_duties p E rho hx i reader t he hne hnh hng h
  intro _ _ _ _ active
  rw [capBroken_clock, disabled] at active
  cases active

end AvailableChain.SAPC
end
