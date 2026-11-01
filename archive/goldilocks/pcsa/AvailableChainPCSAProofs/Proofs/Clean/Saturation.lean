module
public import AvailableChainPCSAProofs.Proofs.Clean.Collect
public import AvailableChainPCSAProofs.Proofs.Clean.AckRun

public section

/-! C3 saturation in reachable stores and the Formation freeze interface. -/

namespace AvailableChain.PCSA
variable {n : Nat}

private theorem row_saturated (p : Params) (st : State p.n) (a : RowWire p.n)
    (h : PCSaturated st) : PCSaturated (admitRow p st a) := by
  delta admitRow
  cases a.decode? <;> dsimp only
  · exact h
  · split <;> exact pcsa_saturated_transfer _ _ h rfl rfl rfl (List.Subset.refl _)

/-- Every delivery leaves all collectable targets installed. -/
theorem pcsa_process_saturated (p : Params) (st : State p.n) (o : Wire p.n)
    (h : PCSaturated st) : PCSaturated (process p st o) := by
  delta process
  cases hd : o.decode with
  | none => exact h
  | some msg => cases msg with
    | vote s i r =>
      apply pcsa_saturated_transfer st _ h
      · exact GridCO.admitVote_blocks _ _ _
      · rfl
      · rfl
      · exact List.Subset.refl _
    | row i body => exact row_saturated p st _ h
    | ack s i r => exact pcsa_collectPCs_saturated _
    | pc C =>
      dsimp only
      delta admitPC
      split
      · exact pcsa_collectPCs_saturated _
      · exact h
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact h
      · cases parentFG st N.erase with
        | none => exact h
        | some P =>
          dsimp only
          split
          · apply List.foldlRecOn
            · exact pcsa_collectPCs_saturated _
            · intro acc ha a _
              exact row_saturated p acc a ha
          · exact h

private theorem normalize_saturated (st : State n) (h : PCSaturated st) :
    PCSaturated (normalizeS st) := by
  delta normalizeS
  split <;> exact pcsa_saturated_transfer _ _ h rfl rfl rfl (List.Subset.refl _)

private theorem gate_saturated (p : Params) (a : Block) (cs : List (PC n))
    (rank : Option PCRank) (st : State n) (s : Slot) (h : PCSaturated st) :
    PCSaturated (gateFrom p a cs rank st s) := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s <;> dsimp only
  · exact pcsa_saturated_transfer _ _ h rfl rfl rfl (List.Subset.refl _)
  · split
    · exact pcsa_saturated_transfer _ _ h rfl rfl rfl (List.Subset.refl _)
    · apply List.foldlRecOn
      · exact pcsa_saturated_transfer _ _ h rfl rfl rfl (List.Subset.refl _)
      · intro acc ha b _
        apply List.foldlRecOn
        · exact ha
        · intro acc' ha' g _
          exact pcsa_saturated_transfer _ _ ha' rfl rfl rfl (List.Subset.refl _)

/-- A clock changes none of the inputs to PC assembly. -/
theorem pcsa_clock_saturated (p : Params) (st : State p.n) (t : Time)
    (h : PCSaturated st) : PCSaturated (clock p st t) := by
  have hpre : PCSaturated (clockPre p st t) := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;>
      exact pcsa_saturated_transfer _ _ h rfl rfl rfl (List.Subset.refl _)
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    apply normalize_saturated
    split
    · exact hpre
    · exact gate_saturated p _ _ _ _ _ hpre
  · exact hpre

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} {m : FGMode}

/-- Saturation holds at every event state, including after a restart. -/
theorem pcsa_saturated_stateBefore (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (j : Nat) (y : V) :
    PCSaturated (V2.D.Run.stateBefore E rho j y).st := by
  have hz : PCSaturated (initial p.n) := by
    rw [PCSaturated_def]
    intro a ha
    exact (List.not_mem_nil ha).elim
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => PCSaturated nd.st) (Nat.zero_le j) y ?_ hz
  intro k e _ _ he hy h
  cases e with
  | restart x t =>
    change x = y at hy
    subst x
    change PCSaturated (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st
    rw [Function.update_self]
    exact hz
  | tick x t =>
    change x = y at hy
    subst x
    change PCSaturated (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k y) y t
    rw [ht]
    exact pcsa_clock_saturated p _ _ h
  | deliver x o t =>
    change x = y at hy
    subst x
    change PCSaturated (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st
    rw [Function.update_self]
    exact pcsa_process_saturated p _ (toWire p o) h

/-- Formation's hFreezeKeep: collection adds no PC at the freeze boundary.
Every collectable target is already installed before the freeze tick. -/
theorem pcsa_collectPCs_after_freeze (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c))
    (hv : V2.D.ScheduleWellFormed E rho) (hn : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) (y : V) (hy : y ∈ rho.honest) (s : Slot)
    (hh : SA.freezeTime p.toParams s ≤ rho.horizon) :
    (collectPCs (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st).pcs ⊆
      (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)).pcs := by
  have hs := pcsa_saturated_stateBefore E rho
    (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) y
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hv] at hs
  rw [pcsa_collectPCs_eq_of_saturated _ hs,
    pcsa_pcs_after_freeze E rho hv hn hdelta y hy s hh]

end AvailableChain.PCSA.Run
end
