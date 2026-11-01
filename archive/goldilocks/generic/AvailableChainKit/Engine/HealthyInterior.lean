module
public import AvailableChainKit.Engine.RunPrefix

@[expose] public section
namespace AvailableChain.Engine
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- A proof environment with the original awake schedule. Only GST is
set to zero. Use a strict healthy cutoff to retain its count premise. -/
def genesisEnv {V : Type} (E : Env V) : Env V :=
  { E with t_GST := 0, t_GST_nonneg := le_refl 0 }

/-- A closed prefix strictly before the healthy boundary is Sleepy.
The cutoff may contain a proposal duty: no emission or root scope is
added, since the original awake schedule is retained. -/
theorem healthyInterior_sleepy {V : Type} [DecidableEq V] [Fintype V]
    {n : Nat} {P : ProtocolSpec n} {E : Env V} {rho : Run V P}
    (hx : ExecutionValid P E rho) (I : Interface P) (boundary cut : Time)
    (nonneg : 0 ≤ cut) (before : cut < boundary) (hh : cut ≤ rho.horizon)
    (roots : RootInjective E I rho)
    (healthy : HealthyPrefixDelivery P E rho boundary)
    (majority : ∀ t, 0 ≤ t → t < boundary → AwakeMajority E rho t) :
    SleepyRegime P (genesisEnv E) I (runPrefix rho cut) 0 := by
  have hs := hx.toScheduleWellFormed
  have execution : ExecutionValid P (genesisEnv E) rho :=
    { hx with }
  have deadline (t : Time) (ht : 0 ≤ t) :
      max t (genesisEnv E).t_GST + (genesisEnv E).Δ = t + E.Δ :=
    congrArg (fun x => x + E.Δ) (max_eq_left ht)
  refine ⟨runPrefix_execution execution cut nonneg hh, ?_, ?_, rfl, rfl, ?_⟩
  · have scope (b : Block) (hb : BlockInRun (genesisEnv E) I (runPrefix rho cut) b) :
        BlockInRun E I rho b := by
      rcases hb with hg | ⟨v, o, t, tip, hp | he, block, ancestor⟩
      · exact Or.inl hg
      · exact Or.inr ⟨v, o, t, tip,
          Or.inl ((runPrefix_processes_iff hs cut v o t).mp hp).1, block, ancestor⟩
      · exact Or.inr ⟨v, o, t, tip,
          Or.inr ((runPrefix_emits_iff hs cut (genesisEnv E) v o t).mp he).1,
          block, ancestor⟩
    exact fun b c hb hc => roots b c (scope b hb) (scope c hc)
  · constructor
    · intro v hv o t he w hw bound excl
      obtain ⟨emit, _⟩ := (runPrefix_emits_iff hs cut (genesisEnv E) v o t).mp he
      obtain ⟨i, tick, mem⟩ := emit
      have ht : 0 ≤ t := (hs.in_horizon _ (List.mem_of_getElem? tick)).1
      rw [deadline t ht] at bound excl
      rw [runPrefix_stateBeforeTime hs cut _ bound] at excl
      obtain ⟨t', lo, hi, j, handles⟩ :=
        healthy.broadcast v hv o t ⟨i, tick, mem⟩ w hw (bound.trans before.le) excl
      exact ⟨t', lo, (deadline t ht).symm ▸ hi, j,
        (runPrefix_handlesAt_iff hs cut j w o t').mpr ⟨handles, hi.le.trans bound⟩⟩
    · intro v hv i o t accept w hw fresh bound excl
      obtain ⟨orig, time⟩ := (runPrefix_acceptsAt_iff hs cut i v o t).mp accept
      obtain ⟨obj, delivery, _⟩ := orig.1
      have ht : 0 ≤ t := (hs.in_horizon _ (List.mem_of_getElem? delivery)).1
      rw [deadline t ht] at bound excl
      rw [runPrefix_stateBeforeTime hs cut _ bound] at excl
      have hi := (index_lt_read_length_iff hs cut delivery).mpr time
      rw [runPrefix_stateBefore cut (i + 1) (Nat.succ_le_of_lt hi)] at fresh
      obtain ⟨t', lo, hi', j, handles⟩ :=
        healthy.relay v hv i o t orig w hw fresh (bound.trans before.le) excl
      exact ⟨t', lo, (deadline t ht).symm ▸ hi', j,
        (runPrefix_handlesAt_iff hs cut j w o t').mpr ⟨handles, hi'.le.trans bound⟩⟩
  · intro t ht bound
    exact majority t ht (bound.trans_lt before)

end AvailableChain.Engine
end
