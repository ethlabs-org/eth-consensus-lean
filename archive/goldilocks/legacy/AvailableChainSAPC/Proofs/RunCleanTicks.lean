module
public import AvailableChainSAPC.Proofs.RunCleanPath

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- A tick between early, HEAD, and gate duties adds only a possible
proposal PC source. An already sourced PC leaves the path unchanged. -/
theorem cleanRunPath_eq_between_duties {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (rho : Run V (sapc p)) (i : Nat) (reader : V) (t : Time)
    (he : rho.events[i]? = some (.tick reader t))
    (hne : ∀ r, t ≠ earlyTime p r) (hnh : ∀ r, t ≠ voteTime p r)
    (hng : ∀ r, t ≠ gateTime p r)
    (hproposal : ∀ r c, t = proposalTime p r → reader ∈ rho.honest →
      capBroken p (clock p (Run.stateBefore (sapc p) rho i reader) t) = false →
      (clock p (Run.stateBefore (sapc p) rho i reader) t).bestPC = some c →
      cleanRunPath p rho i c.target) :
    cleanRunPath p rho (i + 1) = cleanRunPath p rho i := by
  have old (j : Nat) (hj : j < i + 1) (v : V) (time : Time)
      (ht : rho.events[j]? = some (.tick v time)) (hn : t ≠ time) : j < i := by
    have hneq : j ≠ i := by
      rintro rfl
      exact hn (congrArg Event.time (Option.some.inj (he.symm.trans ht)))
    omega
  have source (c : Block) (hc : CleanRunSource p rho (i + 1) c) : cleanRunPath p rho i c := by
    have lift (h : CleanRunSource p rho i c) : cleanRunPath p rho i c :=
      Or.inr ⟨c, h, GridCO.block_preceq_self c⟩
    cases hc with
    | genuine j hj v hv r c ht hb =>
      exact lift (.genuine j (old j hj v _ ht (hng r)) v hv r _ ht hb)
    | timely r c cap src =>
      obtain ⟨v, hv, j, hj, ht, hb⟩ := src
      exact lift (.timely r _ cap ⟨v, hv, j, old j hj v _ ht (hne r), ht, hb⟩)
    | gate j hj v hv r cert ht ha hc =>
      exact lift (.gate j (old j hj v _ ht (hng r)) v hv r cert ht ha hc)
    | head j hj v hv r cert ht ha hc =>
      exact lift (.head j (old j hj v _ ht (hnh r)) v hv r cert ht ha hc)
    | proposal j hj v hv r cert ht ha hc =>
      by_cases hji : j < i
      · exact lift (.proposal j hji v hv r cert ht ha hc)
      · have hji : j = i := by omega
        subst j
        have eq := Option.some.inj (he.symm.trans ht)
        have hv' : reader = v := congrArg Event.node eq
        have ht' : t = proposalTime p r := congrArg Event.time eq
        subst v
        exact hproposal r cert ht' hv (ht'.symm ▸ ha) (ht'.symm ▸ hc)
  funext b
  apply propext
  constructor
  · rintro (hg | ⟨c, hc, hp⟩)
    · exact Or.inl hg
    · exact cleanRunPath_closed p rho i b c hp (source c hc)
  · exact cleanRunPath_mono p rho (Nat.le_succ i)

/-- Reuse the proved local clock step on the run-determined path. -/
theorem jointClean_tick_between_duties {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (i : Nat) (reader : V) (t : Time)
    (he : rho.events[i]? = some (.tick reader t))
    (hne : ∀ r, t ≠ earlyTime p r) (hnh : ∀ r, t ≠ voteTime p r)
    (hng : ∀ r, t ≠ gateTime p r) (h : JointCleanInvariant p E rho i)
    (hproposal : ∀ r c, t = proposalTime p r → reader ∈ rho.honest →
      capBroken p (clock p (Run.stateBefore (sapc p) rho i reader) t) = false →
      (clock p (Run.stateBefore (sapc p) rho i reader) t).bestPC = some c →
      cleanRunPath p rho i c.target) : JointCleanInvariant p E rho (i + 1) := by
  constructor
  · rw [cleanRunPath_eq_between_duties p rho i reader t he hne hnh hng hproposal]
    exact cleanPathFacts_tick_between_duties p E rho hx i reader t he hne hnh hng h.facts hproposal
  · apply h.ordered.step_of_no_gate
    intro v r ht
    exact hng r (congrArg Event.time (Option.some.inj (he.symm.trans ht)))

theorem jointClean_freeze {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (i : Nat) (reader : V) (r : Slot)
    (he : rho.events[i]? = some (.tick reader (freezeTime p r)))
    (h : JointCleanInvariant p E rho i) : JointCleanInvariant p E rho (i + 1) := by
  refine jointClean_tick_between_duties p E rho hx i reader _ he ?_ ?_ ?_ h ?_
  · intro s; exact duty_phase_ne p r s 3 2 (by decide) (by decide) (by decide)
  · intro s; simpa only [Nat.cast_one, one_mul] using!
      duty_phase_ne p r s 3 1 (by decide) (by decide) (by decide)
  · intro s heq
    apply duty_phase_ne p r (s + 1) 3 2 (by decide) (by decide) (by decide)
    change 4 * p.Δ * (r : Time) + 3 * p.Δ = 4 * p.Δ * (s : Time) + 6 * p.Δ at heq
    push_cast
    nlinarith
  · intro s c ht _ _ _
    apply False.elim
    apply duty_phase_ne p r s 3 0 (by decide) (by decide) (by decide)
    simpa only [Nat.cast_zero, zero_mul, add_zero] using! ht

/-- Under the cap, the installed PC's prior honest save is already a
canonical source. Proposal authority therefore adds no new path branch. -/
theorem jointClean_proposal_tick_capped {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (reader : V) (r : Slot)
    (he : rho.events[i]? = some (.tick reader (proposalTime p r)))
    (h : JointCleanInvariant p E rho i) : JointCleanInvariant p E rho (i + 1) := by
  set_option backward.isDefEq.respectTransparency false in
  refine jointClean_tick_between_duties p E rho hx i reader _ he ?_ ?_ ?_ h ?_
  · intro s; simpa only [Nat.cast_zero, zero_mul, add_zero] using!
      duty_phase_ne p r s 0 2 (by decide) (by decide) (by decide)
  · intro s; simpa only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_one, one_mul] using!
      duty_phase_ne p r s 0 1 (by decide) (by decide) (by decide)
  · intro s heq
    apply duty_phase_ne p r (s + 1) 0 2 (by decide) (by decide) (by decide)
    change 4 * p.Δ * (r : Time) = 4 * p.Δ * (s : Time) + 6 * p.Δ at heq
    push_cast
    nlinarith
  · intro s c _ hv _ hc
    rw [clock_bestPC] at hc
    have source := (h.facts.certificates i (le_refl _) reader hv c
      (installedPC_valid_before p rho reader i c hc)).1
    exact Or.inr ⟨c.target, .timely c.slot c.target cap source, GridCO.block_preceq_self _⟩

end AvailableChain.SAPC
end
