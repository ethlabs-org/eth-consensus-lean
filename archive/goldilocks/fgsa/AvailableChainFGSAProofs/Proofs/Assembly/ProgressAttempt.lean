module
public import AvailableChainFGSAProofs.Proofs.Finality.Export -- shake: keep (core types)
public import AvailableChainFGSAProofs.Proofs.Foundations.Export -- shake: keep (channels)

public section

namespace AvailableChain.FGSA.Run

/-- H2 supplies the four budget rows. This record does not assert their production. -/
structure ProgressAttemptRows (p : Params) (G ΔF : Time) : Prop where
  raise_contest : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      ∀ k ev, AttemptValid p c E rho k → rho.events[k.start]? = some ev →
        ev.time + attemptBudget p G k ≤ rho.horizon →
        k.task = .raise → k.phase = .contest →
        AttemptEndsBy p c E rho k (attemptBudget p G k)
  raise_other : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      ∀ k ev, AttemptValid p c E rho k → rho.events[k.start]? = some ev →
        ev.time + attemptBudget p G k ≤ rho.horizon →
        k.task = .raise → k.phase ≠ .contest →
        AttemptEndsBy p c E rho k (attemptBudget p G k)
  firstRow_contest : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      ∀ k ev, AttemptValid p c E rho k → rho.events[k.start]? = some ev →
        ev.time + attemptBudget p G k ≤ rho.horizon →
        k.task = .firstRow → k.phase = .contest →
        AttemptEndsBy p c E rho k (attemptBudget p G k)
  firstRow_other : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      ∀ k ev, AttemptValid p c E rho k → rho.events[k.start]? = some ev →
        ev.time + attemptBudget p G k ≤ rho.horizon →
        k.task = .firstRow → k.phase ≠ .contest →
        AttemptEndsBy p c E rho k (attemptBudget p G k)

/-- Four exact family rows compose to the unchanged public statement. -/
theorem healing_progressAttemptStatement (p : Params) (G ΔF : Time)
    (rows : ProgressAttemptRows p G ΔF) : ProgressAttemptStatement p G ΔF := by
  intro hδ V _ _ In c E rho hset hbound k ev hvalid hstart hhor
  cases ht : k.task with
  | raise =>
    by_cases hp : k.phase = .contest
    · exact rows.raise_contest hδ c E rho hset hbound k ev hvalid hstart hhor ht hp
    · exact rows.raise_other hδ c E rho hset hbound k ev hvalid hstart hhor ht hp
  | firstRow =>
    by_cases hp : k.phase = .contest
    · exact rows.firstRow_contest hδ c E rho hset hbound k ev hvalid hstart hhor ht hp
    · exact rows.firstRow_other hδ c E rho hset hbound k ev hvalid hstart hhor ht hp

end AvailableChain.FGSA.Run
end
