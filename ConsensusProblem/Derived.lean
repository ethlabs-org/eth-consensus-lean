module
public import ConsensusProblem.Properties
public import ConsensusProblem.Network

@[expose] public section

/-! # Derived notions (L0, outside the trusted surface)

Not needed to read `Good`: no definition of `Behaviour`, `Adequate`,
`Realizable` or `Good`, and no L1/L2 definition that the endpoints read, uses
them. They are read by the L0 facts (`Facts/*`), the Goldilocks sheet and the
refinement proofs. Names and bodies are those of the trusted files they came
from. -/

namespace Consensus

namespace EnvPoint

variable {V : Type} [Fintype V] [DecidableEq V] (p : EnvPoint V)

/-- Fewer than fraction `β` of all validators are faulty. -/
def FaultsBelow (β : ℚ) : Prop := (p.faulty.card : ℚ) < β * Fintype.card V

end EnvPoint

namespace Trace

variable {V α Id : Type} (tr : Trace V α Id)

/-- The same trace with every read mapped by `f`. -/
def map {β : Type} (f : List α → List β) : Trace V β Id :=
  ⟨tr.point, tr.cuts, tr.cutTime, fun g v i => f (tr.read g v i)⟩

/-- No two honest reads of `g` at cuts from `t₀` on conflict. -/
abbrev Agree (g : Id) (t₀ : Time) : Prop := tr.AgreeAmong (fun v _ => v ∈ tr.point.honest) g t₀

/-- Safety of `g` from `t₀`. -/
def Safe (g : Id) (t₀ : Time) : Prop := tr.Agree g t₀ ∧ tr.Monotone g t₀

/-- `ReadySafe` restricted to cuts at times `≤ b`: the past up to `b` is safe
for ready readers. -/
def ReadySafeUpTo (c : Time) (g : Id) (t₀ b : Time) : Prop :=
  (∀ u v i j, tr.InCuts t₀ i → tr.InCuts t₀ j → tr.cutTime i ≤ b → tr.cutTime j ≤ b →
      tr.point.Ready c u (tr.cutTime i) → tr.point.Ready c v (tr.cutTime j) →
      Compatible (tr.read g u i) (tr.read g v j)) ∧
  (∀ v i j, tr.InCuts t₀ i → i ≤ j → tr.InCuts t₀ j → tr.cutTime j ≤ b →
      tr.point.Ready c v (tr.cutTime i) → tr.point.Ready c v (tr.cutTime j) →
      tr.read g v i <+: tr.read g v j)

end Trace

namespace CommLog

variable {V M : Type} (p : EnvPoint V) (L : CommLog V M)

/-- No honest send before time `0`. Every valid model run's log has this
(`Model.Run.log_sendsFromZero`). -/
def SendsFromZero : Prop := ∀ v ∈ p.honest, ∀ m t, L.sent v m t → 0 ≤ t

end CommLog

end Consensus

end
