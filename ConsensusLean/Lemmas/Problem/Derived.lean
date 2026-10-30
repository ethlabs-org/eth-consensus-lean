module
public import ConsensusLean.Spec.Problem.Properties
public import ConsensusLean.Spec.Problem.Network

public section

/-! # Derived notions read by instance statements (L0; tag-protected, not a trusted layer)

Not needed to read `Good`: no definition of `Behaviour`, `Adequate`,
`Realizable` or `Good`, and no L1/L2 definition that the endpoints read, uses
them. They are read by the Goldilocks baseline sheet, so this file is in
`trusted_paths` (#38); it holds only those definitions and their characterising
lemmas (which must sit with the unexposed bodies, plan §3). Other derived notions
and their lemmas go in `DerivedFacts.lean`, which is not protected. Names and
bodies are those of the trusted files they came from. -/

namespace Consensus

namespace EnvPoint

variable {V : Type} [Fintype V] [DecidableEq V] (p : EnvPoint V)

/-- Fewer than fraction `β` of all validators are faulty. -/
def FaultsBelow (β : ℚ) : Prop := (p.faulty.card : ℚ) < β * Fintype.card V

variable {p} in
theorem faultsBelow_iff {β : ℚ} : p.FaultsBelow β ↔ (p.faulty.card : ℚ) < β * Fintype.card V :=
  Iff.rfl

end EnvPoint

namespace Trace

variable {V α Id : Type} (tr : Trace V α Id)

/-- No two honest reads of `g` at cuts from `t₀` on conflict. -/
abbrev Agree (g : Id) (t₀ : Time) : Prop := tr.AgreeAmong (fun v _ => v ∈ tr.point.honest) g t₀

/-- Safety of `g` from `t₀`. -/
def Safe (g : Id) (t₀ : Time) : Prop := tr.Agree g t₀ ∧ tr.Monotone g t₀

variable {tr} in
theorem safe_iff {g : Id} {t₀ : Time} : tr.Safe g t₀ ↔ tr.Agree g t₀ ∧ tr.Monotone g t₀ := Iff.rfl

/-- `ReadySafe` restricted to cuts at times `≤ b`: the past up to `b` is safe
for ready readers. -/
def ReadySafeUpTo (c : Time) (g : Id) (t₀ b : Time) : Prop :=
  (∀ u v i j, tr.InCuts t₀ i → tr.InCuts t₀ j → tr.cutTime i ≤ b → tr.cutTime j ≤ b →
      tr.point.Ready c u (tr.cutTime i) → tr.point.Ready c v (tr.cutTime j) →
      Compatible (tr.read g u i) (tr.read g v j)) ∧
  (∀ v i j, tr.InCuts t₀ i → i ≤ j → tr.InCuts t₀ j → tr.cutTime j ≤ b →
      tr.point.Ready c v (tr.cutTime i) → tr.point.Ready c v (tr.cutTime j) →
      tr.read g v i <+: tr.read g v j)

variable {tr} in
theorem readySafeUpTo_iff {c : Time} {g : Id} {t₀ b : Time} : tr.ReadySafeUpTo c g t₀ b ↔
    ((∀ u v i j, tr.InCuts t₀ i → tr.InCuts t₀ j → tr.cutTime i ≤ b → tr.cutTime j ≤ b →
      tr.point.Ready c u (tr.cutTime i) → tr.point.Ready c v (tr.cutTime j) →
      Compatible (tr.read g u i) (tr.read g v j)) ∧
    (∀ v i j, tr.InCuts t₀ i → i ≤ j → tr.InCuts t₀ j → tr.cutTime j ≤ b →
      tr.point.Ready c v (tr.cutTime i) → tr.point.Ready c v (tr.cutTime j) →
      tr.read g v i <+: tr.read g v j)) := Iff.rfl

end Trace

end Consensus

end
