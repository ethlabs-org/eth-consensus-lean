module
public import ConsensusProblem.Properties
@[expose] public section

/-! # Transfer of trace properties along prefix-monotone maps (layer 0)

Mapping every read of a trace by a function that preserves prefixes (for
example, from block chains to transaction ledgers) preserves every
prefix-based property. -/

namespace Consensus

/-- Compatibility transfers along a prefix-monotone map. -/
theorem Compatible.map {α β : Type} {f : List α → List β}
    (hf : ∀ {a b}, a <+: b → f a <+: f b) {a b : List α}
    (h : Compatible a b) : Compatible (f a) (f b) := h.imp hf hf

namespace Trace
variable {V α β Id : Type} {tr : Trace V α Id} {f : List α → List β}
    (hf : ∀ {a b}, a <+: b → f a <+: f b)

include hf

theorem Agree.map {g t} (h : tr.Agree g t) : (tr.map f).Agree g t := by
  intro u hu v hv i j hi hj
  exact (h u hu v hv i j hi hj).map hf

theorem Monotone.map {g t} (h : tr.Monotone g t) : (tr.map f).Monotone g t := by
  intro v hv i j hi hij hj
  exact hf (h v hv i j hi hij hj)

theorem Safe.map {g t} (h : tr.Safe g t) : (tr.map f).Safe g t :=
  ⟨h.1.map hf, h.2.map hf⟩

theorem ReadySafe.map {c g t} (h : tr.ReadySafe c g t) : (tr.map f).ReadySafe c g t := by
  constructor
  · intro u v i j hi hj hu hv
    exact (h.1 u v i j hi hj hu hv).map hf
  · intro v i j hi hij hj hv hw
    exact hf (h.2 v i j hi hij hj hv hw)

theorem Nested.map {g₁ g₂} (h : tr.Nested g₁ g₂) : (tr.map f).Nested g₁ g₂ := by
  intro v hv i hi
  exact hf (h v hv i hi)

theorem ProtectedThrough.map {c src dst T b₀ b₁} (h : tr.ProtectedThrough c src dst T b₀ b₁) :
    (tr.map f).ProtectedThrough c src dst T b₀ b₁ := by
  intro v hv t ht ht' w hw ha
  exact hf (h v hv t ht ht' w hw ha)

theorem CompatibleThrough.map {c src dst T b₀ b₁} (h : tr.CompatibleThrough c src dst T b₀ b₁) :
    (tr.map f).CompatibleThrough c src dst T b₀ b₁ := by
  intro v hv t ht ht' w hw ha
  exact (h v hv t ht ht' w hw ha).map hf
end Trace
end Consensus
end
