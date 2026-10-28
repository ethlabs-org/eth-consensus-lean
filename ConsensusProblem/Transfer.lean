module
public import ConsensusProblem.Properties
@[expose] public section

/-! # Transfer of trace properties along prefix-monotone maps (L0)

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

theorem AgreeAmong.map {R g t} (h : tr.AgreeAmong R g t) : (tr.map f).AgreeAmong R g t :=
  fun u v i j hi hj hu hv => (h u v i j hi hj hu hv).map hf

theorem MonotoneAmong.map {R g t} (h : tr.MonotoneAmong R g t) :
    (tr.map f).MonotoneAmong R g t :=
  fun v i j hi hij hj hv hw => hf (h v i j hi hij hj hv hw)

theorem Safe.map {g t} (h : tr.Safe g t) : (tr.map f).Safe g t :=
  ⟨AgreeAmong.map hf h.1, MonotoneAmong.map hf h.2⟩

theorem ReadySafe.map {c g t} (h : tr.ReadySafe c g t) : (tr.map f).ReadySafe c g t :=
  ⟨AgreeAmong.map hf h.1, MonotoneAmong.map hf h.2⟩

theorem Nested.map {g₁ g₂} (h : tr.Nested g₁ g₂) : (tr.map f).Nested g₁ g₂ := by
  intro v hv i hi
  exact hf (h v hv i hi)

theorem ProtectedUpTo.map {c src dst T b₀ b₁ b} (h : tr.ProtectedUpTo c src dst T b₀ b₁ b) :
    (tr.map f).ProtectedUpTo c src dst T b₀ b₁ b := by
  intro v hv t ht ht' w hw ha
  exact hf (h v hv t ht ht' w hw ha)
end Trace
end Consensus
end
