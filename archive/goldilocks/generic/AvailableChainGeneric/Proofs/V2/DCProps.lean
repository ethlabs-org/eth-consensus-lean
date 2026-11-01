module
public import AvailableChainGeneric.Statements.V2.DCProps
public import AvailableChainGeneric.Statements.Pure.Props

public section

namespace AvailableChain.Gen.V2

open AvailableChain AvailableChain.V2

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}

/-- DC: DecoupledConsensusStatements/Generic/Properties.lean:34 (b241081, 2026-09-28).
GLY r3.19 G37:1039 and S035:1340. Both directions hold without extra premises.
Use `Time`, honest nodes, `outputAt`, and the closed interval from `t₀` to the horizon
in `AvailableChainGeneric/Statements/Pure/Props.lean:24`. -/
theorem compatOn_iff_agreeFrom (E : Generic.Env V) (rho : Run V P)
    (g : Output P) (t₀ : Time) :
    Pure.CompatOn (fun v => v ∈ rho.honest) (fun t v => outputAt E rho g v t)
      (fun t => t₀ ≤ t ∧ t ≤ rho.horizon) ↔ AgreeFrom P E rho g t₀ := by
  constructor
  · intro h u hu v hv t t' ht hh ht' hh'
    exact h t t' u v ⟨ht, hh⟩ ⟨ht', hh'⟩ hu hv
  · intro h t t' u v ht ht' hu hv
    exact h u hu v hv t t' ht.1 ht.2 ht'.1 ht'.2

/-- DC: DecoupledConsensusStatements/Generic/Properties.lean:40 (b241081, 2026-09-28).
GLY r3.19 G37:1039 and S037:1345. Both directions hold without extra premises.
For `MonoOn` in `AvailableChainGeneric/Statements/Pure/Props.lean:48`, transitivity
gives `t ≤ rho.horizon` and `t₀ ≤ t'` from DC's three ordered bounds. -/
theorem monoOn_iff_monotoneFrom (E : Generic.Env V) (rho : Run V P)
    (g : Output P) (t₀ : Time) :
    Pure.MonoOn (fun v => v ∈ rho.honest) (fun t v => outputAt E rho g v t)
      (fun t => t₀ ≤ t ∧ t ≤ rho.horizon) ↔ MonotoneFrom P E rho g t₀ := by
  constructor
  · intro h v hv t t' ht htt' hh'
    exact h t t' v ⟨ht, le_trans htt' hh'⟩ ⟨le_trans ht htt', hh'⟩ htt' hv
  · intro h t t' v ht ht' htt' hv
    exact h v hv t t' ht.1 htt' ht'.2

/-- DC: DecoupledConsensusStatements/Generic/Properties.lean:48 (b241081, 2026-09-28).
GLY r3.19 G37:1039. Both directions hold without extra premises.
The `CompatOn` and `MonoOn` pair in `AvailableChainGeneric/Statements/Pure/Props.lean`
gives the `agree` and `monotone` fields in that order. -/
theorem compatOn_monoOn_iff_safeFrom (E : Generic.Env V) (rho : Run V P)
    (g : Output P) (t₀ : Time) :
    (Pure.CompatOn (fun v => v ∈ rho.honest) (fun t v => outputAt E rho g v t)
        (fun t => t₀ ≤ t ∧ t ≤ rho.horizon) ∧
      Pure.MonoOn (fun v => v ∈ rho.honest) (fun t v => outputAt E rho g v t)
        (fun t => t₀ ≤ t ∧ t ≤ rho.horizon)) ↔ SafeFrom P E rho g t₀ := by
  constructor
  · intro h
    exact ⟨(compatOn_iff_agreeFrom E rho g t₀).mp h.1,
      (monoOn_iff_monotoneFrom E rho g t₀).mp h.2⟩
  · intro h
    exact ⟨(compatOn_iff_agreeFrom E rho g t₀).mpr h.agree,
      (monoOn_iff_monotoneFrom E rho g t₀).mpr h.monotone⟩

/-- DC: DecoupledConsensusStatements/Generic/Properties.lean:124,86 (b241081, 2026-09-28).
GLY r3.19 G37:1039. Both directions hold without extra premises on `T` or `b₀`.
`ServedOn` in `AvailableChainGeneric/Statements/Pure/Props.lean:73` is DC's `InBy`
at every time in the closed interval. Only the binder and premise order changes. -/
theorem persistsFrom_iff_servedOn (E : Generic.Env V) (rho : Run V P)
    (g : Output P) (T b₀ : Time) :
    PersistsFrom P E rho g T b₀ ↔
      ∀ v ∈ rho.honest, ∀ B, Block.Preceq B (outputAt E rho g v T) →
        Pure.ServedOn (fun v => v ∈ rho.honest) (fun t v => outputAt E rho g v t) B
          (fun t => b₀ ≤ t ∧ t ≤ rho.horizon) := by
  constructor
  · intro h v hv B hB t u ht hu
    exact h v hv B hB t ht.1 ht.2 u hu
  · intro h v hv B hB t ht hh u hu
    exact h v hv B hB t u ⟨ht, hh⟩ hu

end AvailableChain.Gen.V2
