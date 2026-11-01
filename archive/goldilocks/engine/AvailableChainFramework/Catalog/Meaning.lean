module
public import AvailableChainFramework.Catalog.Core

@[expose] public section

/-! Meaning pins (async M2). For each core claim, `holds` and `inhabited` in
the Phase 0 form, with L1 predicates only. A change to a claim that changes
its meaning breaks a pin. The one intended difference from Phase 0
(`Claim.lean` at `505b14a`) is the late trigger of `includedConfirmed`:
`H ≤ proposalTime s`. A `True` trigger or regime is left out; the reverse
direction supplies `trivial`, so a change to it breaks the pin. -/

namespace AvailableChain.Framework.Catalog

open AvailableChain AvailableChain.Generic AvailableChain.Statements.Generic

theorem safeConfirmed_holds_iff (I : Instance) :
    safeConfirmed.holds I () ↔
      ∀ (W : Validators) (E : Env W.V), E.Δ = I.Δ → ∀ (rho : Run W.V I.P) (t₀ : Time),
        SleepyRegime I.P E I.iface rho t₀ → SafeFrom I.P rho I.iface.confirmed t₀ :=
  ⟨fun h W E hE rho t₀ hr => h W ⟨E, rho⟩ hE t₀ hr,
   fun h W x hx t₀ hr => h W x.E hx x.rho t₀ hr⟩

theorem safeConfirmed_inhabited_iff (I : Instance) :
    safeConfirmed.inhabited I () ↔
      ∀ H : Time, ∃ (W : Validators) (E : Env W.V) (rho : Run W.V I.P) (t₀ : Time),
        E.Δ = I.Δ ∧ H ≤ rho.horizon ∧ SleepyRegime I.P E I.iface rho t₀ :=
  ⟨fun h H => let ⟨W, x, t₀, hE, hH, hr, _⟩ := h H; ⟨W, x.E, x.rho, t₀, hE, hH, hr⟩,
   fun h H => let ⟨W, E, rho, t₀, hE, hH, hr⟩ := h H; ⟨W, ⟨E, rho⟩, t₀, hE, hH, hr, trivial⟩⟩

theorem safeStable_holds_iff (I : Instance) :
    safeStable.holds I () ↔
      ∀ (W : Validators) (E : Env W.V), E.Δ = I.Δ → ∀ (rho : Run W.V I.P) (t₀ : Time),
        SleepyRegime I.P E I.iface rho t₀ → SafeFrom I.P rho I.iface.stable t₀ :=
  ⟨fun h W E hE rho t₀ hr => h W ⟨E, rho⟩ hE t₀ hr,
   fun h W x hx t₀ hr => h W x.E hx x.rho t₀ hr⟩

theorem safeStable_inhabited_iff (I : Instance) :
    safeStable.inhabited I () ↔
      ∀ H : Time, ∃ (W : Validators) (E : Env W.V) (rho : Run W.V I.P) (t₀ : Time),
        E.Δ = I.Δ ∧ H ≤ rho.horizon ∧ SleepyRegime I.P E I.iface rho t₀ :=
  ⟨fun h H => let ⟨W, x, t₀, hE, hH, hr, _⟩ := h H; ⟨W, x.E, x.rho, t₀, hE, hH, hr⟩,
   fun h H => let ⟨W, E, rho, t₀, hE, hH, hr⟩ := h H; ⟨W, ⟨E, rho⟩, t₀, hE, hH, hr, trivial⟩⟩

/-- `prefixOrder` is unconditional: every run of an admissible environment. -/
theorem prefixOrder_holds_iff (I : Instance) :
    prefixOrder.holds I () ↔
      ∀ (W : Validators) (E : Env W.V), E.Δ = I.Δ → ∀ rho : Run W.V I.P,
        OutputOrder I.P I.iface rho :=
  ⟨fun h W E hE rho => h W ⟨E, rho⟩ hE () trivial,
   fun h W x hx _ _ => h W x.E hx x.rho⟩

theorem prefixOrder_inhabited_iff (I : Instance) :
    prefixOrder.inhabited I () ↔
      ∀ H : Time, ∃ (W : Validators) (E : Env W.V) (rho : Run W.V I.P),
        E.Δ = I.Δ ∧ H ≤ rho.horizon :=
  ⟨fun h H => let ⟨W, x, _, hE, hH, _, _⟩ := h H; ⟨W, x.E, x.rho, hE, hH⟩,
   fun h H => let ⟨W, E, rho, hE, hH⟩ := h H; ⟨W, ⟨E, rho⟩, (), hE, hH, trivial, trivial⟩⟩

theorem includedConfirmed_holds_iff (I : Instance) (D : Time) :
    includedConfirmed.holds I D ↔
      ∀ (W : Validators) (E : Env W.V), E.Δ = I.Δ → ∀ (rho : Run W.V I.P) (t₀ : Time),
        SleepyRegime I.P E I.iface rho t₀ →
          IncludedFrom I.P E I.iface rho I.iface.confirmed t₀ D :=
  ⟨fun h W E hE rho t₀ hr => h W ⟨E, rho⟩ hE t₀ hr,
   fun h W x hx t₀ hr => h W x.E hx x.rho t₀ hr⟩

/-- The Phase 0 form, plus `H ≤ proposalTime s` (I2). -/
theorem includedConfirmed_inhabited_iff (I : Instance) (D : Time) :
    includedConfirmed.inhabited I D ↔
      ∀ H : Time, ∃ (W : Validators) (E : Env W.V) (rho : Run W.V I.P) (t₀ : Time),
        E.Δ = I.Δ ∧ H ≤ rho.horizon ∧ SleepyRegime I.P E I.iface rho t₀ ∧
          ∃ s : Slot, t₀ < I.P.proposalTime s ∧ H ≤ I.P.proposalTime s ∧
            HonestAwakeProposer E rho s ∧ I.P.proposalTime s + D ≤ rho.horizon :=
  ⟨fun h H => let ⟨W, x, t₀, hE, hH, hr, ht⟩ := h H; ⟨W, x.E, x.rho, t₀, hE, hH, hr, ht⟩,
   fun h H => let ⟨W, E, rho, t₀, hE, hH, hr, ht⟩ := h H; ⟨W, ⟨E, rho⟩, t₀, hE, hH, hr, ht⟩⟩

end AvailableChain.Framework.Catalog

end
