module
public import AvailableChainGeneric.Proofs.V2.DCProps -- shake: keep (examples)

public section

namespace AvailableChain.Gen.V2.Tests.DCProps

open AvailableChain AvailableChain.V2

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
  {E : Generic.Env V} {rho : Run V P} {g : Output P}

-- The Gen pair gives DC safety, including compatibility across both endpoints.
example {t₀ : Time}
    (hc : Pure.CompatOn (fun v => v ∈ rho.honest) (fun t v => outputAt E rho g v t)
      (fun t => t₀ ≤ t ∧ t ≤ rho.horizon))
    (hm : Pure.MonoOn (fun v => v ∈ rho.honest) (fun t v => outputAt E rho g v t)
      (fun t => t₀ ≤ t ∧ t ≤ rho.horizon))
    (hh : t₀ ≤ rho.horizon) {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest) :
    Block.Compatible (outputAt E rho g u t₀) (outputAt E rho g v rho.horizon) ∧
      Block.Preceq (outputAt E rho g v t₀) (outputAt E rho g v rho.horizon) := by
  have hs := (compatOn_monoOn_iff_safeFrom E rho g t₀).mp ⟨hc, hm⟩
  exact ⟨hs.agree u hu v hv t₀ rho.horizon le_rfl hh hh le_rfl,
    hs.monotone v hv t₀ rho.horizon le_rfl hh le_rfl⟩

-- A DC safety value supplies both Gen properties in the reverse direction.
example {t₀ : Time} (hs : SafeFrom P E rho g t₀) :
    Pure.CompatOn (fun v => v ∈ rho.honest) (fun t v => outputAt E rho g v t)
        (fun t => t₀ ≤ t ∧ t ≤ rho.horizon) ∧
      Pure.MonoOn (fun v => v ∈ rho.honest) (fun t v => outputAt E rho g v t)
        (fun t => t₀ ≤ t ∧ t ≤ rho.horizon) :=
  (compatOn_monoOn_iff_safeFrom E rho g t₀).mpr hs

-- The horizon itself is a valid singleton interval, even if the horizon is negative.
example
    (hc : Pure.CompatOn (fun v => v ∈ rho.honest) (fun t v => outputAt E rho g v t)
      (fun t => rho.horizon ≤ t ∧ t ≤ rho.horizon))
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest) :
    Block.Compatible (outputAt E rho g u rho.horizon) (outputAt E rho g v rho.horizon) :=
  (compatOn_iff_agreeFrom E rho g rho.horizon).mp hc u hu v hv
    rho.horizon rho.horizon le_rfl le_rfl le_rfl le_rfl

-- Monotonicity allows equality of the two times and needs no nonnegative start.
example (hm : MonotoneFrom P E rho g (-1)) (hh : -1 ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) :
    Block.Preceq (outputAt E rho g v (-1)) (outputAt E rho g v (-1)) :=
  (monoOn_iff_monotoneFrom E rho g (-1)).mpr hm (-1) (-1) v
    ⟨le_rfl, hh⟩ ⟨le_rfl, hh⟩ le_rfl hv

-- An empty interval imposes no restriction on the output reader.
example {t₀ : Time} (he : rho.horizon < t₀) : SafeFrom P E rho g t₀ := by
  apply (compatOn_monoOn_iff_safeFrom E rho g t₀).mp
  constructor
  · intro t _ _ _ ht
    exact (not_le_of_gt he (le_trans ht.1 ht.2)).elim
  · intro t _ _ ht
    exact (not_le_of_gt he (le_trans ht.1 ht.2)).elim

-- Persistence serves every honest node at both endpoints. T has no bound.
example {T b₀ : Time}
    (hs : ∀ v ∈ rho.honest, ∀ B, Block.Preceq B (outputAt E rho g v T) →
      Pure.ServedOn (fun v => v ∈ rho.honest) (fun t v => outputAt E rho g v t) B
        (fun t => b₀ ≤ t ∧ t ≤ rho.horizon))
    (hh : b₀ ≤ rho.horizon) {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest)
    {B : Block} (hB : Block.Preceq B (outputAt E rho g v T)) :
    Block.Preceq B (outputAt E rho g u b₀) ∧
      Block.Preceq B (outputAt E rho g u rho.horizon) := by
  have hp := (persistsFrom_iff_servedOn E rho g T b₀).mpr hs
  exact ⟨hp v hv B hB b₀ le_rfl hh u hu, hp v hv B hB rho.horizon hh le_rfl u hu⟩

-- The reverse bridge does not add an order condition on the source time T.
example {T : Time} (hp : PersistsFrom P E rho g T rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {B : Block}
    (hB : Block.Preceq B (outputAt E rho g v T)) :
    Pure.ServedOn (fun v => v ∈ rho.honest) (fun t v => outputAt E rho g v t) B
      (fun t => rho.horizon ≤ t ∧ t ≤ rho.horizon) :=
  (persistsFrom_iff_servedOn E rho g T rho.horizon).mp hp v hv B hB

end AvailableChain.Gen.V2.Tests.DCProps
