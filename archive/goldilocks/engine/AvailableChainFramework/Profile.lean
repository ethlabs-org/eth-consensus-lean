module
public import AvailableChainFramework.Cert
public import AvailableChainFramework.Instance

@[expose] public section

namespace AvailableChain.Framework

variable {K : ClaimDomain}

/-- One claim of a profile, with the projection of the shared constants to the
claim's own constant (design §4, profiles; PHASE0-REPORT §5.1 (g)). -/
structure Profile.Entry (K : ClaimDomain) (S : Type) where
  spec : ClaimSpec K
  share : S → spec.Const

/-- A named set of catalog claims with shared constants. `valid` holds the
conditions that relate constants of different claims (for `ac-4.3`, all of
`Constants.Valid`). -/
structure Profile (K : ClaimDomain) where
  id : Lean.Name
  Shared : Type
  valid : Shared → Prop
  entries : List (Profile.Entry K Shared)

/-- One certificate per claim of the profile, all for one instance, all at the
projections of ONE shared constant. -/
structure ProfileCert (p : Profile K) (I : K.Inst) : Type 1 where
  shared : p.Shared
  valid : p.valid shared
  certs : ∀ e ∈ p.entries, {x : Cert e.spec I // x.const = e.share shared}

/-- The claims of a profile hold at one shared constant (no inhabitation). -/
def Profile.holdsAt (p : Profile K) (I : K.Inst) (C : p.Shared) : Prop :=
  p.valid C ∧ ∀ e ∈ p.entries, e.spec.valid (e.share C) ∧ e.spec.holds I (e.share C)

theorem ProfileCert.holdsAt {p : Profile K} {I : K.Inst} (pc : ProfileCert p I) :
    p.holdsAt I pc.shared := by
  refine ⟨pc.valid, fun e he => ?_⟩
  obtain ⟨x, hx⟩ := pc.certs e he
  exact ⟨hx ▸ x.valid, hx ▸ x.proof⟩

end AvailableChain.Framework

end
