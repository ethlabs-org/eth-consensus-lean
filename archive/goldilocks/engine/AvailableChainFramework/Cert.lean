module
public import AvailableChainFramework.Claim

@[expose] public section

namespace AvailableChain.Framework

variable {K : ClaimDomain}

/-- A certificate: one instance satisfies one claim at one constant, and the
claim's trigger occurs in its regime. -/
structure Cert (c : ClaimSpec K) (I : K.Inst) where
  const : c.Const
  valid : c.valid const
  inhabited : c.inhabited I const
  proof : c.holds I const

/-- A refutation at one constant. -/
structure Refutation (c : ClaimSpec K) (I : K.Inst) where
  const : c.Const
  valid : c.valid const
  proof : ¬ c.holds I const

/-- No valid constant works. -/
structure RefutationFamily (c : ClaimSpec K) (I : K.Inst) : Prop where
  proof : ∀ k, c.valid k → ¬ c.holds I k

variable {c : ClaimSpec K} {I : K.Inst}

/-- Move a certificate to a weaker constant. Inhabitation does not transport,
so the caller supplies it. -/
def Cert.weaken (x : Cert c I) (k' : c.Const) (hv : c.valid k')
    (hle : c.le x.const k' = true) (hi : c.inhabited I k') : Cert c I where
  const := k'
  valid := hv
  inhabited := hi
  proof := c.transport I x.const k' x.valid hv hle x.proof

theorem Cert.not_refuted (x : Cert c I) (r : RefutationFamily c I) : False :=
  r.proof x.const x.valid x.proof

theorem Refutation.family_of (r : Refutation c I)
    (h : ∀ k, c.valid k → c.holds I k → c.holds I r.const) :
    RefutationFamily c I :=
  ⟨fun k hk hh => r.proof (h k hk hh)⟩

end AvailableChain.Framework

end
