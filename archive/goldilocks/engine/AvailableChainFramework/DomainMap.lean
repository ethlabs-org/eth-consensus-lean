module
public import Mathlib.Logic.Equiv.Defs
public import AvailableChainFramework.Instance
public import AvailableChainFramework.Cert

@[expose] public section

namespace AvailableChain.Framework

variable {K K' : ClaimDomain}

/-- A claim domain map from `K'` to `K` (a facet claim domain to its base, design G2):
an instance map and an equivalence of contexts that keeps admissibility and
the horizon. -/
structure DomainMap (K' K : ClaimDomain) where
  inst : K'.Inst → K.Inst
  ctx : ∀ I W, K'.Ctx I W ≃ K.Ctx (inst I) W
  admissible : ∀ I W x, K'.admissible I W x ↔ K.admissible (inst I) W (ctx I W x)
  horizon : ∀ I W x, K'.horizon I W x = K.horizon (inst I) W (ctx I W x)

namespace ClaimSpec

/-- The claim `c` over `K`, read on `K'` through `m`. Same id, constants and
points. -/
def pull (m : DomainMap K' K) (c : ClaimSpec K) : ClaimSpec K' where
  id := c.id
  Const := c.Const
  valid := c.valid
  le := c.le
  le_refl := c.le_refl
  le_trans := c.le_trans
  Point := c.Point
  regime := fun I k W x p => c.regime (m.inst I) k W (m.ctx I W x) p
  conclusion := fun I k W x p => c.conclusion (m.inst I) k W (m.ctx I W x) p
  trigger := fun I k W x p H => c.trigger (m.inst I) k W (m.ctx I W x) p H
  transport := by
    intro I k k' hk hk' hle h W x hx p hr
    refine c.transport (m.inst I) k k' hk hk' hle ?_ W (m.ctx I W x)
      ((m.admissible I W x).1 hx) p hr
    intro W y hy q hq
    have h' := h W ((m.ctx I W).symm y)
      ((m.admissible I W _).2 (by rwa [Equiv.apply_symm_apply])) q
      (by simpa only [Equiv.apply_symm_apply] using hq)
    simpa only [Equiv.apply_symm_apply] using h'
  refutable := c.refutable

theorem holds_pull (m : DomainMap K' K) (c : ClaimSpec K) (I : K'.Inst) (k : c.Const) :
    (c.pull m).holds I k ↔ c.holds (m.inst I) k := by
  constructor
  · intro h W y hy q hq
    have h' := h W ((m.ctx I W).symm y)
      ((m.admissible I W _).2 (by rwa [Equiv.apply_symm_apply])) q
      (by simpa only [pull, Equiv.apply_symm_apply] using hq)
    simpa only [pull, Equiv.apply_symm_apply] using h'
  · intro h W x hx p hr
    exact h W (m.ctx I W x) ((m.admissible I W x).1 hx) p hr

theorem inhabited_pull (m : DomainMap K' K) (c : ClaimSpec K) (I : K'.Inst) (k : c.Const) :
    (c.pull m).inhabited I k ↔ c.inhabited (m.inst I) k := by
  constructor
  · intro h H
    obtain ⟨W, x, p, ha, hh, hr, ht⟩ := h H
    exact ⟨W, m.ctx I W x, p, (m.admissible I W x).1 ha, m.horizon I W x ▸ hh, hr, ht⟩
  · intro h H
    obtain ⟨W, y, p, ha, hh, hr, ht⟩ := h H
    refine ⟨W, (m.ctx I W).symm y, p, ?_, ?_, ?_, ?_⟩
    · exact (m.admissible I W _).2 (by rwa [Equiv.apply_symm_apply])
    · rw [m.horizon, Equiv.apply_symm_apply]; exact hh
    · simpa only [pull, Equiv.apply_symm_apply] using hr
    · simpa only [pull, Equiv.apply_symm_apply] using ht

end ClaimSpec

/-- A certificate of the base instance is a certificate of the pulled claim. -/
def Cert.pull (m : DomainMap K' K) {c : ClaimSpec K} {I : K'.Inst}
    (x : Cert c (m.inst I)) : Cert (c.pull m) I where
  const := x.const
  valid := x.valid
  inhabited := (ClaimSpec.inhabited_pull m c I x.const).2 x.inhabited
  proof := (ClaimSpec.holds_pull m c I x.const).2 x.proof

/-- The domain of a facet structure `J` over v1 instances: contexts, admissibility
and horizon are those of the base instance, so they cannot drift. -/
@[reducible] def ClaimDomain.ofV1 (id : Lean.Name) (J : Type 1) (base : J → Instance) :
    ClaimDomain where
  id := id
  Inst := J
  Ctx := fun I W => V1Ctx (base I) W
  admissible := fun I _ x => x.E.Δ = (base I).Δ
  horizon := fun _ _ x => x.rho.horizon

/-- The map from a facet domain built by `ClaimDomain.ofV1` to v1: the base
instance and the identity on contexts. A map between two facet domains whose
base instances are only propositionally equal needs a cast of the contexts;
a `▸` rewrite does not elaborate there. -/
def DomainMap.ofV1 (id : Lean.Name) (J : Type 1) (base : J → Instance) :
    DomainMap (ClaimDomain.ofV1 id J base) ClaimDomain.v1 where
  inst := base
  ctx := fun _ _ => Equiv.refl _
  admissible := fun _ _ _ => Iff.rfl
  horizon := fun _ _ _ => rfl

end AvailableChain.Framework

end
