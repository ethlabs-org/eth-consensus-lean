module
public import AvailableChainFramework.Profile
public import AvailableChainStatements.Generic.Regimes

@[expose] public section

namespace AvailableChain.Framework.Catalog

open AvailableChain AvailableChain.Generic AvailableChain.Statements.Generic

/-- The Sleepy regime of an instance. -/
def sleepy (I : Instance) (W : Validators) (E : Env W.V) (rho : Run W.V I.P)
    (t₀ : Time) : Prop :=
  SleepyRegime I.P E I.iface rho t₀

/-- Safety of one output in the Sleepy regime. No constant. -/
def safeOf (id : Lean.Name) (g : (I : Instance) → Output I.P) :
    ClaimSpec ClaimDomain.v1 where
  id := id
  Const := Unit
  valid := fun _ => True
  le := fun _ _ => true
  le_refl := fun _ => rfl
  le_trans := fun _ _ _ _ _ => rfl
  Point := Time
  regime := fun I _ W x t₀ => sleepy I W x.E x.rho t₀
  conclusion := fun I _ _ x t₀ => SafeFrom I.P x.rho (g I) t₀
  trigger := fun _ _ _ _ _ _ => True
  transport := by
    intro I k k' _ _ _ h
    cases k; cases k'; exact h
  refutable := .run

def safeConfirmed : ClaimSpec ClaimDomain.v1 :=
  safeOf `core.safe.confirmed.v1 (fun I => I.iface.confirmed)

def safeStable : ClaimSpec ClaimDomain.v1 :=
  safeOf `core.safe.stable.v1 (fun I => I.iface.stable)

/-- `stable ⪯ confirmed` at every honest node and time, in every run. -/
def prefixOrder : ClaimSpec ClaimDomain.v1 where
  id := `core.prefix.stableConfirmed.v1
  Const := Unit
  valid := fun _ => True
  le := fun _ _ => true
  le_refl := fun _ => rfl
  le_trans := fun _ _ _ _ _ => rfl
  Point := Unit
  regime := fun _ _ _ _ _ => True
  conclusion := fun I _ _ x _ => OutputOrder I.P I.iface x.rho
  trigger := fun _ _ _ _ _ _ => True
  transport := by
    intro I k k' _ _ _ h
    cases k; cases k'; exact h
  refutable := .run

/-- Exact-time inclusion of honest proposals in `confirmed`, Sleepy regime.
`D` is fixed: `le` is equality (design §4). -/
def includedConfirmed : ClaimSpec ClaimDomain.v1 where
  id := `core.included.confirmed.v1
  Const := Time
  valid := fun D => 0 ≤ D
  le := fun a b => decide (a = b)
  le_refl := fun _ => decide_eq_true rfl
  le_trans := by
    intro a b c hab hbc
    have h1 := of_decide_eq_true hab
    have h2 := of_decide_eq_true hbc
    exact decide_eq_true (h1.trans h2)
  Point := Time
  regime := fun I _ W x t₀ => sleepy I W x.E x.rho t₀
  conclusion := fun I D _ x t₀ =>
    IncludedFrom I.P x.E I.iface x.rho I.iface.confirmed t₀ D
  trigger := fun I D _ x t₀ H =>
    ∃ s : Slot, t₀ < I.P.proposalTime s ∧ H ≤ I.P.proposalTime s ∧
      HonestAwakeProposer x.E x.rho s ∧ I.P.proposalTime s + D ≤ x.rho.horizon
  transport := by
    intro I k k' _ _ hle h
    have : k = k' := of_decide_eq_true hle
    subst this; exact h
  refutable := .family

/-- Review Focus 1 (I2): an inhabitation witness of `includedConfirmed` puts
its proposal at a time of at least `H`. -/
theorem includedConfirmed_trigger_late {I : Instance} {D : Time} {H : Time}
    (h : includedConfirmed.inhabited I D) :
    ∃ (W : Validators) (x : ClaimDomain.v1.Ctx I W) (s : Slot),
      H ≤ I.P.proposalTime s ∧ HonestAwakeProposer x.E x.rho s := by
  obtain ⟨W, x, t₀, _, _, _, s, _, hH, hp, _⟩ := h H
  exact ⟨W, x, s, hH, hp⟩

/-- The core floor (design §4): every candidate certifies all four claims.
The shared constant is the inclusion delay `D`. -/
def core : Profile ClaimDomain.v1 where
  id := `core.v1
  Shared := Time
  valid := fun D => 0 ≤ D
  entries :=
    [⟨safeConfirmed, fun _ => ()⟩, ⟨safeStable, fun _ => ()⟩,
     ⟨prefixOrder, fun _ => ()⟩, ⟨includedConfirmed, fun D => D⟩]

/-- A candidate protocol passes the core floor. -/
def Candidate (I : Instance) : Type 1 := ProfileCert core I

/-- A refutation family of a core claim rejects the instance. -/
theorem not_candidate_of_family {I : Instance} {e : Profile.Entry ClaimDomain.v1 Time}
    (he : e ∈ core.entries) (r : RefutationFamily e.spec I) : Candidate I → False := by
  intro pc; exact (pc.certs e he).1.not_refuted r

end AvailableChain.Framework.Catalog

end
