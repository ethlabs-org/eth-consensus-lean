module
public import ConsensusLean.Lemmas.Problem.PublicRoleReader
public import ConsensusLean.Spec.Model.System
public import ConsensusLean.Lemmas.Model.Truncate

/-! # Model role bindings and intended transport edges

All implication contracts below are unproved intended theorem types, not evidence.
Selection/PKI transport does not transport objects, Auth envelopes, payloads or decoders. -/

public section
namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V]
  {O : OutputSchema} {F : ProtocolFamily O}

def validatorCommittee (key : Fin (Fintype.card V) ≃ V)
    (C : Finset (Fin (Fintype.card V))) : Finset V := C.map key.toEmbedding

def modelPublic (p : PublicSkeleton) : Public :=
  ⟨p.n, p.deltaAC, p.deltaAC_pos, p.deltaFG, p.deltaFG_pos⟩

theorem modelPublic_eq (p : PublicSkeleton) :
    modelPublic p = ⟨p.n, p.deltaAC, p.deltaAC_pos, p.deltaFG, p.deltaFG_pos⟩ := by rfl

def moveModelRole {E E' : Env V} (h : publicSkeleton E = publicSkeleton E')
    (r : (protoOf F E).Role) : (protoOf F E').Role :=
  Eq.mp (congrArg (fun p => (F p).Role)
    (show pubOf E = pubOf E' from by
      simpa only [publicSkeleton_eq, modelPublic_eq] using congrArg modelPublic h)) r

/-- An equivalence of the entire role space with exact naturality, not only vote roles. -/
structure ModelReaderBinding
    (R : PublicRoleReader (sysOf O F V) (sysExternal O F V)) where
  roleEquiv : (E : Env V) → R.Role (publicSkeleton E) ≃ (protoOf F E).Role
  natural : ∀ (E E' : Env V) (h : publicSkeleton E = publicSkeleton E') r,
    roleEquiv E' (R.moveRole h r) = moveModelRole h (roleEquiv E r)
  selected_eq : ∀ (E : Env V) (e : (sysExternal O F V).Ext E) r,
    R.selected E e r = validatorCommittee e.1 (e.2 (roleEquiv E r))

/-- Ownership alone is not admission or authorization. -/
def CredentialOwner {E : Env V} (rho : Run F E) : Prop :=
  ∀ (o : (protoOf F E).Object) k r,
    o.auth = .signed k r → rho.signerOf o = some (rho.key k)

/-- Actual admission and its source paths remain independent pending suppliers. -/
def CredentialSelection {E : Env V} (rho : Run F E)
    (admittedAt : V → Nat → (protoOf F E).Object → Prop) : Prop :=
  ∀ v i o, admittedAt v i o → ∀ d, o.Contains d → ∀ k r,
    d.auth = .signed k r → k ∈ rho.sel r

/-- Same-event received admissions only; neither arbitrary arrivals nor later retries. -/
def ReceivedCredentialSelection {E : Env V} (rho : Run F E)
    (admittedAt : V → Nat → (protoOf F E).Object → Prop) : Prop :=
  ∀ v i outer t, rho.events[i]? = some (.deliver v outer t) →
    ∀ d, outer.Contains d → admittedAt v i d → ∀ z, d.Contains z → ∀ k r,
    z.auth = .signed k r → k ∈ rho.sel r

/-- Complete role selection and PKI preservation, not object transport. -/
def SelectionPKITransport {E E' : Env V} (rho : Run F E) (rho' : Run F E')
    (R : PublicRoleReader (sysOf O F V) (sysExternal O F V))
    (B : ModelReaderBinding R) (h : publicSkeleton E = publicSkeleton E') : Prop :=
  rho'.key = rho.key ∧
    ∀ r, rho'.sel (B.roleEquiv E' (R.moveRole h r)) = rho.sel (B.roleEquiv E r)

def PrefixRoleTransportEdge : Prop :=
  ∀ (E : Env V) (rho : Run F E)
    (R : PublicRoleReader (sysOf O F V) (sysExternal O F V))
    (B : ModelReaderBinding R) (b : Time),
    SelectionPKITransport rho (rho.truncate b) R B rfl

def CoverRoleTransport
    (R : PublicRoleReader (sysOf O F V) (sysExternal O F V))
    (B : ModelReaderBinding R) (E : Env V)
    (e : (sysExternal O F V).Ext E) (rho : Run F E) : Prop :=
  rho.key = e.1 ∧ ∀ r, rho.sel (B.roleEquiv E r) = e.2 (B.roleEquiv E r)

/-- The same covering witness must carry adequacy, progress, PKI and all historical roles. -/
def CoverRoleTransportEdge {Prog : Type}
    (Y : Progress (sysOf O F V) Prog) (hY : Y.toExternal = sysExternal O F V)
    (R : PublicRoleReader (sysOf O F V) (sysExternal O F V))
    (B : ModelReaderBinding R) : Prop :=
  ∀ (p : EnvPoint V), 0 ≤ p.horizon →
    ∀ e : (sysExternal O F V).Ext p.env,
    (sysExternal O F V).Admits p.env e → ∀ g : Time,
    ∃ rho : Run F p.env,
      (sysOf O F V).Valid ⟨p.env, rho⟩ ∧
      ¬ (sysOf O F V).Excuse ⟨p.env, rho⟩ ∧
      (sysOf O F V).pt ⟨p.env, rho⟩ = p ∧
      ((sysOf O F V).log ⟨p.env, rho⟩).EagerFrom ((sysOf O F V).pt ⟨p.env, rho⟩) g ∧
      (∀ pi c s t,
        Y.holds pi c s t p (Eq.mp (congrArg (fun X => X.Ext p.env) hY.symm) e) →
        Y.holds pi c s t ((sysOf O F V).pt ⟨p.env, rho⟩) (Y.ext ⟨p.env, rho⟩)) ∧
      CoverRoleTransport R B p.env e rho

end Consensus.Model
