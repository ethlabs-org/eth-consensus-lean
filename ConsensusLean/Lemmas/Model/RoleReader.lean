module
public import ConsensusLean.Spec.Model.System
public import ConsensusLean.Lemmas.Model.Truncate

/-! # Model participation binding

The problem reader uses the actual model selection for the protocol's public
participation role. Selection transport does not transport executions or decoders. -/

public section
namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V]
  {O : OutputSchema} {F : ProtocolFamily O}

def validatorCommittee (key : Fin (Fintype.card V) ≃ V)
    (C : Finset (Fin (Fintype.card V))) : Finset V := C.map key.toEmbedding

/-- The generic observation is the actual run selection, mapped by its own PKI. -/
theorem sysExternal_selected {E : Env V} (rho : Run F E) (t : Time) :
    (sysExternal O F V).selected E ((sysExternal O F V).ext ⟨E, rho⟩) t =
      match (protoOf F E).participationRole t with
      | none => Finset.univ
      | some role => validatorCommittee rho.key (rho.sel role) := by
  dsimp only [sysExternal]
  cases (protoOf F E).participationRole t <;> rfl

/-- Prefix truncation changes neither historical selection nor its interpretation. -/
theorem sysExternal_selected_truncate {E : Env V} (rho : Run F E) (b t : Time) :
    (sysExternal O F V).selected E ((sysExternal O F V).ext ⟨E, rho.truncate b⟩) t =
      (sysExternal O F V).selected E ((sysExternal O F V).ext ⟨E, rho⟩) t := by
  rw [Run.truncate_eq]
  rfl

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

end Consensus.Model
