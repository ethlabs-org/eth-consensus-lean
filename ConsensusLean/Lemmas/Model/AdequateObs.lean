module
public import ConsensusLean.Lemmas.Problem.AdequateObs
public import ConsensusLean.Lemmas.Model.Adequate
public import ConsensusLean.Lemmas.Model.TruncateExt

/-! # Model witnesses preserving identities and the complete slot dictionary

The arbitrary role plan is not asserted to be implemented by an engine or to be public.
Same-environment preservation proves no cross-environment reader publicity. -/

public section

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V]
  {O : OutputSchema} {F : ProtocolFamily O}

/-- Observe the identity equivalence together with all slot committees under a role plan. -/
def dictObs (voteRole : ∀ E : Env V, Nat → (protoOf F E).Role) :
    ExtObs (sysOf O F V) (sysExternal O F V)
      ((Fin (Fintype.card V) ≃ V) × (Nat → Finset (Fin (Fintype.card V)))) :=
  ⟨fun E e => (e.1, fun s => e.2 (voteRole E s))⟩

theorem dictObs_obs (voteRole : ∀ E : Env V, Nat → (protoOf F E).Role)
    (E : Env V) (e : (sysExternal O F V).Ext E) :
    (dictObs voteRole).obs E e = (e.1, fun s => e.2 (voteRole E s)) := by rfl

end Consensus.Model

end
