module
public import ConsensusLean.Spec.Problem.CorrectProtocol

/-! # Observation-preserving adequacy

A homogeneous observation type does not make its reader public. Neither cross-environment
extensionality nor a public role/timing factorisation follows from this interface. -/

public section

namespace Consensus

/-- An observation of external data; its reader may depend on the entire environment. -/
structure ExtObs {V : Type} (S : System V) (X : External S) (Ob : Type) where
  obs : ∀ E, X.Ext E → Ob

variable {V : Type} [Fintype V] [DecidableEq V] {Prog Ob : Type}

/-- Adequacy with prefix and covering witnesses preserving the specified observation.
This is additional proof vocabulary, not an assumption of the certified interface. -/
structure System.AdequateObs (S : System V) (X : Progress S Prog)
    (o : ExtObs S X.toExternal Ob) : Prop where
  adequate : S.Adequate X
  prefixObs : ∀ r, S.Valid r → ∀ b : Time, 0 ≤ b → b ≤ (S.pt r).horizon →
    ∃ r', S.Valid r' ∧
      (S.trace r').PrefixOf (S.trace r) b ∧
      (∀ v i, i ≤ (S.trace r').cuts → S.view r' v i = S.view r v i) ∧
      (S.log r').AgreesUpTo (S.log r) b ∧ (S.Excuse r' → S.Excuse r) ∧
      (∀ π c s t, t ≤ b → X.holds π c s t (S.pt r) (X.ext r) →
        X.holds π c s t (S.pt r') (X.ext r')) ∧
      o.obs _ (X.ext r') = o.obs _ (X.ext r)
  coversObs : ∀ p : EnvPoint V, 0 ≤ p.horizon →
    ∀ e : X.Ext p.env, X.Admits p.env e → ∀ g : Time,
    ∃ r, S.Valid r ∧ ¬ S.Excuse r ∧ S.pt r = p ∧
      (S.log r).EagerFrom (S.pt r) g ∧
      (∀ π c s t, X.holds π c s t p e → X.holds π c s t (S.pt r) (X.ext r)) ∧
      o.obs _ (X.ext r) = o.obs p.env e

end Consensus

end
