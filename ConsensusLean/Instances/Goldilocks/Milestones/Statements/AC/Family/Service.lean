module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Trace

/-! # Statement-layer message service and its retained-evidence closure -/

@[expose] public section

namespace Consensus.Goldilocks.SA.FamilyFacts

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-- Timestamped pool evidence, including two distinct votes by the same signer. -/
def PoolEvidenceBefore (st : SAState sp.n) (v : Vote sp.n) (T : Time) : Prop :=
  SA.HeldBefore st v T ∨ ∃ a b : Vote sp.n, a ≠ b ∧
    a.val = v.val ∧ b.val = v.val ∧ a.slot = v.slot ∧ b.slot = v.slot ∧
    SA.HeldBefore st a T ∧ SA.HeldBefore st b T

/-- Earlier evidence remains usable only across a restart-free interval. -/
def RetainedBefore (o : SATrace sp FGP ro) (y : Fin sp.n) (j : Nat)
    (v : Vote sp.n) (T : Time) : Prop :=
  ∃ q ≤ j, PoolEvidenceBefore (o.state y q) v T ∧
    ∀ r, q ≤ r → r < j → ¬ o.RestartAt y r

/-- Fresh processing before its deadline, or retained timestamped evidence. -/
def MessageServedBefore (o : SATrace sp FGP ro) (y : Fin sp.n) (j : Nat)
    (τ : Time) (v : Vote sp.n) : Prop :=
  (∃ k ≤ j, τ ≤ o.time k ∧ o.ProcessAt y k v ∧ o.time k < o.deadline y k τ) ∨
    RetainedBefore o y j v (o.deadline y j τ)

/-- Source-window message service and actual block acceptance relay. -/
structure ServiceWindowBefore (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (a b : Time) (o : SATrace sp FGP ro) : Prop where
  message : ∀ x ∈ H, ∀ i v, o.SendOrAdmit x i v → a ≤ o.time i →
    ∀ y ∈ H, ∀ j ℓ, o.CallAt y j ℓ → o.deadline y j (o.time i) ≤ b →
      o.deadline y j (o.time i) ≤ o.time j → MessageServedBefore o y j (o.time i) v
  relay : ∀ x ∈ H, ∀ i B, o.AcceptAt x i B → a ≤ o.time i →
    ∀ y ∈ H, ∀ j ℓ, o.CallAt y j ℓ → o.deadline y j (o.time i) ≤ b →
      o.deadline y j (o.time i) ≤ o.time j → Anc U ℓ.frame.F B →
      ∃ k ≤ j, o.AcceptAt y k B ∧ o.time k < o.deadline y k (o.time i)

/-- Service whose source window starts at zero. -/
def ServiceBefore (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (b : Time) (o : SATrace sp FGP ro) : Prop := ServiceWindowBefore H U 0 b o

end Consensus.Goldilocks.SA.FamilyFacts

end
