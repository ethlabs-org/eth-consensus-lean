module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Growing
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool

public section

/-! # SA service under growing faults

The finite service interface reads each sender's honesty at release and each recipient's honesty
at its observation cut. Releases remain owed after the sender is compromised. Retained evidence
and `CarryAt` do not bind an honest set and are reused unchanged.
-/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}

/-- Finite service with independent source-window start and recipient deadline cutoff. -/
structure ServiceWindowBefore (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (a b : Time) (tr : SATrace sp FGP ro) : Prop where
  message : ∀ x i v, x ∈ H (tr.time i) → tr.SendOrAdmit x i v → a ≤ tr.time i →
    ∀ y j ℓ, y ∈ H (tr.time j) → tr.CallAt y j ℓ → tr.deadline y j (tr.time i) ≤ b →
      tr.deadline y j (tr.time i) ≤ tr.time j → MessageServedBefore tr y j (tr.time i) v
  relay : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → a ≤ tr.time i →
    ∀ y j ℓ, y ∈ H (tr.time j) → tr.CallAt y j ℓ → tr.deadline y j (tr.time i) ≤ b →
      tr.deadline y j (tr.time i) ≤ tr.time j → Anc U ℓ.frame.F B →
      ∃ k ≤ j, tr.AcceptAt y k B ∧ tr.time k < tr.deadline y k (tr.time i)

/-- Sleepy service starts at time zero. -/
abbrev ServiceBefore (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (b : Time) (tr : SATrace sp FGP ro) : Prop := ServiceWindowBefore H U 0 b tr

/-- With constant faults the service contract is exactly the static one. -/
theorem serviceWindowBefore_const {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
    {a b : Time} {tr : SATrace sp FGP ro} :
    ServiceWindowBefore (fun _ => H) U a b tr ↔ SA.ServiceWindowBefore H U a b tr := by
  constructor
  · intro h
    exact ⟨fun x hx i v hi hai y hy j ℓ => h.message x i v hx hi hai y j ℓ hy,
      fun x hx i B hi hai y hy j ℓ => h.relay x i B hx hi hai y j ℓ hy⟩
  · intro h
    exact ⟨fun x i v hx hi hai y j ℓ hy => h.message x hx i v hi hai y hy j ℓ,
      fun x i B hx hi hai y j ℓ hy => h.relay x hx i B hi hai y hy j ℓ⟩

/-- A proposer honest through `T` has only one block per slot in frames read by `T`.
The two readers need only be honest at their own cuts. -/
theorem HonestObjects.one_block_before {proposer : Nat → Fin sp.n}
    {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)}
    (h : HonestObjects proposer tr H) (hanti : Antitone H) {T : Time}
    {y y' : Fin sp.n} {i i' : Nat} {ℓ ℓ' : ACLabel (goldilocksSA sp FGP ro)}
    {B B' : Blk sp.n FGP} (hy : y ∈ H (tr.time i)) (hc : tr.CallAt y i ℓ)
    (hB : B ∈ ℓ.frame.tree) (hi : tr.time i ≤ T)
    (hy' : y' ∈ H (tr.time i')) (hc' : tr.CallAt y' i' ℓ')
    (hB' : B' ∈ ℓ'.frame.tree) (hi' : tr.time i' ≤ T)
    (hp : B.proposer ∈ H T) (hpp : B.proposer = B'.proposer) (hs : B.slot = B'.slot) :
    B = B' :=
  h.one_block y i ℓ B y' i' ℓ' B' hy hc hB hy' hc' hB'
    (hanti (max_le hi hi') hp) hpp hs

end Consensus.Goldilocks.SA.Growing

end
