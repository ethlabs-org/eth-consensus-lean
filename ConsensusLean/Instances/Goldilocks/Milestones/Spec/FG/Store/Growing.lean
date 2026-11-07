module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Trace

@[expose] public section

/-! # FG traces under growing faults

`FGLocalRun` (`Spec/FG/Store/Trace`) for a time-indexed honest set `H` (antitone): each law
constrains the nodes honest at the time of the cut it reads, and unforgeability reads the signer's
honesty at the processing time. At `H := fun _ => H₀` it is `FGLocalRun acp₀ H₀ U tr`
(`Lemmas/Growing/Run/Const`). -/

namespace Consensus.Goldilocks.Growing

variable {P : Params} {ACP : Type}

/-- **The FG trace contract under growing faults** (claims C0.5 (c), C0.4). -/
structure FGLocalRun (acp₀ : ACP) (H : Time → Set (Fin P.n)) (U : Set (NodeBlock P ACP))
    (tr : FGTrace P ACP) : Prop where
  /-- Compromise is permanent. -/
  antitone : Antitone H
  /-- `U` is coherent: roots injective, slots increasing along parent edges. -/
  coherent : Coherent U
  /-- Each node honest at time `0` starts from the initial FG state and the empty record. -/
  init : ∀ y ∈ H 0, tr.init y = (Store.init acp₀, FG.Record.empty)
  /-- Each call of a node honest at its time executes the FG on its pre-state. -/
  exec : ∀ i ℓ, tr.label i = some ℓ → tr.node i ∈ H (tr.time i) →
    FGLabel.Step (tr.node i) (tr.state (tr.node i) i) ℓ (tr.post i)
  /-- Every block of the tree that a node holds while honest lies in `U`. -/
  tree_subset : ∀ y i t, (∀ k < i, tr.time k ≤ t) → y ∈ H t → (tr.store y i).tree ⊆ U
  /-- Cuts are at times from `0` on. -/
  time_nonneg : ∀ i, 0 ≤ tr.time i
  /-- The cut order is by time. -/
  time_mono : Monotone tr.time
  /-- A node honest at its call signs only at public times. -/
  attest_public : ∀ y i src signed, y ∈ H (tr.time i) → tr.CallAt y i (.attest src signed) →
    P.IsPublic (tr.time i)
  /-- The tick order, (a), for a node honest at the acceptance of its own proposal. -/
  own_first : ∀ y i B, y ∈ H (tr.time i) → tr.CallAt y i (.block B true) → B.proposer = y →
    P.slotTime B.slot = tr.time i → ∀ k < i, ∀ ℓ, tr.CallAt y k ℓ → tr.time k < tr.time i
  /-- The tick order, (b), for a node honest at its `attest` call. -/
  attest_order : ∀ y j src signed, y ∈ H (tr.time j) → tr.CallAt y j (.attest src signed) →
    ∀ i ℓ, i < j → tr.CallAt y i ℓ → tr.time i = tr.time j →
      ∃ B acc, ℓ = .block B acc ∧ B.proposer = y ∧ P.slotTime B.slot = tr.time j
  /-- The own proposal's payload comes from the pool, for a node honest at the acceptance. -/
  own_payload : ∀ y i B, y ∈ H (tr.time i) → tr.CallAt y i (.block B true) → B.proposer = y →
    P.slotTime B.slot = tr.time i → ∀ a ∈ B.fgPayload, a ∈ (tr.store y i).atts
  /-- Unforgeability: an attestation whose signer is honest at the processing time, processed by
  a node honest then, was signed by that validator at an earlier cut. -/
  unforgeable : ∀ y i a, y ∈ H (tr.time i) → tr.ProcessAt y i a → a.val ∈ H (tr.time i) →
    ∃ j < i, tr.SignAt a.val j a

end Consensus.Goldilocks.Growing

end
