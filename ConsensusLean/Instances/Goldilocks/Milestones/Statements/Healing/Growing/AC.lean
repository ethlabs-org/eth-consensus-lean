module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.AC
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Growing

@[expose] public section

/-! # Goldilocks milestone Healing under growing faults: driven AC traces (statements)

A driven AC trace (`Statements/Healing/AC`) for a time-indexed honest set `H` (antitone): its
clauses constrain the nodes honest at the cut read, and a block of the slot of a proposer honest
at the processing cut is that proposer's proposal.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.SA.Growing

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-- **A driven AC trace under growing faults.** -/
structure Driven (proposer : Nat → Fin sp.n)
    (tr : SATrace sp FGP ro) (H : Time → Set (Fin sp.n)) : Prop where
  /-- (a) Blocks have their slot's proposer, a slot not in the future, and an earlier parent. -/
  blocks : ∀ y i B, y ∈ H (tr.time i) → tr.AcceptAt y i B → B.root ≠ sp.genesisRoot →
    B.proposer = proposer B.slot ∧ B.slot ≤ sp.slot (tr.time i) ∧
    ∃ Pb : Blk sp.n FGP, B.parent = some Pb.root ∧ Pb.slot < B.slot ∧
      (Pb.root = sp.genesisRoot ∨ ∃ k < i, tr.AcceptAt y k Pb)
  /-- (a) A block of the slot of a proposer honest at the processing cut is its proposal. -/
  honest_slot : ∀ y i B, y ∈ H (tr.time i) → tr.AcceptAt y i B → B.root ≠ sp.genesisRoot →
    proposer B.slot ∈ H (tr.time i) → HonestProposal tr (proposer B.slot) B.slot B
  /-- (b) Every node honest and awake at a public time runs its tick there. -/
  tick : ∀ y t, y ∈ H t → 0 ≤ t → sp.toParams.IsPublic t → tr.awake y t →
    ∃ i ℓ, tr.CallAt y i ℓ ∧ ℓ.call = .tick ∧ tr.time i = t
  /-- (b) The joined proposer of slot `s > 0`, honest at `t_s`, runs `ac_proposal` at `t_s`. -/
  proposal : ∀ s : Nat, 0 < s → ∀ p, p ∈ H (sp.ts s) → p = proposer s → tr.awake p (sp.ts s) →
    JoinedAt tr p (sp.ts s) →
    ∃ k ℓ, tr.CallAt p k ℓ ∧ ℓ.call = .proposal ∧ tr.time k = sp.ts s ∧
      ((∃ pay, ProposalAt tr p k ℓ pay) → ∃ P, HonestProposal tr p s P)
  /-- (b) No object received at a public time is processed before the tick there. -/
  tick_first : ∀ y i j ℓ ℓ', y ∈ H (tr.time i) → tr.CallAt y i ℓ → tr.CallAt y j ℓ' →
    ℓ'.call = .tick → tr.time i = tr.time j → (∃ m, ℓ.call = .message m) → j < i
  /-- (b) No object received at a slot start is processed before the proposer's
  `ac_proposal` there. -/
  proposal_first : ∀ y i j ℓ ℓ', y ∈ H (tr.time i) → tr.CallAt y i ℓ → tr.CallAt y j ℓ' →
    ℓ'.call = .proposal → tr.time i = tr.time j →
    ((∃ m, ℓ.call = .message m) ∨ ∃ B, ℓ.call = .block B) → j < i

end Consensus.Goldilocks.SA.Growing

end
