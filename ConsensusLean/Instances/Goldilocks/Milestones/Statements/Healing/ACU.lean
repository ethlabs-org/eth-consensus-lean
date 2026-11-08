module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.AC
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.RelTrace

@[expose] public section

/-! # Goldilocks milestone Healing: H.1's settings with the unlock given (definitions)

H.1's premises over an AC trace of a lock rule (`Milestones/Spec/SA/RelTrace`), beside the
parent's (`Healing/AC`): the honest proposal and the driven duties at the unlock oracle `u`
(`HonestProposalU`, `DrivenU`), the service and awake part of `Healthy(g)` (`HealthyACCore`),
and the healthy base and the standalone run at a write mode `m` (`HealthyBaseU`,
`StandaloneRunU`). The lemmas about them are in `Lemmas/Healing/AC/RelSetting` and
`Lemmas/Healing/AC/Setting`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}

/-- `HonestProposal` with the unlock given: `p`'s `ac_proposal` at `t_s`, at the locks `u k` of
its call, returns a head `d` and the payload `pay`, and `p` passes `P` (on that head, with that
payload) to its own `ac_on_block` at `t_s`. -/
abbrev HonestProposalU (u : Nat → Set Lock) (tr : SATrace sp FGP ro) (p : Fin sp.n) (s : Nat)
    (P : Blk sp.n FGP) : Prop :=
  ∃ k ℓ d pay, tr.CallAt p k ℓ ∧ ℓ.call = .proposal ∧
    (acProposalWith sp (u k) (tr.state p k) ℓ.frame (tr.time k)).2 = some (d, pay) ∧
    tr.time k = sp.ts s ∧ P.parent = some d.head.root ∧ P.slot = s ∧ P.proposer = p ∧
    P.acPayload = pay ∧ ∃ j, k < j ∧ tr.AcceptAt p j P ∧ tr.time j = sp.ts s

/-- `Driven` with the unlock given: the honest proposals are `HonestProposalU`. -/
structure DrivenU (u : Nat → Set Lock) (proposer : Nat → Fin sp.n)
    (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) : Prop where
  /-- (a) Blocks have their slot's proposer, a slot not in the future, and an earlier parent. -/
  blocks : ∀ y ∈ H, ∀ i B, tr.AcceptAt y i B → B.root ≠ sp.genesisRoot →
    B.proposer = proposer B.slot ∧ B.slot ≤ sp.slot (tr.time i) ∧
    ∃ Pb : Blk sp.n FGP, B.parent = some Pb.root ∧ Pb.slot < B.slot ∧
      (Pb.root = sp.genesisRoot ∨ ∃ k < i, tr.AcceptAt y k Pb)
  /-- (a) A block of an honest proposer's slot is that proposer's proposal. -/
  honest_slot : ∀ y ∈ H, ∀ i B, tr.AcceptAt y i B → B.root ≠ sp.genesisRoot →
    proposer B.slot ∈ H → HonestProposalU u tr (proposer B.slot) B.slot B
  /-- (b) Every honest node awake at a public time runs its tick there. -/
  tick : ∀ y ∈ H, ∀ t, 0 ≤ t → sp.toParams.IsPublic t → tr.awake y t →
    ∃ i ℓ, tr.CallAt y i ℓ ∧ ℓ.call = .tick ∧ tr.time i = t
  /-- (b) The honest joined proposer of slot `s > 0` runs `ac_proposal` at `t_s`, after its
  tick; when it returns a payload, it passes its block to its own `ac_on_block` at once. -/
  proposal : ∀ s, 0 < s → ∀ p ∈ H, p = proposer s → tr.awake p (sp.ts s) →
    JoinedAt tr p (sp.ts s) →
    ∃ k ℓ, tr.CallAt p k ℓ ∧ ℓ.call = .proposal ∧ tr.time k = sp.ts s ∧
      ((∃ pay, ProposalAt tr p k ℓ pay) → ∃ P, HonestProposalU u tr p s P)
  /-- (b) No object received at a public time is processed before the tick there. -/
  tick_first : ∀ y ∈ H, ∀ i j ℓ ℓ', tr.CallAt y i ℓ → tr.CallAt y j ℓ' → ℓ'.call = .tick →
    tr.time i = tr.time j → (∃ m, ℓ.call = .message m) → j < i
  /-- (b) No object received at a slot start is processed by its honest proposer before its
  `ac_proposal` there. -/
  proposal_first : ∀ y ∈ H, ∀ i j ℓ ℓ', tr.CallAt y i ℓ → tr.CallAt y j ℓ' →
    ℓ'.call = .proposal → tr.time i = tr.time j →
    ((∃ m, ℓ.call = .message m) ∨ ∃ B, ℓ.call = .block B) → j < i

/-- **`Healthy(g)` without its fault clause**: the message and acceptance-relay service and the
awake honest validators of `HealthyAC`, verbatim; the faults are bounded separately. -/
structure HealthyACCore (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (g : Time) : Prop where
  message : ∀ x ∈ H, ∀ i m, tr.SendOrAdmit x i m →
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → tr.deadline y j (max (tr.time i) g) ≤ tr.time j →
      ∃ k ≤ j, tr.time i ≤ tr.time k ∧ tr.ProcessAt y k m ∧
        tr.time k < tr.deadline y k (max (tr.time i) g)
  relay : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → g ≤ tr.time i →
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → tr.deadline y j (tr.time i) ≤ tr.time j →
      Anc U ℓ.frame.F B → ∃ k ≤ j, tr.AcceptAt y k B ∧ tr.time k < tr.deadline y k (tr.time i)
  awake : ∀ y ∈ H, ∀ t, gbar g ≤ t → tr.awake y t

/-- `HealthyBase` with the writes of the mode `m` and the unlock given by the oracle `u`, and
with the fault bound the cone uses, `f < n/2`, in place of `3f ≤ n − 1`. -/
structure HealthyBaseU (m : WriteMode) (u : Nat → Set Lock) (tr : SATrace sp FGP ro)
    (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (proposer : Nat → Fin sp.n) (g : Time) :
    Prop where
  run : ACRunU m u proposer tr H U
  driven : DrivenU u proposer tr H
  healthy : HealthyACCore tr H U g
  faults : 2 * Hᶜ.ncard < sp.n
  catchUp : CatchAC tr H U g (2 * sp.Δ)

/-- `StandaloneRun` with the writes of the mode `m` and the unlock given by the oracle `u`. -/
structure StandaloneRunU (m : WriteMode) (u : Nat → Set Lock) (tr : SATrace sp FGP ro)
    (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (proposer : Nat → Fin sp.n) (g : Time) : Prop
    extends HealthyBaseU m u tr H U proposer g where
  trivial : TrivialFrames tr H

end Consensus.Goldilocks.SA

end
