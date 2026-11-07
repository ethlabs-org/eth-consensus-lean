module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.AC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.RelTrace

public section

/-! # Goldilocks Healing: H.1's vocabulary with the unlock given

H.1's statements read the proposal of an honest proposer through the parent's `ac_proposal`
(`HonestProposal`, `Driven`), whose head depends on the locks after its unlock. Over a trace with
the unlock given by an oracle `u` (`ACLocalRunU`), the proposal is `acProposalWith` at the locks
`u k` of its call (`HonestProposalU`, `DrivenU`). At the parent's oracle these are the parent's
(`honestProposalU_parent_iff`, `Driven.toU`). -/

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

theorem honestProposalU_iff (u : Nat → Set Lock) (tr : SATrace sp FGP ro) (p : Fin sp.n)
    (s : Nat) (P : Blk sp.n FGP) :
    HonestProposalU u tr p s P ↔ ∃ k ℓ d pay, tr.CallAt p k ℓ ∧ ℓ.call = .proposal ∧
      (acProposalWith sp (u k) (tr.state p k) ℓ.frame (tr.time k)).2 = some (d, pay) ∧
      tr.time k = sp.ts s ∧ P.parent = some d.head.root ∧ P.slot = s ∧ P.proposer = p ∧
      P.acPayload = pay ∧ ∃ j, k < j ∧ tr.AcceptAt p j P ∧ tr.time j = sp.ts s :=
  Iff.rfl

/-- At the parent's oracle, `HonestProposalU` is `HonestProposal`. -/
theorem honestProposalU_parent_iff (tr : SATrace sp FGP ro) (p : Fin sp.n) (s : Nat)
    (P : Blk sp.n FGP) : HonestProposalU (parentOracle sp tr) tr p s P ↔ HonestProposal tr p s
        P := by
  have key : ∀ k (ℓ : ACLabel (goldilocksSA sp FGP ro)), tr.CallAt p k ℓ → ℓ.call = .proposal →
      acProposalWith sp (parentOracle sp tr k) (tr.state p k) ℓ.frame (tr.time k) =
        acProposal sp (tr.state p k) ℓ.frame (tr.time k) := by
    intro k ℓ hc hcall
    simp only [parentOracle, hc.2, hc.1, hcall]
    rfl
  constructor
  · rintro ⟨k, ℓ, d, pay, hc, hcall, hp, rest⟩
    exact ⟨k, ℓ, d, pay, hc, hcall, by rw [← key k ℓ hc hcall]; exact hp, rest⟩
  · rintro ⟨k, ℓ, d, pay, hc, hcall, hp, rest⟩
    exact ⟨k, ℓ, d, pay, hc, hcall, by rw [key k ℓ hc hcall]; exact hp, rest⟩

theorem HonestProposal.toU {tr : SATrace sp FGP ro} {p : Fin sp.n} {s : Nat} {P : Blk sp.n FGP}
    (h : HonestProposal tr p s P) : HonestProposalU (parentOracle sp tr) tr p s P :=
  (honestProposalU_parent_iff tr p s P).2 h

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

/-- A driven parent trace is driven at the parent's oracle. -/
theorem Driven.toU {proposer : Nat → Fin sp.n} {tr : SATrace sp FGP ro} {H : Set (Fin sp.n)}
    (h : Driven proposer tr H) : DrivenU (parentOracle sp tr) proposer tr H where
  blocks := h.blocks
  honest_slot y hy i B hB hg hp := (h.honest_slot y hy i B hB hg hp).toU
  tick := h.tick
  proposal s hs p hp hps ha hj := by
    obtain ⟨k, ℓ, hc, hcall, ht, himp⟩ := h.proposal s hs p hp hps ha hj
    exact ⟨k, ℓ, hc, hcall, ht, fun hpay => (himp hpay).imp fun _ hP => hP.toU⟩
  tick_first := h.tick_first
  proposal_first := h.proposal_first

end Consensus.Goldilocks.SA

end
