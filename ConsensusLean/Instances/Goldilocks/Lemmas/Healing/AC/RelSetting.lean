module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.AC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.RelTrace
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.ACU

public section

/-! # Goldilocks Healing: H.1's vocabulary with the unlock given

H.1's statements read the proposal of an honest proposer through the parent's `ac_proposal`
(`HonestProposal`, `Driven`), whose head depends on the locks after its unlock. Over a trace with
the unlock given by an oracle `u` (`ACLocalRunU`), the proposal is `acProposalWith` at the locks
`u k` of its call (`HonestProposalU`, `DrivenU`, defined in
`Milestones/Statements/Healing/ACU`). At the parent's oracle these are the parent's
(`honestProposalU_parent_iff`, `Driven.toU`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}

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
