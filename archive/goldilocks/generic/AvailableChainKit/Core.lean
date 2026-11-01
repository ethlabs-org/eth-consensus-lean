module
public import Mathlib.Tactic.Linarith
public import AvailableChainStatements.Generic.Properties

@[expose] public section

namespace AvailableChain.Framework.Kit

open AvailableChain AvailableChain.Generic AvailableChain.Statements.Generic

variable {V : Type} [DecidableEq V] {n : Nat} {P : ProtocolSpec n}

theorem block_preceq_trans (A B C : Block) :
    Block.Preceq A B → Block.Preceq B C → Block.Preceq A C := by
  intro hAB hBC
  induction C with
  | genesis =>
      have hB : B = .genesis := by simpa [Block.Preceq, Block.preceq] using hBC
      subst hB; exact hAB
  | node p s r_s x ih =>
      unfold Block.Preceq Block.preceq at hBC
      rcases Bool.or_eq_true_iff.mp hBC with h | h
      · have : B = .node p s r_s x := of_decide_eq_true h
        subst this; exact hAB
      · have := ih h
        unfold Block.Preceq Block.preceq
        exact Bool.or_eq_true_iff.mpr (Or.inr this)

/-- Persistent inclusion follows from safety and exact-time inclusion with
the same `D` (design §4, derived lemma; user decision 2026-09-28). -/
theorem includedPersist_of_safe (E : Env V) (I : Interface P) (rho : Run V P)
    (g : Output P) (t₀ D : Time) (hsafe : SafeFrom P rho g t₀)
    (hinc : IncludedFrom P E I rho g t₀ D) :
    ∀ s : Slot, t₀ < P.proposalTime s → HonestAwakeProposer E rho s →
      P.proposalTime s + D ≤ rho.horizon → 0 ≤ D →
      ∃ B, HonestProposalAt E I rho s B ∧
        ∀ t, P.proposalTime s + D ≤ t → t ≤ rho.horizon → InBy P rho g B t := by
  intro s hs hp hh hD
  obtain ⟨B, hB, hin⟩ := hinc s hs hp hh
  refine ⟨B, hB, fun t ht htH v hv => ?_⟩
  exact block_preceq_trans _ _ _ (hin v hv)
    (hsafe.monotone v hv _ _ (by linarith) ht htH)

end AvailableChain.Framework.Kit

end
