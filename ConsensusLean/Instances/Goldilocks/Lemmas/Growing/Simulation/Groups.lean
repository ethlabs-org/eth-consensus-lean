module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Events
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.GoldilocksStateAgreement

public section

/-! # Coverage by canonical handler groups -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- Every labelled cut, including one preceding a later compromise, belongs to a handler. -/
theorem simTraceAt_grouped (hv : rho.ExecutionValid) :
    ∀ y i c, (simTraceAt S rho hn).CallAt y i c →
      ∃ j e, (simTraceAt S rho hn).InGroup (runProposer S rho hn)
        (digestOf S rho) y j i ((simTraceAt S rho hn).time i) e := by
  obtain ⟨hpr, hdg⟩ := runProposer_digestOf S rho hn
  rw [simTraceAt_eq, (simTrace_encoding S rho hn).1, hpr, hdg]
  exact NodeAsChainShape.CanonicalTrace.grouped _ rho (traceEncoding_lawful S hn) hv

/-- The canonical record expansion obeys the handler cut law at every actual call. -/
theorem simTraceAt_cutLaw (hv : rho.ExecutionValid) :
    ∀ y i c, (simTraceAt S rho hn).CallAt y i c →
      CutStep y ((simTraceAt S rho hn).time i) ((simTraceAt S rho hn).state y i) c
        ((simTraceAt S rho hn).post i) := by
  rw [simTraceAt_eq, (simTrace_encoding S rho hn).1]
  exact NodeAsChainShape.CanonicalTrace.cutLaw _ rho (traceEncoding_lawful S hn) hv

/-- Every trace state's vote permission is its node's installed membership: the init
installs it, and every cut keeps it (the canonical cut law holds with no honesty premise). -/
theorem simTraceAt_mayVote (hv : rho.ExecutionValid) (y : Fin (Fintype.card V)) (i : Nat) :
    ((simTraceAt S rho hn).state y i).ac.mayVote =
      fun s => decide (y ∈ rho.sel (S.vote.voteRole s)) := by
  induction i with
  | zero =>
    change ((simTraceAt S rho hn).init y).ac.mayVote = _
    rw [simTraceAt_eq, simTrace_init_eq]
    funext s
    change (S.vote.installVote _ _).mayVote s = _
    cases hp : S.vote.participationKind with
    | none =>
      have hr : S.vote.voteRole s = .poll := by simp [VoteBinding.voteRole, hp]
      rw [hr]
      simp only [VoteBinding.installVote, hp]
      have hsel := poll_selected S rho hv (rho.key y)
      rw [ownKey_key] at hsel
      exact (decide_eq_true hsel).symm
    | some k => exact S.vote.installVote_mayVote (by simp [hp]) _ _ s
  | succ i ih =>
    by_cases hc : ∃ c, (simTraceAt S rho hn).CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      have hstep := simTraceAt_cutLaw S rho hn hv y i c hc
      rw [(simTraceAt S rho hn).state_succ_of_call hc, ← ih]
      cases c with
      | ac ℓ =>
        obtain ⟨-, he, -, -⟩ := hstep
        have h₁ := AC.step_mayVote y ((simTraceAt S rho hn).state y i).ac ℓ.frame
          ((simTraceAt S rho hn).time i) ℓ.call
        rw [he] at h₁
        exact h₁
      | fg f =>
        cases f with
        | block B acc =>
          cases acc
          · rw [hstep.2]
          · rw [hstep.2.2.1]
        | attestation a => rw [hstep.2.1]
        | attest C r =>
          cases r
          · rw [hstep.2]
          · rw [hstep.2.2]
    · rw [(simTraceAt S rho hn).state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
      exact ih

end Consensus.Goldilocks.Simulation
