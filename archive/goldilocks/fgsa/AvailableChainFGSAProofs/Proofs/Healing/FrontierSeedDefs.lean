module
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchStop

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

/-! The seed predicate has no dependency on object-service proof inputs. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def p0d5aSeedTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d5aSeedTimingLaws (p : Params) :
    FGCompose.FGTimingLaws (p0d5aSeedTiming p) where
  delta_pos := p.deltaPos
  rounds := p.RLarge
  proposal_eq s := by
    change 4 * p.Δ * (s : Time) = 4 * (s : Time) * p.Δ
    ring
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq _ := rfl


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:915–944 and H.6-S:988–1025.
DC: SAME the two-arm seed premise of the frozen TFrontier. -/
def FrontierSeedQualification (p : Params) {V : Type} (E : Generic.Env V)
    (u : Time) (q : Slot) : Prop :=
  (∃ β : Slot,
    u < SA.proposalTime p.toParams β ∧
    (∀ b, u < SA.proposalTime p.toParams b → β ≤ b) ∧
    SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams q) ∨
  (∃ b : Slot,
    u ≤ SA.voteTime p.toParams b ∧
    (∀ i, u ≤ SA.voteTime p.toParams i → b ≤ i) ∧
    p.k ≤ b + 1 ∧
    E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k) ∧
    SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams q)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1333–1350; TF-SEED Q4.
DC: SAME an explicit equation adapter for the frozen two-arm seed premise. -/
theorem frontierSeedQualification_iff (p : Params) {V : Type} (E : Generic.Env V)
    (u : Time) (q : Slot) : FrontierSeedQualification p E u q ↔
  (∃ β : Slot,
    u < SA.proposalTime p.toParams β ∧
    (∀ b, u < SA.proposalTime p.toParams b → β ≤ b) ∧
    SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams q) ∨
  (∃ b : Slot,
    u ≤ SA.voteTime p.toParams b ∧
    (∀ i, u ≤ SA.voteTime p.toParams i → b ≤ i) ∧
    p.k ≤ b + 1 ∧
    E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k) ∧
    SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams q) := by
  exact FGCompose.FrontierSeedQualification_def (p0d5aSeedTiming p) p.k E.t_GST u q


/-- A qualified seed has the earlier cutoff needed by its prior-slot readers. -/
theorem frontier_seed_prior_cut {p : Params} {V : Type} {E : Generic.Env V}
    {u : Time} {q : Slot} (hready : recoveryStart p E ≤ u)
    (hseed : FrontierSeedQualification p E u q) :
    E.t_GST ≤ slotStartZ p ((q : Int) - 1) := by
  apply FGCompose.frontier_seed_prior_cut (p0d5aSeedTiming p)
    (p0d5aSeedTimingLaws p) p.k p.kLarge E.t_GST (recoveryStart p E) ?_ hready hseed
  have := healing_recovery_start_lower (p := p) E
  linarith [p.deltaPos]


end AvailableChain.FGSA.Run
end
