module
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionArithmetic
public import AvailableChainFGSAProofs.Proofs.Healing.CommonEntryHeight -- shake: keep (axiom audit)
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionRows

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run.Tests.P0d3
open AvailableChain.SimplexFG

private abbrev d3a_params : Params :=
  { Δ := 1, n := 1, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 4, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

private theorem d3a_gap_rounding :
    5 ≤ Γ d3a_params 5 ∧ Γ d3a_params 5 < 5 + 4 * d3a_params.Δ :=
  healing_promotion_gap_remainder d3a_params 5
private theorem d3a_maturity :
    (.genesis : FGBlock (Fin d3a_params.n)).slot + d3a_params.δt ≤ 4 :=
  healing_promotion_maturity d3a_params rfl (by decide)

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

-- The production wrapper uses exactly its old hypotheses.
private theorem d3a_fixed_wrapper (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {r height : Nat} {Q : Block} (hentry : OpeningEntry p c E rho r height)
    (hcovered : OpeningCovered p c E rho r Q) :
    ∃ U : FGBlock (Fin p.n), EntryAt p U height ∧
      ∀ x ∈ rho.honest, ∃ K nd j rSent a,
        postClock E rho x (p.actionTime r) = some nd ∧
        actionSourceFG p c E rho x r = some (some K) ∧ K ∈ FGSA.fullTree p nd.st ∧
        Block.Preceq Q (eraseFG K) ∧ FGBlock.Preceq U K ∧ K.slot ≤ r * p.R ∧
        (heightView p K).h = height ∧ (heightView p K).T_h = U ∧
        rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        NamesEntry p .progress a height U :=
  healing_promotion_fixed_rows E rho hrec hentry hcovered

-- The production wrapper uses exactly its old hypotheses.
private theorem d3a_parent_wrapper (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
 {u : Time} {m : Nat}
    {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {r height : Nat} {s : Slot} {Q : Block} {X : FGBlock (Fin p.n)}
    (hentry : OpeningEntry p c E rho r height) (hcovered : OpeningCovered p c E rho r Q)
    (_hready : recoveryStart p E ≤ u)
    (_hphase : PhaseInterval p c E rho u (SA.proposalTime p.toParams s) m J contested)
    (_hu : u ≤ SA.voteTime p.toParams (r * p.R))
    (_hgate : p.actionTime r ≤ SA.proposalTime p.toParams s) (_hs : r * p.R + 2 ≤ s)
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X)) (hslot : X.slot = s)
    (hParents : ∀ x ∈ rho.honest, ∀ K,
      actionSourceFG p c E rho x r = some (some K) →
      Block.Preceq (eraseFG K) (eraseFG X).parent) :
    ∃ U : FGBlock (Fin p.n), EntryAt p U height ∧ U.slot ≤ r * p.R ∧
      FGBlock.Preceq U X.parent ∧
      ∀ x ∈ rho.honest, ∃ K nd j rSent a,
        postClock E rho x (p.actionTime r) = some nd ∧
        actionSourceFG p c E rho x r = some (some K) ∧ K ∈ FGSA.fullTree p nd.st ∧
        Block.Preceq Q (eraseFG K) ∧ FGBlock.Preceq U K ∧ K.slot ≤ r * p.R ∧
        (heightView p K).h = height ∧ (heightView p K).T_h = U ∧
        rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        NamesEntry p .progress a height U ∧
        ((heightView p X.parent).h = height →
          ValidForParent p c E rho X.slot (eraseFG X) a ∧
          HeightMatch p c E rho X.slot (eraseFG X) a) :=
  healing_promotion_same_rows_on E rho hrec hentry hcovered
    _hready _hphase _hu _hgate _hs hnew hslot hParents

#print axioms d3a_gap_rounding
#print axioms d3a_maturity
#print axioms d3a_fixed_wrapper
#print axioms d3a_parent_wrapper
#print axioms AvailableChain.FGSA.Run.healing_promotion_gap_remainder
#print axioms AvailableChain.FGSA.Run.healing_promotion_held_mono
#print axioms AvailableChain.FGSA.Run.healing_promotion_gap
#print axioms AvailableChain.FGSA.Run.healing_promotion_row_deadline
#print axioms AvailableChain.FGSA.Run.healing_promotion_row_deadline_strict
#print axioms AvailableChain.FGSA.Run.healing_promotion_row_receipt
#print axioms AvailableChain.FGSA.Run.healing_promotion_row_receipt_strict
#print axioms AvailableChain.FGSA.Run.healing_promotion_maturity
#print axioms AvailableChain.FGSA.Run.healing_promotion_maturity_of_action
#print axioms AvailableChain.FGSA.Run.healing_promotion_age_gap
#print axioms AvailableChain.FGSA.Run.common_first_opening_labels
#print axioms AvailableChain.FGSA.Run.common_first_time_bound
#print axioms AvailableChain.FGSA.Run.common_source_tick
#print axioms AvailableChain.FGSA.Run.common_source_height_le
#print axioms AvailableChain.FGSA.Run.common_source_below_raw
#print axioms AvailableChain.FGSA.Run.common_sources_compatible
#print axioms AvailableChain.FGSA.Run.common_entry_of_plateau
#print axioms AvailableChain.FGSA.Run.common_low_or_high
#print axioms AvailableChain.FGSA.Run.common_sources_extend_and_cap
#print axioms AvailableChain.FGSA.Run.common_entry_at_high
#print axioms AvailableChain.FGSA.Run.common_next_sources_extend_and_cap
#print axioms AvailableChain.FGSA.Run.common_next_entry
#print axioms AvailableChain.FGSA.Run.common_entry_at_low
#print axioms AvailableChain.FGSA.Run.healing_promotion_fixed_rows
#print axioms AvailableChain.FGSA.Run.healing_promotion_entry_slot
#print axioms AvailableChain.FGSA.Run.healing_promotion_bounded_rows
#print axioms AvailableChain.FGSA.Run.healing_promotion_source_body
#print axioms AvailableChain.FGSA.Run.healing_promotion_source_parent
#print axioms AvailableChain.FGSA.Run.healing_promotion_continuing_service
#print axioms AvailableChain.FGSA.Run.healing_promotion_same_rows
#print axioms AvailableChain.FGSA.Run.healing_promotion_same_rows_on

end AvailableChain.FGSA.Run.Tests.P0d3
end
