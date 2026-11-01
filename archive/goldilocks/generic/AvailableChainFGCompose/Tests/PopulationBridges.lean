module
public import AvailableChainFGCompose.Proofs.Population.Safety
public import AvailableChainFGCompose.Proofs.SafetySlashing

set_option linter.privateModule false

public section

/-! Conditional algebraic specializations, not client/store premise producers.
The separate Population controls provide nonvacuous emitting all-holder witnesses. -/
namespace AvailableChain.FGCompose.Tests.PopulationBridges
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (S : FGSafetyReads P n Wire) (E : Generic.Env V) (rho : V2.D.Run V P)

/-- Old global client laws imply the new actual-tick equation, with exactly the old RHS. -/
private theorem legacy_tick_specialization (Ef : Electorate (Fin n)) (cfg : FGConfig)
    (J : FGSafetyClientLaws S Ef cfg) (e : Fin n ≃ V)
    (he : ∀ i, rho.seatOf S.fgLabel (S.fgSeats i) = e i)
    (Q : FGSelectionReads P n) (client : FGSelectionClientLaws Q S)
    (i : Fin n) (j : Nat) (t : Time) (ht : rho.events[j]? = some (.tick (e i) t)) :
    ((V2.D.Run.emitsAt E rho j).filter P.objSelfVisible).filterMap S.decodeObject =
      if E.awake (e i) t = true ∧ S.enabled t = true then
        (createRowOnce Ef cfg (S.record (V2.D.Run.stateBefore E rho j (e i))) (e.symm (e i))
          (Q.clientInputs (P.clock (V2.D.Run.stateBefore E rho j (e i)) t)).1
          (Q.clientInputs (P.clock (V2.D.Run.stateBefore E rho j (e i)) t)).2).1.toList
      else [] := by
  have hfun : (fun i => e i) = safetyHolder S rho := funext (fun i => (he i).symm)
  have rows := ordinary_FGHolderClientLaws S Ef cfg E rho J e he
  change FGHolderClientLaws S Ef cfg E rho (ordinaryFGExecutionObs E rho) (fun i => e i)
    at rows
  rw [hfun] at rows
  have hh : safetyHolder S rho i = e i := he i
  have h := selection_tick_rows_holder S E rho Ef cfg Q client rows i j t (hh.symm ▸ ht)
  simpa only [hh, J.clock_record, Equiv.symm_apply_apply] using h

/-- The old store/Linked/client premises supply the new minimal safety boundary. -/
private theorem legacy_safety_specialization
    (R : FGCoreReads P n Base Proposal Wire) (Ef : Electorate (Fin n))
    (H : FGHeightView (Fin n)) (f : FGFinalityView (Fin n)) (cfg : FGConfig)
    (Good : P.State → Prop) (C : FGCoreLaws R) (W : FGSafetyWireLaws S)
    (L : FGSafetyStoreLaws R S H f Good) (J : FGSafetyClientLaws S Ef cfg)
    (linked : P.Label → Prop) (hfg : linked S.fgLabel)
    (I : Gen.V2.Duty.SlashingInterface (V := V) P) (hi : safetySlashesRead R S E rho I)
    (hu : V2.D.UnforgeableSignatures E rho) (hl : V2.D.Linked linked rho) :
    Gen.V2.Duty.HonestNeverSlashed I rho := by
  apply safety_honest_never_slashed_holder S E rho R
    (fun t x => safety_read_carriage C L W hu t x) _ I hi
  intro i _
  exact safety_emitted_noSlash S Ef cfg E rho W J linked hfg hl (safetyHolder S rho i)

#print axioms legacy_tick_specialization
#print axioms legacy_safety_specialization

end AvailableChain.FGCompose.Tests.PopulationBridges
end
