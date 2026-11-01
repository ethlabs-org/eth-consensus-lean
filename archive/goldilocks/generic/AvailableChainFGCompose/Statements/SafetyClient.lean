module
public import AvailableChainFGCompose.Statements.SafetyReads
public import AvailableChainGeneric.Statements.Pure.Quorum

@[expose] public section

/-! PROVISIONAL safety contracts. S1 does not freeze these laws. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In}
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
variable (S : FGSafetyReads P n Wire)
variable (Ef : Electorate (Fin n)) (H : FGHeightView (Fin n))
variable (f : FGFinalityView (Fin n)) (cfg : FGConfig)
variable [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V P)

structure FGSafetyClientLaws (S : FGSafetyReads P n Wire)
    (Ef : Electorate (Fin n)) (cfg : FGConfig) : Prop where
  initial_record : S.record P.init = RecordOnce.initial
  clock_record : ∀ nd t, S.record (P.clock nd t) = S.record nd
  process_record : ∀ nd o, S.record (P.process nd o) = S.record nd
  restart_record : ∀ nd t,
    S.record (P.restore (P.durable nd) t) = S.record nd
  own_record : ∀ nd o, S.record (P.recordOwn nd o) =
    safetyRecordStep S (S.record nd) o
  tick_rows : ∀ {V : Type} [DecidableEq V] (E : Generic.Env V)
      (rho : V2.D.Run V P) (e : Fin n ≃ V),
      (∀ i, rho.seatOf S.fgLabel (S.fgSeats i) = e i) →
      ∀ nd x t,
        ((V2.D.tick E rho nd x t).2.filter P.objSelfVisible).filterMap
            S.decodeObject =
          if E.awake x t = true ∧ S.enabled t = true then
            (createRowOnce Ef cfg (S.record nd) (e.symm x)
              (S.inputs (P.clock nd t)).1 (S.inputs (P.clock nd t)).2).1.toList
          else []
structure FGSafetyUnitLaws (Ef : Electorate (Fin n)) : Prop where
  n_pos : 0 < n
  total : Ef.totalWeight = n
  weight : ∀ A : Finset (Fin n), Ef.weightOf A = A.card
  quorum : Ef.q = Gen.Pure.qF n
end AvailableChain.FGCompose
end
