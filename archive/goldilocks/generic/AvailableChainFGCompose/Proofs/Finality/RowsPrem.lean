module
public import AvailableChainFGCompose.Proofs.Population.RowsPrem

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable {R : FGCoreReads P n Base Proposal Wire} {S : FGSafetyReads P n Wire}
variable {O : FGObservationReads R} {T : FGTiming}
variable {E : Generic.Env V} {rho : V2.D.Run V P} {I : V2.D.Interface P}
variable {D : FGHistoryWireReads S} {Ef : Electorate (Fin n)}

variable {decodeProposal : P.Object → Option (Slot × Body)}
variable {bodyErase : Body → Block} {bodyRows : Body → List Wire}
variable {blockWireRows : P.State → List Wire}
variable {parentFG : P.State → Block → Option (FGBlock (Fin n))}
variable {parentHeight : P.State → Slot → FGBlock (Fin n) → Height × BlockId}
variable {validFor : P.State → Slot → FGBlock (Fin n) → Wire → Bool}
variable {makeFG : FGBlock (Fin n) → Block → List Wire → FGBlock (Fin n)}
variable {valid : Wire → Bool} {ac : FGACServiceReads V}
variable {cfg : FGConfig} {K : Nat} {ΔF : Time} {sp : FGServicePoint} {pt : KernelPt} {A : Block}
variable (m : KernelMiddleWitness_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
  blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A)


private def popc_middle_holder :
    KernelMiddleWitnessFG_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A := {
    A₀ := m.A₀
    B := m.B
    U := m.U
    X_D := m.X_D
    cD := m.cD
    d := m.d
    opening := m.opening
    eraseA := m.eraseA
    carrierA := m.carrierA
    carrierB := m.carrierB
    carrierD := m.carrierD
    honestB := m.honestB
    honestD := m.honestD
    slotA := m.slotA
    slotB := m.slotB
    slotD := m.slotD
    earlySlot := m.earlySlot
    heightA := m.heightA
    highA := m.highA
    heightB := m.heightB
    entryB := m.entryB
    freshEntry := m.freshEntry
    strictAU := m.strictAU
    pathUB := m.pathUB
    freshSlot := m.freshSlot
    parentAB := m.parentAB
    parentBD := m.parentBD
    sourceA := m.sourceA
    sourceB := m.sourceB
    serviceD := m.serviceD
    heightD := m.heightD
    justifiedD := m.justifiedD
    justifiedHeightD := m.justifiedHeightD
    pendingD := m.pendingD
    retainedD := m.retainedD
    noFirstHeight := m.noFirstHeight
    noSecondHeight := m.noSecondHeight
    noEarlyFinality := m.noEarlyFinality
    chainA := m.chainA
    chainB := m.chainB
    chainD := m.chainD
    freshD := m.freshD
    noMixedD := m.noMixedD
    batchB := m.batchB
    batchD := m.batchD
    targetsB := fun _ hi => m.targetsB _ hi
    actionsInRun := m.actionsInRun
    capThroughBAction := m.capThroughBAction
    capThroughFinalAction := m.capThroughFinalAction
    finalityThroughFinalAction := m.finalityThroughFinalAction
    heldDAtFinalAction := m.heldDAtFinalAction
    heldAAtEnd := m.heldAAtEnd
  }

/-- The selected action head consumes the exact walk and the middle's held caps. -/
theorem rowsPrem_pending_head (height : FGHeightLaws Ef O.height)
    (bridge : HeightBridge Ef cfg O.height)
    (read : ∀ x nd, postClock E rho x (T.action (pt.r + 2)) = some nd →
      (R.core (V2.D.Run.stateBefore E rho (afterTicksIdx rho (T.action (pt.r + 2))) x)).fg =
        (R.core nd).fg)
    (head : ∀ x nd, x ∈ rho.honest → postClock E rho x (T.action (pt.r + 2)) = some nd →
      ∃ H, R.finalityHead nd = some H ∧ H ∈ (R.core nd).fg.TF)
    (walk : ∀ x nd, x ∈ rho.honest → postClock E rho x (T.action (pt.r + 2)) = some nd →
      ∀ H, R.finalityHead nd = some H → Block.Preceq (R.erase m.X_D) (R.erase H))
    (reflect : ∀ nd A B, A ∈ (R.core nd).fg.TF → B ∈ (R.core nd).fg.TF →
      Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B) :
    ∀ x nd, x ∈ rho.honest → postClock E rho x (T.action (pt.r + 2)) = some nd →
      ∃ H, R.finalityHead nd = some H ∧ FGBlock.Preceq m.X_D H ∧
        (O.height H).h = m.d + 2 ∧ (O.height H).J = m.U ∧
        (O.height H).h_j = m.d + 1 ∧ (O.finality H).h_F < m.d + 1 ∧
        (O.height H).T_h = (O.height m.X_D).T_h := by
  exact rowsPrem_pending_head_holder (popc_middle_holder m) height bridge read head walk reflect

/-- The opening/covered supplier produces an actual source at the middle action. -/
theorem rowsPrem_action_source (CL : FGCoreLaws R) (height : FGHeightLaws Ef O.height)
    (read : ∀ x nd, postClock E rho x (T.action (pt.r + 2)) = some nd →
      (R.core (V2.D.Run.stateBefore E rho (afterTicksIdx rho (T.action (pt.r + 2))) x)).fg =
        (R.core nd).fg)
    (service : ∀ x, x ∈ rho.honest → FGSourceService R E rho x (T.action (pt.r + 2))
      m.cD ((pt.r + 2) * T.roundSlots) m.X_D) :
    ∀ x ∈ rho.honest, ∃ nd C,
      postClock E rho x (T.action (pt.r + 2)) = some nd ∧ R.source nd = some C ∧
      FGBlock.Preceq m.X_D C ∧ (O.height C).h = m.d + 2 ∧
      (O.height C).T_h = (O.height m.X_D).T_h := by
  exact rowsPrem_action_source_holder (popc_middle_holder m) CL height read service

/-- The actual earlier sources and the middle cap bound the anchor height. -/
theorem rowsPrem_anchor_cap (CL : FGCoreLaws R) (L : FGTimingLaws T)
    (hs : V2.D.ScheduleWellFormed E rho) (names : HighRecordNames R S O T E rho D)
    (hcapBefore : ∀ (cut : Time) (b i : Nat) (x : V) (W : FGBlock (Fin n)),
      i ≤ V2.D.Run.idxBefore rho cut → HeldAt R E rho i x W →
      (∀ j z r a u h B timeout, HonestRowAt S E rho T j z r a →
        S.decode a = some u → u.height_pair = .vote h B timeout →
        T.action r < cut → h < b + 1) → (O.height W).h < b + 2) :
    ∀ i x W, i ≤ V2.D.Run.idxBefore rho (T.action (pt.r + 3)) →
      HeldAt R E rho i x W → (O.height W).h ≤ m.d + 3 := by
  exact rowsPrem_anchor_cap_holder (popc_middle_holder m) CL L hs names hcapBefore

/-- The same pending key survives the proved anchor cap or is already covered. -/
theorem rowsPrem_anchor_retained_or_covered
    (height_eq : O.height = KitFG.Window.heightView Ef cfg K)
    (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K) (B : FGBlock (Fin n))
    (hDB : FGBlock.Preceq m.X_D B) (hcap : (O.height B).h ≤ m.d + 3) :
    KitFG.Window.RetainedW Ef cfg K B (m.d + 1) m.U ∨
      KitFG.Window.CoveredW Ef cfg K B (m.d + 1) m.U := by
  exact rowsPrem_anchor_retained_or_covered_holder (popc_middle_holder m)
    height_eq hne hK B hDB hcap

/-- Combine the proved action source, pending head, and record guards at one action. -/
theorem rowsPrem_fresh_rows (height : FGHeightLaws Ef O.height)
    (bridge : HeightBridge Ef cfg O.height)
    (makeWire : Row (Fin n) → Wire)
    (wireDecode : ∀ row, S.decode (makeWire row) = some row)
    (wireValid : ∀ i y U B,
      valid (makeWire ⟨i, .vote (y + 1) B false, some ⟨y, U⟩⟩) = true)
    (client : ∀ nd, (S.inputs nd).1 = R.source nd)
    (release : ∀ i q nd row,
      postClock E rho (safetyHolder S rho i) (T.action q) = some nd →
      E.awake (safetyHolder S rho i) (T.action q) = true →
      (createRowOnce Ef cfg (S.record nd) i (S.inputs nd).1 (S.inputs nd).2).1 = some row →
      ∃ j, rho.events[j]? = some (.tick (safetyHolder S rho i) (T.action q)) ∧
        S.encode (makeWire row) ∈ V2.D.Run.emitsAt E rho j)
    (sources : ∀ x ∈ rho.honest, ∃ nd C,
      postClock E rho x (T.action (pt.r + 2)) = some nd ∧ R.source nd = some C ∧
      FGBlock.Preceq m.X_D C ∧ (O.height C).h = m.d + 2 ∧
      (O.height C).T_h = (O.height m.X_D).T_h)
    (heads : ∀ x nd, x ∈ rho.honest →
      postClock E rho x (T.action (pt.r + 2)) = some nd →
      ∃ H, R.finalityHead nd = some H ∧ FGBlock.Preceq m.X_D H ∧
        (O.height H).h = m.d + 2 ∧ (O.height H).J = m.U ∧
        (O.height H).h_j = m.d + 1 ∧ (O.finality H).h_F < m.d + 1 ∧
        (O.height H).T_h = (O.height m.X_D).T_h)
    (fields : ∀ nd H, R.finalityHead nd = some H →
      (S.inputs nd).2 = certificateHeadFields O.height O.finality H)
    (records : ∀ x nd, x ∈ rho.honest →
      postClock E rho x (T.action (pt.r + 2)) = some nd →
      HighRecordGuard_W (S.record nd) (m.d + 1) m.U ∧
        HighRecordFresh (m.d + 2) (S.record nd))
    (L : FGTimingLaws T) (seats : Finset (Fin n))
    (hS : ∀ i ∈ seats, safetyHolder S rho i ∈ rho.honest) (hQ : Ef.IsQuorum seats)
    (awake : ∀ x ∈ rho.honest, E.awake x (T.action (pt.r + 2)) = true) :
    ∃ rows : Fin n → Wire,
      FreshFinalityRows_W R S O T E rho D Ef valid (pt.r + 2) (m.d + 1) m.U seats rows ∧
      (∀ i ∈ seats, namedEntry (D.heightPair (rows i)) =
        some (m.d + 2, (O.height m.X_D).T_h.root)) ∧
      (∀ i ∈ seats, D.heightPair (rows i) =
        .vote (m.d + 2) (O.height m.X_D).T_h.root false) := by
  exact rowsPrem_fresh_rows_holder (popc_middle_holder m) height bridge makeWire wireDecode
    wireValid client release sources heads fields records L seats hS hQ awake

end AvailableChain.FGCompose
end
