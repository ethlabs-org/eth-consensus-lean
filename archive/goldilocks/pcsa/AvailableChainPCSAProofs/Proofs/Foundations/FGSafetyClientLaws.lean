module
public import AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyClient
public import AvailableChainPCSAProofs.Proofs.Foundations.TickOutput
public import AvailableChainKitFG.ClientOnceSafety
public import AvailableChainKitFG.WeightsBridge

public section

/-! PC-SA client and unit laws for the generic FG safety lift (FG finality
safety, step S6-P). Both FG modes. The FG duty runs `attest` with seat `0`;
the row body does not depend on the seat, and the decoder reads the signer
from the actual FG seat. -/

namespace AvailableChain.PCSA.Run
open AvailableChain.SimplexFG AvailableChain.FGCompose
variable {p : Params} {In : Type} {c : AppCodec In}

/-- The released body of `attest` does not depend on the seat. -/
theorem pcsa_attest_signer_irrel (st : State p.n) (Λ : RecordOnce) (i j : Fin p.n) :
    (attest p st Λ i).1 = (attest p st Λ j).1 := by
  have h := congrArg (Option.map (fun k : NamedHeightPair × Option FinalityPair =>
    RowPayload.vote ⟨k.1, k.2⟩))
    (KitFG.createRowOnce_signer_irrel p.E p.cfg Λ i j (fgInputs p st).1 (fgInputs p st).2).1
  rw [Option.map_map, Option.map_map] at h
  exact h

/-- The seat-`0` row body, released under seat `j`, decodes to the client row
of signer `j`. -/
theorem pcsa_attest_decode_rows (st : State p.n) (Λ : RecordOnce) (j : Fin p.n) :
    ((attest p st Λ ⟨0, p.nPos⟩).1.toList.map
        (fun body => ofRow p ⟨.seat .fg j, body⟩)).filterMap (decodeSafetyRow p) =
      (createRowOnce p.E p.cfg Λ j (fgInputs p st).1 (fgInputs p st).2).1.toList := by
  rw [pcsa_attest_signer_irrel st Λ ⟨0, p.nPos⟩ j]
  change (((createRowOnce p.E p.cfg Λ j (fgInputs p st).1 (fgInputs p st).2).1.map
      (fun a => RowPayload.vote (RowBody.ofRow a))).toList.map
        (fun body => ofRow p ⟨.seat .fg j, body⟩)).filterMap (decodeSafetyRow p) = _
  cases ha : (createRowOnce p.E p.cfg Λ j (fgInputs p st).1 (fgInputs p st).2).1 with
  | none => rfl
  | some a =>
      obtain ⟨_, _, _, _, he, _, _, _⟩ :=
        KitFG.createRowOnce_released p.E p.cfg Λ j (fgInputs p st).1 (fgInputs p st).2 ha
      subst he
      rfl

/-- The tick law of the client: the decoded self-visible output is the client
row of the actual FG seat when the FG duty is enabled, and nothing otherwise. -/
theorem pcsa_safety_tick_rows (m : FGMode) (p : Params) {In : Type} (c : AppCodec In)
    {V : Type} [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (e : Fin p.n ≃ V)
    (he : ∀ i, rho.seatOf (pcsaSafetyReads m p c).fgLabel
      ((pcsaSafetyReads m p c).fgSeats i) = e i)
    (nd : Node p) (x : V) (t : Time) :
    ((V2.D.tick E rho nd x t).2.filter (pcsaWith m p c).objSelfVisible).filterMap
        (pcsaSafetyReads m p c).decodeObject =
      if E.awake x t = true ∧ (pcsaSafetyReads m p c).enabled t = true then
        (createRowOnce p.E p.cfg ((pcsaSafetyReads m p c).record nd) (e.symm x)
          ((pcsaSafetyReads m p c).inputs ((pcsaWith m p c).clock nd t)).1
          ((pcsaSafetyReads m p c).inputs ((pcsaWith m p c).clock nd t)).2).1.toList
      else [] := by
  rw [pcsaSafetyReads_def] at he ⊢
  dsimp only at he ⊢
  have he' : ∀ j, rho.seatOf (.base .fg) j = e j := he
  rw [pcsa_tick_rows_of_seats m E rho e he' nd x t]
  change List.filterMap (decodeSafetyRow p) _ =
    if E.awake x t = true ∧ safetyEnabled m p t = true then
      (createRowOnce p.E p.cfg nd.record (e.symm x) (fgInputs p (PCSA.clock p nd.st t)).1
        (fgInputs p (PCSA.clock p nd.st t)).2).1.toList
    else []
  by_cases hw : E.awake x t = true
  · cases m with
    | idle =>
        rw [ite_eq_right (fun h => FGMode.noConfusion h.2.1),
          ite_eq_right (fun h => Bool.false_ne_true h.2)]
        rfl
    | on =>
        by_cases ha : p.actionTime ((p.slotOf t - 1) / p.R) = t
        · have hen : safetyEnabled .on p t = true := decide_eq_true ha
          rw [ite_eq_left ⟨hw, rfl, ha⟩, ite_eq_left ⟨hw, hen⟩]
          exact pcsa_attest_decode_rows _ _ _
        · have hen : ¬ safetyEnabled .on p t = true := fun h => ha (of_decide_eq_true h)
          rw [ite_eq_right (fun h => ha h.2.2), ite_eq_right (fun h => hen h.2)]
          rfl
  · rw [ite_eq_right (fun h => hw h.1), ite_eq_right (fun h => hw h.1)]
    rfl

/-- The safety reads take the record of the node. -/
theorem pcsa_safetyReads_record (m : FGMode) (p : Params) {In : Type} (c : AppCodec In) :
    (pcsaSafetyReads m p c).record = Node.record := by
  rw [pcsaSafetyReads_def]

/-- The PC-SA client laws, in both FG modes. -/
theorem pcsaSafetyClientLaws (m : FGMode) (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyClientLaws (pcsaSafetyReads m p c) p.E p.cfg where
  initial_record := pcsa_safety_initial_record m p c
  clock_record nd t := (pcsa_safety_clock_record m p c nd t).trans
    (congrFun (pcsa_safetyReads_record m p c) nd).symm
  process_record nd o := (pcsa_safety_process_record m p c nd o).trans
    (congrFun (pcsa_safetyReads_record m p c) nd).symm
  restart_record nd := (pcsa_safety_restart_record m p c nd).trans
    (congrFun (pcsa_safetyReads_record m p c) nd).symm
  own_record nd o := (pcsa_safety_own_record m p c nd o).trans
    (congrArg (fun r => safetyRecordStep (pcsaSafetyReads m p c) r o)
      (congrFun (pcsa_safetyReads_record m p c) nd).symm)
  tick_rows := by
    intro V _ E rho e he nd x t
    exact pcsa_safety_tick_rows m p c E rho e he nd x t

/-- The PC-SA electorate has unit weights and the FG quorum. -/
theorem pcsaSafetyUnitLaws (p : Params) : FGSafetyUnitLaws p.E where
  n_pos := p.nPos
  total := by
    change (∑ _i : Fin p.n, (1 : Nat)) = p.n
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  weight A := by
    change (∑ _i ∈ A, (1 : Nat)) = A.card
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
  quorum := (KitFG.toWeights_q p.E).symm.trans (KitFG.unit_toWeights_q p.n)

end AvailableChain.PCSA.Run
end
