module
public import AvailableChainFGSAProofs.Proofs.Shared.FGCompose -- shake: keep (store-law signature example)
public import AvailableChainFGSARun.Statements.Client -- shake: keep (B1 public client statement interface)
public import AvailableChainFGSAProofs.Proofs.Shared.RowAuth
public import AvailableChainFGSARun.Proofs.ClientTrace
public import AvailableChainFGCompose.Statements.SafetyClient -- shake: keep (client-law signature example)
public import AvailableChainFGCompose.Statements.SafetyStore -- shake: keep (store-law signature example)

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.FGCompose

/-- PROVISIONAL. These are the actual protocol reads. -/
def fgsaSafetyReads (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyReads (fgsa p c) p.n (RowWire p.n) where
  proposalErase := safetyProposalErase p
  proposalRows := safetyProposalRows p
  encode := ofRow p
  decode := RowWire.toRow?
  decodeObject := decodeRowObject p
  fgLabel := .base .fg
  fgSeats := Equiv.refl _
  record := Node.record
  inputs := fun nd => fgInputs p nd.st
  enabled := fun t => decide (p.actionTime ((p.slotOf t - 1) / p.R) = t)
  finalizedOut := finalizedOut
theorem fgsaSafetyReads_def (p : Params) {In : Type} (c : AppCodec In) :
    fgsaSafetyReads p c =
      { proposalErase := safetyProposalErase p
        proposalRows := safetyProposalRows p
        encode := ofRow p
        decode := RowWire.toRow?
        decodeObject := decodeRowObject p
        fgLabel := .base .fg
        fgSeats := Equiv.refl _
        record := Node.record
        inputs := fun nd => fgInputs p nd.st
        enabled := fun t => decide (p.actionTime ((p.slotOf t - 1) / p.R) = t)
        finalizedOut := finalizedOut } := by
  rfl

/-- The producer fits the provisional store-law signature. No law is assumed. -/
example (p : Params) {In : Type} (c : AppCodec In) : Prop :=
  FGSafetyStoreLaws (fgsaCoreReads p c) (fgsaSafetyReads p c)
    (heightView p) (finalityView p) (fun nd => Reachable p nd.st)

example (p : Params) {In : Type} (c : AppCodec In) : Prop :=
  FGSafetyClientLaws (fgsaSafetyReads p c) p.E p.cfg

open AvailableChain.KitFG

/-- The wire adapter preserves signing seats and proposal row carriage. -/
theorem fgsaSafetyWireLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyWireLaws (fgsaSafetyReads p c) where
  encode_injective := ofRow_injective
  decode_encode := by
    intro a
    change decodeRowObject p (ofRow p a) = a.toRow?
    change (match (toWire p (ofRow p a)).payload with
      | .row body => RowWire.toRow? ⟨(toWire p (ofRow p a)).auth, body⟩
      | _ => none) = _
    rw [toWire_ofRow]
  decode_auth := by
    intro a u h
    change (ofRow p a).auth = .seat (.base .fg) u.signer
    rw [ofRow_auth, row_auth_of_toRow a u h]
    rfl
  decoded_visible := by
    intro o u h
    rcases o with ⟨auth, payload⟩
    cases payload with
    | head b => cases h
    | proposal N => cases h
    | row body =>
        cases auth with
        | none => cases h
        | seat l i =>
            cases l with
            | prop s => cases h
            | base l => cases l with
                | head s => cases h
                | fg => rfl
  carried := by
    intro o a h
    change Obj p at o
    change a ∈ safetyProposalRows p o at h
    rw [fgsa_safetyProposalRows_def] at h
    cases hp : o.payload with
    | proposal N =>
        rw [hp] at h
        change a ∈ N.rows at h
        change (match o.payload with
          | .proposal N => ofRow p a ∈ N.raw.map (ofHead p) ∨
              ofRow p a ∈ N.support.map (ofHead p) ∨ ofRow p a ∈ N.rows.map (ofRow p)
          | _ => False)
        rw [hp]
        exact Or.inr (Or.inr (List.mem_map.mpr ⟨a, h, rfl⟩))
    | head b => rw [hp] at h; cases h
    | row b => rw [hp] at h; cases h

/-- The record and tick output implement the persistent FG client. -/
theorem fgsaSafetyClientLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyClientLaws (fgsaSafetyReads p c) p.E p.cfg where
  initial_record := rfl
  clock_record := by intro nd t; rfl
  process_record := by intro nd o; rfl
  restart_record := by intro nd t; rfl
  own_record := by
    intro nd o
    rcases o with ⟨auth, payload⟩
    cases auth with
    | none => cases payload <;> rfl
    | seat l i =>
        cases l with
        | prop s => cases payload <;> rfl
        | base l => cases l <;> cases payload <;> rfl
  tick_rows := by
    intro V _ E rho e he nd x t
    change Node p at nd
    change (((V2.D.tick E rho nd x t).2.filter (fgsa p c).objSelfVisible).filterMap
        (decodeRowObject p)) =
      if E.awake x t = true ∧ decide (p.actionTime ((p.slotOf t - 1) / p.R) = t) = true then
        (createRowOnce p.E p.cfg nd.record (e.symm x)
          (fgInputs p (FGSA.clock p nd.st t)).1
          (fgInputs p (FGSA.clock p nd.st t)).2).1.toList else []
    erw [fgsa_tick_rows_of_seats E rho e he]
    simp only [decide_eq_true_eq]
    by_cases ht : E.awake x t = true ∧ p.actionTime ((p.slotOf t - 1) / p.R) = t
    · rw [ite_eq_left ht, ite_eq_left ht]
      cases ha : (attest p (FGSA.clock p nd.st t) nd.record ⟨0, p.nPos⟩).1 with
      | none =>
          have hj : (attest p (FGSA.clock p nd.st t) nd.record (e.symm x)).1 = none := by
            rw [← attest_signer_irrel _ _ ⟨0, p.nPos⟩ (e.symm x)]
            exact ha
          have hn : (createRowOnce p.E p.cfg nd.record (e.symm x)
              (fgInputs p (FGSA.clock p nd.st t)).1
              (fgInputs p (FGSA.clock p nd.st t)).2).1 = none :=
            Option.map_eq_none_iff.mp hj
          rw [hn]
          rfl
      | some body =>
          have hd := fgsa_attest_decode (FGSA.clock p nd.st t) nd.record (e.symm x) body ha
          change some (body.toRow (e.symm x)) = _ at hd
          rw [← hd]
          rfl
    · rw [ite_eq_right ht, ite_eq_right ht]
      rfl

/-- Each FG seat has weight one and uses the count quorum. -/
theorem fgsaSafetyUnitLaws (p : Params) : FGSafetyUnitLaws p.E where
  n_pos := p.nPos
  total := by
    change (Finset.univ : Finset (Fin p.n)).sum (fun _ => 1) = p.n
    simp
  weight := by
    intro A
    change A.sum (fun _ => 1) = A.card
    simp
  quorum := by
    change (2 * (Finset.univ : Finset (Fin p.n)).sum (fun _ => 1) + 2) / 3 =
      (2 * p.n + 2) / 3
    simp


end AvailableChain.FGSA.Run
end
