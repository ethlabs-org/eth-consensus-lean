module
public import AvailableChainPCSAProofs.Proofs.Shared.FGCompose
public import AvailableChainFGCompose.Statements.SafetyClient
public import AvailableChainFGCompose.Statements.SafetyStore

public section
namespace AvailableChain.PCSA.Run
open AvailableChain.SimplexFG AvailableChain.FGCompose

/-- PROVISIONAL. Mode changes only the honest action hook. -/
def pcsaCoreReadsWith (m : FGMode) (p : Params) {In : Type} (c : AppCodec In) :
    FGCoreReads (pcsaWith m p c) p.n (GridCO.State p.n .root) (Wire p.n) (RowWire p.n) :=
  { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
    erase := PCSA.eraseFG
    source := (pcsaCoreReads p c).source
    headVote := (pcsaCoreReads p c).headVote
    finalityHead := (pcsaCoreReads p c).finalityHead
    proposalFG := (pcsaCoreReads p c).proposalFG }

theorem pcsaCoreReadsWith_def (m : FGMode) (p : Params) {In : Type} (c : AppCodec In) :
    pcsaCoreReadsWith m p c =
      { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
        erase := PCSA.eraseFG
        source := (pcsaCoreReads p c).source
        headVote := (pcsaCoreReads p c).headVote
        finalityHead := (pcsaCoreReads p c).finalityHead
        proposalFG := (pcsaCoreReads p c).proposalFG } := by
  rfl

theorem pcsaCoreReadsWith_on (p : Params) {In : Type} (c : AppCodec In) :
    pcsaCoreReadsWith .on p c = pcsaCoreReads p c := by
  rw [pcsaCoreReadsWith_def, pcsaCoreReads_def]
  rfl

/-- PROVISIONAL. Raw rejected proposals retain their signed row list. -/
def pcsaSafetyReads (m : FGMode) (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyReads (pcsaWith m p c) p.n (RowWire p.n) where
  proposalErase := safetyProposalErase p
  proposalRows := safetyProposalRows p
  encode := ofRow p
  decode := RowWire.toRow?
  decodeObject := decodeSafetyRow p
  fgLabel := .base .fg
  fgSeats := Equiv.refl _
  record := Node.record
  inputs := fun nd => PCSA.fgInputs p nd.st
  enabled := safetyEnabled m p
  finalizedOut := fun nd => PCSA.eraseFG nd.st.fg.F

theorem pcsaSafetyReads_def (m : FGMode) (p : Params) {In : Type} (c : AppCodec In) :
    pcsaSafetyReads m p c =
  { proposalErase := safetyProposalErase p
    proposalRows := safetyProposalRows p
    encode := ofRow p
    decode := RowWire.toRow?
    decodeObject := decodeSafetyRow p
    fgLabel := .base .fg
    fgSeats := Equiv.refl _
    record := Node.record
    inputs := fun nd => PCSA.fgInputs p nd.st
    enabled := safetyEnabled m p
    finalizedOut := fun nd => PCSA.eraseFG nd.st.fg.F } := by
  rfl


theorem pcsa_safety_source_mem (m : FGMode) (p : Params) {In : Type} (c : AppCodec In)
    (nd : Node p) (B : FGBlock (Fin p.n))
    (h : (pcsaCoreReadsWith m p c).source nd = some B) : B ∈ nd.st.fg.TF :=
  pcsa_source_mem_TF p c h

theorem pcsa_safety_own_core (m : FGMode) (p : Params) {In : Type} (c : AppCodec In)
    (nd : Node p) (o : Obj p) :
    (pcsaCoreReadsWith m p c).core ((pcsaWith m p c).recordOwn nd o) =
      (pcsaCoreReadsWith m p c).core nd := by
  rfl

theorem pcsa_safety_encode_injective (p : Params) : Function.Injective (ofRow p) := by
  intro a b h
  have he : (⟨a.auth, Msg.row a.payload⟩ : Wire p.n) = ⟨b.auth, Msg.row b.payload⟩ :=
    (toWireEquiv p).symm.injective h
  have ha := congrArg (fun w : Wire p.n => w.auth) he
  have hp := congrArg (fun w : Wire p.n => w.payload) he
  have hb := Msg.row.inj hp
  cases a
  cases b
  cases ha
  cases hb
  rfl

theorem pcsa_safety_decode_encode (p : Params) (a : RowWire p.n) :
    decodeSafetyRow p (ofRow p a) = a.toRow? := by
  rcases a with ⟨auth, body⟩
  cases auth with
  | none => rfl
  | proposer s => rfl
  | seat l i => cases l <;> rfl

theorem pcsa_safety_row_auth {n : Nat} (a : RowWire n) (u : Row (Fin n))
    (h : a.toRow? = some u) : a.auth = .seat .fg u.signer := by
  rcases a with ⟨auth, body⟩
  cases auth with
  | none => cases h
  | proposer s => cases h
  | seat l i =>
      cases l with
      | head s => cases h
      | ack s => cases h
      | fg =>
          have he : body.toRow i = u := Option.some.inj h
          rw [← he]
          rfl

theorem pcsa_safety_decode_auth (p : Params) (a : RowWire p.n) (u : Row (Fin p.n))
    (h : a.toRow? = some u) : (ofRow p a).auth = .seat (.base .fg) u.signer := by
  change ofAuth p a.auth = _
  rw [pcsa_safety_row_auth a u h]
  rfl

theorem pcsa_safety_decoded_visible (m : FGMode) (p : Params) {In : Type}
    (c : AppCodec In) (o : Obj p) (u : Row (Fin p.n))
    (h : decodeSafetyRow p o = some u) : (pcsaWith m p c).objSelfVisible o = true := by
  rcases o with ⟨auth, payload⟩
  cases payload with
  | head b => cases h
  | proposal N => cases h
  | ack b => cases h
  | pc cert => cases h
  | row body =>
      cases auth with
      | none => cases h
      | seat l i =>
          cases l with
          | prop s => cases h
          | base l => cases l with
              | head s => cases h
              | ack s => cases h
              | fg => rfl

theorem pcsa_safety_carried (m : FGMode) (p : Params) {In : Type} (c : AppCodec In)
    (o : Obj p) (a : RowWire p.n) (h : a ∈ safetyProposalRows p o) :
    (pcsaWith m p c).carries o (ofRow p a) := by
  rw [pcsa_safetyProposalRows_def] at h
  cases hp : o.payload with
  | proposal N =>
      rw [hp] at h
      change a ∈ N.rows at h
      change (o.payload = Msg.proposal N) at hp
      apply Or.inl
      change (match o.payload with
        | .proposal N => ofRow p a ∈ N.raw.map (ofHead p) ∨
            ofRow p a ∈ N.support.map (ofHead p) ∨ ofRow p a ∈ N.rows.map (ofRow p) ∨
            ofRow p a ∈ N.pcAcks.map (ofAck p)
        | .pc cert => ofRow p a ∈ cert.acks.map (ofAck p)
        | _ => False)
      rw [hp]
      exact Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨a, h, rfl⟩)))
  | head b => rw [hp] at h; cases h
  | row b => rw [hp] at h; cases h
  | ack b => rw [hp] at h; cases h
  | pc cert => rw [hp] at h; cases h

theorem pcsaSafetyWireLaws (m : FGMode) (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyWireLaws (pcsaSafetyReads m p c) where
  encode_injective := pcsa_safety_encode_injective p
  decode_encode := pcsa_safety_decode_encode p
  decode_auth := pcsa_safety_decode_auth p
  decoded_visible := pcsa_safety_decoded_visible m p c
  carried := pcsa_safety_carried m p c

theorem pcsa_safety_initial_record (m : FGMode) (p : Params) {In : Type} (c : AppCodec In) :
    (pcsaSafetyReads m p c).record (pcsaWith m p c).init = RecordOnce.initial := by
  rfl

theorem pcsa_safety_clock_record (m : FGMode) (p : Params) {In : Type} (c : AppCodec In)
    (nd : Node p) (t : Time) :
    (pcsaSafetyReads m p c).record ((pcsaWith m p c).clock nd t) = nd.record := by
  rfl

theorem pcsa_safety_process_record (m : FGMode) (p : Params) {In : Type} (c : AppCodec In)
    (nd : Node p) (o : Obj p) :
    (pcsaSafetyReads m p c).record ((pcsaWith m p c).process nd o) = nd.record := by
  rfl

theorem pcsa_safety_restart_record (m : FGMode) (p : Params) {In : Type} (c : AppCodec In)
    (nd : Node p) :
    (pcsaSafetyReads m p c).record
      ((pcsaWith m p c).restore ((pcsaWith m p c).durable nd)) = nd.record := by
  rfl

theorem pcsa_safety_own_record (m : FGMode) (p : Params) {In : Type} (c : AppCodec In)
    (nd : Node p) (o : Obj p) :
    (pcsaSafetyReads m p c).record ((pcsaWith m p c).recordOwn nd o) =
      safetyRecordStep (pcsaSafetyReads m p c) nd.record o := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> rfl
  | seat l i =>
      cases l with
      | prop s => cases payload <;> rfl
      | base l => cases l <;> cases payload <;> rfl

example (m : FGMode) (p : Params) {In : Type} (c : AppCodec In) : Prop :=
  FGSafetyClientLaws (pcsaSafetyReads m p c) p.E p.cfg

end AvailableChain.PCSA.Run
end
