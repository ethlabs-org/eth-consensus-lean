module
public import AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyClient -- shake: keep (#print axioms)
public import AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyStore -- shake: keep (#print axioms)

public import AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyBridge -- shake: keep (#print axioms)
public import AvailableChainPCSAProofs.Proofs.Foundations.FinalitySafety -- shake: keep (#print axioms)

public import AvailableChainPCSAProofs.Proofs.Assembly.Finality -- shake: keep (#print axioms)

public section

#print axioms AvailableChain.PCSA.Run.decodeSafetyRow
#print axioms AvailableChain.PCSA.Run.pcsaCoreReadsWith
#print axioms AvailableChain.PCSA.Run.pcsaCoreReadsWith_def
#print axioms AvailableChain.PCSA.Run.pcsaCoreReadsWith_on
#print axioms AvailableChain.PCSA.Run.pcsaSafetyCertificateLaws
#print axioms AvailableChain.PCSA.Run.pcsaSafetyReads
#print axioms AvailableChain.PCSA.Run.pcsaSafetyReads_def
#print axioms AvailableChain.PCSA.Run.pcsaSafetyWireLaws
#print axioms AvailableChain.PCSA.Run.pcsa_decodeSafetyRow_def
#print axioms AvailableChain.PCSA.Run.pcsa_safetyEnabled_def
#print axioms AvailableChain.PCSA.Run.pcsa_safetyProposalErase_def
#print axioms AvailableChain.PCSA.Run.pcsa_safetyProposalRows_def
#print axioms AvailableChain.PCSA.Run.pcsa_safety_carried
#print axioms AvailableChain.PCSA.Run.pcsa_safety_clock_record
#print axioms AvailableChain.PCSA.Run.pcsa_safety_decode_auth
#print axioms AvailableChain.PCSA.Run.pcsa_safety_decode_encode
#print axioms AvailableChain.PCSA.Run.pcsa_safety_decoded_visible
#print axioms AvailableChain.PCSA.Run.pcsa_safety_encode_injective
#print axioms AvailableChain.PCSA.Run.pcsa_safety_erase_prefix
#print axioms AvailableChain.PCSA.Run.pcsa_safety_finalityView_eq
#print axioms AvailableChain.PCSA.Run.pcsa_safety_initial_record
#print axioms AvailableChain.PCSA.Run.pcsa_safety_initial_tf
#print axioms AvailableChain.PCSA.Run.pcsa_safety_output_eq
#print axioms AvailableChain.PCSA.Run.pcsa_safety_own_core
#print axioms AvailableChain.PCSA.Run.pcsa_safety_own_record
#print axioms AvailableChain.PCSA.Run.pcsa_safety_process_record
#print axioms AvailableChain.PCSA.Run.pcsa_safety_restart_record
#print axioms AvailableChain.PCSA.Run.pcsa_safety_restart_tf
#print axioms AvailableChain.PCSA.Run.pcsa_safety_row_auth
#print axioms AvailableChain.PCSA.Run.pcsa_safety_source_mem
#print axioms AvailableChain.PCSA.Run.safetyEnabled
#print axioms AvailableChain.PCSA.Run.safetyProposalErase
#print axioms AvailableChain.PCSA.Run.safetyProposalRows
#print axioms AvailableChain.PCSA.pcsa_safety_delete_core
#print axioms AvailableChain.PCSA.pcsa_process_F_mono
#print axioms AvailableChain.PCSA.Run.pcsa_safety_process_F
#print axioms AvailableChain.PCSA.Run.pcsaSafetyOrderLaws

#print axioms AvailableChain.PCSA.pcsa_safety_admitBlock_fg_cases
#print axioms AvailableChain.PCSA.pcsa_safety_process_fg_cases
#print axioms AvailableChain.PCSA.pcsa_safety_normalize_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_reconcile_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_collect_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_poolAckRaw_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_fold_poolAckRaw_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_admitRow_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_fold_admitRow_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_poolAck_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_admitBlock_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_process_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_gateFrom_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_clockPre_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_clock_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_decode_block_payload
#print axioms AvailableChain.PCSA.pcsa_safety_process_TF

#print axioms AvailableChain.PCSA.pcsa_safety_parentFG_spec
#print axioms AvailableChain.PCSA.pcsa_safety_blockAccepted_facts
#print axioms AvailableChain.PCSA.pcsa_safety_eraseFG_fgBlock
#print axioms AvailableChain.PCSA.pcsa_safety_storeStepRoots
#print axioms AvailableChain.PCSA.pcsa_safety_window_TF_cases
#print axioms AvailableChain.PCSA.pcsa_safety_storeInvariant
#print axioms AvailableChain.PCSA.pcsa_safety_process_TF_new
#print axioms AvailableChain.PCSA.Run.pcsaCoreLawsWith
#print axioms AvailableChain.PCSA.Run.pcsa_safety_process_new
#print axioms AvailableChain.PCSA.Run.pcsaSafetyStoreLaws

#print axioms AvailableChain.PCSA.Run.pcsa_safety_runBlock_iff
#print axioms AvailableChain.PCSA.Run.pcsa_safety_bound_iff
#print axioms AvailableChain.PCSA.Run.pcsa_safety_finalizedAt_iff
#print axioms AvailableChain.PCSA.Run.pcsa_safety_rows_eq
#print axioms AvailableChain.PCSA.Run.pcsa_safety_emits_iff
#print axioms AvailableChain.PCSA.Run.pcsa_safety_noSlash_iff
#print axioms AvailableChain.PCSA.Run.pcsa_safety_carriage_of
#print axioms AvailableChain.PCSA.Run.pcsa_safety_wholeAccountable_iff
#print axioms AvailableChain.PCSA.Run.pcsa_safety_wholeAgreement_iff
#print axioms AvailableChain.PCSA.Run.pcsa_safety_accountable_supply
#print axioms AvailableChain.PCSA.Run.pcsa_safety_agreement_supply
#print axioms AvailableChain.PCSA.Run.pcsa_safety_eventAgreement_supply
#print axioms AvailableChain.PCSA.Run.pcsa_safety_monotone_supply
#print axioms AvailableChain.PCSA.Run.pcsa_safety_count_supply
#print axioms AvailableChain.PCSA.Run.pcsa_safetySlashesRead
#print axioms AvailableChain.PCSA.Run.pcsa_safety_nonSlashing_supply
#print axioms AvailableChain.PCSA.Run.pcsa_safety_wholeRunAccountable_body
#print axioms AvailableChain.PCSA.Run.pcsa_safety_wholeRunAgreement_body
#print axioms AvailableChain.PCSA.Run.pcsa_safety_eventPrefixAgreement_body
#print axioms AvailableChain.PCSA.Run.pcsa_safety_finalizedMonotone_body
#print axioms AvailableChain.PCSA.Run.pcsa_safety_faultCountSlashableBound_body
#print axioms AvailableChain.PCSA.Run.pcsa_safety_honestNeverSlashed_body

#print axioms AvailableChain.PCSA.Run.pcsa_safety_pureAccountableClaim
#print axioms AvailableChain.PCSA.Run.pcsa_safety_pureAgreementClaim
#print axioms AvailableChain.PCSA.Run.pcsa_safety_wholeRunAccountableClaim
#print axioms AvailableChain.PCSA.Run.pcsa_safety_wholeRunAgreementClaim
#print axioms AvailableChain.PCSA.Run.pcsa_safety_eventPrefixAgreementClaim
#print axioms AvailableChain.PCSA.Run.pcsa_safety_finalizedMonotoneClaim
#print axioms AvailableChain.PCSA.Run.pcsa_safety_faultCountSlashableBoundClaim
#print axioms AvailableChain.PCSA.Run.pcsa_safety_honestNeverSlashedClaim
#print axioms AvailableChain.PCSA.Run.pcsaSafetyFinalityClaims

namespace AvailableChain.PCSA.Run
open AvailableChain.FGCompose AvailableChain.SimplexFG
example (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyWireLaws (pcsaSafetyReads .on p c) := pcsaSafetyWireLaws .on p c
example (p : Params) {In : Type} (c : AppCodec In) (B : FGBlock (Fin p.n))
    (h : B ∈ ((pcsaCoreReadsWith .on p c).core (pcsaWith .on p c).init).fg.TF) :
    B = .genesis := pcsa_safety_initial_tf .on p c B h
example (p : Params) {In : Type} (c : AppCodec In) (nd : Node p) :
    (pcsaSafetyReads .on p c).record
      ((pcsaWith .on p c).restore ((pcsaWith .on p c).durable nd)) = nd.record :=
  pcsa_safety_restart_record .on p c nd
example (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyWireLaws (pcsaSafetyReads .idle p c) := pcsaSafetyWireLaws .idle p c
example (p : Params) {In : Type} (c : AppCodec In) (B : FGBlock (Fin p.n))
    (h : B ∈ ((pcsaCoreReadsWith .idle p c).core (pcsaWith .idle p c).init).fg.TF) :
    B = .genesis := pcsa_safety_initial_tf .idle p c B h
example (p : Params) {In : Type} (c : AppCodec In) (nd : Node p) :
    (pcsaSafetyReads .idle p c).record
      ((pcsaWith .idle p c).restore ((pcsaWith .idle p c).durable nd)) = nd.record :=
  pcsa_safety_restart_record .idle p c nd
example (m : FGMode) (p : Params) {In : Type} (c : AppCodec In) :
    FGCoreLaws (pcsaCoreReadsWith m p c) := pcsaCoreLawsWith m p c
example (m : FGMode) (p : Params) {In : Type} (c : AppCodec In) : Prop :=
  FGSafetyClientLaws (pcsaSafetyReads m p c) p.E p.cfg
example (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyOrderLaws (pcsaCoreReadsWith .on p c) (pcsaSafetyReads .on p c) :=
  pcsaSafetyOrderLaws .on p c
example (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyOrderLaws (pcsaCoreReadsWith .idle p c) (pcsaSafetyReads .idle p c) :=
  pcsaSafetyOrderLaws .idle p c
example (p : Params) {In : Type} (c : AppCodec In) :
    FGCoreLaws (pcsaCoreReadsWith .on p c) := pcsaCoreLawsWith .on p c
example (p : Params) {In : Type} (c : AppCodec In) :
    FGCoreLaws (pcsaCoreReadsWith .idle p c) := pcsaCoreLawsWith .idle p c
example (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyStoreLaws (pcsaCoreReadsWith .on p c) (pcsaSafetyReads .on p c)
      (FGSA.heightView p) (pcsa_finalityView p) (fun nd => Reachable p nd.st) :=
  pcsaSafetyStoreLaws .on p c
example (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyStoreLaws (pcsaCoreReadsWith .idle p c) (pcsaSafetyReads .idle p c)
      (FGSA.heightView p) (pcsa_finalityView p) (fun nd => Reachable p nd.st) :=
  pcsaSafetyStoreLaws .idle p c
end AvailableChain.PCSA.Run


open AvailableChain AvailableChain.SimplexFG AvailableChain.PCSA AvailableChain.PCSA.Run
namespace AvailableChain.PCSA.Run.Tests.FGStore

/-! A local admission fixture. The lease stays compatible with the new F.
The carried PC conflicts with that lease and is valid only under the old F. -/

abbrev p : Params :=
  { Δ := 1, n := 1, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }
def row (h : Nat) (r : BlockId) (f : Option FinalityPair := none) : RowWire 1 :=
  ⟨.seat .fg 0, .vote ⟨.vote h r false, f⟩⟩
def first : NamedProposal 1 := namedProposal p .genesis 1 0 [] [] [row 1 Block.genesis.root] none
def F1 : FGBlock (Fin 1) := fgBlock .genesis first.erase first.rows
def second : NamedProposal 1 := namedProposal p first 2 0 [] [] [row 2 first.root] none
def F2 : FGBlock (Fin 1) := fgBlock F1 second.erase second.rows
def sibling : Block := .node .genesis 1 ⟨99⟩ 0
def cert : PC 1 := ⟨1, sibling, [⟨.seat (.ack 1) 0, sibling.root⟩]⟩
def third (carry : Bool) : NamedProposal 1 :=
  namedProposal p second 3 0 [] [] [row 3 second.root (some ⟨2, first.root⟩)]
    (if carry then some cert else none)
def before : State 1 :=
  { base := { (GridCO.initial 1 .root) with
      now := 12
      blocks := [.genesis, first.erase, second.erase, sibling]
      obligations := [(first.erase, SA.releaseThreshold p.toParams, 100)] }
    fg := [F1, F2].foldl (FGSA.Window.on_block p p.K_W) Store.init
    proposals := [⟨.proposer 1, .proposal first⟩, ⟨.proposer 2, .proposal second⟩] }
def wire (carry : Bool) : Wire 1 := ⟨.proposer 3, .proposal (third carry)⟩

set_option maxRecDepth 8192
set_option exponentiation.threshold 8192

example : before.fg.F = .genesis ∧ pcValid before cert = true ∧
    pcValid { before with fg := { before.fg with F := F1 } } cert = false ∧
    Block.compatible cert.target first.erase = false ∧
    blockAccepted p before 3 (third true) F2 = true := by decide +kernel
example : (process p before (wire true)).base.obligations = [] ∧
    (process p before (wire true)).fg.F = F1 := by decide +kernel
example : (process p before (wire false)).base.obligations = before.base.obligations ∧
    (process p before (wire false)).fg.F = F1 := by decide +kernel

/-- The actual protocol delivery has the same result in both modes. -/
example (m : FGMode) :
    let after := ((pcsaWith m p unitCodec).process ⟨before, RecordOnce.initial⟩
      ((toWireEquiv p).symm (wire true))).st
    after.base.obligations = [] ∧ after.fg.F = F1 := by
  change (process p before (wire true)).base.obligations = [] ∧
    (process p before (wire true)).fg.F = F1
  decide +kernel

end AvailableChain.PCSA.Run.Tests.FGStore

end
