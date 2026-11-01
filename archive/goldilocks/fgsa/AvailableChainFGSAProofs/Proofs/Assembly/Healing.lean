module
public import AvailableChainFGSAProofs.Proofs.Healing.Export -- shake: keep (Healing claim boundary)
public import AvailableChainFGSAProofs.Proofs.Foundations.Export
-- shake: keep (foundation supplier boundary)
public import AvailableChainFGSAProofs.Proofs.Finality.Export
-- shake: keep (progress fold supplier boundary)
public import AvailableChainFGSAProofs.Proofs.Shared.HonestQuorum
-- shake: keep (honest quorum supplier boundary)

public section

namespace AvailableChain.FGSA.Run

variable (p : Params)

/-- An emitted proposal has local service before the next vote in sleep recovery. -/
theorem assembly_healing_proposal_service {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot} {ip : Nat} {x : V}
    {N : NamedProposal p.n} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hem : ofWire p ⟨.proposer s, .proposal N⟩ ∈ rho.emitsAt E ip)
    (hSync : E.t_GST ≤ SA.proposalTime p.toParams s)
    (hhor : SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon)
    (hCompat : Block.Compatible N.erase (eraseFG (rho.stateBeforeTime E
      (SA.proposalTime p.toParams s + p.Δ) x).st.fg.F)) :
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
      (SA.proposalTime p.toParams s) (SA.proposalTime p.toParams s + p.Δ) x) := by
  exact healing_proposal_receipt_recovery p c E rho hrec hx hx hip hem hSync hhor hCompat

/-- Blueprint 21:1356–1425. The sleep regime and named Foundations supply promotion.
P-H2 supplies joined-start promotion. P-H1 supplies the proved permanence producer. -/
theorem fgsa_renewedPromotionClaim : RenewedPromotionClaim p := by
  intro G ΔF hδ V _ _ In c E rho pt h
  have hrec := h.set
  have mono := fgsa_rMonoAll p c E rho
  have crossing := fgsa_rXing (hroots := hrec.base.idealization) p c E rho hrec.base.linked
    (fgsa_faultX_count_rec p hrec.fault) hrec.base.valid.toUnforgeableSignatures
  have perm := healing_tPerm_recovery E rho hrec mono crossing
    (fgsa_leaseOrigins_lastWrite p c E rho hrec.base.valid.toScheduleWellFormed)
  have services := fun (s : Slot) (ip : Nat) (x : V) (N : NamedProposal p.n)
      hx hip hem hSync hhor hCompat =>
    assembly_healing_proposal_service p c E rho hrec (s := s) (ip := ip) (x := x) (N := N)
      hx hip hem hSync hhor hCompat
  intro u m J contested l q Q height hstart hphase hu hq hl hQ hservice hentry hcovered hrepair
  exact healing_renewedPromotion E rho hrec services hδ h.bound mono crossing perm
    (fgsa_tRows_recovery p c E rho hrec.toRecovery₂).receipt
    (fgsa_batchCoverage p ΔF .progress c E rho) (fgsa_foldTrichotomy_progress p)
    (fgsa_faultQ_of_count p hrec.fault)
    (kmid_honest_quorum p c rho hrec.base.linked hrec.fault) pt.r h.hhor
    u m J contested l q Q height hstart
    hphase hu hq hl hQ hservice hentry hcovered hrepair

/-- Blueprint 21:1120–1137 and SO-COV. The local producer supplies complete
row coverage at the current action or an earlier action. -/
theorem fgsa_rowPermissionClaim : RowPermissionClaim p := by
  exact healing_rowPermissionClaim_of p
    (hcovered := fun _c E rho => rowPermission_covered E rho)

end AvailableChain.FGSA.Run
end
