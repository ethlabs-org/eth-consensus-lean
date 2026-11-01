module
public import AvailableChainFGSAProofs.Proofs.Healing.LiveDC -- shake: keep (LIVE-DC service checks)
public import AvailableChainFGSAProofs.Proofs.Shared.Claims -- shake: keep (GST theorem checks)

#check AvailableChain.FGSA.Run.fgsa_finalityLivenessGST_recFE
#check AvailableChain.FGSA.Run.fgsa_finalityLivenessGST_recF4
#check AvailableChain.FGSA.Run.fgsa_proposalFinalGST_recFE
#check AvailableChain.FGSA.Run.fgsa_proposalFinalGST_recF4
#check AvailableChain.FGSA.Run.fgsa_aboveFrontierGST_recFE
#check AvailableChain.FGSA.Run.fgsa_aboveFrontierGST_recF4
#check AvailableChain.FGSA.Run.acceptsFinalBefore_mono_deadline

namespace AvailableChain.FGSA.Run

-- Conditional composition checks: both results use the same H-time and local claims.
example {p : Params} (hH : HTimeClaim p) (hL : FinalityLivenessRecFEClaim_W p)
    (hP : ProposalFinalRecFEClaim_W p) :
    FirstFinalityRecFEClaim_W p ∧ FinalityLivenessGSTClaim_W p .recFE :=
  ⟨fgsa_firstFinality_recFE hH hL,
    fgsa_finalityLivenessGST_recFE hH hL hP (healing_liveDCFromWindows p)⟩

example {p : Params} (hH : HTimeClaim p) (hL : FinalityLivenessRecF4Claim_W p)
    (hP : ProposalFinalRecF4Claim_W p) :
    FirstFinalityRecF4Claim_W p ∧ FinalityLivenessGSTClaim_W p .recF4 :=
  ⟨fgsa_firstFinality_recF4 hH hL,
    fgsa_finalityLivenessGST_recF4 hH hL hP (healing_liveDCFromWindows p)⟩

-- The firstfinality proof accepts exact equality at the total horizon.
example {p : Params} (hH : HTimeClaim p) (hL : FinalityLivenessRecFEClaim_W p)
    (G ΔF : Time) (g : Nat) (hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hset : FinalitySet_W p c E rho G ΔF .recFE g)
    (hhor : recoveryStart p E + B_HF p ΔF G + W_W p ΔF g = rho.horizon) :
    ∃ w, HealingInput p c E rho w ΔF ∧ tstar p w < recoveryStart p E + B_HF p ΔF G := by
  obtain ⟨w, input, hstar, _⟩ := fgsa_firstFinality_recFE hH hL G ΔF g hδ c E rho ()
    ⟨hset, hhor.le⟩
  exact ⟨w, input, hstar⟩

-- The GST trigger can equal the healing bound; its local witness stays strictly earlier.
example {p : Params} (hH : HTimeClaim p) (hL : FinalityLivenessRecFEClaim_W p)
    (hP : ProposalFinalRecFEClaim_W p)
    (G ΔF : Time) (g : Nat) (hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hset : FinalitySet_W p c E rho G ΔF .recFE g)
    (hhor : recoveryStart p E + B_HF p ΔF G + W_W p ΔF g ≤ rho.horizon) :
    ∃ w, HealingInput p c E rho w ΔF ∧ tstar p w < recoveryStart p E + B_HF p ΔF G := by
  obtain ⟨w, input, hstar, _, _⟩ := fgsa_finalityLivenessGST_recFE hH hL hP
    (healing_liveDCFromWindows p) G ΔF g hδ c E rho ⟨recoveryStart p E + B_HF p ΔF G⟩
    ⟨hset, le_rfl, hhor⟩
  exact ⟨w, input, hstar⟩

-- The firstfinality proof accepts exact equality at the total horizon.
example {p : Params} (hH : HTimeClaim p) (hL : FinalityLivenessRecF4Claim_W p)
    (G ΔF : Time) (g : Nat) (hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hset : FinalitySet_W p c E rho G ΔF .recF4 g)
    (hhor : recoveryStart p E + B_HF p ΔF G + W_W p ΔF g = rho.horizon) :
    ∃ w, HealingInput p c E rho w ΔF ∧ tstar p w < recoveryStart p E + B_HF p ΔF G := by
  obtain ⟨w, input, hstar, _⟩ := fgsa_firstFinality_recF4 hH hL G ΔF g hδ c E rho ()
    ⟨hset, hhor.le⟩
  exact ⟨w, input, hstar⟩

-- The GST trigger can equal the healing bound; its local witness stays strictly earlier.
example {p : Params} (hH : HTimeClaim p) (hL : FinalityLivenessRecF4Claim_W p)
    (hP : ProposalFinalRecF4Claim_W p)
    (G ΔF : Time) (g : Nat) (hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hset : FinalitySet_W p c E rho G ΔF .recF4 g)
    (hhor : recoveryStart p E + B_HF p ΔF G + W_W p ΔF g ≤ rho.horizon) :
    ∃ w, HealingInput p c E rho w ΔF ∧ tstar p w < recoveryStart p E + B_HF p ΔF G := by
  obtain ⟨w, input, hstar, _, _⟩ := fgsa_finalityLivenessGST_recF4 hH hL hP
    (healing_liveDCFromWindows p) G ΔF g hδ c E rho ⟨recoveryStart p E + B_HF p ΔF G⟩
    ⟨hset, le_rfl, hhor⟩
  exact ⟨w, input, hstar⟩

end AvailableChain.FGSA.Run
