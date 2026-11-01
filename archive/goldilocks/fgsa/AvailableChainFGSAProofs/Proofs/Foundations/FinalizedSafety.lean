module
public import AvailableChainFGSAProofs.Proofs.Foundations.Accountable
public import AvailableChainFGSAProofs.Proofs.Foundations.Store -- shake: keep (FinalityApi rMono)
public import AvailableChainFGSAClaims.Statements.Packages.Safety

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

set_option linter.unusedVariables false in
/-- ROOT-DIGEST W2b. Finalized safety through the all-run FGSASlashableBound.
DC DecoupledConsensusInternal/Legacy/Definitions/FinalitySafety.lean:83
(WholeRunFinalitySafety); stored non-genesis blocks are run blocks.
The frozen hx and hy binders are unused: reachable stores at any node suffice.
Local F extends through the retained FG store at a restart. -/
theorem fgsa_finalizedSafety (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {Pt : Type} {pt : Pt} (hp : FinalizedSafetyPrem p c E rho pt)
    (e e' : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hroots : NamedRootCollisionFree p c E rho) :
    FGBlock.compatible (storeAt p c E rho e x).fg.F
      (storeAt p c E rho e' y).fg.F = true := by
  exact fgsa_eventPrefixAgreement_of_bound (hroots := hroots) p c E rho
    (fgsa_slashableBound_of_base p c E rho hp.set hp.fault) e e' x y

/-- DC DecoupledConsensusStatements/Generic/Claims.lean:61 (finalizedMonotone),
from DecoupledConsensusProofs/Protocol/Handlers/FinalityMonotoneCore.lean:277
(stateBefore_F_mono). Sorted inclusive time reads inherit event-prefix order.
The legacy interface keeps its NoRestart premise; restore now keeps F;
DC's world events have no restart constructor. No fault or signature premise. -/
theorem fgsa_finalizedMonotone (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : rho.events.Pairwise (fun a b => a.key ≤ b.key))
    (hnr : V2.D.NoRestart rho) :
    ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
      Block.Preceq (finalizedOut (V2.D.Run.readAt E rho t x))
        (finalizedOut (V2.D.Run.readAt E rho t' x)) :=
  fgsa_bridge_finalizedMonotone p c E rho hs hnr

/-- Finalized output is monotone across retained-store restarts. -/
theorem fgsa_finalizedMonotone_restart (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : rho.events.Pairwise (fun a b => a.key ≤ b.key)) :
    ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
      Block.Preceq (finalizedOut (V2.D.Run.readAt E rho t x))
        (finalizedOut (V2.D.Run.readAt E rho t' x)) :=
  fgsa_bridge_finalizedMonotone_restart p c E rho hs

end AvailableChain.FGSA.Run
end
