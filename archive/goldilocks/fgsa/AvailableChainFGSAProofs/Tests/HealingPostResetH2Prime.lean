module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetH2Prime -- shake: keep (H2P fixtures)


set_option linter.privateModule false

/-! Blueprint 21 H2′:3297–3300, proof:3382–3391; Centaur route;
B1/B13/B15/B17/B18. DC: SAME frozen-type and gate-free adapter consumers. -/

section
namespace AvailableChain.FGSA.Run.Tests.HealingPostResetH2Prime
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

section Sources
variable [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho) (cap : RCap p c E rho)
    (source : TSrc p c E rho)
    (rowCovered : ∀ (_hb : Base₂ p c E rho)
      (_hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
      (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ C : FGBlock (Fin p.n),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st → (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    {w : HealingWitness} (h0r : H0Reset p c E rho w)

include hrec mono cap source rowCovered h0r

variable (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    (inv : ∀ i, PostResetInv p c E rho w i)
include xing origin inv

-- H2P-D-frozen: consume D with the frozen H2Prime type, without extra guards.
example : H2Prime p c E rho w :=
  postReset_h2Prime_reset p c E rho hrec mono
    cap source rowCovered h0r xing origin inv

-- H2P-D-first-before-gate: D applies when the run stops before the slot-v gate.
example {v : Slot} {Q H : Block} {x : V}
    (hQ : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v)
    (hx : headReader p E rho x (v + 1) (SA.voteTime p.toParams (v + 1)))
    (hH : headAtLabel p c E rho x (v + 1) = some H)
    (_hshort : rho.horizon < SA.gateTime p.toParams v) : Block.Preceq Q H :=
  postReset_h2Prime_reset p c E rho hrec mono
    cap source rowCovered h0r xing origin inv
    v Q hQ hv x (v + 1) H hx le_rfl hH

end Sources

-- H2P-B-gate-free: consume the Kept adapter without any gate or raw-result input.
example [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    {v : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hgst : E.t_GST ≤ SA.voteTime p.toParams v)
    (hCut : HealingWindow p E 1 v) (heQ : eraseFG Qfg = Q)
    (hbatch : ∀ z ∈ rho.honest, headAtLabel p c E rho z v = some Q)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (v + 1))))
    {X : Finset (FGBlock (Fin p.n))}
    (hXv : X ⊆ voterBlocks p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (v + 1))) (v + 1))
    (hXc : ∀ W ∈ X, ∀ A, FGBlock.Preceq A W → A ∈ X)
    (hkept : Kept p c E rho iy y X Qfg)
    (hRelease : joinedAtTime p (storeAt p c E rho iy y).restartTime
      (SA.releaseTime p.toParams v) = true) :
    Block.Preceq Q (headAtIdx p c E rho iy (v + 1)) :=
  healing_unanimous_next_transfer_kept p c E rho hrec mono hgst heQ hbatch hy hiy
    (healing_next_transfer_scope_recovery E rho hrec hCut hy hiy
      (healing_recovery_joined_vote_next E rho hrec hCut hy hiy)) hCut hRelease hXv
    (fun W hW A _hFA hAW => hXc W hW A hAW) hkept

end AvailableChain.FGSA.Run.Tests.HealingPostResetH2Prime
end
