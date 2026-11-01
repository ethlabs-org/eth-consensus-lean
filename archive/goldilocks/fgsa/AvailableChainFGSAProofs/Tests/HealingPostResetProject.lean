module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetProject -- shake: keep

set_option linter.privateModule false

/-! Blueprint 21 H.14:2823–2845, H2:3259–3263, H2.A:3289–3295;
plan J3 D3–D4; B1/B13/B17/B18. DC: SAME concrete transfer consumers.
Conditional package fixtures use honest source and reader witnesses. -/

section
namespace AvailableChain.FGSA.Run.Tests.HealingPostResetProject
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

section Sources
variable [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (cap : RCap p c E rho)
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

variable (inv : ∀ i, PostResetInv p c E rho w i)
include hrec cap source rowCovered h0r inv

-- J3-B-parent: consume TCarrier for a concrete honest source and proposal.
example {y : V} {r v : Nat} {K : FGBlock (Fin p.n)} {Q : Block}
    (hy : y ∈ rho.honest)
    (hsrc : actionSourceFG p c E rho y r = some (some K)) (hhK : high p w K)
    (hQ : HonestProposal E rho (fgsaInterface p c) v Q) (hv : r * p.R + 2 ≤ v) :
    Block.Preceq (eraseFG K) Q.parent :=
  postReset_tCarrier_reset p c E rho hrec cap source rowCovered h0r inv
    y r K v Q hy hsrc hhK hQ hv

-- J3-C-head: consume H2A for a concrete honest source and later honest HEAD.
example {y x : V} {r s : Nat} {K : FGBlock (Fin p.n)} {H : Block}
    (hy : y ∈ rho.honest)
    (hsrc : actionSourceFG p c E rho y r = some (some K)) (hhK : high p w K)
    (hx : headReader p E rho x s (SA.voteTime p.toParams s)) (hs : r * p.R + 1 ≤ s)
    (hH : headAtLabel p c E rho x s = some H) : Block.Preceq (eraseFG K) H :=
  (postReset_h2A_reset p c E rho hrec cap source rowCovered h0r inv
    y r K hy hsrc hhK).1 x s H hx hs hH

-- J3-C-output: consume H2A with the frozen suffix and horizon guards.
example {y x : V} {r a : Nat} {K : FGBlock (Fin p.n)}
    (hy : y ∈ rho.honest)
    (hsrc : actionSourceFG p c E rho y r = some (some K)) (hhK : high p w K)
    (hx : confirmedReaderIdx p c E rho x a) (hhor : p.actionTime r + 4 * p.Δ ≤ rho.horizon)
    (ha : HealSuffix p c rho (p.actionTime r + 4 * p.Δ) a) :
    Block.Preceq (eraseFG K) (S_at p c E rho a x) :=
  (postReset_h2A_reset p c E rho hrec cap source rowCovered h0r inv
    y r K hy hsrc hhK).2 a x hx hhor ha

end Sources
end AvailableChain.FGSA.Run.Tests.HealingPostResetProject
end
