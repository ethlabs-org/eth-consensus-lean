module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetTHigh -- shake: keep (THIGH-C)

set_option linter.privateModule false

/-! Blueprint 21 H.13:2677–2741, H.14:2826–2846, H.22 H1:3244–3250;
plan THIGH-C tests; B1/B13/B17/B18.
DC: SAME actual supporting HEAD and frozen THigh consumers.
Each fixture is a conditional package with actual selected sources. -/

section
namespace AvailableChain.FGSA.Run.Tests.HealingPostResetTHigh
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- THIGH-C-A-support: consume the selected source's actual own-label HEAD.
example [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (source : TSrc p c E rho) {x : V} {r : Nat} {C : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hsrc : actionSourceFG p c E rho x r = some (some C)) :
    ∃ z H, z ∈ rho.honest ∧ headAtLabel p c E rho z (r * p.R) = some H ∧
      Block.Preceq (eraseFG C) H :=
  postReset_selected_supporting_head p c E rho hrec.toRecovery₂ source hx hsrc

section Sources
variable [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (cap : RCap p c E rho)
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

include hrec cap source rowCovered h0r

variable (inv : ∀ i, PostResetInv p c E rho w i)
include inv

-- THIGH-C-B-later: consume the pairwise clause at these concrete rounds.
example {x y : V} {r : Nat} {C C' : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hC : actionSourceFG p c E rho x (r) = some (some C))
    (hC' : actionSourceFG p c E rho y (r + 1) = some (some C'))
    (hh : high p w C) (hh' : high p w C') :
    Block.Compatible (eraseFG C) (eraseFG C') :=
  postReset_tHigh_pairwise p c E rho hrec cap source rowCovered h0r inv
    x y (r) (r + 1) C C' hx hy hC hC' hh hh'

-- THIGH-C-B-equal: consume the pairwise clause at these concrete rounds.
example {x y : V} {r : Nat} {C C' : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hC : actionSourceFG p c E rho x (r) = some (some C))
    (hC' : actionSourceFG p c E rho y (r) = some (some C'))
    (hh : high p w C) (hh' : high p w C') :
    Block.Compatible (eraseFG C) (eraseFG C') :=
  postReset_tHigh_pairwise p c E rho hrec cap source rowCovered h0r inv
    x y (r) (r) C C' hx hy hC hC' hh hh'

-- THIGH-C-B-earlier: consume the pairwise clause at these concrete rounds.
example {x y : V} {r : Nat} {C C' : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hC : actionSourceFG p c E rho x (r + 1) = some (some C))
    (hC' : actionSourceFG p c E rho y (r) = some (some C'))
    (hh : high p w C) (hh' : high p w C') :
    Block.Compatible (eraseFG C) (eraseFG C') :=
  postReset_tHigh_pairwise p c E rho hrec cap source rowCovered h0r inv
    x y (r + 1) (r) C C' hx hy hC hC' hh hh'

end Sources

section Reset
variable [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉
          @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
            (actView pre) w C)
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)

include hrec mono emittedNonempty emittedName writes xing origin h0r

variable (cap : RCap p c E rho) (source : TSrc p c E rho)
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

include cap source rowCovered

variable (inv : ∀ i, PostResetInv p c E rho w i)
include inv

-- THIGH-C-C-full: consume C's three frozen conjuncts for actual selected sources.
example {x y : V} {r r' : Nat} {C C' : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hC : actionSourceFG p c E rho x r = some (some C))
    (hC' : actionSourceFG p c E rho y r' = some (some C'))
    (hh : high p w C) (hh' : high p w C') :
    Block.Compatible (eraseFG C) (eraseFG C') ∧ Block.Compatible (eraseFG C) w.CStar ∧
      w.sStar ≤ r * p.R :=
  postReset_tHigh_reset p c E rho hrec mono emittedNonempty emittedName writes xing origin
    h0r cap source rowCovered inv x y r r' C C' hx hy hC hC' hh hh'

end Reset
end AvailableChain.FGSA.Run.Tests.HealingPostResetTHigh
end
