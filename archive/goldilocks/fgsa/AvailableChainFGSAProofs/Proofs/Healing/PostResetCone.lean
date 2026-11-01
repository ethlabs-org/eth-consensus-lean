module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetJoint2 -- shake: keep J6
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetConeInput

public section

/-! Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE C6.
DC: SAME retained cone successor at every event cut. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure RetainedWalk

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

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
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
include hrec mono emittedNonempty emittedName writes xing origin h0r

variable (cap : RCap p c E rho)
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
include cap source rowCovered

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE C6.
DC: SAME cut-indexed cone successor for every Nat cut.
The prior cone handles old HEAD cuts. C5 handles the new cut from reset
lease compatibility, lease safety and raw transfer. No reset-time input is added.
Run ports and producers: Recovery₂, H0Reset, fgsa_rMono,
sourceDiscipline_emittedNonempty, emittedName_window,
fgsa_leaseOrigins_lastWrite, fgsa_rXing, sourceDiscipline_qcOrigin,
fgsa_rCap_channel, sourceDiscipline_tSrc and rowPermission_covered. -/
theorem healing_postReset_coneStep (i : Nat) : PostResetConeStep p c E rho w i := by
  rw [PostResetConeStep_def]
  rintro ⟨_hinv, _hrl, _hod, hcone⟩ hrl hlease _hfp hraw
  rw [PostResetRetainedConeP_def] at hcone ⊢
  intro s hs hHeadHorizon hcut ip x hx hip hseat N hem
  by_cases hold : timeIdx rho (SA.voteTime p.toParams s) ≤ i
  · exact hcone s hs hHeadHorizon hold hx hip hseat N hem
  · exact postReset_coneInput_at_cut p c E rho hrec mono emittedNonempty emittedName
      writes xing origin h0r cap source rowCovered (i + 1) hrl hlease hraw
      hs hHeadHorizon hx hip hcut

end AvailableChain.FGSA.Run
end
