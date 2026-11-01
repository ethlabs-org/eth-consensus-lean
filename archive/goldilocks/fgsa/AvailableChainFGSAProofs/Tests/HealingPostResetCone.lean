module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetRead -- shake: keep read tests
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetJoint2 -- shake: keep J6
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetCone -- shake: keep cone tests

set_option linter.privateModule false

/-! Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE T.
DC: SAME all-cut application, empty-cut guard and run-level projection. -/

namespace AvailableChain.FGSA.Run.Tests.HealingPostResetCone
open AvailableChain.SimplexFG Gen.Pure

section Step
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
          (row.1, row.2.1) ∉
          @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
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

-- The producer is consumed as a function over every Nat cut.
example : ∀ i, PostResetConeStep p c E rho w i :=
  healing_postReset_coneStep p c E rho hrec mono emittedNonempty emittedName writes
    xing origin h0r cap source rowCovered

-- C3 at the first label admitted by the frozen cone guard.
example (i : Nat) (hraw : PostResetRawTransfer p c E rho w i)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? =
      some (.tick x (SA.proposalTime p.toParams (w.sStar + 2))))
    (hcut : timeIdx rho (SA.voteTime p.toParams (w.sStar + 2)) ≤ i) :
    ∃ D m, m = maxLiveH p c E rho (w.sStar + 2) ip x ∧
      (heightView p D).h = max (w.M + 1) (m - 1) := by
  obtain ⟨D, m, hm, hh, _, _, _⟩ := postReset_commonPivot_at_cut p c E rho hrec mono
    emittedNonempty emittedName writes xing origin h0r cap source rowCovered
    i hraw le_rfl hx hip hcut
  exact ⟨D, m, hm, hh⟩

end Step

section Projection
variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- The all-cut carrier projects at the proposal's own HEAD cut.
example (w : HealingWitness) (hcone : ∀ i, PostResetRetainedConeP p c E rho w i) :
    PostResetRetainedCone p c E rho w := by
  rw [postResetRetainedCone_iff]
  intro s hs hHeadHorizon ip x hx hip hseat N hem
  have h := hcone (timeIdx rho (SA.voteTime p.toParams s))
  rw [PostResetRetainedConeP_def] at h
  exact h s hs hHeadHorizon le_rfl hx hip hseat N hem

-- An actual proposal makes the guarded vote-time cut positive.
example (w : HealingWitness) : PostResetRetainedConeP p c E rho w 0 := by
  rw [PostResetRetainedConeP_def]
  intro s _hs _hh hcut ip x _hx hip
  have hpv : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hpos : 0 < timeIdx rho (SA.voteTime p.toParams s) := by
    exact List.length_pos_of_mem (List.mem_filter.mpr
      ⟨List.mem_of_getElem? hip, decide_eq_true hpv⟩)
  exact (Nat.not_lt_of_ge hcut hpos).elim

-- The maximum includes the proposer when the event list is empty.
example (s : Slot) (ip : Nat) (x : V) (he : rho.events = []) :
    maxLiveH p c E rho s ip x = (storeAt p c E rho ip x).fg.h_max := by
  rw [maxLiveH_def, he]
  simp

end Projection

#check healing_postReset_coneStep
#print axioms healing_postReset_coneStep

end AvailableChain.FGSA.Run.Tests.HealingPostResetCone
