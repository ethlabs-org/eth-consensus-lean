module
public import AvailableChainFGSAProofs.Proofs.Healing.Delivery
public import AvailableChainFGSAProofs.Proofs.Healing.ResetTransfer
public import AvailableChainFGSAProofs.Proofs.Healing.Repair
public import AvailableChainFGSAProofs.Proofs.Healing.CommonEntry
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierService
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseService
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetKeep
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetLease

public section

/-! Blueprint 21 H.12–H.18:2646–3095, H.22:3250–3344; post-reset plan J9.
B1/B13/B17/B18/B31/B32. DC: SAME package fields; INTENTIONAL reset-only
adapters and explicit Foundations channels. Assembly closes these inputs.
The all-cut carrier is a named input. This module proves no global induction. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.12:2646–2666, H.22 T-contract; plan J9 A;
B1/B13/B17/B31. DC: SAME seven fields from their Healing producers.
The reset adapter uses each public H0 only through toH0Reset.
The unused _h0r input stays for signature uniformity. -/
theorem healing_healTContract_reset [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (xing : RXing p c E rho) (cap : RCap p c E rho)
    (source : TSrc p c E rho) (origin : RQCOrigin p c E rho)
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
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    {w : HealingWitness} (_h0r : H0Reset p c E rho w) : HealTContract p c E rho w := by
  have repairScopes := healing_repair_service_scopes_recovery E rho hrec mono
  have openingScopes := healing_opening_service_scopes_recovery E rho hrec mono
  have frontierScopes : ∀ q v, recoveryStart p E ≤ SA.proposalTime p.toParams q →
      SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon → FrontierServiceScopes E rho q v :=
    fun q v _ _ _ =>
    healing_frontier_service_scopes_recovery E rho hrec mono q v
  exact
    { del := healing_tDel_recovery E rho hrec source mono
      delReset := healing_tDelReset_recovery E rho hrec source mono w
        (fun h0 _ => healing_low_finality_at_reset_reset E rho hrec.toRecovery₂
          xing cap source w h0)
      perm := healing_tPerm E rho hrec mono xing writes openingScopes.permanence
      repair := healing_tRepair E rho hrec mono xing origin repairScopes writes
      common := healing_tCommon E rho hrec mono xing openingScopes writes rowCoverage
      frontier := frontier_service E rho hrec mono xing frontierScopes writes rowCoverage
      geom := healing_tGeom p c E rho hrec.base.valid.toScheduleWellFormed }

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.14:2847–2861; plan J9 B; B1/B13/B17/B18/B32.
DC: SAME kept-view conclusion. Consume H0 only through toH0Reset.
J10 must replace the named all-cut carrier when its producer is available. -/
theorem healing_rKeep_of_reset (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (inv : ∀ i, PostResetInv p c E rho w i)
    (hroots : NamedRootCollisionFree p c E rho) :
    RKeep p c E rho w := by
  intro h0
  exact postReset_rKeep_body (hroots := hroots) p c E rho xing origin h0.toH0Reset inv

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.17/H.18:2946–3095; plan J9 B; B1/B13/B17/B31.
DC: SAME both provenance clauses. The seven named inputs have J4's types.
Consume H0 only through toH0Reset; no first-proposal field is read. -/
theorem healing_rFProv_of_reset (hv : V2.D.ExecutionValid E rho)
    (origin : RQCOrigin p c E rho)
    (heldRows : ∀ e x W, HeldAt p c E rho e x W →
      ∀ u ∈ chainRows W, ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < e ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho e z r a ∧ p.actionTime r ≤ t)
    (cap : ∀ (y i : Nat), 0 < y → ∀ x W, HeldAt p c E rho i x W →
      y ≤ (finalityView p W).h_F →
      ∃ z r a u, HonestRowBefore p c E rho i z r a ∧ RowSigner p c rho a z ∧
        RowWire.toRow? a = some u ∧ u ∈ chainRows W ∧
        u.finality_pair = some ⟨(finalityView p W).h_F, (finalityView p W).F.root⟩)
    (hhead : ∀ {j r : Nat} {z : V} {a : RowWire p.n} {u : Row (Fin p.n)},
      HonestRowAt p c E rho j z r a → RowSigner p c rho a z →
      a.toRow? = some u → ∀ fp, u.finality_pair = some fp →
      ∃ H, HeldAt p c E rho j z H ∧ fp.height = (heightView p H).h_j ∧
        fp.target = (heightView p H).J.root ∧
        KitFG.TargetQCAt p.E H fp.height (heightView p H).J)
    (xing : RXing p c E rho) (w : HealingWitness)
    (hroots : NamedRootCollisionFree p c E rho) : RFProv p c E rho w := by
  intro h0
  exact postReset_rFProv_reset (hroots := hroots) p c E rho hv origin heldRows cap hhead xing
    h0.toH0Reset

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.13–H.18:2668–3095; plan J9 B; B1/B13/B17/B18/B31/B32.
DC: SAME six fields. Crossing and capacity are named channels;
phase and descent use their producers, keep and provenance use the H0 adapters.
The unused _h0r input stays for signature uniformity. -/
theorem healing_healRContract_reset [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (xing : RXing p c E rho) (cap : RCap p c E rho)
    (origin : RQCOrigin p c E rho)
    (heldRows : ∀ e x W, HeldAt p c E rho e x W →
      ∀ u ∈ chainRows W, ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < e ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho e z r a ∧ p.actionTime r ≤ t)
    (finalityCap : ∀ (y i : Nat), 0 < y → ∀ x W, HeldAt p c E rho i x W →
      y ≤ (finalityView p W).h_F →
      ∃ z r a u, HonestRowBefore p c E rho i z r a ∧ RowSigner p c rho a z ∧
        RowWire.toRow? a = some u ∧ u ∈ chainRows W ∧
        u.finality_pair = some ⟨(finalityView p W).h_F, (finalityView p W).F.root⟩)
    (hhead : ∀ {j r : Nat} {z : V} {a : RowWire p.n} {u : Row (Fin p.n)},
      HonestRowAt p c E rho j z r a → RowSigner p c rho a z →
      a.toRow? = some u → ∀ fp, u.finality_pair = some fp →
      ∃ H, HeldAt p c E rho j z H ∧ fp.height = (heightView p H).h_j ∧
        fp.target = (heightView p H).J.root ∧
        KitFG.TargetQCAt p.E H fp.height (heightView p H).J)
    {w : HealingWitness} (_h0r : H0Reset p c E rho w)
    (inv : ∀ i, PostResetInv p c E rho w i)
    (hroots : NamedRootCollisionFree p c E rho) : HealRContract p c E rho w := by
  exact
    { xing := xing
      cap := cap
      phase := healing_rPhase_recovery E rho hrec mono xing
      excl := healing_rExcl (hroots := hroots) p c E rho xing origin
      keep := healing_rKeep_of_reset (hroots := hroots) p c E rho xing origin inv
      fprov := healing_rFProv_of_reset (hroots := hroots) p c E rho hrec.base.valid origin heldRows
        finalityCap hhead xing w }

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.22 H1/H2:3250–3263; plan J9 C; B13/B17.
DC: SAME T-stream fields, with explicit row delay. Each field is a named
hypothesis of its full frozen type, including THigh's global round range. -/
theorem healing_healT_of {w : HealingWitness} {ΔF : Time}
    (tHigh : THigh p c E rho w) (tCarrier : TCarrier p c E rho w)
    (rows : TRows p c E rho ΔF) : HealT p c E rho w ΔF :=
  { h1 := tHigh, h2 := tCarrier, rows := rows }

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.22 H2.A–H6:3289–3344; plan J9 C; B13/B17/B31.
DC: SAME six AC fields. Each field is a separate named hypothesis;
the finite-horizon guards remain in H2A and H5RawTransfer. -/
theorem healing_healAC_of {w : HealingWitness}
    (h2A : H2A p c E rho w) (h2Prime : H2Prime p c E rho w)
    (h3 : H3 p c E rho w) (h4 : H4 p c E rho w)
    (h5 : H5RawTransfer p c E rho w) (h6 : H6GateService p c E rho w) :
    HealAC p c E rho w :=
  { h2A := h2A, h2' := h2Prime, h3 := h3, h4 := h4, h5 := h5, h6 := h6 }

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.18:3073–3095, H.22; plan J9 D; B1/B13/B17.
DC: SAME HealingInput fields. H.18 must supply sourcePrefix. Only this
constructor uses PostResetStart and its full-H0 adapter. -/
theorem healing_healingInput_of {w : HealingWitness} {ΔF : Time}
    (healed : Healed p c E rho (tstar p w)) (start : PostResetStart p c E rho w)
    (sourcePrefix : Block.Preceq w.CStar w.QStar)
    (t : HealT p c E rho w ΔF) (ac : HealAC p c E rho w) :
    HealingInput p c E rho w ΔF :=
  { healed := healed, wit := PostResetStart.toH0 p c E rho start sourcePrefix, t := t, ac := ac }

end AvailableChain.FGSA.Run
end
