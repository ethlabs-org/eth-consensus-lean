module
public import AvailableChainFGSAProofs.Proofs.Healing.Repair -- shake: keep (R1–R5 tests)

set_option linter.privateModule false

/-! H-REPAIR tests. Signatures of G-H6 (R1), G-H6S (R2), the gate geometry (R3), the two
repair branches (R4) and `healing_tRepair` at the exact frozen TRepair type (R5). The
boundary cases of plan steps 3 and 12: u = v_b, a deadline equal to the preceding HEAD
time, a last write at w = s − 2, and the H6-C bound at k = 2R + 1. -/

public section
namespace AvailableChain.FGSA.Run.Tests.HealingRepair
open AvailableChain.SimplexFG

section Signatures

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- R5: the exact frozen TRepair under the standing Recovery₂ and the R-contracts.
example
    [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    (services : RepairServiceScopes E rho)
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
    : TRepair p c E rho :=
  healing_tRepair E rho hrec mono crossing qc services writes

-- R1: the retained H.6 input at an actual honest proposal/HEAD pair after β + 2k − 1.
example
    [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (perm : TPerm p c E rho)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {β : Slot} (hβ : u < SA.proposalTime p.toParams β) {s : Slot}
    (hls : SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams s)
    (hvs : SA.voteTime p.toParams s ≤ v)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (scope : ProposalSupportScope E rho ip x (s - 1) (SA.proposalTime p.toParams s))
    {ih : Nat} {y : V} (hy : y ∈ rho.honest)
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s))) :
    RetainedH6Input p (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s :=
  retainedH6Input_on_repaired_reads E rho hrec mono crossing writes perm hgst hphase hβ hls hvs
    hx hip scope hy hih

-- R2 at the boundary u = v_b: the H.6-S input with the b + k cut.
example
    [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (perm : TPerm p c E rho)
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
    {v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} {b : Slot}
    (hgst : recoveryStart p E ≤ SA.voteTime p.toParams b)
    (hphase : PhaseInterval p c E rho (SA.voteTime p.toParams b) v m J contested)
    (hwindow : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k)) {s : Slot}
    (hls : SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams s)
    (hvs : SA.voteTime p.toParams s ≤ v)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (scope : ProposalSupportScope E rho ip x (s - 1) (SA.proposalTime p.toParams s))
    {ih : Nat} {y : V} (hy : y ∈ rho.honest)
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s))) :
    RetainedH6Input p (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s :=
  retainedH6Input_on_synchronous_reads E rho hrec mono crossing writes perm hgst hphase le_rfl
    hwindow hls hvs hx hip scope hy hih

-- R2: the H.6-S HEAD equality at the boundary u = v_b.
example
    [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (perm : TPerm p c E rho)
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
    {v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} {b : Slot}
    (hgst : recoveryStart p E ≤ SA.voteTime p.toParams b)
    (hphase : PhaseInterval p c E rho (SA.voteTime p.toParams b) v m J contested)
    (hwindow : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k)) {s : Slot}
    (hls : SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams s)
    (hvs : SA.voteTime p.toParams s ≤ v) {Q : Block}
    (heads : ∀ ip x (N : NamedProposal p.n), x ∈ rho.honest →
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
      (ofWire p ⟨.proposer s, .proposal N⟩) ∈ rho.emitsAt E ip →
      RepairHeadServices E rho s ip x N)
    (hp : HonestProposal E rho (fgsaInterface p c) s Q) :
    ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
      headAtLabel p c E rho y s = some Q :=
  repair_head_one E rho hrec mono crossing writes perm hgst hphase le_rfl hwindow hls hvs heads hp

-- R3: all five gate geometry fields, as a separate theorem.
example
    [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} (hus : u ≤ SA.voteTime p.toParams s) (hgate : SA.gateTime p.toParams s ≤ v)
    {Q : Block} (hQs : Q.slot = s)
    (hhead : ∀ y ∈ rho.honest, headAtLabel p c E rho y s = some Q)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho i x s)
    (gates : RepairGateScope E rho s) :
    ExactServiceGateGeometry E rho i x s Q := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  exact repair_gate_geometry E rho hrec mono crossing qc writes hGST hphase hus hgate
    hQs (fun y hy _ => hhead y hy)
    hx ht gates

-- R4: the two-lease branch; the ρΓ budget is inclusive.
example
    [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    (services : RepairServiceScopes E rho)
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
    {Gp : Time} (hgap : ProposalGap p c E rho Gp)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {β : Slot} (hβ : u < SA.proposalTime p.toParams β)
    (hmin : ∀ b, u < SA.proposalTime p.toParams b → β ≤ b) :
    RepairAfter p c E rho (β + 2 * p.k - 1) v ∧
    (u + ρΓ p Gp ≤ v → ∃ s Q,
      SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams s ∧
      SA.gateTime p.toParams s ≤ u + ρΓ p Gp ∧
      HonestProposal E rho (fgsaInterface p c) s Q ∧ ExactService p c E rho s Q) :=
  repair_two_lease E rho hrec mono crossing qc services writes hgap hgst hphase hβ hmin

-- R4: the synchronous branch at u = v_b; the ρ₁ budget keeps the strict bound.
example
    [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    (services : RepairServiceScopes E rho)
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
    {Gp : Time} (hgap : ProposalGap p c E rho Gp)
    {v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} {b : Slot}
    (hgst : recoveryStart p E ≤ SA.voteTime p.toParams b)
    (hphase : PhaseInterval p c E rho (SA.voteTime p.toParams b) v m J contested)
    (hmin : ∀ i, SA.voteTime p.toParams b ≤ SA.voteTime p.toParams i → b ≤ i)
    (hwindow : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k)) :
    RepairAfter p c E rho (b + p.k) v ∧
    (SA.voteTime p.toParams b + ρ₁ p Gp ≤ v → ∃ s Q,
      SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams s ∧
      SA.gateTime p.toParams s < SA.voteTime p.toParams b + ρ₁ p Gp ∧
      HonestProposal E rho (fgsaInterface p c) s Q ∧ ExactService p c E rho s Q) :=
  repair_synchronous E rho hrec mono crossing qc services writes hgap hgst hphase
    le_rfl hmin hwindow

end Signatures

section Boundary

variable (p : Params)

-- Step 3/12: a last write with w + k + 2 = s has its deadline EQUAL to v_(s−1); a read at
-- or after t_s does not see the row live.
example {w s : Nat} (hws : w + p.k + 2 = s) {t : Time}
    (ht : SA.proposalTime p.toParams s ≤ t) :
    SA.gateTime p.toParams w + SA.lifetime p.toParams = SA.voteTime p.toParams (s - 1) ∧
      ¬ t < SA.gateTime p.toParams w + SA.lifetime p.toParams := by
  have hd := p.deltaPos
  have hs : ((s - 1 : Nat) : Int) = (w : Int) + p.k + 1 := by omega
  have hs' : (s : Int) = (w : Int) + p.k + 2 := by exact_mod_cast hws.symm
  change 4 * p.Δ * (s : Int) ≤ t at ht
  refine ⟨?_, ?_⟩
  · change 4 * p.Δ * (w : Int) + 6 * p.Δ + (4 * (p.k : Int) - 1) * p.Δ =
      4 * p.Δ * ((s - 1 : Nat) : Int) + p.Δ
    rw [hs]
    ring
  · change ¬ t < 4 * p.Δ * (w : Int) + 6 * p.Δ + (4 * (p.k : Int) - 1) * p.Δ
    rw [hs'] at ht
    intro h
    nlinarith

-- Step 3/12: a last write at w = s − 2 is before the reads of s and has Transfers at the
-- preceding HEAD label s − 1 = w + 1; a gate at s − 1 is after v_s.
example (w : Nat) :
    SA.gateTime p.toParams w < SA.proposalTime p.toParams (w + 2) ∧
      w + 1 ≤ (w + 2) - 1 ∧
      SA.voteTime p.toParams (w + 2) < SA.gateTime p.toParams (w + 1) := by
  have hd := p.deltaPos
  refine ⟨?_, by omega, ?_⟩
  · change 4 * p.Δ * (w : Int) + 6 * p.Δ < 4 * p.Δ * ((w + 2 : Nat) : Int)
    push_cast
    linarith
  · change 4 * p.Δ * ((w + 2 : Nat) : Int) + p.Δ < 4 * p.Δ * ((w + 1 : Nat) : Int) + 6 * p.Δ
    push_cast
    linarith

-- H6-C at the boundary k = 2R + 1 and u = GST + 2P + 3Δ = v_b.
example {g : Time} {b : Nat} (hk : p.k = 2 * p.R + 1)
    (hb : g + 2 * P p + 3 * p.Δ = SA.voteTime p.toParams b) (hkb : p.k ≤ b + 1) :
    g ≤ SA.voteTime p.toParams (b + 1 - p.k) :=
  repair_h6c_window (le_of_eq hk) (le_of_eq hb) le_rfl hkb

-- GUP r2: G ≤ Γ, so the G-window gives t_s ≤ t_l + Γ.
example {Gp : Time} {l s : Nat}
    (hs : SA.proposalTime p.toParams s ≤ SA.proposalTime p.toParams l + Gp) :
    SA.proposalTime p.toParams s ≤ SA.proposalTime p.toParams l + Γ p Gp ∧
      Gp < Γ p Gp + 4 * p.Δ :=
  ⟨repair_grid_Γ hs, repair_lt_Γ Gp⟩

end Boundary

end AvailableChain.FGSA.Run.Tests.HealingRepair
end
