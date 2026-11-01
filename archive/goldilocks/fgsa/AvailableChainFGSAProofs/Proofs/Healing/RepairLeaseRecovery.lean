module
-- shake keep reason: HealingRecoveryPermAxioms and HealingRun use RecoveryPerm exports.
public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryPerm -- shake: keep
public import AvailableChainFGSAProofs.Proofs.Healing.RepairH6S -- shake: keep (source declarations)

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Classify actual writes with a permanence supplier for this phase only. -/
private theorem lease_cover_at_cut (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) {u v : Time} {cut l : Slot}
    (origins : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ w C, IsGateTick p c rho j x w ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some C) ∧ Block.Preceq row.1 C ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams w))) w C ∧
        row.2.2 = SA.gateTime p.toParams w + SA.lifetime p.toParams)
    (perm : ∀ w B, u ≤ SA.voteTime p.toParams w → SA.gateTime p.toParams w ≤ v →
      PhaseBody p c E rho w B → Transfers p c E rho w B v)
    (hcurrent : u ≤ SA.voteTime p.toParams cut)
    (hsync : E.t_GST ≤ SA.voteTime p.toParams (cut + 1 - p.k))
    (hold : ∀ w, w < cut → w + p.k + 1 ≤ l)
    {s : Slot} (hls : SA.proposalTime p.toParams l < SA.proposalTime p.toParams s)
    (hvs : SA.voteTime p.toParams s ≤ v) : RepairLeaseCover E rho s := by
  apply repair_lease_cover_of_split E rho hS (a := cut) (l := l) _ hls hvs
  intro i x row hiv hx hr
  obtain ⟨j, hji, w, C, ht, hpass, hres, hrow, hkey, hd⟩ := origins i x row hr
  refine ⟨j, hji, w, C, ht, hpass, hres, hrow, ?_⟩
  by_cases hw : w < cut
  · left
    have hdeadline : row.2.2 ≤ SA.voteTime p.toParams l :=
      hd ▸ healing_support_deadline_le_vote p (hold w hw)
    exact ⟨hdeadline, fun s hs =>
      hdeadline.trans (healing_support_vote_before_proposal p hs)⟩
  · right
    have hcw : cut ≤ w := Nat.le_of_not_gt hw
    have hgv : SA.gateTime p.toParams w ≤ v :=
      (V2.D.Engine.index_lt_read_length_iff hS v ht).mp (hji.trans_le hiv)
    have hu : u ≤ SA.voteTime p.toParams w := by
      refine hcurrent.trans ?_
      change 4 * p.Δ * (cut : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + p.Δ
      have hcw' : (cut : Int) ≤ w := by exact_mod_cast hcw
      nlinarith [p.deltaPos]
    have hwin : E.t_GST ≤ SA.voteTime p.toParams (w + 1 - p.k) := by
      refine hsync.trans ?_
      change 4 * p.Δ * ((cut + 1 - p.k : Nat) : Int) + p.Δ ≤
        4 * p.Δ * ((w + 1 - p.k : Nat) : Int) + p.Δ
      have hm : ((cut + 1 - p.k : Nat) : Int) ≤ ((w + 1 - p.k : Nat) : Int) := by
        exact_mod_cast Nat.sub_le_sub_right (Nat.succ_le_succ hcw) p.k
      nlinarith [p.deltaPos]
    exact ⟨hcw, perm w row.1 hu hgv
      (healing_support_phaseBody_of_write p c E rho hS hx ht hpass hres hkey hwin)⟩

/-- The phase-local lease adapter uses only the matching proved P5 service record.
Old writes expire; later writes use permanence in this phase. -/
theorem repair_lease_cover_two_at [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    (hServices : SupportPermanenceServices E rho u v m J contested)
    {β : Slot} (hβ : u < SA.proposalTime p.toParams β) {s : Slot}
    (hls : SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams s)
    (hvs : SA.voteTime p.toParams s ≤ v)
 : RepairLeaseCover E rho s := by
  have hk := p.kLarge
  have hcur : u ≤ SA.voteTime p.toParams (β + p.k - 1) := by
    refine hβ.le.trans ?_
    change 4 * p.Δ * (β : Int) ≤ 4 * p.Δ * ((β + p.k - 1 : Nat) : Int) + p.Δ
    have h : (β : Int) ≤ ((β + p.k - 1 : Nat) : Int) := by
      exact_mod_cast (show β ≤ β + p.k - 1 by
        dsimp only [Slot] at *
        omega)
    nlinarith [p.deltaPos]
  have hsync : E.t_GST ≤ SA.voteTime p.toParams (β + p.k - 1 + 1 - p.k) := by
    have he : β + p.k - 1 + 1 - p.k = β := by
      dsimp only [Slot] at *
      omega
    rw [he]
    have := healing_recovery_start_lower (p := p) E
    change E.t_GST ≤ 4 * p.Δ * (β : Int) + p.Δ
    change u < 4 * p.Δ * (β : Int) at hβ
    linarith [p.deltaPos]
  apply lease_cover_at_cut E rho hrec.base.valid.toScheduleWellFormed
    (cut := β + p.k - 1) (l := β + 2 * p.k - 1) _
    (fun _ _ => healing_tPerm_at E rho hrec mono crossing writes hready hphase hServices)
    hcur hsync _ hls hvs
  · intro i x row hr
    obtain ⟨j, hji, w, C, ht, hp, hc, hrow, hk, hd, _⟩ := writes i x row hr
    exact ⟨j, hji, w, C, ht, hp, hc, hrow, hk, hd⟩
  · intro w hw
    dsimp only [Slot] at *
    omega

/-- The phase-local lease adapter uses only the matching proved P5 service record.
Old writes expire; later writes use permanence in this phase. -/
theorem repair_lease_cover_one_at [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    (hServices : SupportPermanenceServices E rho u v m J contested)
    {b : Slot} (hb : u ≤ SA.voteTime p.toParams b)
    (hSync : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k)) {s : Slot}
    (hls : SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams s)
    (hvs : SA.voteTime p.toParams s ≤ v)
 : RepairLeaseCover E rho s := by
  apply lease_cover_at_cut E rho hrec.base.valid.toScheduleWellFormed
    (cut := b) (l := b + p.k) _
    (fun _ _ => healing_tPerm_at E rho hrec mono crossing writes hready hphase hServices)
    hb hSync (by
      intro w hw
      dsimp only [Slot] at *
      omega) hls hvs
  intro i x row hr
  obtain ⟨j, hji, w, C, ht, hp, hc, hrow, hk, hd, _⟩ := writes i x row hr
  exact ⟨j, hji, w, C, ht, hp, hc, hrow, hk, hd⟩

end AvailableChain.FGSA.Run
end
