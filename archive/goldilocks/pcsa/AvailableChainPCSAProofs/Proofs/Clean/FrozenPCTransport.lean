module
public import AvailableChainPCSAProofs.Proofs.Clean.RelayReceipt
public import AvailableChainPCSAProofs.Proofs.Clean.SnapshotContents
public import AvailableChainPCSAProofs.Proofs.Clean.ViewOrigins
public import AvailableChainPCSAProofs.Proofs.Clean.BodyPaths

public section

/-! C6 FrozenPCTransport: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- A held target is frame-active at an honest stage-one clocked read. -/
theorem pcsa_clock_target_active (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hF : StageOneFrame p c E rho)
    (k : Nat) (x : V) (hx : x ∈ rho.honest) (t : Time) (C : PC p.n)
    (hm : C.target ∈ (clock p (V2.D.Run.stateBefore E rho k x).st t).base.blocks) :
    frameActive p (clock p (V2.D.Run.stateBefore E rho k x).st t) C = true := by
  have hf : FrameVacuous p (clock p (V2.D.Run.stateBefore E rho k x).st t) := by
    change (clock p _ t).fg.F = .genesis ∧
      (KitFG.storeControlsView (FGSA.heightView p) (clock p _ t).fg).Z = .genesis ∧
      (KitFG.storeControlsView (FGSA.heightView p) (clock p _ t).fg).lo = 0
    rw [pcsa_body_clock_fg]
    exact hF x hx k
  rw [frameActive_def, pcsa_fullTree_of_frame p _ hf]
  apply decide_eq_true
  exact (pcsa_tree_correspondence p _ (Reachable.tick t (pcsa_reachable_stateBefore E rho k x))
    C.target).mp hm
/-- In the delivery window: Every frozen voter PC has a matching active key at the honest proposer
read. -/
theorem pcsa_frozen_pc_in_proposer_win [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (C : PC p.n)
    (hk : rho.events[k]? = some (.tick y (SA.proposalTime p.toParams (s + 1))))
    (hT : T₀ ≤ SA.freezeTime p.toParams s) (hc : SA.proposalTime p.toParams (s + 1) ≤ cut)
    (hC : C ∈ pcSnapshotAt (clock p (V2.D.Run.stateBefore E rho a x).st
      (SA.voteTime p.toParams (s + 1))) s) :
    ∃ D ∈ (clock p (V2.D.Run.stateBefore E rho k y).st
      (SA.proposalTime p.toParams (s + 1))).pcs, D.slot = C.slot ∧ D.target = C.target ∧
        frameActive p (clock p (V2.D.Run.stateBefore E rho k y).st
          (SA.proposalTime p.toParams (s + 1))) D = true := by
  have hsnap : pcSnapshotAt (clock p (V2.D.Run.stateBefore E rho a x).st
      (SA.voteTime p.toParams (s + 1))) s = pcSnapshotAt (V2.D.Run.stateBefore E rho a x).st s := by
    delta pcSnapshotAt
    rw [pcsa_vote_snapshot]
  rw [hsnap] at hC
  obtain ⟨j, _, hj, hm⟩ := pcsa_snapshot_pc_origin E rho a x s C hC
  have hpre := V2.D.Engine.stateBefore_tick_eq_stateBeforeTime h.valid.toScheduleWellFormed
    h.noRestart hj
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ h.valid.toScheduleWellFormed] at hpre
  rw [hpre] at hm
  have hpub : V2.PublicTime E (SA.freezeTime p.toParams s) := by
    refine ⟨4 * s + 3, ?_⟩
    rw [h.delta]
    change 4 * p.Δ * (s : Int) + 3 * p.Δ = ((4 * s + 3 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hz : 0 ≤ SA.freezeTime p.toParams s := by
    have hp := p.deltaPos
    change 0 ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    positivity
  have he : SA.freezeTime p.toParams s + E.Δ = SA.proposalTime p.toParams (s + 1) := by
    rw [h.delta]
    change 4 * p.Δ * (s : Int) + 3 * p.Δ + p.Δ = 4 * p.Δ * ((s + 1 : Nat) : Int)
    push_cast
    ring
  have hidx : V2.D.Run.idxBefore rho (SA.proposalTime p.toParams (s + 1)) ≤ k := by
    apply Nat.le_of_not_gt
    intro hn
    exact lt_irrefl _ ((Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hk _).mp hn)
  obtain ⟨D, hDmem, hDs, hDt⟩ := pcsa_pc_before_public_cut_relay_win E rho h hF hFault hD
    (hT := hT) _ k x y hx hy _ hpub hz (le_refl _) (by rwa [he]) (by rwa [he]) C
        hm
  have hDclock : D ∈ (clock p (V2.D.Run.stateBefore E rho k y).st
      (SA.proposalTime p.toParams (s + 1))).pcs := by
    rwa [pcsa_clock_pcs]
  refine ⟨D, hDclock, hDs, hDt, pcsa_clock_target_active E rho hF k y hy _ D ?_⟩
  rw [pcsa_clock_blocks]
  exact pcsa_pc_targets_held p _ (pcsa_reachable_stateBefore E rho k y) D hDmem
/-- Every frozen voter PC has a matching active key at the honest proposer read. -/
theorem pcsa_frozen_pc_in_proposer [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (C : PC p.n)
    (hk : rho.events[k]? = some (.tick y (SA.proposalTime p.toParams (s + 1))))
    (hc : SA.proposalTime p.toParams (s + 1) ≤ cut)
    (hC : C ∈ pcSnapshotAt (clock p (V2.D.Run.stateBefore E rho a x).st
      (SA.voteTime p.toParams (s + 1))) s) :
    ∃ D ∈ (clock p (V2.D.Run.stateBefore E rho k y).st
      (SA.proposalTime p.toParams (s + 1))).pcs, D.slot = C.slot ∧ D.target = C.target ∧
        frameActive p (clock p (V2.D.Run.stateBefore E rho k y).st
          (SA.proposalTime p.toParams (s + 1))) D = true :=
  pcsa_frozen_pc_in_proposer_win E rho h hF hFault (pcsa_strictFrom_of_healthy E rho hD 0) a k x y
    hx hy s C hk (pcsa_floor_freeze (pcsa_zero_le_proposal s)) hc hC
end AvailableChain.PCSA.Run

end
