module
public import AvailableChainPCSAProofs.Proofs.Clean.ResultPaths
public import AvailableChainPCSAProofs.Proofs.Clean.GateReads

public section

/-! C6 VoteTransport: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Every post-clock read names its exact scheduled tick and clocked store. -/
theorem pcsa_postClock_source (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (t : Time) (nd : Node p)
    (h : pcsa_postClock E rho x t = some nd) :
    ∃ k, rho.events[k]? = some (.tick x t) ∧
      nd.st = clock p (V2.D.Run.stateBefore E rho k x).st t := by
  rw [pcsa_postClock_def] at h
  obtain ⟨pre, hpre, he⟩ := Option.map_eq_some_iff.mp h
  rw [pcsa_preTick_def] at hpre
  obtain ⟨k, hk, hpre⟩ := Option.map_eq_some_iff.mp hpre
  subst pre
  subst nd
  exact ⟨k, V2.D.Run.tickIdx?_spec hk, rfl⟩
/-- Result-to-HEAD extension needs a floor at the early time of label `s`. -/
theorem pcsa_next_head_above_result_of_root_from_early (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (x y : V) (hx : x ∈ rho.honest) (s : Slot) (X H : Block)
    (hT : T₀ ≤ SA.earlyTime p.toParams s) (hc : SA.gateTime p.toParams s ≤ cut)
    (hX : gateResultAt p c E rho x s = some (some X))
    (hH : HonestHeadAt p c E rho y (s + 1) H)
    (hroot : ∀ R, liveRootAt p c E rho y (s + 1) = some R → Block.Compatible R X) :
    Block.Preceq X H := by
  obtain ⟨a, ha, hresult⟩ := pcsa_gateResultAt_source E rho x s X hX
  have hy := hH.1
  have hhead := hH.2.2
  rw [pcsa_voteHeadAt_def] at hhead
  obtain ⟨nd, hnd, hhead⟩ := Option.map_eq_some_iff.mp hhead
  obtain ⟨k, hk, hstore⟩ := pcsa_postClock_source E rho y _ nd hnd
  have hr : liveRootAt p c E rho y (s + 1) =
      some (liveRoot p nd.st (voterPC p nd.st (s + 1))) := by
    rw [pcsa_liveRootAt_def, hnd]
    rfl
  have hcompat := hroot _ hr
  rw [hstore] at hhead hcompat
  let dst := clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s + 1))
  have hfcut : SA.freezeTime p.toParams s ≤ cut := by
    apply le_trans _ hc
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    linarith
  have hfk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ k := by
    apply Nat.le_of_not_gt
    intro hlt
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hk _).mp hlt
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 3 * p.Δ at ht
    push_cast at ht
    have hp := p.deltaPos
    nlinarith
  have hpaths := pcsa_result_prefixes_retained_win E rho h hF hD (hT := hT) a k x y
    hx hy (SA.gateTime p.toParams s) (SA.voteTime p.toParams (s + 1)) s X hfcut hfk hresult
  have hcover := pcsa_gate_voter_walk_counts_from_early E rho h hF hD (hT := hT) a k x y hx hy s X
    (voterPC p dst (s + 1))
    (erasedList dst (KitFG.storeFrameView (FGSA.heightView p) dst.fg (voterBlocks p dst (s + 1))))
    hc ha hk hresult hcompat (fun C _ hCX => (hpaths C hCX).2)
  delta headVote at hhead
  rw [ite_eq_right (Nat.succ_ne_zero s)] at hhead
  rw [← hhead]
  exact hcover
/-- In the delivery window: Actual receipt and retained paths turn root compatibility into HEAD
extension. -/
theorem pcsa_next_head_above_result_of_root_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (x y : V) (hx : x ∈ rho.honest) (s : Slot) (X H : Block)
    (hT : T₀ ≤ SA.proposalTime p.toParams s) (hc : SA.gateTime p.toParams s ≤ cut)
    (hX : gateResultAt p c E rho x s = some (some X))
    (hH : HonestHeadAt p c E rho y (s + 1) H)
    (hroot : ∀ R, liveRootAt p c E rho y (s + 1) = some R → Block.Compatible R X) :
    Block.Preceq X H :=
  pcsa_next_head_above_result_of_root_from_early E rho h hF hD x y hx s X H
    (pcsa_floor_early hT) hc hX hH hroot
/-- Actual receipt and retained paths turn root compatibility into HEAD extension. -/
theorem pcsa_next_head_above_result_of_root (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (x y : V) (hx : x ∈ rho.honest) (s : Slot) (X H : Block)
    (hc : SA.gateTime p.toParams s ≤ cut)
    (hX : gateResultAt p c E rho x s = some (some X))
    (hH : HonestHeadAt p c E rho y (s + 1) H)
    (hroot : ∀ R, liveRootAt p c E rho y (s + 1) = some R → Block.Compatible R X) :
    Block.Preceq X H := by
  obtain ⟨a, ha, hresult⟩ := pcsa_gateResultAt_source E rho x s X hX
  have hy := hH.1
  have hhead := hH.2.2
  rw [pcsa_voteHeadAt_def] at hhead
  obtain ⟨nd, hnd, hhead⟩ := Option.map_eq_some_iff.mp hhead
  obtain ⟨k, hk, hstore⟩ := pcsa_postClock_source E rho y _ nd hnd
  have hr : liveRootAt p c E rho y (s + 1) =
      some (liveRoot p nd.st (voterPC p nd.st (s + 1))) := by
    rw [pcsa_liveRootAt_def, hnd]
    rfl
  have hcompat := hroot _ hr
  rw [hstore] at hhead hcompat
  let dst := clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s + 1))
  have hfcut : SA.freezeTime p.toParams s ≤ cut := by
    apply le_trans _ hc
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    linarith
  have hfk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ k := by
    apply Nat.le_of_not_gt
    intro hlt
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hk _).mp hlt
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 3 * p.Δ at ht
    push_cast at ht
    have hp := p.deltaPos
    nlinarith
  have hpaths := pcsa_result_prefixes_retained E rho h hF hD a k x y hx hy
    (SA.gateTime p.toParams s) (SA.voteTime p.toParams (s + 1)) s X hfcut hfk hresult
  have hcover := pcsa_gate_voter_walk_counts E rho h hF hD a k x y hx hy s X
    (voterPC p dst (s + 1))
    (erasedList dst (KitFG.storeFrameView (FGSA.heightView p) dst.fg (voterBlocks p dst (s + 1))))
    hc ha hk hresult hcompat (fun C _ hCX => (hpaths C hCX).2)
  delta headVote at hhead
  rw [ite_eq_right (Nat.succ_ne_zero s)] at hhead
  rw [← hhead]
  exact hcover
end AvailableChain.PCSA.Run

end
