module
public import AvailableChainPCSAProofs.Proofs.Clean.HeadEvidence
public import AvailableChainPCSAProofs.Proofs.Clean.VoteTransport

public section

/-! C6 HonestReceipt: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- An honest HEAD decision emits its exact root under each seat held by its node. -/
theorem pcsa_honest_head_emits (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (s : Slot) (i : Fin p.n) (H : Block)
    (hi : rho.seatOf (.base (.head s)) i = x) (hH : HonestHeadAt p c E rho x s H) :
    V2.D.Run.emits E rho x (⟨.seat (.base (.head s)) i, .head H.root⟩ : Obj p)
      (SA.voteTime p.toParams s) := by
  have hh := hH.2.2
  rw [pcsa_voteHeadAt_def] at hh
  obtain ⟨nd, hnd, hh⟩ := Option.map_eq_some_iff.mp hh
  obtain ⟨k, hk, hs⟩ := pcsa_postClock_source E rho x _ nd hnd
  rw [hs] at hh
  refine ⟨k, hk, ?_⟩
  rw [(V2.D.Run.step_tick_eq E rho hk).2]
  apply (V2.D.Engine.mem_tick_seat_iff E rho _ x _ (.base (.head s)) i (.head H.root)).mpr
  refine ⟨hH.2.1, hi, .headAction s, rfl, rfl, ?_⟩
  cases m <;> change some (Msg.head (headVote p
    (clock p (V2.D.Run.stateBefore E rho k x).st (SA.voteTime p.toParams s)) s).root) = some
      (.head H.root)
  all_goals rw [hh]
/-- A HEAD of an honest seat cannot be excluded before its early cutoff. -/
theorem pcsa_honest_head_not_excluded_early (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (y : V) (s : Slot) (i : Fin p.n) (r : BlockId)
    (hi : rho.seatOf (.base (.head s)) i ∈ rho.honest) :
    (pcsaWith m p c).excludes
      (V2.D.Run.stateBeforeTime E rho (SA.earlyTime p.toParams s) y)
      (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) = false := by
  have hp := p.deltaPos
  have hpos : 0 < SA.earlyTime p.toParams s := by
    change 0 < 4 * p.Δ * (s : Int) + 2 * p.Δ
    positivity
  have hnow : (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) y).st.base.now <
      SA.earlyTime p.toParams s := by
    have hr := pcsa_clock_read p c (m := m) (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) y)
    rcases V2.D.Engine.stateBefore_now_source_noRestart (pcsaClock p c) E rho h.noRestart
      (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) y with hz | ⟨j, hj, he⟩
    · rw [hr] at hz
      rw [hz]
      exact hpos
    · rw [hr] at he
      exact (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed he _).mp hj
  have hslot : (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) y).st.slot p ≤ s := by
    change ((V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) y).st.base.now / (4 * p.Δ)).toNat ≤ s
    apply Int.toNat_le.mpr
    apply (Int.ediv_le_iff_le_mul (show 0 < 4 * p.Δ by positivity)).mpr
    change (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) y).st.base.now <
      4 * p.Δ * (s : Int) + 2 * p.Δ at hnow
    nlinarith
  apply Bool.eq_false_iff.mpr
  intro he
  change GridCO.excludes p.toParams.engine
    (V2.D.Run.stateBeforeTime E rho (SA.earlyTime p.toParams s) y).st.base
    ⟨.seat s i, .head r⟩ = true at he
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ h.valid.toScheduleWellFormed] at he
  obtain ⟨_, hold | hcap⟩ := (FGSA.Run.Internal.grid_excludes_head_iff _ s i r).mp he
  · change s + 1 < (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) y).st.slot p at hold
    exact (Nat.not_lt.mpr (hslot.trans (Nat.le_succ s))) hold
  · have hf := pcsa_honest_head_pool_not_capped E rho h.valid
      (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) y s i hi
    rw [hcap] at hf
    cases hf
/-- From the window floor, strict broadcast puts each honest HEAD in the pool with a
strict early stamp. -/
theorem pcsa_honest_head_before_early_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (x y : V) (hy : y ∈ rho.honest) (s : Slot) (i : Fin p.n) (H : Block)
    (hi : rho.seatOf (.base (.head s)) i = x) (hH : HonestHeadAt p c E rho x s H)
    (hT : T₀ ≤ SA.voteTime p.toParams s)
    (hc : SA.earlyTime p.toParams s ≤ cut) (k : Nat)
    (hk : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ k) :
    (⟨.seat s i, .head H.root⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho k y).st.base.votes ∧
    GridCO.stampVote (V2.D.Run.stateBefore E rho k y).st.base
      ⟨.seat s i, .head H.root⟩ < SA.earlyTime p.toParams s := by
  have hh : rho.seatOf (.base (.head s)) i ∈ rho.honest := by rw [hi]; exact hH.1
  have he := pcsa_honest_head_emits E rho x s i H hi hH
  have htime : SA.voteTime p.toParams s + E.Δ = SA.earlyTime p.toParams s := by
    rw [h.delta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 2 * p.Δ
    ring
  have hNX : (pcsaWith m p c).excludes
      (V2.D.Run.stateBeforeTime E rho (SA.voteTime p.toParams s + E.Δ) y)
      (⟨.seat (.base (.head s)) i, .head H.root⟩ : Obj p) = false := by
    rw [htime]
    exact pcsa_honest_head_not_excluded_early E rho h y s i H.root hh
  obtain ⟨t, hlo, hhi, j, hhandle⟩ := pcsa_strict_broadcast_win E rho hD _
    (by intro body heq; cases heq) x y _ hH.1 hy he hT (by rwa [htime]) hNX
  rw [htime] at hhi
  have hstart : GridCO.proposalTime p.toParams.engine s ≤ t := by
    change 4 * p.Δ * (s : Int) ≤ t
    change 4 * p.Δ * (s : Int) + p.Δ ≤ t at hlo
    have hp := p.deltaPos
    linarith
  have hgate : t < SA.gateTime p.toParams s := by
    change t < 4 * p.Δ * (s : Int) + 2 * p.Δ at hhi
    change t < 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    linarith
  have hj : j + 1 ≤ V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) := by
    obtain ⟨parent, hevent, _⟩ := hhandle
    exact Nat.succ_le_of_lt
      ((Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hevent _).mpr hhi)
  have hm : (⟨.seat s i, .head H.root⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho (j + 1) y).st.base.votes := by
    rcases pcsa_handled_head_stateBefore_mem_or_cap E rho h j y t s i H.root hstart hgate hhandle
      with hm | he
    · exact hm
    · have hf := pcsa_honest_head_pool_not_capped E rho h.valid (j + 1) y s i hh
      rw [he] at hf
      cases hf
  refine ⟨pcsa_heads_stateBefore_mono E rho h.noRestart y (hj.trans hk) hm, ?_⟩
  rw [pcsa_head_stamp_stateBefore_eq E rho h.noRestart y (hj.trans hk) _ hm]
  exact pcsa_head_stamp_lt_of_index_cut E rho h.valid.toScheduleWellFormed h.noRestart
    (j + 1) y s i H.root _ hj hm
/-- Strict broadcast puts each honest HEAD in the pool with a strict early stamp. -/
theorem pcsa_honest_head_before_early (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (x y : V) (hy : y ∈ rho.honest) (s : Slot) (i : Fin p.n) (H : Block)
    (hi : rho.seatOf (.base (.head s)) i = x) (hH : HonestHeadAt p c E rho x s H)
    (hc : SA.earlyTime p.toParams s ≤ cut) (k : Nat)
    (hk : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ k) :
    (⟨.seat s i, .head H.root⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho k y).st.base.votes ∧
    GridCO.stampVote (V2.D.Run.stateBefore E rho k y).st.base
      ⟨.seat s i, .head H.root⟩ < SA.earlyTime p.toParams s := by
  have hT : (0 : Time) ≤ SA.voteTime p.toParams s := by
    have hd := p.deltaPos
    change (0 : Time) ≤ 4 * p.Δ * (s : Int) + p.Δ
    positivity
  exact pcsa_honest_head_before_early_win E rho h (pcsa_strictFrom_of_healthy E rho hD 0) x y
    hy s i H hi hH hT hc k hk
end AvailableChain.PCSA.Run

end
