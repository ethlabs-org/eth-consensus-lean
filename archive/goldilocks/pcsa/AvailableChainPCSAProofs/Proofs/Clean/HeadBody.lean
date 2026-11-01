module
public import AvailableChainPCSAProofs.Proofs.Clean.VoteTransport

public section

/-! C6 HeadBody: concrete receipt and count support. -/
namespace AvailableChain.PCSA
/-- In a vacuous frame, the live root is a held body for any PC view. -/
theorem pcsa_liveRoot_body_mem (p : Params) (st : State p.n) (view : Option (PC p.n))
    (hTree : ∀ B, B ∈ st.base.blocks ↔ ∃ D ∈ st.fg.TF, eraseFG D = B)
    (hZ : (controls p st).Z = .genesis) (hgen : Block.genesis ∈ st.base.blocks) :
    liveRoot p st view ∈ st.base.blocks := by
  have held (B : Block) (hh : ∃ D ∈ fullTree p st, eraseFG D = B) : B ∈ st.base.blocks := by
    obtain ⟨D, hD, he⟩ := hh
    apply (hTree B).mpr
    refine ⟨D, ?_, he⟩
    rw [fullTree_def, KitFG.storeFrameView_def] at hD
    exact ((KitFG.mem_filteredFromView (FGSA.heightView p) (controls p st) st.fg.TF D).mp hD).1
  rcases pcsa_liveRoot_origin p st view with he | hm
  · rw [he]
    cases view with
    | none =>
      change eraseFG (controls p st).Z ∈ st.base.blocks
      rw [hZ]
      exact hgen
    | some C =>
      change (if frameActive p st C then C.target else eraseFG (controls p st).Z) ∈ _
      split
      · rename_i hc
        exact held C.target (of_decide_eq_true hc)
      · rw [hZ]
        exact hgen
  · obtain ⟨_, _, _, _, hb, _⟩ := (pcsa_walkLocks_mem p st view _).mp hm
    exact held _ hb
/-- A stage-1 HEAD vote selects a body from the cumulative pool. -/
theorem pcsa_headVote_body_mem (p : Params) (st : State p.n) (s : Slot)
    (hTree : ∀ B, B ∈ st.base.blocks ↔ ∃ D ∈ st.fg.TF, eraseFG D = B)
    (hZ : (controls p st).Z = .genesis) (hgen : Block.genesis ∈ st.base.blocks) :
    headVote p st s ∈ st.base.blocks := by
  delta headVote
  split
  · exact hgen
  · rcases pcsa_headInTree_mem_or_root p st (voterPC p st s) _ _ _ with he | hm
    · rw [he]
      exact pcsa_liveRoot_body_mem p st _ hTree hZ hgen
    · exact (List.mem_filter.mp hm).1
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- An honest HEAD's exact body is held and stamped before its vote tick. -/
theorem pcsa_honest_head_body_before_vote (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (x : V) (s : Slot) (H : Block)
    (hH : HonestHeadAt p c E rho x s H) :
    ∃ k, rho.events[k]? = some (.tick x (SA.voteTime p.toParams s)) ∧
      H ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks ∧
      GridCO.stampBlock (V2.D.Run.stateBefore E rho k x).st.base H < SA.voteTime p.toParams s := by
  have hx := hH.1
  have hh := hH.2.2
  rw [pcsa_voteHeadAt_def] at hh
  obtain ⟨nd, hnd, hhead⟩ := Option.map_eq_some_iff.mp hh
  obtain ⟨k, hk, hstore⟩ := pcsa_postClock_source E rho x _ nd hnd
  rw [hstore] at hhead
  have hreach := Reachable.tick (SA.voteTime p.toParams s) (pcsa_reachable_stateBefore E rho k x)
  have hZ : (controls p (clock p (V2.D.Run.stateBefore E rho k x).st
      (SA.voteTime p.toParams s))).Z = .genesis := by
    change (KitFG.storeControlsView (FGSA.heightView p) (clock p _ _).fg).Z = .genesis
    rw [pcsa_body_clock_fg]
    exact (hF x hx k).2.1
  have hgen : Block.genesis ∈ (clock p (V2.D.Run.stateBefore E rho k x).st
      (SA.voteTime p.toParams s)).base.blocks := by
    rw [pcsa_clock_blocks]
    exact (pcsa_genesis_body_stamp E rho h.noRestart k x).1
  have hm := pcsa_headVote_body_mem p _ s (pcsa_tree_correspondence p _ hreach) hZ hgen
  rw [hhead, pcsa_clock_blocks] at hm
  refine ⟨k, hk, hm, ?_⟩
  by_cases hg : H = .genesis
  · rw [hg, (pcsa_genesis_body_stamp E rho h.noRestart k x).2]
    have hp := p.deltaPos
    change 0 < 4 * p.Δ * (s : Int) + p.Δ
    positivity
  · have he := V2.D.Engine.stateBefore_tick_eq_stateBeforeTime
      h.valid.toScheduleWellFormed h.noRestart hk
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ h.valid.toScheduleWellFormed] at he
    rw [he] at hm ⊢
    exact pcsa_body_stamp_lt_of_index_cut E rho h.valid.toScheduleWellFormed h.noRestart
      _ x H _ (le_refl _) hg hm
/-- In the delivery window: Every honest receiver holds the exact HEAD body before the early
cutoff. -/
theorem pcsa_honest_head_body_before_early_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (x y : V) (hy : y ∈ rho.honest) (s : Slot) (H : Block)
    (hH : HonestHeadAt p c E rho x s H) (hT : T₀ ≤ SA.voteTime p.toParams s) (hc : SA.earlyTime
        p.toParams s ≤ cut)
    (k : Nat) (hk : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ k) :
    H ∈ (V2.D.Run.stateBefore E rho k y).st.base.blocks ∧
      GridCO.stampBlock (V2.D.Run.stateBefore E rho k y).st.base H < SA.earlyTime p.toParams s := by
  by_cases hg : H = .genesis
  · subst H
    obtain ⟨hm, ht⟩ := pcsa_genesis_body_stamp E rho h.noRestart k y
    refine ⟨hm, ?_⟩
    rw [ht]
    have hp := p.deltaPos
    change 0 < 4 * p.Δ * (s : Int) + 2 * p.Δ
    positivity
  · obtain ⟨a, _, hm, ht⟩ := pcsa_honest_head_body_before_vote E rho h hF x s H hH
    have he : SA.voteTime p.toParams s + E.Δ = SA.earlyTime p.toParams s := by
      rw [h.delta]
      change 4 * p.Δ * (s : Int) + p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 2 * p.Δ
      ring
    have hp : V2.PublicTime E (SA.voteTime p.toParams s) := by
      refine ⟨4 * s + 1, ?_⟩
      rw [h.delta]
      change 4 * p.Δ * (s : Int) + p.Δ = ((4 * s + 1 : Nat) : Int) * p.Δ
      push_cast
      ring
    have hz : 0 ≤ SA.voteTime p.toParams s := by
      have hp := p.deltaPos
      change 0 ≤ 4 * p.Δ * (s : Int) + p.Δ
      positivity
    have hh := pcsa_body_before_public_cut_relay_win E rho h hF hD (hT := hT) a k x
        y hH.1 hy H _
      hp hz
      (by rwa [he]) (by rwa [he]) hg hm ht
    rwa [he] at hh

/-- Every honest receiver holds the exact HEAD body before the early cutoff. -/
theorem pcsa_honest_head_body_before_early (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (x y : V) (hy : y ∈ rho.honest) (s : Slot) (H : Block)
    (hH : HonestHeadAt p c E rho x s H) (hc : SA.earlyTime p.toParams s ≤ cut)
    (k : Nat) (hk : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ k) :
    H ∈ (V2.D.Run.stateBefore E rho k y).st.base.blocks ∧
      GridCO.stampBlock (V2.D.Run.stateBefore E rho k y).st.base H < SA.earlyTime p.toParams s :=
  pcsa_honest_head_body_before_early_win E rho h hF (pcsa_strictFrom_of_healthy E rho hD 0) x y hy
    s H hH (pcsa_floor_vote (pcsa_zero_le_proposal s)) hc k hk
/-- An honest HEAD cannot name a body from a future slot. -/
theorem pcsa_honest_head_slot_le (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (x : V) (s : Slot) (H : Block)
    (hH : HonestHeadAt p c E rho x s H) : H.slot ≤ s := by
  by_cases hg : H = .genesis
  · rw [hg]
    exact Nat.zero_le _
  · obtain ⟨k, hk, hm, _⟩ := pcsa_honest_head_body_before_vote E rho h hF x s H hH
    obtain ⟨j, hjk, t, o, slot, N, P, hj, _, hErase, _, hAcc, _⟩ :=
      pcsa_body_receipt_origin E rho h.valid k x H hg hm
    have ht : t < SA.voteTime p.toParams s := by
      by_contra hn
      have hkj := V2.D.Engine.tick_index_lt_delivery E rho h.valid.toScheduleWellFormed
        hk hj (le_of_not_gt hn)
      omega
    have hnow := V2.D.Engine.stateBefore_now_le_event_noRestart (pcsaClock p c) E rho
      h.valid.toScheduleWellFormed h.noRestart hj x
    rw [pcsa_clock_read p c (m := m) (V2.D.Run.stateBefore E rho j x)] at hnow
    have hslot := pcsa_blockAccepted_slot p _ slot N P hAcc
    rw [hErase] at hslot
    apply hslot.trans
    change ((V2.D.Run.stateBefore E rho j x).st.base.now / (4 * p.Δ)).toNat ≤ s
    apply Int.toNat_le.mpr
    have hp := p.deltaPos
    apply (Int.ediv_le_iff_le_mul (show 0 < 4 * p.Δ by positivity)).mpr
    change t < 4 * p.Δ * (s : Int) + p.Δ at ht
    change (V2.D.Run.stateBefore E rho j x).st.base.now ≤ t at hnow
    nlinarith
end AvailableChain.PCSA.Run

end
