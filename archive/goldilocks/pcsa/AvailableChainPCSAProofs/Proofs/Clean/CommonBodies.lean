module
public import AvailableChainPCSAProofs.Proofs.Clean.ForwardReceipt

public section

/-! C6 CommonBodies: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- In the delivery window: Every body held at the actual proposer tick reaches the voter before
its vote. -/
theorem pcsa_proposer_body_before_vote_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (B : Block)
    (ha : rho.events[a]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hk : V2.D.Run.idxBefore rho (SA.voteTime p.toParams s) ≤ k)
    (hT : T₀ ≤ SA.proposalTime p.toParams s) (hc : SA.voteTime p.toParams s ≤ cut)
    (hm : B ∈ (clock p (V2.D.Run.stateBefore E rho a x).st
      (SA.proposalTime p.toParams s)).base.blocks) :
    B ∈ (V2.D.Run.stateBefore E rho k y).st.base.blocks := by
  rw [pcsa_clock_blocks] at hm
  by_cases hg : B = .genesis
  · subst B
    exact (pcsa_genesis_body_stamp E rho h.noRestart k y).1
  · have hpre := V2.D.Engine.stateBefore_tick_eq_stateBeforeTime
      h.valid.toScheduleWellFormed h.noRestart ha
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ h.valid.toScheduleWellFormed] at hpre
    rw [hpre] at hm
    have ht := pcsa_body_stamp_lt_of_index_cut E rho h.valid.toScheduleWellFormed
      h.noRestart _ x B _ (le_refl _) hg hm
    have hpub : V2.PublicTime E (SA.proposalTime p.toParams s) := by
      refine ⟨4 * s, ?_⟩
      rw [h.delta]
      change 4 * p.Δ * (s : Int) = ((4 * s : Nat) : Int) * p.Δ
      push_cast
      ring
    have hz : 0 ≤ SA.proposalTime p.toParams s := by
      have hp := p.deltaPos
      change 0 ≤ 4 * p.Δ * (s : Int)
      positivity
    have he : SA.proposalTime p.toParams s + E.Δ = SA.voteTime p.toParams s := by
      rw [h.delta]
      rfl
    exact (pcsa_body_before_public_cut_relay_win E rho h hF hD (hT := hT) _ k x y hx hy B _ hpub hz
      (by rwa [he]) (by rwa [he]) hg hm ht).1
/-- Every body held at the actual proposer tick reaches the voter before its vote. -/
theorem pcsa_proposer_body_before_vote (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (B : Block)
    (ha : rho.events[a]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hk : V2.D.Run.idxBefore rho (SA.voteTime p.toParams s) ≤ k)
    (hc : SA.voteTime p.toParams s ≤ cut)
    (hm : B ∈ (clock p (V2.D.Run.stateBefore E rho a x).st
      (SA.proposalTime p.toParams s)).base.blocks) :
    B ∈ (V2.D.Run.stateBefore E rho k y).st.base.blocks :=
  pcsa_proposer_body_before_vote_win E rho h hF (pcsa_strictFrom_of_healthy E rho hD 0) a k x y hx
    hy s B ha hk (pcsa_zero_le_proposal s) hc hm
/-- In the delivery window: A frozen support body reaches the honest proposer before its proposal
tick. -/
theorem pcsa_frozen_body_in_proposer_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (B : Block) (v : Time)
    (hk : rho.events[k]? = some (.tick y (SA.proposalTime p.toParams (s + 1))))
    (hT : T₀ ≤ SA.freezeTime p.toParams s) (hc : SA.proposalTime p.toParams (s + 1) ≤ cut)
    (hm : B ∈ (clock p (V2.D.Run.stateBefore E rho a x).st v).base.blocks)
    (hs : GridCO.stampBlock (clock p (V2.D.Run.stateBefore E rho a x).st v).base B <
      SA.freezeTime p.toParams s) :
    B ∈ (clock p (V2.D.Run.stateBefore E rho k y).st
      (SA.proposalTime p.toParams (s + 1))).base.blocks := by
  rw [pcsa_clock_blocks] at hm ⊢
  by_cases hg : B = .genesis
  · subst B
    exact (pcsa_genesis_body_stamp E rho h.noRestart k y).1
  · have hs' : GridCO.stampBlock (V2.D.Run.stateBefore E rho a x).st.base B <
        SA.freezeTime p.toParams s := by
      have he : GridCO.stampBlock (clock p (V2.D.Run.stateBefore E rho a x).st v).base B =
          GridCO.stampBlock (V2.D.Run.stateBefore E rho a x).st.base B := by
        obtain ⟨row, hr⟩ := pcsa_body_stamp_lookup E rho a x B hm
        delta GridCO.stampBlock
        rw [pcsa_clock_bodyStamps, hr]
        rfl
      rwa [he] at hs
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
      exact lt_irrefl _ ((Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hk _).mp
        hn)
    exact (pcsa_body_before_public_cut_relay_win E rho h hF hD (hT := hT) a k x y
        hx hy B _
      hpub hz (by rwa [he]) (by rwa [he]) hg hm hs').1
/-- A frozen support body reaches the honest proposer before its proposal tick. -/
theorem pcsa_frozen_body_in_proposer (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (B : Block) (v : Time)
    (hk : rho.events[k]? = some (.tick y (SA.proposalTime p.toParams (s + 1))))
    (hc : SA.proposalTime p.toParams (s + 1) ≤ cut)
    (hm : B ∈ (clock p (V2.D.Run.stateBefore E rho a x).st v).base.blocks)
    (hs : GridCO.stampBlock (clock p (V2.D.Run.stateBefore E rho a x).st v).base B <
      SA.freezeTime p.toParams s) :
    B ∈ (clock p (V2.D.Run.stateBefore E rho k y).st
      (SA.proposalTime p.toParams (s + 1))).base.blocks :=
  pcsa_frozen_body_in_proposer_win E rho h hF (pcsa_strictFrom_of_healthy E rho hD 0) a k x y hx
    hy s B v hk (pcsa_floor_freeze (pcsa_zero_le_proposal s)) hc hm hs
end AvailableChain.PCSA.Run

end
