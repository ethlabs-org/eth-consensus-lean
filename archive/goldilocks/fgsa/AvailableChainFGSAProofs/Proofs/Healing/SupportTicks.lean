module
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSAProofs.Proofs.Healing.SupportRecovery

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- The selected honest seats whose HEAD duty is enabled at label s. -/
noncomputable abbrev healingJoinedSeats (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) : Finset (Fin p.n) := by
  classical
  exact Finset.univ.filter (fun q => rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
    joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s))

omit [DecidableEq V] in
/-- Membership carries the selected actor's actual join fact. -/
theorem healingJoinedSeats_mem (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) (q : Fin p.n) : q ∈ healingJoinedSeats E rho s ↔
    rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
    joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s) := by
  classical
  delta healingJoinedSeats
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

omit [DecidableEq V] in
/-- Seat and node counts agree at the same joined HEAD vote. -/
theorem healingJoinedSeats_card (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (s : Slot) :
    (healingJoinedSeats E rho s).card =
      (joinedHonest p E rho (SA.voteTime p.toParams s)).card := by
  classical
  have hb := hC (.base (.head s)) trivial
  have hslot : slotAt p (SA.voteTime p.toParams s) = s := by
    let x := rho.seatOf (.base (.head s)) ⟨0, p.nPos⟩
    exact (fgsa_postClock_slot (c := c) (rho.stateBefore E 0 x) _).2.symm.trans
      (fgsa_vote_slot (c := c) _ s)
  have himage : (healingJoinedSeats E rho s).image (rho.seatOf (.base (.head s))) =
      joinedHonest p E rho (SA.voteTime p.toParams s) := by
    ext x
    change x ∈ (healingJoinedSeats E rho s).image (rho.seatOf (.base (.head s))) ↔
      x ∈ rho.honest.filter (fun x => joinedAt p E rho x
        (slotAt p (SA.voteTime p.toParams s)) (SA.voteTime p.toParams s))
    constructor
    · intro hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hq, hj⟩ := (healingJoinedSeats_mem E rho s q).mp hq
      exact Finset.mem_filter.mpr ⟨hq, by simpa only [hslot] using hj⟩
    · intro hx
      obtain ⟨hx, hj⟩ := Finset.mem_filter.mp hx
      obtain ⟨q, rfl⟩ := hb.2 x
      exact Finset.mem_image.mpr ⟨q,
        (healingJoinedSeats_mem E rho s q).mpr ⟨hx, by simpa only [hslot] using hj⟩, rfl⟩
  exact himage ▸ (Finset.card_image_of_injective (healingJoinedSeats E rho s) hb.1).symm

/-- Recovery produces the joined-seat release and batch counts in a late window. -/
theorem healing_recovery_seat_counts [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot}
    (h : HealingWindow p E 1 s) (hh : SA.voteTime p.toParams s ≤ rho.horizon) :
    SA.releaseThreshold p.toParams ≤ (healingJoinedSeats E rho s).card ∧
      Gen.Pure.Batch (healingJoinedSeats E rho s).card (Gen.V2.Duty.faulty rho).card := by
  rw [healingJoinedSeats_card E rho hrec.base.cstar s]
  exact healing_recovery_joined_counts E rho hrec s h.2 h.sync hh

/-- Readiness gives the release and Batch counts through the CStar seat bridge. -/
theorem healing_ready_seat_counts [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot}
    (hready : recoveryStart p E ≤ SA.voteTime p.toParams s)
    (hhor : SA.voteTime p.toParams s ≤ rho.horizon) :
    SA.releaseThreshold p.toParams ≤ (healingJoinedSeats E rho s).card ∧
      Gen.Pure.Batch (healingJoinedSeats E rho s).card (Gen.V2.Duty.faulty rho).card :=
  healing_recovery_seat_counts E rho hrec
    (healing_window_of_cut E (healing_ready_vote_cutoff E hready)) hhor

/-- With the batch cutoff, every seat outside the selected set is faulty. -/
theorem healing_recovery_seat_rivals [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot}
    (h : HealingWindow p E 1 s) (hh : SA.voteTime p.toParams s ≤ rho.horizon)
    (pool : Finset (Fin p.n)) :
    (pool \ healingJoinedSeats E rho s).card ≤ (Gen.V2.Duty.faulty rho).card := by
  classical
  apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head s)))
  · intro q hq
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hx
    exact (Finset.mem_sdiff.mp hq).2 ((healingJoinedSeats_mem E rho s q).mpr
      ⟨hx, healing_recovery_joined_window E rho hrec h hx hh⟩)
  · intro q _ r _ hqr
    exact (hrec.base.cstar (.base (.head s)) trivial).1 hqr

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:709–715 (H.2); plan H-SUPPORT §4 step 7.
DC: SAME an honest node ticks at each awake vote time inside the horizon. -/
theorem healing_support_vote_tick (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (hDelta : E.Δ = p.Δ) {z : V}
    (hz : z ∈ rho.honest) (i : Slot) (hh : SA.voteTime p.toParams i ≤ rho.horizon)
    (hawake : E.awake z (SA.voteTime p.toParams i) = true) :
    ∃ j : Nat, rho.events[j]? = some (.tick z (SA.voteTime p.toParams i)) := by
  have htime : ((4 * i + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams i := by
    change ((4 * i + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * (i : Int) + p.Δ
    push_cast
    ring
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hS hDelta z hz (4 * i + 1)
    (htime ▸ hh) (htime ▸ hawake)
  rw [htime] at hj
  exact ⟨j, hj⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:709–715 (H.2); plan H-SUPPORT §4 step 7.
DC: SAME a joined honest holder emits its HEAD at its vote tick, and this HEAD is its
read at the label. -/
theorem healing_support_honest_emits (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) {i : Slot} {k : Fin p.n} {j : Nat}
    (hj : rho.events[j]? = some (.tick (rho.seatOf (.base (.head i)) k)
      (SA.voteTime p.toParams i)))
    (hawake : E.awake (rho.seatOf (.base (.head i)) k) (SA.voteTime p.toParams i) = true)
    (hjoined : joinedNow p (FGSA.clock p (V2.D.Run.stateBefore E rho j
      (rho.seatOf (.base (.head i)) k)).st (SA.voteTime p.toParams i)) = true) :
    let K := headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho j
      (rho.seatOf (.base (.head i)) k)).st (SA.voteTime p.toParams i)) i
    V2.D.Run.emits E rho (rho.seatOf (.base (.head i)) k)
        (ofHead p ⟨.seat (.head i) k, K.root⟩) (SA.voteTime p.toParams i) ∧
      headAtLabel p c E rho (rho.seatOf (.base (.head i)) k) i = some K := by
  intro K
  refine ⟨⟨j, hj, ?_⟩, ?_⟩
  · rw [(V2.D.Run.step_tick_eq E rho hj).2]
    exact (fgsa_emits_head E rho _ _ _ i k K.root).mpr ⟨hawake, rfl, rfl, hjoined, rfl⟩
  · unfold headAtLabel
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hj]
    rfl

end AvailableChain.FGSA.Run
end
