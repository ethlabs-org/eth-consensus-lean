module
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchStop
public import AvailableChainFGCompose.Statements.Population.FrontierSearch

public section

/-! Blueprint 21 HG.4:1698--1720; frontier plan §3.3.
The row tail uses the saved seed's continuing local service across same-frontier
events. A rise supplies an earlier row through RCap. This module does not assert the
terminal rise tail. The continuing service of the actual saved seed is a leaf. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot)
variable (O : FGObservationReads R) (T : FGTiming) (I : V2.D.Interface Prot)
variable (pair : Wire → NamedHeightPair)
variable (chainRows : Prot.State → Block → List Wire)
variable (Ef : Electorate (Fin n)) (obs : FGObservationLaws R O)
variable (cert : FGCertificateLaws Ef O.height O.finality)
variable (inv : ∀ i x, FGStoreInvariant O.height O.finality
  (R.core (rho.stateBefore E i x)).fg)

include cert inv in
/-- Blueprint 21 HG.4 and IF.3(a); frontier plan §3.3/§4.
DC: SAME first honest height-m row within P-4Δ of the saved seed.
The closed horizon includes equality. No phase through this endpoint is assumed:
the actual seed's continuing local service is read under the honest cap. -/
theorem healing_frontierTail_row_holder (hT : FGTimingLaws T) (hs : V2.D.ScheduleWellFormed E rho)
    (honestSeats : (FGHonestSeats S rho).Nonempty)
    (mono : FGRunOrderLaws E rho R)
    (cap : RCap R S E rho O T (fun a => namedEntry (pair a)) chainRows)
    {u t : Time} {m q : Nat} {J : Option (FGBlock (Fin n))} {contested : Bool}
    {Q : Block} {Qfg : FGBlock (Fin n)}
    (hp : PhaseInterval R E rho O u (T.gate q) m J contested)
    (_hQ : HonestProposal E rho I q Q) (hqt : T.gate q ≤ t)
    (service : ∀ v, T.gate q ≤ v → v ≤ rho.horizon →
      (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
        (R.core (rho.stateBefore E i x)).fg.h_max ≤ m) →
      FrontierLocalServiceFG R S E rho O T I pair q Q Qfg m v)
    (hhor : t + (FGCompose.P T - 4 * T.delta) ≤ rho.horizon) :
    FirstHeightRowBy S E rho T pair m (t + (FGCompose.P T - 4 * T.delta)) := by
  classical
  have p0d5c_tail_frontier_mono (R : FGCoreReads Prot n Base Proposal Wire)
      (E : Generic.Env V) (rho : V2.D.Run V Prot) (mono : FGRunOrderLaws E rho R) {i j : Nat}
      (hij : i ≤ j) : frontierAtIdx R E rho i ≤ frontierAtIdx R E rho j := by
    apply Finset.sup_le
    intro x hx
    exact (mono.mono i j x hx hij).2.2.trans
      (Finset.le_sup (f := fun y => (R.core (rho.stateBefore E j y)).fg.h_max) hx)
  -- First-opening time at the least eligible round.
  have p0d5c_tail_first_time (T : FGTiming) (hT : FGTimingLaws T) {q r : Nat}
      (hqr : q ≤ r * T.roundSlots) (hfirst : ∀ r', q ≤ r' * T.roundSlots → r ≤ r') :
      T.action r ≤ T.gate q + FGCompose.P T - 4 * T.delta := by
    have hd := hT.delta_pos
    rw [hT.action_eq, hT.gate_eq, hT.gate_eq, hT.proposal_eq, hT.proposal_eq]
    have hup : r * T.roundSlots + 1 ≤ q + T.roundSlots := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr
        have := hT.rounds
        omega
      · have hlt : ¬ q ≤ (r - 1) * T.roundSlots := fun h => by
          have := hfirst (r - 1) h
          omega
        have he : (r - 1) * T.roundSlots + T.roundSlots = r * T.roundSlots := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hr]
        omega
    have hupI : ((r * T.roundSlots : Nat) : Time) + 1 ≤ (q : Time) + T.roundSlots := by
      exact_mod_cast hup
    unfold FGCompose.P
    nlinarith
  -- Action times preserve round order.
  have p0d5c_tail_action_mono (T : FGTiming) (hT : FGTimingLaws T) {a b : Nat} (h : a ≤ b) :
      T.action a ≤ T.action b := by
    rw [hT.action_eq, hT.action_eq, hT.gate_eq, hT.gate_eq, hT.proposal_eq, hT.proposal_eq]
    have hI : ((a * T.roundSlots : Nat) : Time) ≤ ((b * T.roundSlots : Nat) : Time) := by
      exact_mod_cast Nat.mul_le_mul_right _ h
    nlinarith [hT.delta_pos]
  let Dl := t + (FGCompose.P T - 4 * T.delta)
  have hm : 1 ≤ m := hp.2.2.1
  have hd := hT.delta_pos
  have hP : 8 * T.delta ≤ FGCompose.P T := by
    have hR : (2 : Time) ≤ T.roundSlots := by exact_mod_cast hT.rounds
    change 8 * T.delta ≤ 4 * (T.roundSlots : Time) * T.delta
    nlinarith
  by_cases hhigh : ∃ x, x ∈ rho.honest ∧
      m < (R.core (rho.stateBefore E (timeIdx rho Dl) x)).fg.h_max
  · obtain ⟨x, hx, hh⟩ := hhigh
    obtain ⟨W, hW, hWh⟩ := healing_phase_frontier_witness (R := R) (E := E) (rho := rho)
      (O := O) (Ef := Ef) (cert := cert) (inv := inv) (timeIdx rho Dl) x
    obtain ⟨j, z, r, a, e, hj, hr, hn, _⟩ := cap (m - 1) (timeIdx rho Dl) x W
      ⟨hx, hW⟩ (by simp only [Height] at *; omega)
    have hn' : namedEntry (pair a) = some (m, e) := by
      simpa only [Nat.sub_add_cancel hm] using hn
    exact frontierSearch_first_row S E rho T pair hT ⟨j, z, a, e, hr, hn'⟩
      (frontierSearch_event_time_le E rho hs hr.2.1 hj)
  · have hcap (i : Nat) (x : V) (hi : i ≤ timeIdx rho Dl) (hx : x ∈ rho.honest) :
        (R.core (rho.stateBefore E i x)).fg.h_max ≤ m := by
      have hfront : frontierAtIdx R E rho (timeIdx rho Dl) ≤ m :=
        Finset.sup_le (fun y hy => le_of_not_gt (fun hh => hhigh ⟨y, hy, hh⟩))
      exact (healing_phase_local_le_frontier (R := R) (E := E) (rho := rho) hx).trans
        ((p0d5c_tail_frontier_mono R E rho mono hi).trans hfront)
    have hex : ∃ r, q ≤ r * T.roundSlots := ⟨q, by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left q
        (show 1 ≤ T.roundSlots from (by decide : 1 ≤ 2).trans hT.rounds)⟩
    let r := Nat.find hex
    have hqr : q ≤ r * T.roundSlots := Nat.find_spec hex
    have hfirst : ∀ r', q ≤ r' * T.roundSlots → r ≤ r' :=
      fun r' hr' => Nat.find_min' hex hr'
    have h1 := p0d5c_tail_first_time T hT hqr hfirst
    have har : T.action r ≤ Dl := by dsimp only [Dl]; linarith
    have hqD : T.gate q ≤ Dl := by dsimp only [Dl]; linarith
    have hf := service Dl hqD hhor (fun i x _ hi hx => hcap i x hi hx)
    obtain ⟨hc, ⟨e, he⟩, _⟩ := hf.2.2.2.2 r hqr har
    obtain ⟨seat, hseat⟩ := honestSeats
    let x := safetyHolder S rho seat
    have hx : x ∈ rho.honest := by
      simpa only [FGHonestSeats_def, Finset.mem_filter, Finset.mem_univ, true_and] using hseat
    obtain ⟨K, nd, j, rSent, a, _, hK, _, _, hrs, hr, hn⟩ := hc seat hseat
    have hKh := (he x K hx hK).1
    rw [hKh] at hn
    exact frontierSearch_first_row S E rho T pair hT ⟨j, x, a, _, hr, hn⟩
      ((p0d5c_tail_action_mono T hT hrs).trans har)

end AvailableChain.FGCompose
end
