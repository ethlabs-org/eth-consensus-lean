module
import all AvailableChainFGCompose.Tests.PopulationSearchSeed
import all AvailableChainFGCompose.Tests.PopulationSearchPhase
import AvailableChainFGCompose.Proofs.Population.FrontierSearchRise

-- Standalone generic event-fold controls; exact accepted private fixture data are reused.
noncomputable section
namespace AvailableChain.FGCompose.Tests.POP6aTail
open AvailableChain.SimplexFG AvailableChain.KitFG
open PopulationSearchSeed PopulationSearchSeed.Fixture
open PopulationSearchPhase.Fixture

private abbrev tailCore : FGCoreReads missingProtocol 1 Unit Unit (Row (Fin 1)) :=
  { missingCore with headVote := fun _ _ => .genesis }

private abbrev tailObs : FGObservationReads tailCore where
  height := c5H
  finality := c5F
  controls nd := treeStoreControlsView c5H (tailCore.core nd).fg
  viable nd X := treeStoreFrameView c5H (tailCore.core nd).fg X

private abbrev tailRows (_ : missingProtocol.State) (_ : Block) : List (Row (Fin 1)) := [row]

private theorem geometry_premises_sat {V : Type} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V missingProtocol) :
    FGCertificateLaws c5E tailObs.height tailObs.finality ∧
    (∀ i x, FGStoreInvariant tailObs.height tailObs.finality
      (tailCore.core (rho.stateBefore E i x)).fg) ∧
    FGRunOrderLaws E rho tailCore ∧
    RCap tailCore missingReads E rho tailObs timing
      (fun a => namedEntry (Row.height_pair a)) tailRows ∧
    (∀ i x, (tailCore.core (rho.stateBefore E i x)).fg.h_max = 1) := by
  refine ⟨c5cert, ?_, ?_, ?_, fun _ _ => rfl⟩
  · intro i x
    change FGStoreInvariant c5H c5F Store.init
    constructor <;> decide +kernel
  · constructor
    intro i j x _ _
    exact ⟨show FGBlock.Preceq (FGBlock.genesis : FGBlock (Fin 1)) .genesis from rfl,
      le_rfl, le_rfl⟩
  · intro y i x W hW hy
    have hgen : W = .genesis := Finset.mem_singleton.mp hW.2
    subst W
    have hh : (tailObs.height FGBlock.genesis).h = 1 := by decide +kernel
    rw [hh] at hy
    exact (Nat.not_succ_le_self 1 ((Nat.le_add_left 2 y).trans hy)).elim

#print axioms geometry_premises_sat

private theorem mixed_premises_sat :
    V2.D.ScheduleWellFormed env missingRun ∧ FGTimingLaws timing ∧
    (FGHonestSeats missingReads missingRun).Nonempty ∧
    HonestProposal env missingRun missingIface 2 .genesis ∧
    PhaseInterval tailCore env missingRun tailObs 0 (timing.gate 2) 1
      (some .genesis) false ∧
    (∀ v, timing.gate 2 ≤ v → v ≤ missingRun.horizon →
      FrontierLocalServiceFG tailCore missingReads env missingRun tailObs timing missingIface
        Row.height_pair 2 .genesis .genesis 1 v) ∧
    HonestRowAt missingReads env missingRun timing 13 9 0 row ∧
    (∀ x ∈ missingRun.honest,
      actionSourceFG tailCore env missingRun timing x 1 = some (some .genesis)) ∧
    V2.D.proposerOf missingRun missingIface 2 = 7 ∧
    timing.action 0 = 6 ∧ timing.action 1 = 14 ∧
    14 + (FGCompose.P timing - 4 * timing.delta) ≤ missingRun.horizon := by
  have hrow : HonestRowAt missingReads env missingRun timing 13 9 0 row := by
    unfold HonestRowAt
    decide +kernel
  have hsource : ∀ x ∈ missingRun.honest,
      actionSourceFG tailCore env missingRun timing x 1 = some (some .genesis) := by
    intro x hx
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl <;> decide +kernel
  have hc : OpeningCoveredFG tailCore missingReads env missingRun c5H timing Row.height_pair
      (FGHonestSeats missingReads missingRun) 1 .genesis := by
    intro i _
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact ⟨.genesis, missingRun.stateBefore env 29 9, 13, 0, row,
      rfl, hsource 9 (by decide), by decide, by decide, by decide, hrow, rfl⟩
  refine ⟨missing_receiver_premises_sat.1, saved_seed_premises_sat.1,
    ⟨0, by decide⟩, missing_receiver_premises_sat.2.2.2.2.1, ?_, ?_, hrow, hsource,
    rfl, rfl, rfl, by decide⟩
  · refine ⟨by decide, by decide, by decide, ?_⟩
    intro i x _ _ _
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro v _ hv
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x s H _ _ _ hH
      obtain ⟨nd, _, he⟩ := Option.map_eq_some_iff.mp hH
      change Block.genesis = H at he
      subst H
      rfl
    · intro s B _ _ hp
      obtain ⟨_, o, _, hb⟩ := hp
      have hB : B = .genesis := (Option.some.inj hb).symm
      subst B
      rfl
    · intro i x _ _ _ _
      rfl
    · intro s B _ _ hp ht x hx _
      obtain ⟨_, o, _, hb⟩ := hp
      have hB : B = .genesis := (Option.some.inj hb).symm
      subst B
      have hs : (s : Nat) ≤ 4 := by
        change 4 * (s : Int) + 1 ≤ 18 at ht
        simp only [Slot, Time] at *
        omega
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx' with rfl | rfl <;> interval_cases s <;> decide +kernel
    · intro r hqr ht
      have hrt := ht.trans hv
      change @LE.le Nat _ 2 (r * 2) at hqr
      change 8 * (r : Int) + 6 ≤ 18 at hrt
      have hr : @Eq Nat r 1 := by omega
      subst r
      refine ⟨hc, ⟨genesisRoot, ?_⟩, ?_, fun _ => by decide⟩
      · intro x K hx hK
        rw [hsource x hx] at hK
        cases hK
        exact ⟨rfl, rfl⟩
      · intro x K hx hK
        rw [hsource x hx] at hK
        cases hK
        rfl

#print axioms mixed_premises_sat

private theorem nonholder_no_encoded (j : Nat) (t : Time)
    (hj : missingRun.events[j]? = some (.tick 7 t)) (a : Row (Fin 1)) :
    missingReads.encode a ∉ V2.D.Run.emitsAt env missingRun j := by
  have table : ∀ k : Fin 38, missingRun.events[k.val]?.map V2.Event.node = some 7 →
      (V2.D.Run.emitsAt env missingRun k.val).all
        (fun o => decide (o.auth ≠ .seat 6 0)) = true := by
    decide +kernel
  have hlen : j < 38 := (List.getElem?_eq_some_iff.mp hj).1
  have hnode : missingRun.events[j]?.map V2.Event.node = some 7 := by rw [hj]; rfl
  have hsafe := table ⟨j, hlen⟩ hnode
  intro ha
  have hn := of_decide_eq_true ((List.all_eq_true.mp hsafe) (missingReads.encode a) ha)
  exact hn rfl

#print axioms nonholder_no_encoded

private theorem row_identity {j r x : Nat} {a : Row (Fin 1)}
    (h : HonestRowAt missingReads env missingRun timing j x r a) :
    j = 13 ∧ x = 9 ∧ r = 0 ∧ a = row := by
  have ht := (mixed_premises_sat.1.in_horizon _ (List.mem_of_getElem? h.2.1)).2
  have hr : r ≤ 1 := by change 8 * (r : Int) + 6 ≤ 18 at ht; omega
  have hx : x = 7 ∨ x = 9 := by simpa using h.1
  rcases hx with rfl | rfl
  · exact (nonholder_no_encoded j _ h.2.1 a h.2.2).elim
  · obtain ⟨_, hj, ha⟩ := h
    have hjlt : j < 38 := (List.getElem?_eq_some_iff.mp hj).1
    interval_cases r
    · have hu : ∀ k : Fin 38,
          missingRun.events[k.val]? = some (.tick 9 6) → k.val = 13 := by
        decide +kernel
      have hj' : j = 13 := hu ⟨j, hjlt⟩ hj
      subst j
      have hall : (V2.D.Run.emitsAt env missingRun 13).all
          (fun o => decide (o.payload = row)) = true := by decide +kernel
      exact ⟨rfl, rfl, rfl,
        of_decide_eq_true ((List.all_eq_true.mp hall) (missingReads.encode a) ha)⟩
    · have hu : ∀ k : Fin 38,
          missingRun.events[k.val]? = some (.tick 9 14) → k.val = 29 := by
        decide +kernel
      have hj' : j = 29 := hu ⟨j, hjlt⟩ hj
      subst j
      have hall : (V2.D.Run.emitsAt env missingRun 29).all
          (fun o => decide (o.auth ≠ .seat 6 0)) = true := by decide +kernel
      exact (of_decide_eq_true
        ((List.all_eq_true.mp hall) (missingReads.encode a) ha) rfl).elim

#print axioms row_identity

private theorem mixed_no_rise_tail :
    FirstHeightRowBy missingReads env missingRun timing Row.height_pair 1 18 ∧
    (∃ r j x a e, HeightRow missingReads env missingRun timing
      (fun a => namedEntry (Row.height_pair a)) r 1 ∧
      HonestRowAt missingReads env missingRun timing j x r a ∧
      namedEntry (Row.height_pair a) = some (1, e) ∧
      j = 13 ∧ x = 9 ∧ r = 0 ∧ a = row ∧ timing.action r = 6) ∧
    V2.D.proposerOf missingRun missingIface 2 = 7 ∧
    (∀ i x, (tailCore.core (missingRun.stateBefore env i x)).fg.h_max = 1) := by
  obtain ⟨cert, inv, mono, cap, noRise⟩ := geometry_premises_sat env missingRun
  obtain ⟨schedule, ht, hne, hp, phase, service, _, _, hproposer, _, _, hhor⟩ :=
    mixed_premises_sat
  have result := healing_frontierTail_row_holder tailCore missingReads env missingRun tailObs
    timing missingIface Row.height_pair tailRows c5E cert inv ht schedule hne mono cap
    phase hp (le_rfl : timing.gate 2 ≤ (14 : Time))
    (fun v hv hh _ => service v hv hh) hhor
  refine ⟨result, ?_, hproposer, noRise⟩
  obtain ⟨r, hr, _, _⟩ := result
  obtain ⟨j, x, a, e, hrow, hn⟩ := hr
  obtain ⟨hj, hx, hrs, ha⟩ := row_identity hrow
  exact ⟨r, j, x, a, e, ⟨j, x, a, e, hrow, hn⟩, hrow, hn, hj, hx, hrs, ha,
    hrs ▸ rfl⟩

#print axioms mixed_no_rise_tail

private theorem saved_tail_premises_sat :
    StrongServedFG tailCore missingReads env missingRun tailObs timing missingIface
      Row.height_pair 0 1 1 14 := by
  obtain ⟨_, _, _, hp, phase, service, _⟩ := mixed_premises_sat
  refine ⟨0, some .genesis, false, 2, .genesis, .genesis, by decide, hp, rfl, rfl,
    ?_, ?_, by decide, phase, le_rfl, by decide, ?_, service 14 le_rfl (by decide)⟩
  · intro _ x hx _
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl <;> decide +kernel
  · exact Or.inr ⟨0, by decide, fun _ _ => Nat.zero_le _, by decide, by decide, by decide⟩
  · intro i x _ _ _
    exact le_rfl

#print axioms saved_tail_premises_sat

-- The sole failed legacy premise is coverage at the honest nonholder proposer.
private theorem old_proposer_call_rejected :
    ¬ OpeningCovered tailCore missingReads env missingRun c5H timing Row.height_pair
      1 .genesis := by
  intro hc
  obtain ⟨K, nd, j, rSent, a, _, _, _, _, _, hrow, _⟩ := hc 7 (by decide)
  exact nonholder_no_encoded j _ hrow.2.1 a hrow.2.2

#print axioms old_proposer_call_rejected

private abbrev emptyRun : V2.D.Run Nat missingProtocol where
  honest := {7}
  horizon := 18
  events := (List.range 19).map fun (t : Nat) => .tick 7 (t : Time)
  seatOf := missingRun.seatOf
  input := missingRun.input

private theorem empty_seats_premises_sat :
    V2.D.ScheduleWellFormed env emptyRun ∧ FGTimingLaws timing ∧
    FGHonestSeats missingReads emptyRun = ∅ ∧ emptyRun.honest.Nonempty ∧
    HonestProposal env emptyRun missingIface 2 .genesis ∧
    PhaseInterval tailCore env emptyRun tailObs 0 (timing.gate 2) 1
      (some .genesis) false ∧
    (∀ v, timing.gate 2 ≤ v → v ≤ emptyRun.horizon →
      FrontierLocalServiceFG tailCore missingReads env emptyRun tailObs timing missingIface
        Row.height_pair 2 .genesis .genesis 1 v) ∧
    14 + (FGCompose.P timing - 4 * timing.delta) ≤ emptyRun.horizon := by
  have he : FGHonestSeats missingReads emptyRun = ∅ := by
    ext i
    simp [FGHonestSeats_def, safetyHolder, missingReads, reads, emptyRun]
  have hsource : ∀ x ∈ emptyRun.honest,
      actionSourceFG tailCore env emptyRun timing x 1 = some (some .genesis) := by
    intro x hx
    have hx' : x = 7 := Finset.mem_singleton.mp hx
    subst x
    decide +kernel
  refine ⟨?_, mixed_premises_sat.2.1, he, ⟨7, by decide⟩, ?_, ?_, ?_, by decide⟩
  · refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
    · intro x t ht
      obtain ⟨k, _, hk⟩ := List.mem_map.mp ht
      obtain ⟨hx, htt⟩ := V2.Event.tick.inj hk
      subst x
      subst t
      exact ⟨k, by simp⟩
    · intro x hx t ht _ hh _
      have hx' : x = 7 := Finset.mem_singleton.mp hx
      subst x
      obtain ⟨k, rfl⟩ := ht
      have hk : k < 19 := by change (k : Int) * 1 ≤ 18 at hh; omega
      exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, by simp⟩
  · exact ⟨⟨by decide, by decide⟩, ⟨.seat 8 0, row⟩,
      ⟨8, by decide +kernel, by decide +kernel⟩, rfl⟩
  · refine ⟨by decide, by decide, by decide, ?_⟩
    intro i x _ _ _
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro v _ hv
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x s H _ _ _ hH
      obtain ⟨nd, _, hH'⟩ := Option.map_eq_some_iff.mp hH
      change Block.genesis = H at hH'
      subst H
      rfl
    · intro s B _ _ hp
      obtain ⟨_, o, _, hb⟩ := hp
      have hB : B = .genesis := (Option.some.inj hb).symm
      subst B
      rfl
    · intro i x _ _ _ _
      rfl
    · intro s B _ _ hp ht x hx _
      obtain ⟨_, o, _, hb⟩ := hp
      have hB : B = .genesis := (Option.some.inj hb).symm
      subst B
      have hs : (s : Nat) ≤ 4 := by
        change 4 * (s : Int) + 1 ≤ 18 at ht
        simp only [Slot, Time] at *
        omega
      have hx' : x = 7 := Finset.mem_singleton.mp hx
      subst x
      interval_cases s <;> decide +kernel
    · intro r hqr ht
      have hrt := ht.trans hv
      change @LE.le Nat _ 2 (r * 2) at hqr
      change 8 * (r : Int) + 6 ≤ 18 at hrt
      have hr : @Eq Nat r 1 := by omega
      subst r
      refine ⟨?_, ⟨genesisRoot, ?_⟩, ?_, fun _ => by decide⟩
      · intro i hi
        rw [he] at hi
        simp at hi
      · intro x K hx hK
        rw [hsource x hx] at hK
        cases hK
        exact ⟨rfl, rfl⟩
      · intro x K hx hK
        rw [hsource x hx] at hK
        cases hK
        rfl

#print axioms empty_seats_premises_sat

-- Every other row-tail premise is proved above or by geometry_premises_sat.
private theorem empty_seats_row_tail_rejected :
    ¬ (FGHonestSeats missingReads emptyRun).Nonempty := by
  rw [empty_seats_premises_sat.2.2.1]
  exact Finset.not_nonempty_empty

#print axioms empty_seats_row_tail_rejected

-- A read-only frontier fixture: both stores satisfy the same certificate invariant.
-- At cut 14, nonholder 7 holds height 2 while holder 9 holds only genesis (height 1).
private abbrev maximumCore : FGCoreReads missingProtocol 1 Unit Unit (Row (Fin 1)) :=
  { tailCore with core := fun nd => ⟨(),
      if nd.sent.isEmpty then ⟨{.genesis, c5x1}, .genesis, .genesis, 1, 2⟩ else Store.init,
      [], []⟩ }

private theorem nonholder_frontier_premises_sat :
    missingRun.honest = {7, 9} ∧
    FGHonestSeats missingReads missingRun = {0} ∧
    safetyHolder missingReads missingRun 0 = 9 ∧
    (∀ i x, FGStoreInvariant c5H c5F
      (maximumCore.core (missingRun.stateBefore env i x)).fg) ∧
    (maximumCore.core (missingRun.stateBefore env 14 7)).fg.h_max = 2 ∧
    (maximumCore.core (missingRun.stateBefore env 14 9)).fg.h_max = 1 ∧
    frontierAtIdx maximumCore env missingRun 14 = 2 ∧
    (FGHonestSeats missingReads missingRun).sup
      (fun i => (maximumCore.core
        (missingRun.stateBefore env 14 (safetyHolder missingReads missingRun i))).fg.h_max) =
        1 := by
  refine ⟨rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    decide
  · intro i x
    change FGStoreInvariant c5H c5F
      (if (missingRun.stateBefore env i x).sent.isEmpty then
        ⟨{.genesis, c5x1}, .genesis, .genesis, 1, 2⟩ else Store.init)
    split <;> constructor <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

#print axioms nonholder_frontier_premises_sat

end AvailableChain.FGCompose.Tests.POP6aTail
end
