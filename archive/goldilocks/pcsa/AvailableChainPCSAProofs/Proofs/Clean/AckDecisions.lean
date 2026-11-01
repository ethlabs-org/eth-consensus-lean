module
public import AvailableChainPCSAProofs.Proofs.Clean.AckOrigins
public import AvailableChainPCSAProofs.Proofs.Clean.PCScope
public import AvailableChainPCSAProofs.Proofs.Clean.StepAck
public import AvailableChainGeneric.Proofs.V2.Duty.Signatures

public section

/-! C6 AckDecisions: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- The post-clock reader returns the store at any specified unique tick. -/
theorem pcsa_postClock_at_tick (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hn : rho.events.Nodup)
    (k : Nat) (x : V) (t : Time) (hk : rho.events[k]? = some (.tick x t)) :
    pcsa_postClock E rho x t =
      some ((pcsaWith m p c).clock (V2.D.Run.stateBefore E rho k x) t) := by
  have hm : (V2.D.Run.tickIdx? rho x t).isSome = true := by
    delta V2.D.Run.tickIdx?
    rw [List.findIdx?_isSome]
    exact List.any_eq_true.mpr ⟨.tick x t, List.mem_of_getElem? hk, decide_eq_true ⟨rfl, rfl⟩⟩
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hm
  have he : j = k := (List.Nodup.getElem?_inj
    (List.getElem?_eq_some_iff.mp (V2.D.Run.tickIdx?_spec hj)).1 hn).mp
      ((V2.D.Run.tickIdx?_spec hj).trans hk.symm)
  subst j
  rw [pcsa_postClock_def, pcsa_preTick_def, hj]
  rfl
/-- An honest ack emission is the exact decision read at its early duty. -/
theorem pcsa_honest_ack_of_emission (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hn : rho.events.Nodup)
    (x : V) (hx : x ∈ rho.honest) (s : Slot) (i : Fin p.n) (r : BlockId) (t : Time)
    (he : V2.D.Run.emits E rho x (ackObj p s i r) t) :
    t = SA.earlyTime p.toParams s ∧ ∃ B, HonestAckAt p c E rho x s B ∧ B.root = r := by
  obtain ⟨k, hk, ho⟩ := he
  rw [(V2.D.Run.step_tick_eq E rho hk).2] at ho
  have hsingle : Gen.V2.Duty.SingleDuty (pcsaWith m p c) (.base (.ack s)) := by
    refine ⟨.ackAction s, rfl, ?_⟩
    intro d hd
    exact (signLabel_ack_iff d s).mp hd
  obtain ⟨hw, ht, _, hact⟩ := (Gen.V2.Duty.mem_tick_singleDuty_iff E rho _ x t
    (.base (.ack s)) hsingle (.ackAction s) rfl i (.ack r)).mp ho
  have htime : t = SA.earlyTime p.toParams s := ht.symm
  subst t
  change rho.events[k]? = some (.tick x (SA.earlyTime p.toParams s)) at hk
  have hopt : (ackFor p (clock p (V2.D.Run.stateBefore E rho k x).st
      (SA.earlyTime p.toParams s)) s).map (fun B => (Msg.ack B.root : Msg p.n)) = some (.ack r)
        := by
    cases m <;> exact hact
  obtain ⟨B, hB, hroot⟩ := Option.map_eq_some_iff.mp hopt
  refine ⟨rfl, B, ⟨hx, hw, ?_⟩, Msg.ack.inj hroot⟩
  rw [pcsa_ackAt_def, pcsa_postClock_at_tick E rho hn k x _ hk]
  change some (ackFor p (clock p (V2.D.Run.stateBefore E rho k x).st
    (SA.earlyTime p.toParams s)) s) = some (some B)
  exact congrArg some hB
/-- A held PC before a cut has an honest ack decision on its exact full target. -/
theorem pcsa_pc_honest_ack_before [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFault : FaultsBelowQA p c rho) (k : Nat) (x : V) (hx : x ∈ rho.honest)
    (bound : Time) (hk : k ≤ V2.D.Run.idxBefore rho bound) (C : PC p.n)
    (hC : C ∈ (V2.D.Run.stateBefore E rho k x).st.pcs) :
    C.wellFormed = true ∧ ∃ y, HonestAckAt p c E rho y C.slot C.target ∧
      SA.earlyTime p.toParams C.slot < bound := by
  obtain ⟨hw, i, hi, t, ht, hem⟩ := pcsa_pc_honest_emission_before E rho h hFault k x bound hk C hC
  obtain ⟨he, B, hAck, hroot⟩ := pcsa_honest_ack_of_emission E rho h.valid.nodup _ hi
    C.slot i C.target.root t hem
  have hBs := pcsa_honestAck_body_scope E rho _ C.slot B hAck
  have hCs := pcsa_clean_pc_scope E rho k x hx C hC
  have hBC := pcsa_scoped_root_eq E rho h.idealization B C.target hBs hCs hroot
  refine ⟨hw, rho.seatOf (.base (.ack C.slot)) i, ?_, he ▸ ht⟩
  exact hBC ▸ hAck
/-- A PC held before the next vote cannot have a later slot. -/
theorem pcsa_pc_slot_before_vote [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFault : FaultsBelowQA p c rho) (k : Nat) (x : V) (s : Slot)
    (hk : k ≤ V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1)))
    (C : PC p.n) (hC : C ∈ (V2.D.Run.stateBefore E rho k x).st.pcs) : C.slot ≤ s := by
  have ht := (pcsa_pc_early_before E rho h hFault k x _ hk C hC).2
  change 4 * p.Δ * (C.slot : Int) + 2 * p.Δ <
    4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ at ht
  push_cast at ht
  by_contra hn
  have hs : (s : Int) + 1 ≤ (C.slot : Int) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)
  have hp := p.deltaPos
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4 * p.Δ by positivity)
  nlinarith
/-- No valid PC can be held strictly before the first gate. -/
theorem pcsa_pcs_before_first_gate_empty [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFault : FaultsBelowQA p c rho) (k : Nat) (x : V)
    (hk : k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams 0)) :
    (V2.D.Run.stateBefore E rho k x).st.pcs = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro C hC
  obtain ⟨hw, ht⟩ := pcsa_pc_early_before E rho h hFault k x _ hk C hC
  have hpos : 0 < C.slot := of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).1).1).1).1
  have hs : (1 : Int) ≤ (C.slot : Int) := by exact_mod_cast hpos
  have hp := p.deltaPos
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4 * p.Δ by positivity)
  change 4 * p.Δ * (C.slot : Int) + 2 * p.Δ < 4 * p.Δ * (0 : Int) + 6 * p.Δ at ht
  nlinarith

omit [DecidableEq V] in
/-- Every event in an inclusive earlier read lies before the later strict cutoff. -/
theorem pcsa_readAt_index_before_cut (rho : V2.D.Run V (pcsaWith m p c))
    (t bound : Time) (ht : t < bound) :
    (rho.events.filter (fun e => decide (e.time ≤ t))).length ≤ V2.D.Run.idxBefore rho bound := by
  rw [V2.D.Run.idxBefore_def, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true (lt_of_le_of_lt (of_decide_eq_true he) ht))
/-- The inclusive PC reader has an exact honest ack witness below any later cutoff. -/
theorem pcsa_pc_honest_ack_storeAt [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFault : FaultsBelowQA p c rho) (x : V) (hx : x ∈ rho.honest) (t bound : Time)
    (ht : t < bound) (C : PC p.n) (hC : C ∈ (storeAt p c E rho x t).pcs) :
    C.wellFormed = true ∧ ∃ y, HonestAckAt p c E rho y C.slot C.target ∧
      SA.earlyTime p.toParams C.slot < bound := by
  rw [storeAt_def, V2.D.Engine.readAt_eq_stateBefore h.valid.toScheduleWellFormed] at hC
  exact pcsa_pc_honest_ack_before E rho h hFault _ x hx bound
    (pcsa_readAt_index_before_cut rho t bound ht) C hC
end AvailableChain.PCSA.Run

end
