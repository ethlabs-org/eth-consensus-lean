module
public import AvailableChainPCSAProofs.Proofs.Clean.C9View
public import AvailableChainPCSAProofs.Proofs.Clean.TargetCollect
public import AvailableChainPCSAProofs.Proofs.Clean.Saturation
public import AvailableChainPCSAProofs.Proofs.Shared.RelayRun
public import AvailableChainPCSAProofs.Proofs.Shared.StageRun
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

public section

/-! C9 acks and stamping (pcsa34-r4.3 §5.3, steps 3–4). Every node of
`awakeHonestLabel s` acks `P`; its fresh ack seats give a PC quorum. Each
honest ack reaches every honest node strictly before `z_s` and is admitted to
its pool; with `P` held, the pre-freeze store collects the PC and the freeze
tick keeps it. -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

omit [DecidableEq V] in
/-- `idxBefore` is monotone in the read time. -/
theorem pcsa_c9_idxBefore_mono (rho : V2.D.Run V (pcsaWith m p c)) {t u : Time}
    (htu : t ≤ u) : V2.D.Run.idxBefore rho t ≤ V2.D.Run.idxBefore rho u := by
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def, ← List.countP_eq_length_filter,
    ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro e _ he
  exact decide_eq_true ((of_decide_eq_true he).trans_le htu)

/-- An honest early ack decision emits the exact ack for each owned seat. -/
theorem pcsa_c9_ack_emits (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (P : Block) (y : V) (i : Fin p.n)
    (hAck : HonestAckAt p c E rho y s P) (hSeat : rho.seatOf (.base (.ack s)) i = y) :
    V2.D.Run.emits E rho y (ackObj p s i P.root) (SA.earlyTime p.toParams s) := by
  have ha := hAck
  rw [pcsa_HonestAckAt_def] at ha
  have hread := ha.2.2
  rw [pcsa_ackAt_def] at hread
  obtain ⟨nd, hnd, hfor⟩ := Option.map_eq_some_iff.mp hread
  rw [pcsa_postClock_def] at hnd
  obtain ⟨pre, hpre, hclock⟩ := Option.map_eq_some_iff.mp hnd
  rw [pcsa_preTick_def] at hpre
  obtain ⟨k, hk, he⟩ := Option.map_eq_some_iff.mp hpre
  subst pre
  subst nd
  have ht := V2.D.Run.tickIdx?_spec hk
  refine ⟨k, ht, ?_⟩
  rw [(V2.D.Run.step_tick_eq E rho ht).2]
  apply (V2.D.Engine.mem_tick_seat_iff E rho _ y _ (.base (.ack s)) i (.ack P.root)).mpr
  refine ⟨ha.2.1, hSeat, .ackAction s, rfl, rfl, ?_⟩
  cases m <;>
    change (ackFor p (clock p (V2.D.Run.stateBefore E rho k y).st
      (SA.earlyTime p.toParams s)) s).map (fun B => Msg.ack B.root) = some (.ack P.root)
  all_goals
    change ackFor p (clock p (V2.D.Run.stateBefore E rho k y).st
      (SA.earlyTime p.toParams s)) s = some P at hfor
    rw [hfor]
    rfl

/-- The fresh ack seats of `awakeHonestLabel s` give an emitted PC quorum on `P`. -/
theorem pcsa_c9_ack_quorum (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) (s : Slot) (P : Block)
    (hQ : nQuorum p.n ≤ (awakeHonestLabel p c E rho s).card)
    (hAck : ∀ y ∈ rho.honest, E.awake y (SA.earlyTime p.toParams s) = true →
      HonestAckAt p c E rho y s P) :
    ∃ Q : Finset (Fin p.n), pcQuorum p.n ≤ Q.card ∧
      ∀ i ∈ Q, rho.seatOf (.base (.ack s)) i ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i)
          (ackObj p s i P.root) (SA.earlyTime p.toParams s) := by
  classical
  let H : Finset V := awakeHonestLabel p c E rho s
  let holder : Fin p.n → V := rho.seatOf (.base (.ack s))
  let Q : Finset (Fin p.n) := Finset.univ.filter (fun i => holder i ∈ H)
  have hbij : Function.Bijective holder := h.cstar (.base (.ack s)) trivial
  have hcard : Q.card = H.card := by
    apply Finset.card_bij (fun i _ => holder i)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i _ j _ he
      exact hbij.injective he
    · intro y hy
      obtain ⟨i, hi⟩ := hbij.surjective y
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi ▸ hy⟩, hi⟩
  have hn : nQuorum p.n ≤ Q.card := hcard ▸ hQ
  have hq : pcQuorum p.n ≤ Q.card := by
    have hi := pcsa_n_inter_card hn hn
    rwa [Finset.inter_self] at hi
  refine ⟨Q, hq, ?_⟩
  intro i hi
  have hm : rho.seatOf (.base (.ack s)) i ∈ awakeHonestLabel p c E rho s :=
    (Finset.mem_filter.mp hi).2
  rw [pcsa_awakeHonestLabel_def] at hm
  have he := (Finset.mem_inter.mp hm).2
  rw [Gen.V2.Duty.awakeHonest_def] at he
  obtain ⟨hy, haw⟩ := Finset.mem_filter.mp he
  exact ⟨hy, pcsa_c9_ack_emits E rho s P _ i (hAck _ hy haw) rfl⟩

/-- An emitted honest PC quorum on a held slot-`s` block is stamped at every honest node. -/
theorem pcsa_c9_stamped_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (s : Slot) (P : Block) (hs : 0 < s) (hslot : P.slot = s)
    (hT : T₀ ≤ SA.earlyTime p.toParams s)
    (hz : SA.freezeTime p.toParams s ≤ cut) (hhor : SA.freezeTime p.toParams s ≤ rho.horizon)
    (hBody : ∀ y ∈ rho.honest, P ∈ (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) y).st.base.blocks)
    (hQ : ∃ Q : Finset (Fin p.n), pcQuorum p.n ≤ Q.card ∧
      ∀ i ∈ Q, rho.seatOf (.base (.ack s)) i ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i)
          (ackObj p s i P.root) (SA.earlyTime p.toParams s)) :
    ∀ y ∈ rho.honest, PCStampedBefore p c E rho y (SA.freezeTime p.toParams s) s P := by
  intro y hy
  obtain ⟨Q, hq, hQi⟩ := hQ
  have hpool : ∀ i ∈ Q, (⟨.seat (.ack s) i, P.root⟩ : AckWire p.n) ∈
      (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s))
        y).st.ackPool := by
    intro i hi
    obtain ⟨hih, hie⟩ := hQi i hi
    obtain ⟨t', het, htz, j, hj⟩ := pcsa_ack_handled_before_freeze_win E rho hD h.delta s i P.root y
      hih hy hie hT hz
    have hadm := pcsa_honest_ack_admitted E rho h y hy s i P.root j t' hih het hj
    obtain ⟨_, hje, _⟩ := hj
    have hjlt := (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hje _).mpr htz
    exact pcsa_ackPool_mono_run E rho h.noRestart y (Nat.succ_le_of_lt hjlt) hadm
  obtain ⟨C, hC, hCs, hCt⟩ := pcsa_collect_held_target E rho h hF _ y hy s P hs hslot
    (hBody y hy) Q hq hpool
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ h.valid.toScheduleWellFormed] at hC
  rw [pcsa_PCStampedBefore_def]
  exact ⟨C, pcsa_collectPCs_after_freeze E rho h.valid.toScheduleWellFormed h.noRestart h.delta
    y hy s hhor hC, hCs, hCt⟩


/-- An emitted honest PC quorum on a held slot-`s` block is stamped at every honest node. -/
theorem pcsa_c9_stamped (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (s : Slot) (P : Block) (hs : 0 < s) (hslot : P.slot = s)
    (hz : SA.freezeTime p.toParams s ≤ cut) (hhor : SA.freezeTime p.toParams s ≤ rho.horizon)
    (hBody : ∀ y ∈ rho.honest, P ∈ (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) y).st.base.blocks)
    (hQ : ∃ Q : Finset (Fin p.n), pcQuorum p.n ≤ Q.card ∧
      ∀ i ∈ Q, rho.seatOf (.base (.ack s)) i ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i)
          (ackObj p s i P.root) (SA.earlyTime p.toParams s)) :
    ∀ y ∈ rho.honest, PCStampedBefore p c E rho y (SA.freezeTime p.toParams s) s P :=
  pcsa_c9_stamped_win E rho h hF
    (pcsa_strictFrom_of_healthy E rho hD (SA.earlyTime p.toParams s)) s P hs hslot (le_refl _)
    hz hhor hBody hQ


/-- The quarter fault cap is strictly below the PC quorum. -/
theorem pcsa_c9_faultsBelowQA_of_quarterCap [Fintype V] (rho : V2.D.Run V (pcsaWith m p c))
    (h : QuarterCap p c rho) : FaultsBelowQA p c rho := by
  rw [QuarterCap_def] at h
  rw [FaultsBelowQA_def]
  change (Gen.V2.Duty.faulty rho).card < (p.n + 1) / 2
  have hn : 0 < p.n := p.nPos
  omega

/-- A PC at an after-ticks read is still held at the inclusive read of that time. -/
theorem pcsa_c9_afterTicks_pcs_storeAt (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (y : V) (hy : y ∈ rho.honest) (t : Time) :
    (storeAfterTicks p c E rho y t).pcs ⊆ (storeAt p c E rho y t).pcs := by
  change (FGSA.Run.afterTicks E rho t y).st.pcs ⊆ (V2.D.Run.readAt E rho t y).st.pcs
  rw [FGSA.Run.afterTicks_eq_stateBefore E rho h.valid.toScheduleWellFormed,
    V2.D.Engine.readAt_eq_stateBefore h.valid.toScheduleWellFormed]
  exact (pcsa_stageOne_mono E rho h.noRestart hF y hy
    (FGSA.Run.preIdx_le_afterTicksIdx E rho h.valid.toScheduleWellFormed t).2).1

end AvailableChain.PCSA.Run

end
