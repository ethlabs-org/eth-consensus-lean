module
public import AvailableChainPCSAProofs.Proofs.Clean.GateCounts
public import AvailableChainPCSAProofs.Proofs.Clean.GateReads
public import AvailableChainPCSAProofs.Proofs.Clean.VoteTransport
public import AvailableChainPCSAProofs.Proofs.Clean.StepAck
public import AvailableChainPCSAProofs.Proofs.Shared.CleanPC

public section

/-! C6 NCounts: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}
/-- In the delivery window: An actual N observation is compatible with every same-label honest
result. -/
theorem pcsa_N_same_label_result_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (v : Time) (s : Slot) (B X : Block) (hT : T₀ ≤ SA.freezeTime p.toParams s) (hc : SA.gateTime
        p.toParams s ≤ cut)
    (hN : holdsN p (actView (clock p (V2.D.Run.stateBefore E rho a x).st v)) s B = true)
    (hX : gateResultAt p c E rho y s = some (some X)) : Block.Compatible B X := by
  classical
  obtain ⟨b, hb, hresult⟩ := pcsa_gateResultAt_source E rho y s X hX
  let src := clock p (V2.D.Run.stateBefore E rho a x).st v
  let dst := clock p (V2.D.Run.stateBefore E rho b y).st (SA.gateTime p.toParams s)
  let Nvotes := (timelyHeads p (actView src) s).filter
    (fun o => GridCO.resolvedHead? (actView src) o == some B)
  let N := (GridCO.seats p.n Nvotes).toFinset
  let P := GridCO.cleanSupport p.toParams.engine (actView dst) s
  let L := GridCO.lateVotes p.toParams.engine (actView dst) s
  let S := (GridCO.seats p.n P).toFinset.filter
    (fun i => (GridCO.equivocates P i || Gen.AC.Root.poolSupports dst.base.blocks P i X) = true)
  have hNcard : nQuorum p.n ≤ N.card := by
    have hn : nQuorum p.n ≤ nCount p (actView src) s B := of_decide_eq_true hN
    rw [pcsa_nCount_card] at hn
    exact hn
  have hfd : dst.fg.F = .genesis := by
    change (clock p _ _).fg.F = _
    rw [pcsa_body_clock_fg]
    exact (hF y hy b).1
  have hdd : dst.base.headDomain = none := by
    change (clock p _ _).base.headDomain = none
    rw [pcsa_clock_headDomain, pcsa_headDomain_stateBefore_none]
  have hmaj := pcsa_gate_result_majority p (actView dst) _ X s hresult
  rw [pcsa_gate_score_of_genesis p dst s X hfd hdd,
    Gen.AC.Root.vote_pool_score_card, Gen.AC.Root.vote_pool_voterCount_card] at hmaj
  have hNL : N ⊆ (GridCO.seats p.n L).toFinset := by
    intro i hi
    obtain ⟨o, ho, hoi⟩ := (Gen.AC.Root.vote_pool_mem_seats Nvotes i).mp hi
    have hearly : o ∈ GridCO.earlyVotes p.toParams.engine (actView src) s :=
      (List.mem_filter.mp (List.mem_filter.mp ho).1).1
    rcases pcsa_early_input_gate_relay_win E rho h hD (hT := hT) a b x y hx hy s o i v hc hb hearly
        hoi with hm
      | he
    · exact (Gen.AC.Root.vote_pool_mem_seats L i).mpr ⟨o, hm, hoi⟩
    · exact Gen.AC.Root.vote_pool_equivocates_participant L i he
  have hSL : S ⊆ (GridCO.seats p.n L).toFinset :=
    (Finset.filter_subset _ _).trans (FGSA.fgsa_cleanSupport_seats_subset_late p (actView dst) s)
  apply pcsa_cl4_same_label B X N S (GridCO.seats p.n L).toFinset
    hFault hNcard hNL hSL hmaj
  intro i hi
  obtain ⟨hiN, hiS⟩ := Finset.mem_inter.mp hi
  obtain ⟨o, ho, hoi⟩ := (Gen.AC.Root.vote_pool_mem_seats Nvotes i).mp hiN
  have hearly : o ∈ GridCO.earlyVotes p.toParams.engine (actView src) s :=
    (List.mem_filter.mp (List.mem_filter.mp ho).1).1
  have hrB : GridCO.resolvedHead? (actView src) o = some B :=
    beq_iff_eq.mp (List.mem_filter.mp ho).2
  have hs := (Finset.mem_filter.mp hiS).2
  have hcapP : GridCO.equivocates P i = false :=
    FGSA.fgsa_cleanSupport_no_equivocation p (actView dst) s i
  change (GridCO.equivocates P i || Gen.AC.Root.poolSupports dst.base.blocks P i X) = true at hs
  rw [hcapP, Bool.false_or] at hs
  obtain ⟨o', ho', ho'i, hscore⟩ :=
    (Gen.AC.Root.vote_pool_support_witness dst.base.blocks P i X).mp hs
  have heq : o = o' := by
    rcases pcsa_early_input_gate_relay_win E rho h hD (hT := hT) a b x y hx hy s o i v hc hb hearly
        hoi with hm
      | he
    · exact pcsa_clean_input_unique_late p (actView dst) s o' i ho' ho'i o hm hoi
    · have hf := pcsa_clean_input_not_capped p (actView dst) s o' i ho' ho'i
      rw [he] at hf
      cases hf
  subst o'
  obtain ⟨H, hrH, hXH⟩ := pcsa_read_vote_support_body E rho hF b y hy _ o X hscore
  have hsame := pcsa_run_common_head_resolution E rho h a b x y hx hy v _ o B H hrB hrH
  refine ⟨B, Gen.Pure.block_preceq_refl B, ?_⟩
  rw [hsame]
  exact hXH
/-- An actual N observation is compatible with every same-label honest result. -/
theorem pcsa_N_same_label_result (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (v : Time) (s : Slot) (B X : Block) (hc : SA.gateTime p.toParams s ≤ cut)
    (hN : holdsN p (actView (clock p (V2.D.Run.stateBefore E rho a x).st v)) s B = true)
    (hX : gateResultAt p c E rho y s = some (some X)) : Block.Compatible B X :=
  pcsa_N_same_label_result_win E rho h hF hFault (pcsa_strictFrom_of_healthy E rho hD 0) a x y hx
    hy v s B X (pcsa_floor_freeze (pcsa_zero_le_proposal s)) hc hN hX
/-- An honest ack target and a same-label result are compatible with a freeze floor. -/
theorem pcsa_honestAck_same_label_result_from_freeze (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {T₀ cut : Time}
    (h : Base₂ p c E rho) (hD : StrictFrom E rho T₀ cut) (hF : StageOneFrame p c E rho)
    (hFault : FaultsBelowQA p c rho) (x y : V) (hy : y ∈ rho.honest)
    (s : Slot) (B X : Block) (hT : T₀ ≤ SA.freezeTime p.toParams s)
    (hc : SA.gateTime p.toParams s ≤ cut)
    (hAck : HonestAckAt p c E rho x s B)
    (hX : gateResultAt p c E rho y s = some (some X)) : Block.Compatible B X := by
  obtain ⟨nd, hnd, _, _, hN, _⟩ := pcsa_honestAck_N_source E rho x s B hAck
  obtain ⟨a, _, hstore⟩ := pcsa_postClock_source E rho x _ nd hnd
  rw [hstore] at hN
  exact pcsa_N_same_label_result_win E rho h hF hFault hD
    (hT := hT) a x y hAck.1 hy _ s B X hc hN hX
/-- In the delivery window: An honest ack target is compatible with every same-label clean result.
-/
theorem pcsa_honestAck_same_label_result_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {j₀ : Slot} {T₀ cut : Time}
    (h : CleanWindow E rho j₀ T₀ cut) (hF : StageOneFrame p c E rho)
    (hFault : FaultsBelowQA p c rho) (x y : V) (hy : y ∈ rho.honest)
    (s : Slot) (B X : Block) (hs : j₀ ≤ s) (hc : SA.gateTime p.toParams s ≤ cut)
    (hAck : HonestAckAt p c E rho x s B)
    (hX : gateResultAt p c E rho y s = some (some X)) : Block.Compatible B X :=
  pcsa_honestAck_same_label_result_from_freeze E rho h.base h.strict hF hFault x y hy s B X
    (pcsa_floor_freeze (pcsa_cleanWindow_floor E rho h s hs)) hc hAck hX
/-- An honest ack target is compatible with every same-label clean result. -/
theorem pcsa_honestAck_same_label_result (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (hFault : FaultsBelowQA p c rho) (x y : V) (hy : y ∈ rho.honest)
    (s : Slot) (B X : Block) (hc : SA.gateTime p.toParams s ≤ cut)
    (hAck : HonestAckAt p c E rho x s B)
    (hX : gateResultAt p c E rho y s = some (some X)) : Block.Compatible B X := by
  obtain ⟨nd, hnd, _, _, hN, _⟩ := pcsa_honestAck_N_source E rho x s B hAck
  obtain ⟨a, _, hstore⟩ := pcsa_postClock_source E rho x _ nd hnd
  rw [hstore] at hN
  exact pcsa_N_same_label_result E rho h.base hF hFault h.healthy a x y hAck.1 hy _ s B X hc hN hX
end AvailableChain.PCSA.Run

end
