module
public import AvailableChainPCSAProofs.Proofs.Clean.HonestSupport

public section

/-! C6 HonestBatch: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- An awake honest node has a HEAD decision at each scheduled vote in the run. -/
theorem pcsa_honest_head_exists (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (x : V) (hx : x ∈ rho.honest) (s : Slot)
    (hw : E.awake x (SA.voteTime p.toParams s) = true)
    (ht : SA.voteTime p.toParams s ≤ rho.horizon) :
    ∃ H, HonestHeadAt p c E rho x s H := by
  have hp : V2.PublicTime E (SA.voteTime p.toParams s) := by
    refine ⟨4 * s + 1, ?_⟩
    rw [h.delta]
    change 4 * p.Δ * (s : Int) + p.Δ = ((4 * s + 1 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hz : 0 ≤ SA.voteTime p.toParams s := by
    have hd := p.deltaPos
    change 0 ≤ 4 * p.Δ * (s : Int) + p.Δ
    positivity
  have hm := h.valid.tick_total x hx _ hp hz ht
  have hs : (V2.D.Run.tickIdx? rho x (SA.voteTime p.toParams s)).isSome = true := by
    delta V2.D.Run.tickIdx?
    rw [List.findIdx?_isSome]
    apply List.any_eq_true.mpr
    refine ⟨.tick x (SA.voteTime p.toParams s), hm, ?_⟩
    exact decide_eq_true ⟨rfl, rfl⟩
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
  refine ⟨headVote p (clock p (V2.D.Run.stateBefore E rho k x).st
    (SA.voteTime p.toParams s)) s, hx, hw, ?_⟩
  rw [pcsa_voteHeadAt_def, pcsa_postClock_def, pcsa_preTick_def, hk]
  rfl
/-- The label bound `a < h_s` gives an honest HEAD-seat batch at label `s` that is
larger than the faults. -/
theorem pcsa_head_batch_of_label [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) (s : Slot)
    (hlab : (Gen.V2.Duty.faulty rho).card < (awakeHonestLabel p c E rho s).card) :
    ∃ Hon : Finset (Fin p.n),
      (∀ i, i ∈ Hon ↔ rho.seatOf (.base (.head s)) i ∈ rho.honest ∧
        E.awake (rho.seatOf (.base (.head s)) i) (SA.voteTime p.toParams s) = true) ∧
      (Gen.V2.Duty.faulty rho).card < Hon.card := by
  classical
  let A := Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)
  let e : Fin p.n ≃ V := Equiv.ofBijective _ (h.cstar (.base (.head s)) trivial)
  let Hon := A.image e.symm
  refine ⟨Hon, ?_, ?_⟩
  · intro i
    have he : i ∈ Hon ↔ e i ∈ A := by
      change i ∈ A.image e.symm ↔ e i ∈ A
      simp only [Finset.mem_image, e.symm_apply_eq]
      exact ⟨fun ⟨_, hy, he⟩ => he ▸ hy, fun hi => ⟨e i, hi, rfl⟩⟩
    rw [he]
    change rho.seatOf (.base (.head s)) i ∈
      Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s) ↔ _
    rw [Gen.V2.Duty.awakeHonest_def]
    exact Finset.mem_filter
  · have hcard : Hon.card = A.card := Finset.card_image_of_injective A e.symm.injective
    rw [hcard]
    have hsub : awakeHonestLabel p c E rho s ⊆ A := Finset.inter_subset_left
    exact lt_of_lt_of_le hlab (Finset.card_le_card hsub)
/-- In the window from `j₀`, the label bound gives an honest HEAD-seat batch at each label
`s ≥ j₀` that is larger than the faults. -/
theorem pcsa_clean_head_batch_win [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {j₀ : Slot} {T₀ cut : Time}
    (h : CleanWindow E rho j₀ T₀ cut) (s : Slot) (hs : j₀ ≤ s)
    (hc : SA.gateTime p.toParams s ≤ cut) :
    ∃ Hon : Finset (Fin p.n),
      (∀ i, i ∈ Hon ↔ rho.seatOf (.base (.head s)) i ∈ rho.honest ∧
        E.awake (rho.seatOf (.base (.head s)) i) (SA.voteTime p.toParams s) = true) ∧
      (Gen.V2.Duty.faulty rho).card < Hon.card := by
  have hearly : SA.earlyTime p.toParams s ≤ cut := by
    apply le_trans _ hc
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    linarith
  exact pcsa_head_batch_of_label E rho h.base s (h.labels s hs hearly)
/-- The clean participation premise gives an honest HEAD-seat batch larger than faults. -/
theorem pcsa_clean_head_batch [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (s : Slot) (hc : SA.gateTime p.toParams s ≤ cut) :
    ∃ Hon : Finset (Fin p.n),
      (∀ i, i ∈ Hon ↔ rho.seatOf (.base (.head s)) i ∈ rho.honest ∧
        E.awake (rho.seatOf (.base (.head s)) i) (SA.voteTime p.toParams s) = true) ∧
      (Gen.V2.Duty.faulty rho).card < Hon.card :=
  pcsa_clean_head_batch_win E rho (pcsa_cleanWindow_of_clean E rho h) s (Nat.zero_le s) hc
/-- The late denominator contains only awake honest HEAD seats and faulty seats. -/
theorem pcsa_late_participant_bound [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (k : Nat) (y : V) (u : Time) (s : Slot) (Hon : Finset (Fin p.n))
    (hHon : ∀ i, i ∈ Hon ↔ rho.seatOf (.base (.head s)) i ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head s)) i) (SA.voteTime p.toParams s) = true) :
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s) ≤
      Hon.card + (Gen.V2.Duty.faulty rho).card := by
  classical
  let F := Finset.univ.filter (fun i : Fin p.n => rho.seatOf (.base (.head s)) i ∉ rho.honest)
  have hsub : (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s)).toFinset ⊆ Hon ∪ F := by
    intro i hi
    obtain ⟨o, ho, hoi⟩ := (Gen.AC.Root.vote_pool_mem_seats _ i).mp hi
    have hl : GridCO.headLabel? o = some s :=
      beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp ho).1).2
    obtain ⟨r, rfl⟩ := pcsa_count_head_shape o s i hl hoi
    by_cases hh : rho.seatOf (.base (.head s)) i ∈ rho.honest
    · apply Finset.mem_union.mpr
      left
      have hm := (List.mem_filter.mp (List.mem_filter.mp ho).1).1
      change _ ∈ (clock p (V2.D.Run.stateBefore E rho k y).st u).base.votes at hm
      rw [pcsa_clock_heads] at hm
      obtain ⟨t, he⟩ := pcsa_pool_head_emission E rho h.valid.toUnforgeableSignatures k y s i r
        hh hm
      have hw := (pcsa_head_emission_time_awake E rho _ s i r t he).2
      exact (hHon i).mpr ⟨hh, hw⟩
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩
  have hF : F.card ≤ (Gen.V2.Duty.faulty rho).card := by
    apply Finset.card_le_card_of_injOn (fun i : Fin p.n => rho.seatOf (.base (.head s)) i)
    · intro i hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    · intro i _ j _ he
      exact (h.cstar (.base (.head s)) trivial).1 he
  rw [Gen.AC.Root.vote_pool_voterCount_card]
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hF _))
/-- Label-local core: if every honest HEAD of label `s` covers a prefix, it has a strict
majority at the actual gate. The window needs only `T₀ ≤ v_s` and the label-`s` count. -/
theorem pcsa_gate_majority_of_label [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {T₀ cut : Time}
    (h : Base₂ p c E rho) (hS : StrictFrom E rho T₀ cut) (hF : StageOneFrame p c E rho)
    (k : Nat) (y : V) (hy : y ∈ rho.honest) (s : Slot) (B : Block)
    (hk : rho.events[k]? = some (.tick y (SA.gateTime p.toParams s)))
    (hT : T₀ ≤ SA.voteTime p.toParams s)
    (hlab : (Gen.V2.Duty.faulty rho).card < (awakeHonestLabel p c E rho s).card)
    (hc : SA.gateTime p.toParams s ≤ cut) (hcut : cut ≤ rho.horizon)
    (hheads : ∀ x H, HonestHeadAt p c E rho x s H → Block.Preceq B H) :
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s) <
      2 * SA.Root.prefixSupport p.toParams
        (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s B := by
  classical
  let st := clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s)
  let P := GridCO.cleanSupport p.toParams.engine (actView st) s
  obtain ⟨Hon, hHon, hbatch⟩ := pcsa_head_batch_of_label E rho h s hlab
  have hbound := pcsa_late_participant_bound E rho h k y (SA.gateTime p.toParams s) s Hon hHon
  have hearly : SA.earlyTime p.toParams s ≤ cut := by
    apply le_trans _ hc
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    linarith
  have hvote : SA.voteTime p.toParams s ≤ rho.horizon := by
    apply le_trans _ (hearly.trans hcut)
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    have hp := p.deltaPos
    linarith
  have hidx : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ k := by
    apply Nat.le_of_not_gt
    intro hlt
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hk _).mp hlt
    change 4 * p.Δ * (s : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int) + 2 * p.Δ at ht
    have hp := p.deltaPos
    linarith
  have hf : st.fg.F = .genesis := by
    change (clock p _ _).fg.F = _
    rw [pcsa_body_clock_fg]
    exact (hF y hy k).1
  have hd : st.base.headDomain = none := by
    change (clock p _ _).base.headDomain = none
    rw [pcsa_clock_headDomain, pcsa_headDomain_stateBefore_none]
  have hsupport : Hon.card ≤ SA.Root.prefixSupport p.toParams (actView st) s B := by
    rw [pcsa_gate_score_of_genesis p st s B hf hd, Gen.AC.Root.vote_pool_score_card]
    apply Finset.card_le_card
    intro i hi
    obtain ⟨hih, hiw⟩ := (hHon i).mp hi
    obtain ⟨H, hH⟩ := pcsa_honest_head_exists E rho h _ hih s hiw hvote
    obtain ⟨hm, hr⟩ := pcsa_honest_head_clean_support_win E rho h hF hS (hT := hT) _ y hy s i H
      rfl hH hearly k hidx (SA.gateTime p.toParams s)
    apply Finset.mem_filter.mpr
    refine ⟨(Gen.AC.Root.vote_pool_mem_seats _ i).mpr ⟨_, hm, rfl⟩, ?_⟩
    apply Bool.or_eq_true_iff.mpr
    right
    apply (Gen.AC.Root.vote_pool_support_witness st.base.blocks P i B).mpr
    refine ⟨_, hm, rfl, ?_⟩
    apply (Gen.AC.Root.vote_support_body st.base.blocks B _).mpr
    refine ⟨H, ?_, ?_, pcsa_honest_head_slot_le E rho h hF _ s H hH, hheads _ H hH⟩
    · have hlook := FGSA.Run.resolvedHead_target _ _ hr
      have hdom : GridCO.resolutionTree (actView st) = st.base.blocks := by
        change st.base.headDomain.getD st.base.blocks = st.base.blocks
        rw [hd]
        rfl
      rw [hdom] at hlook
      exact hlook
    · exact (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hr)).1
  change GridCO.voterCount (GridCO.lateVotes p.toParams.engine (actView st) s) <
    2 * SA.Root.prefixSupport p.toParams (actView st) s B
  change GridCO.voterCount (GridCO.lateVotes p.toParams.engine (actView st) s) ≤
    Hon.card + (Gen.V2.Duty.faulty rho).card at hbound
  omega
/-- In the delivery window: If every honest HEAD covers a prefix, it has a strict majority at the
actual gate. -/
theorem pcsa_clean_gate_majority_win [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {j₀ : Slot} {T₀ cut : Time}
    (h : CleanWindow E rho j₀ T₀ cut) (hF : StageOneFrame p c E rho)
    (k : Nat) (y : V) (hy : y ∈ rho.honest) (s : Slot) (B : Block)
    (hk : rho.events[k]? = some (.tick y (SA.gateTime p.toParams s)))
    (hs : j₀ ≤ s) (hc : SA.gateTime p.toParams s ≤ cut)
    (hheads : ∀ x H, HonestHeadAt p c E rho x s H → Block.Preceq B H) :
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s) <
      2 * SA.Root.prefixSupport p.toParams
        (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s B := by
  have hearly : SA.earlyTime p.toParams s ≤ cut := by
    apply le_trans _ hc
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    linarith
  exact pcsa_gate_majority_of_label E rho h.base h.strict hF k y hy s B hk
    (pcsa_floor_vote (pcsa_cleanWindow_floor E rho h s hs)) (h.labels s hs hearly) hc h.cut.2
    hheads
/-- If every honest HEAD covers a prefix, it has a strict majority at the actual gate. -/
theorem pcsa_clean_gate_majority [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (k : Nat) (y : V) (hy : y ∈ rho.honest) (s : Slot) (B : Block)
    (hk : rho.events[k]? = some (.tick y (SA.gateTime p.toParams s)))
    (hc : SA.gateTime p.toParams s ≤ cut)
    (hheads : ∀ x H, HonestHeadAt p c E rho x s H → Block.Preceq B H) :
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s) <
      2 * SA.Root.prefixSupport p.toParams
        (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s B :=
  pcsa_clean_gate_majority_win E rho (pcsa_cleanWindow_of_clean E rho h) hF k y hy s B hk
    (Nat.zero_le _) hc hheads
end AvailableChain.PCSA.Run

end
