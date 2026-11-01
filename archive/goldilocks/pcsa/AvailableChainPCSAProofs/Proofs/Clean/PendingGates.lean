module
public import AvailableChainPCSAProofs.Proofs.Clean.GateBatch
public import AvailableChainPCSAProofs.Proofs.Clean.ZeroViews

public section

/-! C6 PendingGates: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- The clean participation premise gives an honest HEAD-seat batch larger than faults. -/
theorem pcsa_clean_head_batch_early [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (s : Slot) (hc : SA.earlyTime p.toParams s ≤ cut) :
    ∃ Hon : Finset (Fin p.n),
      (∀ i, i ∈ Hon ↔ rho.seatOf (.base (.head s)) i ∈ rho.honest ∧
        E.awake (rho.seatOf (.base (.head s)) i) (SA.voteTime p.toParams s) = true) ∧
      (Gen.V2.Duty.faulty rho).card < Hon.card := by
  classical
  let A := Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)
  let e : Fin p.n ≃ V := Equiv.ofBijective _ (h.base.cstar (.base (.head s)) trivial)
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
  · have hearly := hc
    have hcard : Hon.card = A.card := Finset.card_image_of_injective A e.symm.injective
    rw [hcard]
    have hsub : awakeHonestLabel p c E rho s ⊆ A := Finset.inter_subset_left
    exact lt_of_lt_of_le (h.labels s hearly) (Finset.card_le_card hsub)
/-- If every honest HEAD covers a prefix, it has a strict majority at the actual gate. -/
theorem pcsa_clean_gate_majority_early [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (k : Nat) (y : V) (hy : y ∈ rho.honest) (s : Slot) (B : Block)
    (hk : rho.events[k]? = some (.tick y (SA.gateTime p.toParams s)))
    (hc : SA.earlyTime p.toParams s ≤ cut)
    (hheads : ∀ x H, HonestHeadAt p c E rho x s H → Block.Preceq B H) :
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s) <
      2 * SA.Root.prefixSupport p.toParams
        (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s B := by
  classical
  let st := clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s)
  let P := GridCO.cleanSupport p.toParams.engine (actView st) s
  obtain ⟨Hon, hHon, hbatch⟩ := pcsa_clean_head_batch_early E rho h s hc
  have hbound := pcsa_late_participant_bound E rho h.base k y (SA.gateTime p.toParams s) s Hon hHon
  have hearly := hc
  have hvote : SA.voteTime p.toParams s ≤ rho.horizon := by
    apply le_trans _ (hearly.trans h.cut.2)
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    have hp := p.deltaPos
    linarith
  have hidx : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ k := by
    apply Nat.le_of_not_gt
    intro hlt
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff h.base.valid.toScheduleWellFormed hk _).mp hlt
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
    obtain ⟨H, hH⟩ := pcsa_honest_head_exists E rho h.base _ hih s hiw hvote
    obtain ⟨hm, hr⟩ := pcsa_honest_head_clean_support E rho h.base hF h.healthy _ y hy s i H
      rfl hH hearly k hidx (SA.gateTime p.toParams s)
    apply Finset.mem_filter.mpr
    refine ⟨(Gen.AC.Root.vote_pool_mem_seats _ i).mpr ⟨_, hm, rfl⟩, ?_⟩
    apply Bool.or_eq_true_iff.mpr
    right
    apply (Gen.AC.Root.vote_pool_support_witness st.base.blocks P i B).mpr
    refine ⟨_, hm, rfl, ?_⟩
    apply (Gen.AC.Root.vote_support_body st.base.blocks B _).mpr
    refine ⟨H, ?_, ?_, pcsa_honest_head_slot_le E rho h.base hF _ s H hH, hheads _ H hH⟩
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

/-- The honest batch gives a genuine result above every common honest HEAD prefix. -/
theorem pcsa_clean_gate_covers_heads_early [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (k : Nat) (y : V) (hy : y ∈ rho.honest) (s : Slot) (B : Block)
    (hk : rho.events[k]? = some (.tick y (SA.gateTime p.toParams s)))
    (hc : SA.earlyTime p.toParams s ≤ cut)
    (hheads : ∀ x H, HonestHeadAt p c E rho x s H → Block.Preceq B H) :
    ∃ X, SA.Root.confirmationFrom p.toParams
      (eraseFG (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s)).fg.F)
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s = some
        X ∧
      Block.Preceq B X := by
  let st := clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s)
  have hb := pcsa_clean_gate_majority_early E rho h hF k y hy s B hk hc hheads
  have ha := pcsa_clean_gate_majority_early E rho h hF k y hy s .genesis hk hc
    (fun _ H _ => Gen.Pure.block_genesis_preceq H)
  obtain ⟨Hon, hHon, hbatch⟩ := pcsa_clean_head_batch_early E rho h s hc
  have hpos : 0 < Hon.card := lt_of_le_of_lt (Nat.zero_le _) hbatch
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  obtain ⟨hih, hiw⟩ := (hHon i).mp hi
  have hearly := hc
  have hvote : SA.voteTime p.toParams s ≤ rho.horizon := by
    apply le_trans _ (hearly.trans h.cut.2)
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    have hp := p.deltaPos
    linarith
  have hidx : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ k := by
    apply Nat.le_of_not_gt
    intro hlt
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff h.base.valid.toScheduleWellFormed hk _).mp hlt
    change 4 * p.Δ * (s : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int) + 2 * p.Δ at ht
    have hp := p.deltaPos
    linarith
  obtain ⟨H, hH⟩ := pcsa_honest_head_exists E rho h.base _ hih s hiw hvote
  have hBH := hheads _ H hH
  obtain ⟨hm, _⟩ := pcsa_honest_head_body_before_early E rho h.base hF h.healthy _ y hy s H
    hH hearly k hidx
  have hclock : H ∈ st.base.blocks := by
    change H ∈ (clock p _ _).base.blocks
    rw [pcsa_clock_blocks]
    exact hm
  have hf : st.fg.F = .genesis := by
    change (clock p _ _).fg.F = _
    rw [pcsa_body_clock_fg]
    exact (hF y hy k).1
  have hpath : ∀ C, Block.Preceq .genesis C → Block.Preceq C B → C ≠ .genesis →
      C ∈ (actView st).blocks := by
    intro C _ hCB _
    rw [pcsa_actView_blocks_of_genesis st hf]
    exact pcsa_body_prefix_mem p st
      (Reachable.tick _ (pcsa_reachable_stateBefore E rho k y)) H hclock C
      (Gen.Pure.block_preceq_trans hCB hBH)
  obtain ⟨X, hr, hBX⟩ := FGSA.fgsa_confirmationFrom_covers_majority p (actView st)
    .genesis B s B.root
    (Gen.Pure.block_compatible_of_common (Gen.Pure.block_genesis_preceq B)
      (Gen.Pure.block_preceq_refl B)) ha hb hpath
  refine ⟨X, ?_, hBX⟩
  change SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s = some X
  rw [hf]
  exact hr
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}
/-- A pending result covers every common honest HEAD prefix once its early read is in the cut. -/
theorem pcsa_pending_result_covers_heads (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (y : V) (hy : y ∈ rho.honest) (s : Slot) (B X : Block)
    (hc : SA.earlyTime p.toParams s ≤ cut)
    (hheads : ∀ x H, HonestHeadAt p c E rho x s H → Block.Preceq B H)
    (hr : gateResultAt p c E rho y s = some (some X)) : Block.Preceq B X := by
  obtain ⟨k, hk, hX⟩ := pcsa_gateResultAt_source E rho y s X hr
  obtain ⟨Y, hY, hBY⟩ := pcsa_clean_gate_covers_heads_early E rho h hF k y hy s B hk hc hheads
  have he : Y = X := Option.some.inj (hY.symm.trans hX)
  exact he ▸ hBY
/-- A gate read cannot return an empty result when its honest early batch is in the cut. -/
theorem pcsa_pending_result_nonempty (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (y : V) (hy : y ∈ rho.honest) (s : Slot) (hc : SA.earlyTime p.toParams s ≤ cut) :
    gateResultAt p c E rho y s ≠ some none := by
  intro hnone
  rw [pcsa_gateResultAt_def] at hnone
  obtain ⟨st, hst, hr⟩ := Option.map_eq_some_iff.mp hnone
  obtain ⟨k, hk, he⟩ := pcsa_gateInAt_source E rho y s st hst
  rw [he] at hr
  obtain ⟨X, hX, _⟩ := pcsa_clean_gate_covers_heads_early E rho h hF k y hy s .genesis hk hc
    (fun _ H _ => Gen.Pure.block_genesis_preceq H)
  rw [pcsa_clock_confirmation_eq_pre] at hX
  have hn := hr.symm.trans hX
  cases hn
end AvailableChain.PCSA.Run

end
