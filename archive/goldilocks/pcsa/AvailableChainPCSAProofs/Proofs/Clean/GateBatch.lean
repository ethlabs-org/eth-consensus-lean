module
public import AvailableChainPCSAProofs.Proofs.Clean.HonestBatch
public import AvailableChainPCSAProofs.Proofs.Clean.GateReads
public import AvailableChainPCSAProofs.Proofs.Clean.BodyPaths

public section

/-! C6 GateBatch: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- The exact claim reader agrees with the raw result at its scheduled tick. -/
theorem pcsa_gateResultAt_at_tick (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hn : rho.events.Nodup)
    (k : Nat) (y : V) (s : Slot)
    (hk : rho.events[k]? = some (.tick y (SA.gateTime p.toParams s))) :
    gateResultAt p c E rho y s = some (SA.Root.confirmationFrom p.toParams
      (eraseFG (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s)).fg.F)
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s) := by
  have hm : (V2.D.Run.tickIdx? rho y (SA.gateTime p.toParams s)).isSome = true := by
    delta V2.D.Run.tickIdx?
    rw [List.findIdx?_isSome]
    apply List.any_eq_true.mpr
    exact ⟨.tick y (SA.gateTime p.toParams s), List.mem_of_getElem? hk, decide_eq_true ⟨rfl, rfl⟩⟩
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hm
  have he : j = k := (List.Nodup.getElem?_inj
    (List.getElem?_eq_some_iff.mp (V2.D.Run.tickIdx?_spec hj)).1 hn).mp
      ((V2.D.Run.tickIdx?_spec hj).trans hk.symm)
  subst j
  rw [pcsa_gateResultAt_def, pcsa_gateInAt_def, pcsa_preTick_def, hj]
  change some (SA.Root.confirmationFrom p.toParams (eraseFG (clockPre p _ _).fg.F)
    (actView (clockPre p _ _)) s) = _
  rw [pcsa_clock_confirmation_eq_pre]
/-- At label `s`, the honest batch gives a result above every common honest HEAD prefix. -/
theorem pcsa_gate_covers_heads_of_label [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {T₀ cut : Time}
    (h : Base₂ p c E rho) (hS : StrictFrom E rho T₀ cut) (hF : StageOneFrame p c E rho)
    (k : Nat) (y : V) (hy : y ∈ rho.honest) (s : Slot) (B : Block)
    (hk : rho.events[k]? = some (.tick y (SA.gateTime p.toParams s)))
    (hT : T₀ ≤ SA.voteTime p.toParams s)
    (hlab : (Gen.V2.Duty.faulty rho).card < (awakeHonestLabel p c E rho s).card)
    (hc : SA.gateTime p.toParams s ≤ cut) (hcut : cut ≤ rho.horizon)
    (hheads : ∀ x H, HonestHeadAt p c E rho x s H → Block.Preceq B H) :
    ∃ X, SA.Root.confirmationFrom p.toParams
      (eraseFG (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s)).fg.F)
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s = some
        X ∧
      Block.Preceq B X := by
  let st := clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s)
  have hb := pcsa_gate_majority_of_label E rho h hS hF k y hy s B hk hT hlab hc hcut hheads
  have ha := pcsa_gate_majority_of_label E rho h hS hF k y hy s .genesis hk hT hlab hc hcut
    (fun _ H _ => Gen.Pure.block_genesis_preceq H)
  obtain ⟨Hon, hHon, hbatch⟩ := pcsa_head_batch_of_label E rho h s hlab
  have hpos : 0 < Hon.card := lt_of_le_of_lt (Nat.zero_le _) hbatch
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  obtain ⟨hih, hiw⟩ := (hHon i).mp hi
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
  obtain ⟨H, hH⟩ := pcsa_honest_head_exists E rho h _ hih s hiw hvote
  have hBH := hheads _ H hH
  obtain ⟨hm, _⟩ := pcsa_honest_head_body_before_early_win E rho h hF hS
    (hT := hT) _ y hy s H
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
/-- In the delivery window: The honest batch gives a genuine result above every common honest HEAD
prefix. -/
theorem pcsa_clean_gate_covers_heads_win [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {j₀ : Slot} {T₀ cut : Time}
    (h : CleanWindow E rho j₀ T₀ cut) (hF : StageOneFrame p c E rho)
    (k : Nat) (y : V) (hy : y ∈ rho.honest) (s : Slot) (B : Block)
    (hk : rho.events[k]? = some (.tick y (SA.gateTime p.toParams s)))
    (hs : j₀ ≤ s) (hc : SA.gateTime p.toParams s ≤ cut)
    (hheads : ∀ x H, HonestHeadAt p c E rho x s H → Block.Preceq B H) :
    ∃ X, SA.Root.confirmationFrom p.toParams
      (eraseFG (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s)).fg.F)
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s = some
        X ∧
      Block.Preceq B X := by
  have hearly : SA.earlyTime p.toParams s ≤ cut := by
    apply le_trans _ hc
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  exact pcsa_gate_covers_heads_of_label E rho h.base h.strict hF k y hy s B hk
    (pcsa_floor_vote (pcsa_cleanWindow_floor E rho h s hs)) (h.labels s hs hearly) hc h.cut.2
    hheads
/-- The honest batch gives a genuine result above every common honest HEAD prefix. -/
theorem pcsa_clean_gate_covers_heads [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (k : Nat) (y : V) (hy : y ∈ rho.honest) (s : Slot) (B : Block)
    (hk : rho.events[k]? = some (.tick y (SA.gateTime p.toParams s)))
    (hc : SA.gateTime p.toParams s ≤ cut)
    (hheads : ∀ x H, HonestHeadAt p c E rho x s H → Block.Preceq B H) :
    ∃ X, SA.Root.confirmationFrom p.toParams
      (eraseFG (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s)).fg.F)
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s = some
        X ∧
      Block.Preceq B X := by
  let st := clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s)
  have hb := pcsa_clean_gate_majority E rho h hF k y hy s B hk hc hheads
  have ha := pcsa_clean_gate_majority E rho h hF k y hy s .genesis hk hc
    (fun _ H _ => Gen.Pure.block_genesis_preceq H)
  obtain ⟨Hon, hHon, hbatch⟩ := pcsa_clean_head_batch E rho h s hc
  have hpos : 0 < Hon.card := lt_of_le_of_lt (Nat.zero_le _) hbatch
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  obtain ⟨hih, hiw⟩ := (hHon i).mp hi
  have hearly : SA.earlyTime p.toParams s ≤ cut := by
    apply le_trans _ hc
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    linarith
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
/-- The vote floor and label-`s` bound give a nonempty claim-level result. -/
theorem pcsa_result_exists_of_label [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {T₀ cut : Time}
    (h : Base₂ p c E rho) (hS : StrictFrom E rho T₀ cut) (hF : StageOneFrame p c E rho)
    (y : V) (hy : y ∈ rho.honest) (s : Slot) (hT : T₀ ≤ SA.voteTime p.toParams s)
    (hlab : (Gen.V2.Duty.faulty rho).card < (awakeHonestLabel p c E rho s).card)
    (hc : SA.gateTime p.toParams s ≤ cut) (hcut : cut ≤ rho.horizon) :
    ∃ X, gateResultAt p c E rho y s = some (some X) := by
  have hp : V2.PublicTime E (SA.gateTime p.toParams s) := by
    refine ⟨4 * s + 6, ?_⟩
    rw [h.delta]
    change 4 * p.Δ * (s : Int) + 6 * p.Δ = ((4 * s + 6 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hz : 0 ≤ SA.gateTime p.toParams s := by
    have hd := p.deltaPos
    change 0 ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    positivity
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp
    (h.valid.tick_total y hy _ hp hz (hc.trans hcut))
  obtain ⟨X, hr, _⟩ := pcsa_gate_covers_heads_of_label E rho h hS hF k y hy s .genesis hk hT hlab
      hc hcut
    (fun _ H _ => Gen.Pure.block_genesis_preceq H)
  refine ⟨X, ?_⟩
  rw [pcsa_gateResultAt_at_tick E rho h.valid.nodup k y s hk, hr]
/-- In the delivery window: Every clean gate in the healthy cut has a nonempty claim-level result.
-/
theorem pcsa_clean_result_exists_win [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {j₀ : Slot} {T₀ cut : Time}
    (h : CleanWindow E rho j₀ T₀ cut) (hF : StageOneFrame p c E rho)
    (y : V) (hy : y ∈ rho.honest) (s : Slot) (hs : j₀ ≤ s) (hc : SA.gateTime p.toParams s ≤ cut) :
    ∃ X, gateResultAt p c E rho y s = some (some X) := by
  have hearly : SA.earlyTime p.toParams s ≤ cut := by
    apply le_trans _ hc
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  exact pcsa_result_exists_of_label E rho h.base h.strict hF y hy s
    (pcsa_floor_vote (pcsa_cleanWindow_floor E rho h s hs)) (h.labels s hs hearly) hc h.cut.2
/-- Every clean gate in the healthy cut has a nonempty claim-level result. -/
theorem pcsa_clean_result_exists [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (y : V) (hy : y ∈ rho.honest) (s : Slot) (hc : SA.gateTime p.toParams s ≤ cut) :
    ∃ X, gateResultAt p c E rho y s = some (some X) := by
  have hp : V2.PublicTime E (SA.gateTime p.toParams s) := by
    refine ⟨4 * s + 6, ?_⟩
    rw [h.base.delta]
    change 4 * p.Δ * (s : Int) + 6 * p.Δ = ((4 * s + 6 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hz : 0 ≤ SA.gateTime p.toParams s := by
    have hd := p.deltaPos
    change 0 ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    positivity
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp
    (h.base.valid.tick_total y hy _ hp hz (hc.trans h.cut.2))
  obtain ⟨X, hr, _⟩ := pcsa_clean_gate_covers_heads E rho h hF k y hy s .genesis hk hc
    (fun _ H _ => Gen.Pure.block_genesis_preceq H)
  refine ⟨X, ?_⟩
  rw [pcsa_gateResultAt_at_tick E rho h.base.valid.nodup k y s hk, hr]
/-- With the vote floor and label-`s` bound, a result covers every common honest HEAD prefix. -/
theorem pcsa_result_covers_heads_of_label [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {T₀ cut : Time}
    (h : Base₂ p c E rho) (hS : StrictFrom E rho T₀ cut) (hF : StageOneFrame p c E rho)
    (y : V) (hy : y ∈ rho.honest) (s : Slot) (B X : Block)
    (hT : T₀ ≤ SA.voteTime p.toParams s)
    (hlab : (Gen.V2.Duty.faulty rho).card < (awakeHonestLabel p c E rho s).card)
    (hc : SA.gateTime p.toParams s ≤ cut) (hcut : cut ≤ rho.horizon)
    (hheads : ∀ x H, HonestHeadAt p c E rho x s H → Block.Preceq B H)
    (hr : gateResultAt p c E rho y s = some (some X)) : Block.Preceq B X := by
  obtain ⟨k, hk, hX⟩ := pcsa_gateResultAt_source E rho y s X hr
  obtain ⟨Y, hY, hBY⟩ := pcsa_gate_covers_heads_of_label E rho h hS hF k y hy s B hk hT hlab hc hcut
      hheads
  have he : Y = X := Option.some.inj (hY.symm.trans hX)
  exact he ▸ hBY
/-- In the delivery window: A claim-level result extends any prefix covered by every honest HEAD of
its label. -/
theorem pcsa_clean_result_covers_heads_win [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {j₀ : Slot} {T₀ cut : Time}
    (h : CleanWindow E rho j₀ T₀ cut) (hF : StageOneFrame p c E rho)
    (y : V) (hy : y ∈ rho.honest) (s : Slot) (B X : Block)
    (hs : j₀ ≤ s) (hc : SA.gateTime p.toParams s ≤ cut)
    (hheads : ∀ x H, HonestHeadAt p c E rho x s H → Block.Preceq B H)
    (hr : gateResultAt p c E rho y s = some (some X)) : Block.Preceq B X := by
  have hearly : SA.earlyTime p.toParams s ≤ cut := by
    apply le_trans _ hc
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  exact pcsa_result_covers_heads_of_label E rho h.base h.strict hF y hy s B X
    (pcsa_floor_vote (pcsa_cleanWindow_floor E rho h s hs)) (h.labels s hs hearly) hc h.cut.2
    hheads hr
/-- A claim-level result extends any prefix covered by every honest HEAD of its label. -/
theorem pcsa_clean_result_covers_heads [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (y : V) (hy : y ∈ rho.honest) (s : Slot) (B X : Block)
    (hc : SA.gateTime p.toParams s ≤ cut)
    (hheads : ∀ x H, HonestHeadAt p c E rho x s H → Block.Preceq B H)
    (hr : gateResultAt p c E rho y s = some (some X)) : Block.Preceq B X := by
  obtain ⟨k, hk, hX⟩ := pcsa_gateResultAt_source E rho y s X hr
  obtain ⟨Y, hY, hBY⟩ := pcsa_clean_gate_covers_heads E rho h hF k y hy s B hk hc hheads
  have he : Y = X := Option.some.inj (hY.symm.trans hX)
  exact he ▸ hBY
end AvailableChain.PCSA.Run

end
