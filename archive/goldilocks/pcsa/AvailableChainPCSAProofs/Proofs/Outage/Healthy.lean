module
public import AvailableChainPCSAProofs.Proofs.Outage.ArmCore
public import AvailableChainGeneric.Statements.V2.Duty.PCCompanion
public import AvailableChainPCSAClaims.Statements.OutageItems

public section

/-! ARM-healthy (pcsa34-r4.3 §5.4.2): in a clean prefix up to `b₀`, a PC held
at `T` with `T + 3Δ ≤ b₀` satisfies ARM(s, B, j₀) for the first label `j₀`
with `v_{j₀} ≥ b₀`, so 5.4.1 gives persistence of the strong read. The two
ARM items in a clean prefix are Clean-lane facts. They are the named
hypotheses `CleanHeldPCRelay` (item (a): relay within `Δ`) and
`CleanArmAcks` (item (b): CI 5.2.2 (d) and the honest N HEAD). -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}

/-! ### Reads -/

omit [DecidableEq V] [Fintype V] in
/-- Every event before the read index of `T` is at a time at most `T`. -/
theorem pcsa_read_events_le (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) (T : Time) :
    ∀ k < (rho.events.filter (fun e => decide (e.time ≤ T))).length,
      ∀ e, rho.events[k]? = some e → e.time ≤ T := by
  intro k hk e he
  have hf := V2.D.Engine.filter_eq_take hs (fun e => decide (e.time ≤ T)) (by
    intro e f hkf hf
    exact decide_eq_true (le_trans (V2.D.Engine.time_le_of_key_le _ _ hkf) (of_decide_eq_true hf)))
  have hm : e ∈ rho.events.filter (fun e => decide (e.time ≤ T)) := by
    rw [hf]
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hk]; exact he)
  exact of_decide_eq_true (List.mem_filter.mp hm).2

omit [Fintype V] in
/-- In stage 1, the PCs after the ticks of `t` are held at the read of `t`. -/
theorem pcsa_afterTicks_read_pcs (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hfr : StageOneFrame p c E rho) (y : V) (hy : y ∈ rho.honest)
    (t : Time) : (storeAfterTicks p c E rho y t).pcs ⊆ (storeAt p c E rho y t).pcs := by
  have hs := h.valid.toScheduleWellFormed
  have hidx : FGSA.Run.afterTicksIdx rho t ≤
      (rho.events.filter (fun e => decide (e.time ≤ t))).length := by
    change (rho.events.filter (FGSA.Run.cutPred t)).length ≤ _
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro e _ he
    have hk : toLex (e.time, e.phase) ≤ toLex (t, (1 : Nat)) := of_decide_eq_true he
    rcases Prod.Lex.toLex_le_toLex.mp hk with hlt | ⟨heq, -⟩
    · exact decide_eq_true (le_of_lt hlt)
    · exact decide_eq_true (le_of_eq heq)
  change (FGSA.Run.afterTicks E rho t y).st.pcs ⊆ _
  rw [FGSA.Run.afterTicks_eq_stateBefore E rho hs t, pcsa_storeAt_index E rho hs]
  exact (pcsa_stageOne_mono E rho h.noRestart hfr y hy hidx).1

/-- The strong read of a store with latest PC `d` is its target. -/
theorem pcsa_strong_of_latest (st : State p.n) (d : PC p.n) (h : latestPC st = some d) :
    strong st = d.target := by
  change ((latestPC st).map PC.target).getD .genesis = _
  rw [h]
  rfl

/-- The strong read of a store without a PC is genesis. -/
theorem pcsa_strong_of_none (st : State p.n) (h : latestPC st = none) :
    strong st = .genesis := by
  change ((latestPC st).map PC.target).getD .genesis = _
  rw [h]
  rfl

/-! ### Slot times -/

/-- Some vote time is at least `b`. -/
theorem pcsa_vote_exists (b : Time) : ∃ j : Slot, b ≤ SA.voteTime p.toParams j := by
  have hΔ : (1 : Int) ≤ p.Δ := p.deltaPos
  refine ⟨b.toNat, ?_⟩
  change b ≤ 4 * p.Δ * ((b.toNat : Nat) : Int) + p.Δ
  have h1 : b ≤ ((b.toNat : Nat) : Int) := Int.self_le_toNat b
  have h2 : (0 : Int) ≤ ((b.toNat : Nat) : Int) := Int.natCast_nonneg _
  nlinarith

/-- Vote times increase with the slot. -/
theorem pcsa_vote_mono {a b : Slot} (h : a ≤ b) :
    SA.voteTime p.toParams a ≤ SA.voteTime p.toParams b := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  change 4 * p.Δ * (a : Int) + p.Δ ≤ 4 * p.Δ * (b : Int) + p.Δ
  have : (a : Int) ≤ b := by exact_mod_cast h
  nlinarith

/-- The vote time is before the early time of a slot. -/
theorem pcsa_vote_lt_early (s : Slot) :
    SA.voteTime p.toParams s < SA.earlyTime p.toParams s := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  change 4 * p.Δ * (s : Int) + p.Δ < 4 * p.Δ * (s : Int) + 2 * p.Δ
  linarith

/-- The freeze before the first vote time `≥ b₀` is at least `b₀ − 2Δ`. -/
theorem pcsa_freeze_pred_ge (j : Slot) (hj : 0 < j) :
    SA.voteTime p.toParams j = SA.freezeTime p.toParams (j - 1) + 2 * p.Δ := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, (Nat.sub_add_cancel hj).symm⟩
  rw [Nat.add_sub_cancel]
  change 4 * p.Δ * ((j' + 1 : Nat) : Int) + p.Δ = 4 * p.Δ * (j' : Int) + 3 * p.Δ + 2 * p.Δ
  push_cast
  ring

/-! ### ARM-healthy -/

/-- [pcsa34-r4.3 §5.4.2 ARM-healthy] A PC held by an honest node at `T` with
`T + 3Δ ≤ b₀` has its target in every honest strong read from `b₀`, given
the two Clean-lane ARM items. -/
theorem pcsa_armHealthy_pc (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {T b₀ ΔF : Time} (hC : Clean₂ p c E rho b₀ ΔF) (hf : FaultsBelowQA p c rho)
    (hfr : StageOneFrame p c E rho) (hT0 : 0 ≤ T) (hT3 : T + 3 * E.Δ ≤ b₀)
    (hrelay : CleanHeldPCRelay p c E rho b₀) (hacks : CleanArmAcks p c E rho b₀)
    (v : V) (hv : v ∈ rho.honest) (d : PC p.n) (hd : d ∈ (storeAt p c E rho v T).pcs)
    (w : V) (hw : w ∈ rho.honest) (t : Time) (hbt : b₀ ≤ t) :
    Block.Preceq d.target (strong (storeAt p c E rho w t)) := by
  classical
  have h := hC.base
  have hs := h.valid.toScheduleWellFormed
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have hEΔ := h.delta
  -- the slot of `d` votes before `b₀`
  have hcs : CertSafe (AckOriginBy rho T) (storeAt p c E rho v T) := by
    rw [pcsa_storeAt_index E rho hs]
    exact pcsa_certSafe_by E rho _ v T (pcsa_read_events_le E rho hs T)
  have hO : OutageStore (RootBlockInRun p c E rho) (storeAt p c E rho v T) := by
    rw [pcsa_storeAt_index E rho hs]
    exact pcsa_outageStore_stateBefore E rho _ v hv
  obtain ⟨hwf, ho, -⟩ := pcsa_source_facts _ rho T _ hO hcs 0 0 d (Or.inl hd)
  have he := (pcsa_pc_honest_ack_by E rho h hf T d hwf ho).1
  have hvs : SA.voteTime p.toParams d.slot < b₀ := by
    have := pcsa_vote_lt_early (p := p) d.slot
    rw [hEΔ] at hT3
    linarith
  -- the first label `j₀` with `b₀ ≤ v_{j₀}`
  have hex := pcsa_vote_exists (p := p) b₀
  set j₀ := Nat.find hex with hj₀
  have hj₀b : b₀ ≤ SA.voteTime p.toParams j₀ := Nat.find_spec hex
  have hsj : d.slot < j₀ := by
    by_contra hn
    have := pcsa_vote_mono (p := p) (Nat.le_of_not_lt hn)
    linarith
  have hpos : 0 < j₀ := lt_of_le_of_lt (Nat.zero_le _) hsj
  have hz : T + E.Δ ≤ SA.freezeTime p.toParams (j₀ - 1) := by
    have := pcsa_freeze_pred_ge (p := p) j₀ hpos
    rw [hEΔ] at hT3 ⊢
    linarith
  have harm : Arm p c E rho d.slot d.target j₀ := by
    refine ⟨fun y hy => hrelay v hv T d hT0 (by linarith) hd y hy _ hz, ?_⟩
    intro y s' X h1 h2 hX
    refine hacks v hv T d hT0 hT3 hd y s' X h1 ?_ hX
    by_contra hn
    exact Nat.find_min hex h2 (not_lt.mp hn)
  have hheld : ∃ pc ∈ (storeAt p c E rho w t).pcs, pc.slot = d.slot ∧ pc.target = d.target := by
    obtain ⟨d', hd', h1, h2⟩ := hrelay v hv T d hT0 (by linarith) hd w hw t (by linarith)
    exact ⟨d', pcsa_afterTicks_read_pcs E rho h hfr w hw t hd', h1, h2⟩
  exact (pcsa_arm_outputs E rho h hf hfr hsj harm w hw t t le_rfl hheld).1

/-- [pcsa34-r4.3 §5.4.2 ARM-healthy; App. B pcPersistence, lag 3Δ] The
stage-1 companion persistence of the strong read, given the two Clean-lane
ARM items. -/
theorem pcsa_armHealthy_of (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {T b₀ ΔF : Time} (hC : Clean₂ p c E rho b₀ ΔF) (hf : FaultsBelowQA p c rho)
    (hfr : StageOneFrame p c E rho) (hT0 : 0 ≤ T) (hT3 : T + 3 * E.Δ ≤ b₀)
    (hrelay : CleanHeldPCRelay p c E rho b₀) (hacks : CleanArmAcks p c E rho b₀) :
    Gen.V2.Duty.PersistsFrom E rho (pcsaInterface p c (m := m)).strong T b₀ := by
  rw [Gen.V2.Duty.PersistsFrom_def]
  intro v hv B hB t hbt _
  rw [Gen.V2.Duty.InBy_def]
  intro w hw
  change Block.Preceq B (strong (storeAt p c E rho v T)) at hB
  change Block.Preceq B (strong (storeAt p c E rho w t))
  cases hl : latestPC (storeAt p c E rho v T) with
  | none =>
    rw [pcsa_strong_of_none _ hl] at hB
    rw [Gen.Pure.block_preceq_antisymm hB (Gen.Pure.block_genesis_preceq B)]
    exact Gen.Pure.block_genesis_preceq _
  | some d =>
    rw [pcsa_strong_of_latest _ d hl] at hB
    exact Gen.Pure.block_preceq_trans hB (pcsa_armHealthy_pc E rho hC hf hfr hT0 hT3 hrelay
      hacks v hv d (bestPC_mem _ d hl) w hw t hbt)

end AvailableChain.PCSA.Run
end
