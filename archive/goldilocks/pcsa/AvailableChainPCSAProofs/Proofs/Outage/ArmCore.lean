module
public import AvailableChainPCSAProofs.Proofs.Outage.ArmTiming
public import AvailableChainPCSAProofs.Proofs.Foundations.SnapshotRun
public import AvailableChainPCSAClaims.Statements.Premises
public import AvailableChainPCSAProofs.Proofs.Foundations.Output

public section

/-! PC persistence under ARM, stage 1 (pcsa34-r4.3 §5.4.1 steps 1–5). The
induction runs over HEAD labels `j ≥ j₀`: the frozen view holds `PC(s, B)`,
every view source of rank at least it has a target `⪰ B` (slot `s` by
uniqueness, slots in `(s, j₀)` by ARM (b), later slots by the induction), so
the live root and the HEAD are `⪰ B`; an honest ack names an honest HEAD.
The outputs follow from the same rank split over the held PCs. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}

/-! ### Held PCs -/

omit [Fintype V] in
/-- Every indexed store has certificates delivered by the horizon. -/
theorem pcsa_certSafe_horizon (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (j : Nat) (v : V) :
    CertSafe (AckOriginBy rho rho.horizon) (V2.D.Run.stateBefore E rho j v).st :=
  pcsa_certSafe_by E rho j v _ (pcsa_events_le_horizon E rho h.valid.toScheduleWellFormed j)

/-- A PC held at an honest indexed state has a scoped target and an honest
ack of its slot on that target. -/
theorem pcsa_held_pc_ack (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : FaultsBelowQA p c rho) (y : V) (hy : y ∈ rho.honest)
    (k : Nat) (d : PC p.n) (hd : d ∈ (V2.D.Run.stateBefore E rho k y).st.pcs) :
    RootBlockInRun p c E rho d.target ∧ ∃ x, HonestAckAt p c E rho x d.slot d.target := by
  have hO := pcsa_outageStore_stateBefore E rho k y hy
  obtain ⟨hw, ho, hb⟩ := pcsa_source_facts _ rho _ _ hO (pcsa_certSafe_horizon E rho h k y)
    0 0 d (Or.inl hd)
  have hr : RootBlockInRun p c E rho d.target := by
    obtain ⟨B, hB, he⟩ := hO.lift _ hb
    rw [← he]
    exact hO.tf B hB
  obtain ⟨-, x, X, hX, hroot⟩ := pcsa_pc_honest_ack_by E rho h hf _ d hw ho
  have he := pcsa_outage_rootBlock_eq E rho h (pcsa_honest_ack_support E rho h x _ X hX).1
    hr hroot
  exact ⟨hr, x, he ▸ hX⟩

/-! ### The rank split -/

/-- [pcsa34-r4.3 §5.4.1 steps 1, 4, 5] A PC of slot at least `s` whose acks
were delivered by `T` has a target `⪰ B`: slot `s` names `B`, slots in
`(s, j₀)` have an honest ack `⪰ B` (ARM (b)), and slots `≥ j₀` with early
time at most `T` are covered by `hIH`. -/
theorem pcsa_arm_pc_above (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : FaultsBelowQA p c rho) {s j₀ : Slot} {B : Block}
    (hacks : ∀ y s' X, s + 1 ≤ s' → s' < j₀ → HonestAckAt p c E rho y s' X →
      Block.Preceq B X)
    (hB : ∃ y, HonestAckAt p c E rho y s B) (T : Time)
    (hIH : ∀ j', j₀ ≤ j' → SA.earlyTime p.toParams j' ≤ T →
      ∀ x X, HonestAckAt p c E rho x j' X → Block.Preceq B X)
    (d : PC p.n) (hw : d.wellFormed = true) (ho : ∀ a ∈ d.acks, AckOriginBy rho T a)
    (hr : RootBlockInRun p c E rho d.target) (hs : s ≤ d.slot) :
    Block.Preceq B d.target := by
  obtain ⟨hT, y, X, hX, hroot⟩ := pcsa_pc_honest_ack_by E rho h hf T d hw ho
  have he := pcsa_outage_rootBlock_eq E rho h (pcsa_honest_ack_support E rho h y _ X hX).1
    hr hroot
  subst he
  rcases Nat.lt_or_eq_of_le hs with hlt | heq
  · by_cases hj : d.slot < j₀
    · exact hacks y d.slot _ hlt hj hX
    · exact hIH d.slot (Nat.le_of_not_lt hj) hT y _ hX
  · obtain ⟨y₀, hB⟩ := hB
    rw [← heq] at hX
    rw [pcsa_honest_ack_unique E rho h hf y₀ y s B _ hB hX]
    exact Gen.Pure.block_preceq_refl _

/-! ### Ticks of one node -/

omit [DecidableEq V] [Fintype V] in
/-- Two ticks of one node are in time order. -/
theorem pcsa_tick_index_le (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) {k k' : Nat} {y : V} {t t' : Time}
    (hk : rho.events[k]? = some (.tick y t)) (hk' : rho.events[k']? = some (.tick y t'))
    (h : t ≤ t') : k ≤ k' := by
  rcases lt_or_eq_of_le h with hlt | heq
  · exact le_of_lt (pcsa_index_lt_of_time_lt E rho hs hk hk' hlt)
  · subst heq
    exact le_of_eq ((List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.mp hk).1 hs.nodup).mp
      (hk.trans hk'.symm))

/-! ### Store reads -/

omit [DecidableEq V] [Fintype V] in
/-- A PC of a frozen row is in a stored row, and the row is present. -/
theorem pcsa_pcSnapshotAt_row (st : State p.n) (k : Slot) (d : PC p.n)
    (hd : d ∈ pcSnapshotAt st k) :
    (st.pcSnapshot.find? (fun row => row.1 == k)).isSome ∧
      ∃ row ∈ st.pcSnapshot, d ∈ row.2 := by
  change d ∈ ((st.pcSnapshot.find? (fun row => row.1 == k)).map Prod.snd).getD [] at hd
  cases hf : st.pcSnapshot.find? (fun row => row.1 == k) with
  | none =>
    rw [hf] at hd
    exact absurd hd (List.not_mem_nil)
  | some row =>
    rw [hf] at hd
    exact ⟨rfl, row, List.mem_of_find?_eq_some hf, hd⟩

omit [Fintype V] in
/-- The clock of a tick is the state after the tick. -/
theorem pcsa_clock_tick_succ (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) {k : Nat} {y : V} {t : Time}
    (hk : rho.events[k]? = some (.tick y t)) :
    clock p (V2.D.Run.stateBefore E rho k y).st t = (V2.D.Run.stateBefore E rho (k + 1) y).st :=
  (pcsa_storeAfterTicks_tick E rho hs hk).1.symm.trans (pcsa_storeAfterTicks_tick E rho hs hk).2

omit [Fintype V] in
/-- After the tick at `t`, every held certificate has its acks delivered by `t`. -/
theorem pcsa_certSafe_tick (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) {k : Nat} {y : V} {t : Time}
    (hk : rho.events[k]? = some (.tick y t)) (v : V) :
    CertSafe (AckOriginBy rho t) (V2.D.Run.stateBefore E rho (k + 1) v).st := by
  refine pcsa_certSafe_by E rho (k + 1) v t (fun k' hk' e he => ?_)
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hlt | heq
  · exact pcsa_events_before_tick E rho hs hk k' hlt e he
  · subst heq
    rw [hk] at he
    cases Option.some.inj he
    exact le_rfl

/-! ### The induction -/

/-- [pcsa34-r4.3 §5.4.1 steps 1–3] At the tick of an honest node at `v_j`
(`j ≥ j₀`), the slot-`j` view is frame-active and `⪰ B`: the frozen row of
`j − 1` holds `PC(s, B)` (ARM (a) and stage-1 monotonicity), so the view has
slot at least `s`, and its acks were delivered by `v_j`. `hIH` covers the
honest acks of the slots in `[j₀, j)`. -/
theorem pcsa_arm_view (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : FaultsBelowQA p c rho) (hfr : StageOneFrame p c E rho)
    {s j₀ : Slot} {B : Block} (hsj : s < j₀) (harm : Arm p c E rho s B j₀)
    (x : V) (hx : x ∈ rho.honest) (j : Slot) (hj : j₀ ≤ j) (k : Nat)
    (hk : rho.events[k]? = some (.tick x (SA.voteTime p.toParams j)))
    (hIH : ∀ j', j₀ ≤ j' → j' < j → ∀ y X, HonestAckAt p c E rho y j' X →
      Block.Preceq B X) :
    ∃ cv, voterPC p (clock p (V2.D.Run.stateBefore E rho k x).st
        (SA.voteTime p.toParams j)) j = some cv ∧
      frameActive p (clock p (V2.D.Run.stateBefore E rho k x).st
        (SA.voteTime p.toParams j)) cv = true ∧ Block.Preceq B cv.target := by
  have hs := h.valid.toScheduleWellFormed
  rw [pcsa_clock_tick_succ E rho hs hk]
  have hO := pcsa_outageStore_stateBefore E rho (k + 1) x hx
  have hv := hfr x hx (k + 1)
  have hj0 : 0 < j := lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.zero_le s) hsj) hj
  have hvh : SA.voteTime p.toParams j ≤ rho.horizon := pcsa_tick_le_horizon E rho hs hk
  have hzj := pcsa_freeze_pred_lt_vote (p := p) j hj0
  have hz0 : SA.freezeTime p.toParams (j₀ - 1) ≤ SA.freezeTime p.toParams (j - 1) :=
    pcsa_freeze_mono (Nat.sub_le_sub_right hj 1)
  obtain ⟨i₁, hi₁⟩ := pcsa_tick_exists E rho hs x hx _ (pcsa_freeze_public E h.delta (j - 1))
    (le_of_lt (pcsa_freeze_pos _)) (le_trans (le_of_lt hzj) hvh)
  obtain ⟨i₀, hi₀⟩ := pcsa_tick_exists E rho hs x hx _ (pcsa_freeze_public E h.delta (j₀ - 1))
    (le_of_lt (pcsa_freeze_pos _)) (le_trans hz0 (le_trans (le_of_lt hzj) hvh))
  have h01 : i₀ ≤ i₁ := pcsa_tick_index_le E rho hs hi₀ hi₁ hz0
  have h1k : i₁ < k := pcsa_index_lt_of_time_lt E rho hs hi₁ hk hzj
  obtain ⟨d₀, hd₀, hds, hdt⟩ := harm.stamped x hx
  change d₀ ∈ (storeAfterTicks p c E rho x _).pcs at hd₀
  rw [(pcsa_storeAfterTicks_tick E rho hs hi₀).2] at hd₀
  have hd₁ := (pcsa_stageOne_mono E rho h.noRestart hfr x hx (Nat.succ_le_succ h01)).1 hd₀
  have hsnap := snapshot_afterTicks E rho hs h.delta x hx (j - 1) (le_trans (le_of_lt hzj) hvh)
  rw [(pcsa_storeAfterTicks_tick E rho hs hi₁).2] at hsnap
  rw [← hsnap] at hd₁
  obtain ⟨hrow, -⟩ := pcsa_pcSnapshotAt_row _ _ _ hd₁
  obtain ⟨g1, -⟩ := (pcsa_stageOne_mono E rho h.noRestart hfr x hx h1k).2 (j - 1) hrow
  obtain ⟨g3, -⟩ := (pcsa_stageOne_mono E rho h.noRestart hfr x hx (Nat.le_succ k)).2 (j - 1)
    ((pcsa_stageOne_mono E rho h.noRestart hfr x hx h1k).2 (j - 1) hrow).2
  have hd₃ : d₀ ∈ pcSnapshotAt (V2.D.Run.stateBefore E rho (k + 1) x).st (j - 1) := by
    rw [g3, g1]
    exact hd₁
  have hdin : d₀ ∈ (pcSnapshotAt (V2.D.Run.stateBefore E rho (k + 1) x).st (j - 1) ++
      carriedPCs (V2.D.Run.stateBefore E rho (k + 1) x).st j).filter
        (frameActive p (V2.D.Run.stateBefore E rho (k + 1) x).st) := by
    refine List.mem_filter.mpr ⟨List.mem_append_left _ hd₃, ?_⟩
    obtain ⟨-, row, hr, hdr⟩ := pcsa_pcSnapshotAt_row _ _ _ hd₃
    exact (pcsa_frameActive_vacuous p _ hv d₀).mpr
      (hO.lift _ (hO.pcBlocks d₀ (hO.snapSub row hr d₀ hdr)))
  obtain ⟨cv, hcv, hle⟩ := pcsa_bestPC_slot_ge _ d₀ hdin
  have hmem := List.mem_filter.mp (bestPC_mem _ cv hcv)
  have hB : ∃ y, HonestAckAt p c E rho y s B := by
    obtain ⟨-, y, hy⟩ := pcsa_held_pc_ack E rho h hf x hx (i₀ + 1) d₀ hd₀
    rw [hds, hdt] at hy
    exact ⟨y, hy⟩
  obtain ⟨hw, ho, hb⟩ := pcsa_source_facts _ rho _ _ hO (pcsa_certSafe_tick E rho hs hk x)
    (j - 1) j cv (Or.inr (List.mem_append.mp hmem.1))
  refine ⟨cv, hcv, hmem.2, pcsa_arm_pc_above E rho h hf harm.acks hB _ ?_ cv hw ho
    (pcsa_outage_block_prop hO _ hb) (by rw [← hds]; exact hle)⟩
  intro j' hj' hT y X hX
  exact hIH j' hj' (pcsa_early_le_vote_lt j' j hT) y X hX

/-- [pcsa34-r4.3 §5.4.1 step 3] An honest HEAD at `v_j` (`j ≥ j₀`) extends
its view, so it is `⪰ B`. -/
theorem pcsa_arm_head_step (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : FaultsBelowQA p c rho) (hfr : StageOneFrame p c E rho)
    {s j₀ : Slot} {B : Block} (hsj : s < j₀) (harm : Arm p c E rho s B j₀)
    (j : Slot) (hj : j₀ ≤ j)
    (hIH : ∀ j', j₀ ≤ j' → j' < j → ∀ y X, HonestAckAt p c E rho y j' X →
      Block.Preceq B X)
    (x : V) (H : Block) (hH : HonestHeadAt p c E rho x j H) : Block.Preceq B H := by
  obtain ⟨hx, -, hr⟩ := hH
  rw [pcsa_voteHeadAt_def] at hr
  obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hr
  obtain ⟨k, hk, hst⟩ := pcsa_postClock_some E rho hnd
  obtain ⟨cv, hcv, hact, hBcv⟩ := pcsa_arm_view E rho h hf hfr hsj harm x hx j hj k hk hIH
  have hj0 : j ≠ 0 := Nat.pos_iff_ne_zero.mp
    (lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.zero_le s) hsj) hj)
  rw [hst]
  delta headVote
  rw [ite_eq_right hj0, hcv]
  exact Gen.Pure.block_preceq_trans hBcv (pcsa_headInTree_extends_view p _ cv _ _ _ hact)

/-- [pcsa34-r4.3 §5.4.1] Every honest HEAD of a label `≥ j₀` is `⪰ B`
(strong induction on the label). -/
theorem pcsa_arm_heads (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : FaultsBelowQA p c rho) (hfr : StageOneFrame p c E rho)
    {s j₀ : Slot} {B : Block} (hsj : s < j₀) (harm : Arm p c E rho s B j₀) :
    ∀ j, j₀ ≤ j → ∀ x H, HonestHeadAt p c E rho x j H → Block.Preceq B H := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj x H hH
    refine pcsa_arm_head_step E rho h hf hfr hsj harm j hj (fun j' hj' hlt y X hX => ?_) x H hH
    obtain ⟨z, hz⟩ := pcsa_honest_ack_head E rho h hf hfr y j' X hX
    exact ih j' hlt hj' z X hz

/-- [pcsa34-r4.3 §5.4.1, 5.1] Every honest ack of a slot `≥ j₀` is `⪰ B`. -/
theorem pcsa_arm_acks (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : FaultsBelowQA p c rho) (hfr : StageOneFrame p c E rho)
    {s j₀ : Slot} {B : Block} (hsj : s < j₀) (harm : Arm p c E rho s B j₀)
    (j : Slot) (x : V) (X : Block) (hj : j₀ ≤ j) (hX : HonestAckAt p c E rho x j X) :
    Block.Preceq B X := by
  obtain ⟨y, hy⟩ := pcsa_honest_ack_head E rho h hf hfr x j X hX
  exact pcsa_arm_heads E rho h hf hfr hsj harm j hj y X hy

/-- [pcsa34-r4.3 §5.4.1 step 5] From the time an honest node holds `PC(s, B)`,
its strong and available outputs are `⪰ B`: the held PC stays held, the
latest PC has slot at least `s`, and its acks were delivered in the run. -/
theorem pcsa_arm_outputs (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : FaultsBelowQA p c rho) (hfr : StageOneFrame p c E rho)
    {s j₀ : Slot} {B : Block} (hsj : s < j₀) (harm : Arm p c E rho s B j₀)
    (w : V) (hw : w ∈ rho.honest) (t t' : Time) (htt : t ≤ t')
    (hheld : ∃ pc ∈ (storeAt p c E rho w t).pcs, pc.slot = s ∧ pc.target = B) :
    Block.Preceq B (strong (storeAt p c E rho w t')) ∧
      Block.Preceq B (confirmed (storeAt p c E rho w t')) := by
  have hs := h.valid.toScheduleWellFormed
  obtain ⟨d₀, hd₀, hds, hdt⟩ := hheld
  rw [pcsa_storeAt_index E rho hs] at hd₀
  rw [pcsa_storeAt_index E rho hs w t']
  have hd₁ := (pcsa_stageOne_mono E rho h.noRestart hfr w hw
    (pcsa_storeAt_index_mono rho htt)).1 hd₀
  obtain ⟨cv, hcv, hle⟩ := pcsa_bestPC_slot_ge _ d₀ hd₁
  have hO := pcsa_outageStore_stateBefore E rho
    (rho.events.filter (fun e => decide (e.time ≤ t'))).length w hw
  obtain ⟨hwf, ho, hb⟩ := pcsa_source_facts _ rho _ _ hO (pcsa_certSafe_horizon E rho h _ w)
    0 0 cv (Or.inl (bestPC_mem _ cv hcv))
  have hB : ∃ y, HonestAckAt p c E rho y s B := by
    obtain ⟨-, y, hy⟩ := pcsa_held_pc_ack E rho h hf w hw _ d₀ hd₀
    rw [hds, hdt] at hy
    exact ⟨y, hy⟩
  have hBc := pcsa_arm_pc_above E rho h hf harm.acks hB rho.horizon
    (fun j' hj' _ y X hX => pcsa_arm_acks E rho h hf hfr hsj harm j' y X hj' hX) cv hwf ho
    (pcsa_outage_block_prop hO _ hb) (by rw [← hds]; exact hle)
  have hstrong : strong (V2.D.Run.stateBefore E rho
      (rho.events.filter (fun e => decide (e.time ≤ t'))).length w).st = cv.target := by
    change ((bestPC _).map PC.target).getD .genesis = _
    rw [hcv]
    rfl
  rw [← hstrong] at hBc
  exact ⟨hBc, Gen.Pure.block_preceq_trans hBc (strong_preceq_confirmed _)⟩

/-- [pcsa34-r4.3 §5.4.1 Theorem] The persistence conclusion under ARM. -/
theorem pcsa_arm_concl (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : FaultsBelowQA p c rho) (hfr : StageOneFrame p c E rho)
    {s j₀ : Slot} {B : Block} (hsj : s < j₀) (harm : Arm p c E rho s B j₀) :
    ArmConcl p c E rho s B j₀ := by
  rw [pcsa_ArmConcl_def]
  exact ⟨fun j x H hj hH => pcsa_arm_heads E rho h hf hfr hsj harm j hj x H hH,
    fun j x X hj hX => pcsa_arm_acks E rho h hf hfr hsj harm j x X hj hX,
    fun w hw t t' htt hheld => pcsa_arm_outputs E rho h hf hfr hsj harm w hw t t' htt hheld⟩

end AvailableChain.PCSA.Run
end
