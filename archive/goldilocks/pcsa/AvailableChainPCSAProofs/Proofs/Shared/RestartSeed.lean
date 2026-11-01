module
public import AvailableChainPCSAProofs.Proofs.Shared.StageRun
public import AvailableChainPCSAProofs.Proofs.Shared.PCViews
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainPCSAProofs.Proofs.Shared.VoterView
public import AvailableChainPCSAProofs.Proofs.Shared.StampKeep

public section

/-! The restart seed of the clean induction at a label `a > 0` (pcsa34-r5 §5.5;
CI restart step 4). The seed block `A` has slot `a`; every honest node holds
`PC(a, A)` before `z_a`; every honest HEAD and honest proposal of label `a` is
`A`; every honest raw result of label `a` is `A`; every lock that an honest
node stores from `z_a` to the input of gate `a` is below `A`; and C8 holds for
`(a, A)` from label `a + 1`. Label `0` keeps its own seed. -/

namespace AvailableChain.PCSA.Run

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In) {m : FGMode}
    (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))

/-- The restart seed at label `a` with block `A`. -/
structure CleanRestartSeed [Fintype V] (a : Slot) (A : Block) : Prop where
  slotPos : 0 < a
  slot : A.slot = a
  stamped : ∀ x ∈ rho.honest, PCStampedBefore p c E rho x (SA.freezeTime p.toParams a) a A
  heads : ∀ x H, HonestHeadAt p c E rho x a H → H = A
  proposal : ∀ P, Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface
    rho a P → P = A
  result : ∀ x ∈ rho.honest, ∀ R, gateResultAt p c E rho x a = some R → R = some A
  locksFromFreeze : ∀ x ∈ rho.honest, ∀ k,
    V2.D.Run.idxBefore rho (SA.freezeTime p.toParams a) ≤ k →
    k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams a) →
    ∀ row ∈ (V2.D.Run.stateBefore E rho k x).st.base.obligations, Block.Preceq row.1 A
  arm : ArmConcl p c E rho a A (a + 1)

end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- A PC stamped before `t` is held at every later indexed store in stage one. -/
theorem pcsa_stamped_held (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    (hf : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest)
    (t : Time) (s : Slot) (B : Block) (hp : PCStampedBefore p c E rho x t s B)
    (k : Nat) (hk : FGSA.Run.afterTicksIdx rho t ≤ k) :
    ∃ C ∈ (V2.D.Run.stateBefore E rho k x).st.pcs, C.slot = s ∧ C.target = B := by
  obtain ⟨C, hC, hslot, hb⟩ := hp
  have hr : storeAfterTicks p c E rho x t =
      (V2.D.Run.stateBefore E rho (FGSA.Run.afterTicksIdx rho t) x).st := by
    change (FGSA.Run.afterTicks E rho t x).st = _
    rw [FGSA.Run.afterTicks_eq_stateBefore E rho hs]
  rw [hr] at hC
  exact ⟨C, pcsa_run_pcs_mono E rho hf hnr x hx _ _ hk hC, hslot, hb⟩

/-- In stage one every held PC of an honest indexed store is frame-active. -/
theorem pcsa_held_frameActive (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hf : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest) (k : Nat)
    (C : PC p.n) (hC : C ∈ (V2.D.Run.stateBefore E rho k x).st.pcs) :
    frameActive p (V2.D.Run.stateBefore E rho k x).st C = true := by
  have ho := pcsa_outageStore_stateBefore E rho k x hx
  exact (pcsa_frameActive_vacuous p _ (hf x hx k) C).mpr (ho.lift _ (ho.pcBlocks C hC))

/-- A max-rank choice ranks at least every member. -/
theorem pcsa_bestPC_slot_of_mem (cs : List (PC n)) (C D : PC n)
    (hC : C ∈ cs) (hD : bestPC cs = some D) : C.slot ≤ D.slot := by
  have hb := pcsa_bestPC_rank_max cs C D hC hD
  by_contra hn
  have hlt : D.slot < C.slot := Nat.lt_of_not_le hn
  change (decide (D.slot < C.slot) || _) = false at hb
  rw [decide_eq_true hlt, Bool.true_or] at hb
  exact Bool.false_ne_true hb.symm

/-- K1, proposer read: from `z_a`, the proposer PC of an honest node has slot at least `a`. -/
theorem pcsa_restart_proposerPC_slot (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) (hf : StageOneFrame p c E rho)
    (x : V) (hx : x ∈ rho.honest) (a : Slot) (A : Block)
    (hp : PCStampedBefore p c E rho x (SA.freezeTime p.toParams a) a A)
    (k : Nat) (hk : FGSA.Run.afterTicksIdx rho (SA.freezeTime p.toParams a) ≤ k) :
    ∃ D, proposerPC p (V2.D.Run.stateBefore E rho k x).st = some D ∧ a ≤ D.slot := by
  obtain ⟨C, hC, hslot, _⟩ := pcsa_stamped_held E rho hs hnr hf x hx _ a A hp k hk
  have hm : C ∈ (V2.D.Run.stateBefore E rho k x).st.pcs.filter
      (frameActive p (V2.D.Run.stateBefore E rho k x).st) :=
    List.mem_filter.mpr ⟨hC, pcsa_held_frameActive E rho hf x hx k C hC⟩
  cases hD : proposerPC p (V2.D.Run.stateBefore E rho k x).st with
  | none =>
    have he := pcsa_bestPC_none _ hD
    rw [he] at hm
    exact absurd hm List.not_mem_nil
  | some D => exact ⟨D, rfl, hslot ▸ pcsa_bestPC_slot_of_mem _ C D hm hD⟩

omit [DecidableEq V] in
/-- A tick strictly after `t` is at or after the post-tick cut of `t`. -/
theorem pcsa_afterTicksIdx_le_tick (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {v : V} {t u : Time}
    (hi : rho.events[i]? = some (.tick v u)) (ht : t < u) :
    FGSA.Run.afterTicksIdx rho t ≤ i := by
  by_contra hn
  have hf := V2.D.Engine.filter_eq_take hs (FGSA.Run.cutPred t) (fun e f hk hf =>
    decide_eq_true (hk.trans (of_decide_eq_true hf)))
  have hm : (V2.Event.tick v u : V2.Event V (pcsaWith m p c).Object) ∈
      rho.events.filter (FGSA.Run.cutPred t) := by
    rw [hf]
    apply List.mem_of_getElem? (i := i)
    change (rho.events.take (FGSA.Run.afterTicksIdx rho t))[i]? = some _
    rw [List.getElem?_take_of_lt (Nat.lt_of_not_le hn)]
    exact hi
  have hkey : toLex (u, (1 : Nat)) ≤ toLex (t, (1 : Nat)) :=
    of_decide_eq_true (List.mem_filter.mp hm).2
  rcases Prod.Lex.toLex_le_toLex.mp hkey with h | ⟨h, _⟩
  · exact absurd (h.trans ht) (lt_irrefl _)
  · have hut : u = t := h
    rw [hut] at ht
    exact absurd ht (lt_irrefl _)

/-- K1, voter read: from its freeze tick `z_s` with `s ≥ a`, the frozen row of label
`s` holds the seed PC at every later indexed store. -/
theorem pcsa_restart_snapshot_held (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) (hf : StageOneFrame p c E rho)
    (x : V) (hx : x ∈ rho.honest) (a : Slot) (A : Block)
    (hp : PCStampedBefore p c E rho x (SA.freezeTime p.toParams a) a A)
    (s : Slot) (has : a ≤ s) (i : Nat)
    (hi : rho.events[i]? = some (.tick x (SA.freezeTime p.toParams s)))
    (k : Nat) (hk : i < k) :
    ∃ C ∈ pcSnapshotAt (V2.D.Run.stateBefore E rho k x).st s, C.slot = a ∧ C.target = A := by
  have hheld : ∃ C ∈ (V2.D.Run.stateBefore E rho i x).st.pcs, C.slot = a ∧ C.target = A := by
    rcases has.lt_or_eq with hlt | he
    · apply pcsa_stamped_held E rho hs hnr hf x hx _ a A hp i
      apply pcsa_afterTicksIdx_le_tick E rho hs hi
      change 4 * p.Δ * (a : Int) + 3 * p.Δ < 4 * p.Δ * (s : Int) + 3 * p.Δ
      have hlt' : (a : Int) < s := by exact_mod_cast hlt
      nlinarith [p.deltaPos]
    · subst he
      obtain ⟨C, hC, hslot, hb⟩ := hp
      have hr : storeAfterTicks p c E rho x (SA.freezeTime p.toParams a) =
          clock p (V2.D.Run.stateBefore E rho i x).st (SA.freezeTime p.toParams a) := by
        change (FGSA.Run.afterTicks E rho (SA.freezeTime p.toParams a) x).st = _
        rw [FGSA.Run.afterTicks_node E rho hs hi]
        exact pcsa_tick_st E rho _ _ _
      rw [hr, pcsa_clock_pcs] at hC
      exact ⟨C, hC, hslot, hb⟩
  obtain ⟨C, hC, hslot, hb⟩ := hheld
  have habs := snapshot_absent_before_tick E rho hs.nodup i x s hi
  have hrow : ((V2.D.Run.stateBefore E rho (i + 1) x).st.pcSnapshot.find?
      (fun row => row.1 == s)).isSome := by
    rw [V2.D.Run.stateBefore_succ E rho hi]
    rw [pcsa_tick_step]
    have hsnap := clock_freeze_snapshot p (V2.D.Run.stateBefore E rho i x).st s habs
    cases hfind : (clock p (V2.D.Run.stateBefore E rho i x).st
        (SA.freezeTime p.toParams s)).pcSnapshot.find? (fun row => row.1 == s) with
    | some _ => rfl
    | none =>
      rw [pcSnapshotAt_absent _ s hfind, pcsa_clock_pcs] at hsnap
      rw [← hsnap] at hC
      exact absurd hC List.not_mem_nil
  have he := ((pcsa_stageOne_mono E rho hnr hf x hx (Nat.succ_le_of_lt hk)).2 s hrow).1
  refine ⟨C, ?_, hslot, hb⟩
  rw [he, V2.D.Run.stateBefore_succ E rho hi]
  rw [pcsa_tick_step, clock_freeze_snapshot p _ s habs, pcsa_clock_pcs]
  exact hC

/-- K1, gate read: at a gate `s > a`, the gate rank of an honest node has slot at least `a`. -/
theorem pcsa_restart_gateRank_slot (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) (hf : StageOneFrame p c E rho)
    (x : V) (hx : x ∈ rho.honest) (a : Slot) (A : Block)
    (hp : PCStampedBefore p c E rho x (SA.freezeTime p.toParams a) a A)
    (s : Slot) (has : a < s) (g : Nat)
    (hg : rho.events[g]? = some (.tick x (SA.gateTime p.toParams s))) :
    ∃ r, gateRank p (clockPre p (V2.D.Run.stateBefore E rho g x).st
      (SA.gateTime p.toParams s)) s = some r ∧ a ≤ r.slot := by
  have hs := h.valid.toScheduleWellFormed
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  let i₀ := FGSA.Run.afterTicksIdx rho (SA.freezeTime p.toParams a)
  obtain ⟨C, hC, hslot, -⟩ := pcsa_stamped_held E rho hs h.noRestart hf x hx _ a A hp i₀ le_rfl
  have hbound : StampBound (SA.earlyTime p.toParams s) (V2.D.Run.stateBefore E rho i₀ x).st := by
    apply pcsa_stampBound_of_ticks E rho i₀ x _
    · change 0 < 4 * p.Δ * (s : Int) + 2 * p.Δ
      positivity
    · intro k hk u hu
      by_contra hn
      have hle := pcsa_afterTicksIdx_le_tick E rho hs hu (t := SA.freezeTime p.toParams a) (by
        have has' : (a : Int) + 1 ≤ s := by exact_mod_cast has
        have hn' : 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ u := le_of_not_gt hn
        change 4 * p.Δ * (a : Int) + 3 * p.Δ < u
        nlinarith)
      omega
  obtain ⟨τ, hτlt, hτ⟩ := held_pcStamp _ _ hbound C hC
  have hg₀ : i₀ ≤ g := by
    apply pcsa_afterTicksIdx_le_tick E rho hs hg
    have has' : (a : Int) + 1 ≤ s := by exact_mod_cast has
    change 4 * p.Δ * (a : Int) + 3 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
    nlinarith
  have hτg := pcsa_run_stamp_keep E rho h hf x hx i₀ g hg₀ C τ hC hτ
  have hCg := pcsa_run_pcs_mono E rho hf h.noRestart x hx i₀ g hg₀ hC
  let pre := clockPre p (V2.D.Run.stateBefore E rho g x).st (SA.gateTime p.toParams s)
  have hfg : pre.fg = (V2.D.Run.stateBefore E rho g x).st.fg :=
    (clockPre_output_fields p _ _).1
  have hvac : FrameVacuous p pre := by
    change pre.fg.F = .genesis ∧
      (KitFG.storeControlsView (FGSA.heightView p) pre.fg).Z = .genesis ∧
      (KitFG.storeControlsView (FGSA.heightView p) pre.fg).lo = 0
    rw [hfg]
    exact hf x hx g
  have hact : frameActive p pre C = true := by
    apply (pcsa_frameActive_vacuous p pre hvac C).mpr
    rw [hfg]
    exact (pcsa_frameActive_vacuous p _ (hf x hx g) C).mp
      (pcsa_held_frameActive E rho hf x hx g C hCg)
  have hpre : pcStamp? pre C = some τ := by
    simp only [pre, pcStamp?_def, clockPre_pcStamps] at hτg ⊢
    exact hτg
  have hm := (gateRank_candidate_iff p pre s C).mpr
    ⟨(clockPre_pcs p _ _).symm ▸ hCg, hact, τ, hpre, hτlt⟩
  change ∃ r, gateRank p pre s = some r ∧ a ≤ r.slot
  rw [gateRank_def]
  cases hD : bestPC (pre.pcs.filter (fun c => frameActive p pre c &&
      (pcStamp? pre c).any (fun t => t < SA.earlyTime p.toParams s))) with
  | none =>
    rw [pcsa_bestPC_none _ hD] at hm
    exact absurd hm List.not_mem_nil
  | some D => exact ⟨D.rank, rfl, hslot ▸ pcsa_bestPC_slot_of_mem _ C D hm hD⟩

end AvailableChain.PCSA.Run

end
