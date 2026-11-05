module
public import ConsensusLeanTest.Goldilocks.Runs.Asleep.Run
import ConsensusLean.Lemmas.Tactic.Linarith
@[expose] public section

/-! # The two-validator asleep run is `Sleepy`, with a proposal at every slot

On the run `tr2` of `Goldilocks/Runs/Asleep/Run` (two honest validators, only `w0` awake, at every
`t ≥ 0`; `Δ = 1`, `t_s = 4s`):

* (a) `tr2_syncOn`: `Sync` for every window, relay window and effective send time `eff τ ≥ τ`,
  with `Δ_F = 1` (only `w0` calls, and it processes its own objects inside the tick);
* (a) `tr2_faultBound`, `tr2_sleepy`: `f = 0 < h_t = 1` at every `t ≥ 0`, so `SleepyRun` holds
  (with `Δ_F = 1`);
* (a) `tr2_proposesAt`: at every slot `s ≥ 1` the own block of the tick of `t_s` (cut
  `8·t_s + 2`) is a proposal of `w0` of slot `s`, processed with `w0` joined there.

Validator `w1` is honest and asleep throughout, so `h_t = 1` while `n = 2`: an optimistic
confirmation (three quarters of the committee) never fires, which
`Goldilocks/AC/InclusionUpdateRejection` uses. -/

namespace Consensus.Goldilocks.Witness.Two

open SA Node

theorem tr2_no_restart (y : Fin sp2.n) (k : Nat) : ¬ tr2.RestartAt y k :=
  tickRun_no_restart (A := N2) (dg := dg2) y k

theorem tr2_time (i : Nat) : tr2.time i = ((i / 8 : Nat) : Int) := rfl

/-- `w0` never restarts, so its restart time stays `⊥`. -/
theorem restartTime_bot : ∀ i, ((tickRun N2 dg2).state v0 i).ac.restartTime = ⊥
  | 0 => rfl
  | i + 1 => by
    simp only [Trace.state]
    split_ifs with hl
    · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hl.2
      have hcall : (tickRun N2 dg2).CallAt v0 i c := ⟨hl.1, hc⟩
      have hstep := cutStep_ac (tickRun_cutStep_v0 hcall)
      cases c with
      | fg ℓ => rw [hstep.1 ℓ rfl]; exact restartTime_bot i
      | ac ℓ =>
        have hac : ((tickRun N2 dg2).post i).ac = (ACInterface.step N2 v0
            ((tickRun N2 dg2).state v0 i).ac ℓ.frame ((tickRun N2 dg2).time i) ℓ.call).1 :=
          (congrArg Prod.fst (hstep.2 ℓ rfl)).symm
        rw [hac]
        refine (SA.step_restartTime v0 _ _ _ _ fun hr => ?_).trans (restartTime_bot i)
        exact tickRun_no_restart v0 i ⟨ℓ, hcall, hr⟩
    · exact restartTime_bot i

/-- `w0` is joined at every cut. -/
theorem joined_w0 (i : Nat) (t : Time) : joined sp2 (tr2.state w0 i).ac t := by
  unfold joined; rw [tr2_state, restartTime_bot]; exact bot_le

/-- `w0` is joined at every time (no restart). -/
theorem joinedAt (y : Fin sp2.n) (t : Time) : tr2.JoinedAt y t :=
  fun k hk => absurd hk (tr2_no_restart y k)

/-! ## The pool along the run -/

/-- The pool only grows along the run. -/
theorem pool_mono {i i' : Nat} (h : i ≤ i') (σ : Nat) :
    ((tickRun N2 dg2).state v0 i).ac.pool σ ⊆ ((tickRun N2 dg2).state v0 i').ac.pool σ := by
  induction i', h using Nat.le_induction with
  | base => exact fun _ h => h
  | succ i' _ ih =>
    refine List.Subset.trans ih ?_
    intro v hv
    simp only [Trace.state]
    split_ifs with hl
    · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hl.2
      have hcall : (tickRun N2 dg2).CallAt v0 i' c := ⟨hl.1, hc⟩
      have hstep := cutStep_ac (tickRun_cutStep_v0 hcall)
      cases c with
      | fg ℓ => rw [hstep.1 ℓ rfl]; exact hv
      | ac ℓ =>
        have hac : ((tickRun N2 dg2).post i').ac = (ACInterface.step N2 v0
            ((tickRun N2 dg2).state v0 i').ac ℓ.frame ((tickRun N2 dg2).time i') ℓ.call).1 :=
          (congrArg Prod.fst (hstep.2 ℓ rfl)).symm
        rw [hac]
        rcases onTick_ac_call N2 dg2 _ _ _ _ (tickRun_label_mem hc) with
          hcl | hcl | ⟨B, hcl⟩ | hcl <;>
          rw [hcl]
        · exact SAPool.acOnTick_pool_mono sp2 v0 _ _ _ σ hv
        · rw [ACInterface.step, SAPool.acProposal_pool]; exact hv
        · exact SAPool.acOnBlock_pool_mono sp2 v0 _ _ _ B σ hv
        · rw [ACInterface.step, SAPool.acToFG_pool]; exact hv
    · exact hv

/-- Pool `σ` holds votes of slot `σ`. -/
theorem slotOK (i : Nat) : SAPool.SlotOK sp2 ((tickRun N2 dg2).state v0 i).ac := by
  induction i with
  | zero => intro σ w hw; simp [Trace.state, tickRun, Node.init, SAState.initial] at hw
  | succ i ih =>
    simp only [Trace.state]
    split_ifs with hl
    · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hl.2
      have hcall : (tickRun N2 dg2).CallAt v0 i c := ⟨hl.1, hc⟩
      have hstep := cutStep_ac (tickRun_cutStep_v0 hcall)
      cases c with
      | fg ℓ => rw [hstep.1 ℓ rfl]; exact ih
      | ac ℓ =>
        have hac : ((tickRun N2 dg2).post i).ac = (ACInterface.step N2 v0
            ((tickRun N2 dg2).state v0 i).ac ℓ.frame ((tickRun N2 dg2).time i) ℓ.call).1 :=
          (congrArg Prod.fst (hstep.2 ℓ rfl)).symm
        rw [hac]
        rcases onTick_ac_call N2 dg2 _ _ _ _ (tickRun_label_mem hc) with
          hcl | hcl | ⟨B, hcl⟩ | hcl <;>
          rw [hcl]
        · exact SAPool.acOnTick_slot sp2 v0 _ _ _ ih
        · exact SAPool.slot_of_pool_eq sp2 (SAPool.acProposal_pool sp2 _ _ _) ih
        · exact SAPool.acOnBlock_slot sp2 v0 _ _ _ B ih
        · exact SAPool.slot_of_pool_eq sp2 (SAPool.acToFG_pool sp2 _ _ _) ih
    · exact ih

/-- Every AC message `w0` sends or admits, it emits at that cut. -/
theorem sendOrAdmit {i : Nat} {m : Vote sp2.n}
    (h : (tickRun N2 dg2).SendOrAdmitAt v0 i m) : (tickRun N2 dg2).EmitAt v0 i m := by
  obtain ⟨ℓ, hcall, h | ⟨-, hnot, hhold⟩⟩ := h
  · exact ⟨ℓ, hcall, h⟩
  change m ∉ ((tickRun N2 dg2).state v0 i).ac.pool m.slot at hnot
  change m ∈ ((tickRun N2 dg2).post i).ac.pool m.slot at hhold
  have hs := (cutStep_ac (tickRun_cutStep_v0 hcall)).2 ℓ rfl
  have hac : ((tickRun N2 dg2).post i).ac = (ACInterface.step N2 v0
      ((tickRun N2 dg2).state v0 i).ac ℓ.frame ((tickRun N2 dg2).time i) ℓ.call).1 :=
    (congrArg Prod.fst hs).symm
  have hem : ℓ.emits = (ACInterface.step N2 v0
      ((tickRun N2 dg2).state v0 i).ac ℓ.frame ((tickRun N2 dg2).time i) ℓ.call).2 :=
    (congrArg Prod.snd hs).symm
  rw [hac] at hhold
  have hmem := tickRun_label_mem hcall.2
  rcases onTick_ac_call N2 dg2 _ _ _ _ hmem with hcl | hcl | ⟨B, hcl⟩ | hcl <;>
    rw [hcl] at hhold hem
  · rcases SAPool.acOnTick_pool sp2 v0 _ _ _ _ m hhold with h | h
    · exact absurd h hnot
    · exact ⟨ℓ, hcall, by rw [hem]; exact h⟩
  · rw [ACInterface.step, SAPool.acProposal_pool] at hhold; exact absurd hhold hnot
  · rcases SAPool.acOnBlock_pool sp2 v0 _ _ _ B _ m hhold with h | h | h
    · exact absurd h hnot
    · exfalso
      obtain ⟨d, p, hr, hB⟩ := onTick_block_made N2 dg2 _ _ _ _ hmem (Or.inr ⟨ℓ, rfl, hcl⟩)
      rw [hB] at h
      obtain ⟨σ', h'⟩ := acProposal_payload _ _ hr m h
      rw [← tickMid_one, ← state_one] at h'
      have hp := pos_of_ne_tick hcall.2 (fun ℓ' h'' => by
        cases h''; rw [hcl]; exact fun h => by cases h)
      have hσ := slotOK _ σ' m h'
      subst hσ
      exact hnot (pool_mono (by omega) _ h')
    · exact ⟨ℓ, hcall, by rw [hem]; exact h⟩
  · rw [ACInterface.step, SAPool.acToFG_pool] at hhold; exact absurd hhold hnot

/-- A signing cut is followed by its `on_attestation`, at the same time. -/
theorem sign_next {i : Nat} {a : FG.Att sp2.n} (h : (tickRun N2 dg2).SignAt v0 i a) :
    (tickRun N2 dg2).AttCallAt v0 (i + 1) a ∧
      (tickRun N2 dg2).time (i + 1) = (tickRun N2 dg2).time i := by
  obtain ⟨C, hc⟩ := h
  obtain ⟨hk, he⟩ := tickRun_label_get hc.2
  have hn := onTick_sign_next (A := N2) (dg := dg2) v0 _ _ 0 (k := i % 8) (C := C) (a := a)
    (by change (tickCuts N2 dg2 (i / 8))[i % 8]? = _; rw [List.getElem?_eq_getElem hk, he])
  have hlen := (List.getElem?_eq_some_iff.1 hn).1
  have hl7 := tickCuts_length N2 dg2 (i / 8)
  have hq : (i + 1) / 8 = i / 8 := by
    change i % 8 + 1 < (tickCuts N2 dg2 (i / 8)).length at hlen; omega
  have hr : (i + 1) % 8 = i % 8 + 1 := by
    change i % 8 + 1 < (tickCuts N2 dg2 (i / 8)).length at hlen; omega
  refine ⟨⟨rfl, ?_⟩, by rw [tickRun_time, tickRun_time, hq]⟩
  rw [tickRun_label, hq, hr]
  exact hn

/-! ## `Sync` and `Sleepy` -/

theorem tr2_lastWake (y : Fin sp2.n) : ∀ k, tr2.lastWake y k = ⊥
  | 0 => by simp [RunTrace.lastWake, tr2_no_restart]
  | k + 1 => by simp [RunTrace.lastWake, tr2_no_restart, tr2_lastWake y k]

theorem tr2_deadline (y : Fin sp2.n) (k : Nat) (τ Δ' : Time) :
    tr2.deadline y k τ Δ' = τ + Δ' := by
  simp only [RunTrace.deadline, tr2_lastWake]
  rfl

/-- Cuts at a later time come later. -/
theorem lt_of_time {i j : Nat} (h : tr2.time i < tr2.time j) : i < j := by
  change ((i / 8 : Nat) : Int) < ((j / 8 : Nat) : Int) at h
  have : i / 8 < j / 8 := by exact_mod_cast h
  omega

theorem eq_w0_of_isCall {y : Fin sp2.n} {j : Nat} (h : tr2.IsCall y j) : y = w0 := by
  obtain ⟨c, hc⟩ := h
  exact eq_v0_of_callAt (tr2_callAt.1 hc)

/-- **`Sync` holds on the run** for every window, relay window and effective send time
`eff τ ≥ τ`, with `Δ_F = 1`. -/
theorem tr2_syncOn (W Wr : Time → Prop) (eff : Time → Time) (heff : ∀ τ, τ ≤ eff τ) :
    tr2.SyncOn Set.univ 1 W Wr eff where
  deltaF := one_pos
  delta_le := le_rfl
  message x _ i m h _ y _ j hj hdl := by
    obtain rfl := eq_w0_of_isCall hj
    obtain ⟨ℓ, hc, hh⟩ := h
    obtain rfl := eq_v0_of_callAt (tr2_callAt.1 hc)
    have h' : (tickRun N2 dg2).SendOrAdmitAt v0 i m := ⟨ℓ, hc, by rwa [tr2_state] at hh⟩
    rw [tr2_deadline, show sp2.toParams.Δ = 1 from rfl] at hdl
    have := heff (tr2.time i)
    have hij : i < j := lt_of_time (i := i) (j := j) (by linarith)
    refine ⟨i, hij.le, le_rfl, Or.inr (sendOrAdmit h'), ?_⟩
    rw [tr2_deadline, show sp2.toParams.Δ = 1 from rfl]; linarith
  block x _ i B h _ y _ j hj hdl := by
    obtain rfl := eq_w0_of_isCall hj
    rw [tr2_deadline, show sp2.toParams.Δ = 1 from rfl] at hdl
    have := heff (tr2.time i)
    have hij : i < j := lt_of_time (i := i) (j := j) (by linarith)
    have hB : tr2.BlockCallAt v0 i B := by
      rcases h with h | h
      · rw [eq_v0_of_callAt (tr2_callAt.1 h)] at h; exact ⟨true, h⟩
      · obtain ⟨⟨acc, hc⟩, -⟩ := h
        rw [eq_v0_of_callAt (tr2_callAt.1 hc)] at hc; exact ⟨acc, hc⟩
    refine ⟨i, hij.le, le_rfl, hB, ?_⟩
    rw [tr2_deadline, show sp2.toParams.Δ = 1 from rfl]; linarith
  relay x _ i B h _ y _ j hj hdl _ := by
    obtain rfl := eq_w0_of_isCall hj
    rw [tr2_deadline, show sp2.toParams.Δ = 1 from rfl] at hdl
    have := heff (tr2.time i)
    have hij : i < j := lt_of_time (i := i) (j := j) (by linarith)
    refine ⟨i, hij.le, ?_, ?_⟩
    · rw [eq_v0_of_callAt (tr2_callAt.1 h)] at h; exact h
    · rw [tr2_deadline, show sp2.toParams.Δ = 1 from rfl]; linarith
  attestation x _ i a h _ y _ j hj hdl := by
    obtain rfl := eq_w0_of_isCall hj
    rw [tr2_deadline] at hdl
    have := heff (tr2.time i)
    have hij : i < j := lt_of_time (i := i) (j := j) (by linarith)
    rcases h with ⟨C, hc⟩ | ⟨ℓ, hcall, hnot, hin⟩
    · obtain rfl := eq_v0_of_callAt (tr2_callAt.1 hc)
      obtain ⟨hatt, ht⟩ := sign_next ⟨C, hc⟩
      have ht' : tr2.time (i + 1) = tr2.time i := ht
      have hij' : i + 1 < j := lt_of_time (i := i + 1) (j := j) (by rw [ht']; linarith)
      refine ⟨i + 1, hij'.le, Or.inl hatt, ?_⟩
      rw [tr2_deadline, ht']; linarith
    · obtain rfl := eq_v0_of_callAt (tr2_callAt.1 hcall)
      rw [tr2_state] at hnot
      have hle : i ≤ j := hij.le
      have hdl' : tr2.time i < tr2.deadline v0 i (eff (tr2.time i)) 1 := by
        rw [tr2_deadline]; linarith
      rcases cutStep_atts N2 (tickRun_cutStep_v0 (tr2_callAt.1 hcall)) a hin with
        h | ⟨B, hB, ha⟩ | hB
      · exact absurd h hnot
      · cases hB
        exact ⟨i, hle, Or.inr ⟨B, hcall, ha⟩, hdl'⟩
      · cases hB
        exact ⟨i, hle, Or.inl hcall, hdl'⟩

/-- `f = 0 < h_t = 1` at every time `t ≥ 0`: `w0` is awake and joined, `w1` asleep. -/
theorem tr2_faultBound {t : Time} (ht : 0 ≤ t) : tr2.FaultBound Set.univ t := by
  unfold RunTrace.FaultBound RunTrace.honestAwakeJoined
  have : {y | y ∈ (Set.univ : Set (Fin sp2.n)) ∧ tr2.awake y t ∧ tr2.JoinedAt y t} =
      {w0} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and, Set.mem_singleton_iff]
    exact ⟨fun h => h.1.1, fun h => ⟨⟨h, ht⟩, joinedAt y t⟩⟩
  rw [this, Set.compl_univ, Set.ncard_empty, Set.ncard_singleton]
  exact one_pos

/-- (a) **`Sleepy` holds on the run** (with `Δ_F = 1`). -/
theorem tr2_sleepy : tr2.SleepyRun Set.univ 1 := by
  refine ⟨tr2_syncOn _ _ id (fun _ => le_rfl), fun s =>
    ⟨tr2_faultBound ?_, tr2_faultBound ?_, tr2_faultBound ?_⟩⟩
  · change (0 : Int) ≤ 4 * (s : Int); positivity
  · change (0 : Int) ≤ 4 * (s : Int) + 1; positivity
  · change (0 : Int) ≤ 4 * (s : Int) + 2 * 1; positivity

/-! ## A proposal at every slot -/

/-- The Goldilocks node's AC meets requirements 1–5. -/
theorem n2_requirements : N2.Requirements :=
  have h := SA.interface_requirements sp2 (List (FG.Att sp2.n)) ro2
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, SA.proposal_payload_valid sp2 _ ro2⟩

theorem slotOf_ts (s : Nat) : sp2.toParams.slotOf (sp2.ts s) = s :=
  SA.slot_of_mem sp2 s le_rfl ((SA.ts_lt_iff sp2).2 (by omega))

theorem ts_eq (s : Nat) : sp2.ts s = (((4 * s : Nat) : Int)) := by
  simp only [SAParams.ts]; push_cast; ring

/-- (a) **A proposal at every slot `s ≥ 1`**: `w0` processes its own block `B` of slot `s` at
cut `8·t_s + 2`, joined there. -/
theorem tr2_proposesAt (s : Nat) (hs : 1 ≤ s) :
    ∃ B, tr2.ProposesAt w0 (8 * (4 * s) + 2) B ∧ B.slot = s := by
  have hrun := asleepRun_goldilocksRun
  have hnc := dg2_noColl tr2
  set t : Nat := 4 * s with ht
  have hg : tr2.GroupAt (fun _ => w0) dg2 w0 (8 * t) (t : Int) (.tick 0) :=
    asleepRun_groupAt.2 (tickRun_groupAt_v0 t)
  have hts : ((t : Nat) : Int) = sp2.ts s := (ts_eq s).symm
  have hslot : sp2.toParams.slotOf ((t : Nat) : Int) = s := by rw [hts]; exact slotOf_ts s
  have hP : Node.Proposes (fun _ => w0) w0 ((t : Nat) : Int) :=
    ⟨by rw [hslot]; exact hs, by rw [hslot, hts]; rfl, rfl⟩
  have hjoin : SA.joined sp2 (Node.tickStep (fun _ => w0) dg2 w0 (tr2.state w0 (8 * t))
      ((t : Nat) : Int) 0 .acTick).1.ac ((t : Nat) : Int) := by
    unfold SA.joined
    have : (Node.tickStep (fun _ => w0) dg2 w0 (tr2.state w0 (8 * t)) ((t : Nat) : Int) 0
        .acTick).1.ac.restartTime = ⊥ := by
      change ((N2).step v0 _ _ _ .tick).1.restartTime = ⊥
      rw [SA.step_restartTime v0 _ _ _ _ (by intro h; cases h), tr2_state, restartTime_bot]
    rw [this]; exact bot_le
  obtain ⟨d, pay, hr⟩ : ∃ d pay, (Node.acProposal (Node.tickStep (fun _ => w0) dg2 w0
      (tr2.state w0 (8 * t)) ((t : Nat) : Int) 0 .acTick).1 ((t : Nat) : Int)).2.2 =
        some (d, pay) := by
    change ∃ d pay, (SA.acProposal sp2 _ _ _).2 = some (d, pay)
    unfold SA.acProposal
    simp only [hjoin, not_true_eq_false, ↓reduceIte]
    exact ⟨_, _, rfl⟩
  obtain ⟨hacc, htk⟩ := Healing.own_block_accepted hrun.toLocalRun n2_requirements dg2_genesis
    hnc (Set.mem_univ w0) hg hP hr
  refine ⟨_, ⟨⟨⟨true, hacc⟩, ?_⟩, rfl, ?_⟩, hslot⟩
  · change (8 * t + 2) % 8 ≠ 0; omega
  · rw [htk]; change ((t : Nat) : Int) = sp2.toParams.slotTime (sp2.toParams.slotOf _)
    rw [hslot, hts]; rfl

end Consensus.Goldilocks.Witness.Two

end
