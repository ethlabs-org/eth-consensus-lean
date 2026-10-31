module
public import ConsensusLeanTest.GoldilocksTickRun
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Final
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
@[expose] public section

/-! # A one-validator run of the Goldilocks node: the regime premises are consistent

Non-vacuity of the regime premises (consensus-lean#69, the follow-up recorded in #87): a
`GoldilocksRun` meeting the healing and pattern premises of R.3, R.4, R.6, node O.1 and C1.3. With
one validator (`n = 1`, `f = 0`) this shows the premises **consistent**, not met with faults (a
witness with a faulty validator, e.g. `n = 4`, `f = 1` silent, is a follow-up).

* **The tick run** (`ConsensusLeanTest/GoldilocksTickRun`; `tickRun`, for any node AC `A` with
  `n = 1`, `Δ = 1`): the validator is awake at every time `t ≥ 0` and ticks there with input `0`;
  nothing else happens. Its node states are the handler's (`Node.exec`) folded over the ticks; the
  cuts of the tick of time `t` are at the indices `8t, 8t + 1, …` (a tick makes at most seven cuts,
  `onTick_length`), the rest of each block of eight unlabelled under its own event id.
  (a) `tickRun_localRun`: it is a `Node.LocalRun` (own votes count as processed through their
  emission, own blocks and attestations are processed inside the tick, so no delivery is needed);
  the attestation pool holds only attestations the validator signed earlier (`tickRun_pool`).
* **The Goldilocks node** (`One`: `goldilocksNode` with `k = 2`, `δ_t = 2`, `t_s = 4s`, a
  collision-free digest `dg1`): (a) `tickRun_goldilocksRun`: the tick run is a `GoldilocksRun` (the
  vote pool holds only votes the validator emitted earlier, `tickRun_votes`, so carried votes are
  unforgeable); (a) `tickRun_syncOn`, `tickRun_healthy`, `tickRun_catch`, `tickRun_hsShared`:
  `Sync` for every window, `Healthy(g)`, `Catch(κ)` and the HS shared premises hold on it; (a) a
  ready proposal at every slot `s ≥ 1` (`tickRun_readyProposal`) and `Prop⁺(G_p)` for `G_p ≥ 4Δ`
  (`tickRun_propPlus`).
* **The regime premises.** Here `tickRun_healedPremises`, `tickRun_patternPremises` and
  `tickRun_finalPremises` reduce `HealedPremises`, `PatternPremises` and `FinalPremises` to the
  reset (`IsReset`), H.3 (c)'s bridge (`BridgeAt`) and `UPat(1, M)`. Those three facts are proved
  for this run in `ConsensusLeanTest/GoldilocksWitnessRun` (`tickRun_isReset`, with `a_z = aZ g`;
  `tickRun_bridgeAt`; `tickRun_upat`, over `GoldilocksWitnessChain` and `GoldilocksWitnessTicks`),
  so the premises hold with no hypothesis left beyond the parameter bounds: (a)
  `healedPremises_tickRun`, `patternPremises_tickRun`, `finalPremises_tickRun` (there). Caveat:
  `BridgeAt`'s `Geo` part holds vacuously here (`not_inSettledPhase`: the own block, accepted at
  `t_p` between `ac_proposal` and the vote, raises `h_max`, so no proposal and its votes lie in one
  settled phase); the witness does not exercise `Geo`. -/


namespace Consensus.Goldilocks.Witness

open Node

/-! ## The Goldilocks node with one validator -/

namespace One

open SA

/-- The shared parameters: one validator, `Δ = 1`, `t_s = 4s`, genesis root `0`, `δ_t = 2`. -/
abbrev P1 : Params where
  n := 1
  hn := le_rfl
  Δ := 1
  hΔ := one_pos
  slotTime := fun s => 4 * (s : Int)
  slotTime_zero := by simp
  slotTime_strictMono := fun a b h => by change 4 * (a : Int) < 4 * (b : Int); omega
  slotTime_public := fun _ => one_dvd _
  genesisRoot := 0
  δt := 2

/-- The SA parameters: `P1` with `k = 2`. -/
abbrev sp1 : SAParams where
  toParams := P1
  slotTime_eq := fun s => by change 4 * (s : Int) = 4 * 1 * s; omega
  k := 2
  two_le_k := le_rfl

/-- A replay order (never used: nobody restarts). -/
noncomputable abbrev ro1 : ReplayOrder sp1 (List (FG.Att sp1.n)) := ReplayOrder.choice sp1

/-- The node: the Goldilocks SA with these parameters. -/
noncomputable abbrev N1 : NodeAC sp1.toParams := goldilocksNode sp1 ro1

instance (n : Nat) : Countable (FG.Att n) :=
  Function.Injective.countable (f := fun a : FG.Att n => (a.val, a.h, a.T, a.timeout, a.fin))
    (by rintro ⟨⟩ ⟨⟩ h; simp_all)

instance (n : Nat) : Countable (Vote n) :=
  Function.Injective.countable (f := fun v : Vote n => (v.val, v.slot, v.head))
    (by rintro ⟨⟩ ⟨⟩ h; simp_all)

/-- The content of a block (what its root digests). -/
abbrev Content := Option Nat × Nat × Nat × List (FG.Att sp1.n) × Payload sp1.n

/-- An injective code of block contents. -/
noncomputable def code : Content → Nat := (Countable.exists_injective_nat Content).choose

theorem code_injective : Function.Injective code :=
  (Countable.exists_injective_nat Content).choose_spec

/-- The genesis content. -/
def genContent : Content := (none, 0, 0, [], ([], []))

open Classical in
/-- A collision-free digest whose value at the genesis content is the genesis root `0`. -/
noncomputable def dg1 : Digest (List (FG.Att sp1.n)) (Payload sp1.n) := fun p s x a q =>
  if (p, s, x, a, q) = genContent then 0 else code (p, s, x, a, q) + 1

theorem dg1_injective {p s x a q p' s' x' a' q'} (h : dg1 p s x a q = dg1 p' s' x' a' q') :
    (p, s, x, a, q) = ((p', s', x', a', q') : Content) := by
  unfold dg1 at h
  split_ifs at h with h₁ h₂ h₃ <;> first
    | exact h₁.trans h₂.symm
    | exact code_injective (by omega)

theorem dg1_genesis : (sp1.toParams.genesisBlock N1.genesisPayload).RootOk dg1 := by
  change (0 : Nat) = dg1 none 0 0 [] ([], [])
  unfold dg1; simp [genContent]

theorem dg1_noColl (tr : RunTrace N1) : Compose.NoCollRun dg1 tr := by
  intro B _ C _ h
  have := dg1_injective h
  simp only [Prod.mk.injEq] at this
  exact this

/-- The votes `ac_proposal` puts in the payload are in the pool. -/
theorem acProposal_payload (st : NodeState N1) (t : Time) {d : DutyHead sp1.n _ (Payload sp1.n)}
    {p : Payload sp1.n} (h : (Node.acProposal st t).2.2 = some (d, p)) :
    ∀ v ∈ p.1, ∃ σ, v ∈ st.ac.pool σ := by
  intro v hv
  change (SA.acProposal sp1 st.ac (frame st) t).2 = some (d, p) at h
  unfold SA.acProposal at h
  split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  simp only [voteViewList, List.mem_filter] at hv
  unfold SAState.poolAt at hv
  split_ifs at hv
  · simp at hv
  · exact ⟨_, hv.1⟩

/-- The support votes `ac_proposal` puts in the payload are in the pool. -/
theorem acProposal_support (st : NodeState N1) (t : Time) {d : DutyHead sp1.n _ (Payload sp1.n)}
    {p : Payload sp1.n} (h : (Node.acProposal st t).2.2 = some (d, p)) :
    ∀ v ∈ p.2, ∃ σ, v ∈ st.ac.pool σ := by
  intro v hv
  change (SA.acProposal sp1 st.ac (frame st) t).2 = some (d, p) at h
  unfold SA.acProposal at h
  split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  simp only [voteViewList, List.mem_filter] at hv
  unfold SAState.poolAt at hv
  split_ifs at hv
  · simp at hv
  · exact ⟨_, hv.1.1⟩

/-- The validator's position-`≥ 1` cuts: a cut that is not its tick's `ac_on_tick`. -/
theorem pos_of_ne_tick {i : Nat} {c : Cut N1} (h : (tickRun N1 dg1).label i = some c)
    (hne : ∀ ℓ : ACLabel N1, c = .ac ℓ → ℓ.call ≠ .tick) : 1 ≤ i % 8 := by
  by_contra h0
  have := tickRun_label_zero h (by omega)
  exact hne _ this rfl

/-- Every vote in the pool before cut `i` was emitted by the validator at an earlier cut. -/
theorem tickRun_votes :
    ∀ i σ, ∀ v ∈ ((tickRun N1 dg1).state v0 i).ac.pool σ,
      ∃ j < i, (tickRun N1 dg1).EmitAt v0 j v := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro σ v hv
    rcases i with _ | i
    · simp [Trace.state, tickRun, Node.init, SAState.initial] at hv
    simp only [Trace.state] at hv
    split_ifs at hv with hl
    · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hl.2
      have hcall : (tickRun N1 dg1).CallAt v0 i c := ⟨hl.1, hc⟩
      have hstep := cutStep_ac (tickRun_cutStep rfl hcall)
      have old : v ∈ ((tickRun N1 dg1).state v0 i).ac.pool σ →
          ∃ j < i + 1, (tickRun N1 dg1).EmitAt v0 j v := fun h => by
        obtain ⟨j, hj, he⟩ := ih i (by omega) σ v h
        exact ⟨j, by omega, he⟩
      have hmem := tickRun_label_mem hc
      cases c with
      | fg ℓ => exact old (hstep.1 ℓ rfl ▸ hv)
      | ac ℓ =>
        have hs := hstep.2 ℓ rfl
        have hac : ((tickRun N1 dg1).post i).ac = (ACInterface.step N1 v0
            ((tickRun N1 dg1).state v0 i).ac ℓ.frame ((tickRun N1 dg1).time i) ℓ.call).1 :=
          (congrArg Prod.fst hs).symm
        have hem : ℓ.emits = (ACInterface.step N1 v0
            ((tickRun N1 dg1).state v0 i).ac ℓ.frame ((tickRun N1 dg1).time i) ℓ.call).2 :=
          (congrArg Prod.snd hs).symm
        rw [hac] at hv
        have emitted : (∃ e ∈ ℓ.emits, e.msg = v) → ∃ j < i + 1, (tickRun N1 dg1).EmitAt v0 j v :=
          fun ⟨e, he, hm⟩ => ⟨i, by omega, ℓ, hcall, e, he, hm⟩
        rcases onTick_ac_call N1 dg1 _ _ _ _ hmem with hcl | hcl | ⟨B, hcl⟩ | hcl <;>
          rw [hcl] at hv hem
        · rcases SAPool.acOnTick_pool sp1 v0 _ _ _ σ v hv with h | h
          · exact old h
          · exact emitted (by rw [hem]; exact h)
        · exact old (by rw [ACInterface.step, SAPool.acProposal_pool] at hv; exact hv)
        · rcases SAPool.acOnBlock_pool sp1 v0 _ _ _ B σ v hv with h | h | h
          · exact old h
          · obtain ⟨d, p, hr, hB⟩ := onTick_block_made N1 dg1 _ _ _ _ hmem (Or.inr ⟨ℓ, rfl, hcl⟩)
            rw [hB] at h
            obtain ⟨σ', h'⟩ := acProposal_payload _ _ hr v h
            rw [← tickMid_one, ← show ((tickRun N1 dg1).state v0 (8 * (i / 8) + 1)) =
              tickMid N1 dg1 (i / 8) 1 by
                rw [tickRun_state rfl]; congr 1 <;> omega] at h'
            have hp := pos_of_ne_tick hc (fun ℓ' h'' => by
              cases h''; rw [hcl]; exact fun h => by cases h)
            obtain ⟨j, hj, he⟩ := ih (8 * (i / 8) + 1) (by omega) σ' v h'
            exact ⟨j, by omega, he⟩
          · exact emitted (by rw [hem]; exact h)
        · exact old (by rw [ACInterface.step, SAPool.acToFG_pool] at hv; exact hv)
    · obtain ⟨j, hj, he⟩ := ih i (by omega) σ v hv
      exact ⟨j, by omega, he⟩

/-- **The one-validator tick run is a Goldilocks run.** -/
theorem tickRun_goldilocksRun :
    GoldilocksRun (sp := sp1) (ro := ro1) (fun _ => v0) dg1 Set.univ (tickRun N1 dg1) where
  toLocalRun := tickRun_localRun rfl rfl _
  genesis_root_ok := dg1_genesis
  carried_vote_unforgeable y _ i B hB v hv _ := by
    obtain ⟨acc, hc⟩ := hB
    obtain ⟨d, p, hr, hB⟩ := onTick_block_made N1 dg1 _ _ _ _ (tickRun_label_mem hc.2)
      (Or.inl ⟨acc, rfl⟩)
    rw [hB] at hv
    obtain ⟨σ', h'⟩ := acProposal_payload _ _ hr v hv
    rw [← tickMid_one, ← show ((tickRun N1 dg1).state v0 (8 * (i / 8) + 1)) =
      tickMid N1 dg1 (i / 8) 1 by rw [tickRun_state rfl]; congr 1 <;> omega] at h'
    have hp := pos_of_ne_tick hc.2 (fun ℓ h => by cases h)
    obtain ⟨j, hj, he⟩ := tickRun_votes (8 * (i / 8) + 1) σ' v h'
    rw [eq_v0 rfl v.val]
    exact ⟨j, by omega, he⟩

/-- The pool only grows along the tick run. -/
theorem tickRun_pool_mono {i i' : Nat} (h : i ≤ i') (σ : Nat) :
    ((tickRun N1 dg1).state v0 i).ac.pool σ ⊆ ((tickRun N1 dg1).state v0 i').ac.pool σ := by
  induction i', h using Nat.le_induction with
  | base => exact fun _ h => h
  | succ i' _ ih =>
    refine List.Subset.trans ih ?_
    intro v hv
    simp only [Trace.state]
    split_ifs with hl
    · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hl.2
      have hcall : (tickRun N1 dg1).CallAt v0 i' c := ⟨hl.1, hc⟩
      have hstep := cutStep_ac (tickRun_cutStep rfl hcall)
      cases c with
      | fg ℓ => rw [hstep.1 ℓ rfl]; exact hv
      | ac ℓ =>
        have hac : ((tickRun N1 dg1).post i').ac = (ACInterface.step N1 v0
            ((tickRun N1 dg1).state v0 i').ac ℓ.frame ((tickRun N1 dg1).time i') ℓ.call).1 :=
          (congrArg Prod.fst (hstep.2 ℓ rfl)).symm
        rw [hac]
        rcases onTick_ac_call N1 dg1 _ _ _ _ (tickRun_label_mem hc) with
          hcl | hcl | ⟨B, hcl⟩ | hcl <;>
          rw [hcl]
        · exact SAPool.acOnTick_pool_mono sp1 v0 _ _ _ σ hv
        · rw [ACInterface.step, SAPool.acProposal_pool]; exact hv
        · exact SAPool.acOnBlock_pool_mono sp1 v0 _ _ _ B σ hv
        · rw [ACInterface.step, SAPool.acToFG_pool]; exact hv
    · exact hv

/-- No wake in the tick run. -/
theorem tickRun_lastWake (y : Fin sp1.n) : ∀ k, (tickRun N1 dg1).lastWake y k = ⊥
  | 0 => by simp [RunTrace.lastWake, tickRun_no_restart]
  | k + 1 => by simp [RunTrace.lastWake, tickRun_no_restart, tickRun_lastWake y k]

theorem tickRun_deadline (y : Fin sp1.n) (k : Nat) (τ Δ' : Time) :
    (tickRun N1 dg1).deadline y k τ Δ' = τ + Δ' := by
  simp only [RunTrace.deadline, tickRun_lastWake]
  rfl

/-- In the tick run, pool `σ` holds votes of slot `σ`. -/
theorem tickRun_slotOK (i : Nat) : SAPool.SlotOK sp1 ((tickRun N1 dg1).state v0 i).ac := by
  induction i with
  | zero => intro σ w hw; simp [Trace.state, tickRun, Node.init, SAState.initial] at hw
  | succ i ih =>
    simp only [Trace.state]
    split_ifs with hl
    · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hl.2
      have hcall : (tickRun N1 dg1).CallAt v0 i c := ⟨hl.1, hc⟩
      have hstep := cutStep_ac (tickRun_cutStep rfl hcall)
      cases c with
      | fg ℓ => rw [hstep.1 ℓ rfl]; exact ih
      | ac ℓ =>
        have hac : ((tickRun N1 dg1).post i).ac = (ACInterface.step N1 v0
            ((tickRun N1 dg1).state v0 i).ac ℓ.frame ((tickRun N1 dg1).time i) ℓ.call).1 :=
          (congrArg Prod.fst (hstep.2 ℓ rfl)).symm
        rw [hac]
        rcases onTick_ac_call N1 dg1 _ _ _ _ (tickRun_label_mem hc) with
          hcl | hcl | ⟨B, hcl⟩ | hcl <;>
          rw [hcl]
        · exact SAPool.acOnTick_slot sp1 v0 _ _ _ ih
        · exact SAPool.slot_of_pool_eq sp1 (SAPool.acProposal_pool sp1 _ _ _) ih
        · exact SAPool.acOnBlock_slot sp1 v0 _ _ _ B ih
        · exact SAPool.slot_of_pool_eq sp1 (SAPool.acToFG_pool sp1 _ _ _) ih
    · exact ih

/-- Every AC message the validator sends or admits, it emits at that cut. -/
theorem tickRun_sendOrAdmit {i : Nat} {m : Vote sp1.n}
    (h : (tickRun N1 dg1).SendOrAdmitAt v0 i m) : (tickRun N1 dg1).EmitAt v0 i m := by
  obtain ⟨ℓ, hcall, h | ⟨-, hnot, hhold⟩⟩ := h
  · exact ⟨ℓ, hcall, h⟩
  change m ∉ ((tickRun N1 dg1).state v0 i).ac.pool m.slot at hnot
  change m ∈ ((tickRun N1 dg1).post i).ac.pool m.slot at hhold
  have hs := (cutStep_ac (tickRun_cutStep rfl hcall)).2 ℓ rfl
  have hac : ((tickRun N1 dg1).post i).ac = (ACInterface.step N1 v0
      ((tickRun N1 dg1).state v0 i).ac ℓ.frame ((tickRun N1 dg1).time i) ℓ.call).1 :=
    (congrArg Prod.fst hs).symm
  have hem : ℓ.emits = (ACInterface.step N1 v0
      ((tickRun N1 dg1).state v0 i).ac ℓ.frame ((tickRun N1 dg1).time i) ℓ.call).2 :=
    (congrArg Prod.snd hs).symm
  rw [hac] at hhold
  have hmem := tickRun_label_mem hcall.2
  rcases onTick_ac_call N1 dg1 _ _ _ _ hmem with hcl | hcl | ⟨B, hcl⟩ | hcl <;>
    rw [hcl] at hhold hem
  · rcases SAPool.acOnTick_pool sp1 v0 _ _ _ _ m hhold with h | h
    · exact absurd h hnot
    · exact ⟨ℓ, hcall, by rw [hem]; exact h⟩
  · rw [ACInterface.step, SAPool.acProposal_pool] at hhold; exact absurd hhold hnot
  · rcases SAPool.acOnBlock_pool sp1 v0 _ _ _ B _ m hhold with h | h | h
    · exact absurd h hnot
    · exfalso
      obtain ⟨d, p, hr, hB⟩ := onTick_block_made N1 dg1 _ _ _ _ hmem (Or.inr ⟨ℓ, rfl, hcl⟩)
      rw [hB] at h
      obtain ⟨σ', h'⟩ := acProposal_payload _ _ hr m h
      rw [← tickMid_one, ← show ((tickRun N1 dg1).state v0 (8 * (i / 8) + 1)) =
        tickMid N1 dg1 (i / 8) 1 by rw [tickRun_state rfl]; congr 1 <;> omega] at h'
      have hp := pos_of_ne_tick hcall.2 (fun ℓ' h'' => by
        cases h''; rw [hcl]; exact fun h => by cases h)
      have hσ := tickRun_slotOK _ σ' m h'
      subst hσ
      exact hnot (tickRun_pool_mono (by omega) _ h')
    · exact ⟨ℓ, hcall, by rw [hem]; exact h⟩
  · rw [ACInterface.step, SAPool.acToFG_pool] at hhold; exact absurd hhold hnot

/-- A signing cut of the tick run is followed by its `on_attestation`, at the same time. -/
theorem tickRun_sign_next {i : Nat} {a : FG.Att sp1.n} (h : (tickRun N1 dg1).SignAt v0 i a) :
    (tickRun N1 dg1).AttCallAt v0 (i + 1) a ∧
      (tickRun N1 dg1).time (i + 1) = (tickRun N1 dg1).time i := by
  obtain ⟨C, hc⟩ := h
  obtain ⟨hk, he⟩ := tickRun_label_get hc.2
  have hn := onTick_sign_next (A := N1) (dg := dg1) v0 _ _ 0 (k := i % 8) (C := C) (a := a)
    (by change (tickCuts N1 dg1 (i / 8))[i % 8]? = _; rw [List.getElem?_eq_getElem hk, he])
  have hlen := (List.getElem?_eq_some_iff.1 hn).1
  have hl7 := tickCuts_length N1 dg1 (i / 8)
  have hq : (i + 1) / 8 = i / 8 := by
    change i % 8 + 1 < (tickCuts N1 dg1 (i / 8)).length at hlen; omega
  have hr : (i + 1) % 8 = i % 8 + 1 := by
    change i % 8 + 1 < (tickCuts N1 dg1 (i / 8)).length at hlen; omega
  refine ⟨⟨rfl, ?_⟩, by rw [tickRun_time, tickRun_time, hq]⟩
  rw [tickRun_label, hq, hr]
  exact hn

/-- Cuts at a later time come later. -/
theorem tickRun_lt_of_time {i j : Nat} (h : (tickRun N1 dg1).time i < (tickRun N1 dg1).time j) :
    i < j := by
  change ((i / 8 : Nat) : Int) < ((j / 8 : Nat) : Int) at h
  have : i / 8 < j / 8 := by exact_mod_cast h
  omega

/-- **`Sync` holds on the tick run** for every window, relay window and effective send time
`eff τ ≥ τ`, with `Δ_F = 1`. -/
theorem tickRun_syncOn (W Wr : Time → Prop) (eff : Time → Time) (heff : ∀ τ, τ ≤ eff τ) :
    (tickRun N1 dg1).SyncOn Set.univ 1 W Wr eff where
  deltaF := le_rfl
  message x _ i m h _ y _ j _ hdl := by
    rw [eq_v0 rfl x] at h
    rw [eq_v0 rfl y] at hdl ⊢
    rw [tickRun_deadline, show sp1.toParams.Δ = 1 from rfl] at hdl
    have := heff ((tickRun N1 dg1).time i)
    have hij : i < j := tickRun_lt_of_time (i := i) (j := j) (by linarith)
    refine ⟨i, hij.le, le_rfl,
      Or.inr (tickRun_sendOrAdmit h), ?_⟩
    rw [tickRun_deadline, show sp1.toParams.Δ = 1 from rfl]; linarith
  block x _ i B h _ y _ j _ hdl := by
    rw [eq_v0 rfl y] at hdl ⊢
    rw [tickRun_deadline, show sp1.toParams.Δ = 1 from rfl] at hdl
    have := heff ((tickRun N1 dg1).time i)
    have hij : i < j := tickRun_lt_of_time (i := i) (j := j) (by linarith)
    have hB : (tickRun N1 dg1).BlockCallAt v0 i B := by
      rcases h with h | h
      · exact ⟨true, by rw [eq_v0 rfl x] at h; exact h⟩
      · rw [eq_v0 rfl x] at h; exact h.1
    refine ⟨i, hij.le, le_rfl, hB, ?_⟩
    rw [tickRun_deadline, show sp1.toParams.Δ = 1 from rfl]; linarith
  relay x _ i B h _ y _ j _ hdl _ := by
    rw [eq_v0 rfl y] at hdl ⊢
    rw [tickRun_deadline, show sp1.toParams.Δ = 1 from rfl] at hdl
    have := heff ((tickRun N1 dg1).time i)
    have hij : i < j := tickRun_lt_of_time (i := i) (j := j) (by linarith)
    refine ⟨i, hij.le, ?_, ?_⟩
    · rw [eq_v0 rfl x] at h; exact h
    · rw [tickRun_deadline, show sp1.toParams.Δ = 1 from rfl]; linarith
  attestation x _ i a h _ y _ j _ hdl := by
    rw [eq_v0 rfl x] at h
    rw [eq_v0 rfl y] at hdl ⊢
    rw [tickRun_deadline] at hdl
    have := heff ((tickRun N1 dg1).time i)
    have hij : i < j := tickRun_lt_of_time (i := i) (j := j) (by linarith)
    rcases h with h | ⟨ℓ, hcall, hnot, hin⟩
    · obtain ⟨hatt, ht⟩ := tickRun_sign_next h
      have hij' : i + 1 < j := tickRun_lt_of_time (i := i + 1) (j := j) (by rw [ht]; linarith)
      refine ⟨i + 1, hij'.le, by rw [ht], Or.inl hatt, ?_⟩
      rw [tickRun_deadline, ht]; linarith
    · have hle : i ≤ j := hij.le
      have hdl' : (tickRun N1 dg1).time i < (tickRun N1 dg1).deadline v0 i (eff
          ((tickRun N1 dg1).time i)) 1 := by
        rw [tickRun_deadline]; linarith
      rcases cutStep_atts N1 (tickRun_cutStep rfl hcall) a hin with h | ⟨B, hB, ha⟩ | hB
      · exact absurd h hnot
      · cases hB
        exact ⟨i, hle, le_rfl, Or.inr ⟨B, hcall, ha⟩, hdl'⟩
      · cases hB
        exact ⟨i, hle, le_rfl, Or.inl hcall, hdl'⟩

/-! ## A ready proposal at every slot -/

/-- The Goldilocks node's AC meets requirements 1–5. -/
theorem n1_requirements : N1.Requirements :=
  have h := SA.interface_requirements sp1 (List (FG.Att sp1.n)) ro1
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, SA.proposal_payload_valid sp1 _ ro1⟩

/-- The validator never restarts, so its restart time stays `⊥`. -/
theorem tickRun_restartTime : ∀ i, ((tickRun N1 dg1).state v0 i).ac.restartTime = ⊥
  | 0 => rfl
  | i + 1 => by
    simp only [Trace.state]
    split_ifs with hl
    · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hl.2
      have hcall : (tickRun N1 dg1).CallAt v0 i c := ⟨hl.1, hc⟩
      have hstep := cutStep_ac (tickRun_cutStep rfl hcall)
      cases c with
      | fg ℓ => rw [hstep.1 ℓ rfl]; exact tickRun_restartTime i
      | ac ℓ =>
        have hac : ((tickRun N1 dg1).post i).ac = (ACInterface.step N1 v0
            ((tickRun N1 dg1).state v0 i).ac ℓ.frame ((tickRun N1 dg1).time i) ℓ.call).1 :=
          (congrArg Prod.fst (hstep.2 ℓ rfl)).symm
        rw [hac]
        refine (SA.step_restartTime v0 _ _ _ _ fun hr => ?_).trans (tickRun_restartTime i)
        exact tickRun_no_restart v0 i ⟨ℓ, hcall, hr⟩
    · exact tickRun_restartTime i

theorem slotOf_ts (s : Nat) : sp1.toParams.slotOf (sp1.ts s) = s :=
  SA.slot_of_mem sp1 s le_rfl ((SA.ts_lt_iff sp1).2 (by omega))

theorem ts_eq (s : Nat) : sp1.ts s = (((4 * s : Nat) : Int)) := by
  simp only [SAParams.ts]; push_cast; ring

/-- A block of the validator's tree before cut `j` has a slot at most `slot(time j)`. -/
theorem tree_slot_le {j : Nat} {X : SA.Blk sp1.n (List (FG.Att sp1.n))}
    (hX : X ∈ ((tickRun N1 dg1).state v0 j).fg.tree) :
    X.slot ≤ sp1.slot ((tickRun N1 dg1).time j) := by
  rcases Compose.tree_cases (tickRun_goldilocksRun).toLocalRun (Set.mem_univ v0) hX with
    rfl | ⟨k, hk, hacc⟩
  · exact Nat.zero_le _
  · exact ((tickRun_goldilocksRun.cutLaw v0 (Set.mem_univ _) k _ hacc).1).trans
      (SA.slot_mono sp1 (tickRun_goldilocksRun.time_nonneg k)
        (tickRun_goldilocksRun.time_mono hk.le))

/-- **A ready proposal at every slot `s ≥ 1`**: the own block of the tick of `t_s`, at cut
`8·t_s + 2`. -/
theorem tickRun_readyProposal (s : Nat) (hs : 1 ≤ s) :
    ∃ k B, Healing.ReadyProposal (tickRun N1 dg1) Set.univ (fun _ => v0) v0 k s B ∧
      k = 8 * (4 * s) + 2 := by
  have hrun := tickRun_goldilocksRun
  have hnc := dg1_noColl (tickRun N1 dg1)
  set t : Nat := 4 * s with ht
  have hg := tickRun_groupAt (A := N1) (dg := dg1) rfl t
  have hts : ((t : Nat) : Int) = sp1.ts s := (ts_eq s).symm
  have hslot : sp1.toParams.slotOf ((t : Nat) : Int) = s := by rw [hts]; exact slotOf_ts s
  have hP : Node.Proposes (fun _ => v0) (v0 : Fin sp1.n) ((t : Nat) : Int) :=
    ⟨by rw [hslot]; exact hs, by rw [hslot, hts]; rfl, rfl⟩
  -- `ac_proposal` returns a payload: the validator is joined
  have hjoin : SA.joined sp1 (Node.tickStep (fun _ => v0) dg1 v0
      ((tickRun N1 dg1).state v0 (8 * t))
      ((t : Nat) : Int) 0 .acTick).1.ac ((t : Nat) : Int) := by
    unfold SA.joined
    have : (Node.tickStep (fun _ => v0) dg1 v0
        ((tickRun N1 dg1).state v0 (8 * t)) ((t : Nat) : Int) 0
        .acTick).1.ac.restartTime = ⊥ := by
      change ((N1).step v0 _ _ _ .tick).1.restartTime = ⊥
      rw [SA.step_restartTime v0 _ _ _ _ (by intro h; cases h), tickRun_restartTime]
    rw [this]; exact bot_le
  obtain ⟨d, pay, hr⟩ : ∃ d pay, (Node.acProposal (Node.tickStep (fun _ => v0) dg1 v0
      ((tickRun N1 dg1).state v0 (8 * t)) ((t : Nat) : Int) 0 .acTick).1
      ((t : Nat) : Int)).2.2 = some (d, pay) := by
    change ∃ d pay, (SA.acProposal sp1 _ _ _).2 = some (d, pay)
    unfold SA.acProposal
    simp only [hjoin, not_true_eq_false, ↓reduceIte]
    exact ⟨_, _, rfl⟩
  obtain ⟨hacc, htk⟩ := Healing.own_block_accepted hrun.toLocalRun n1_requirements dg1_genesis
    hnc (Set.mem_univ v0) hg hP hr
  set B := Node.mkBlock dg1 v0 (Node.acProposal (Node.tickStep (fun _ => v0) dg1 v0
    ((tickRun N1 dg1).state v0 (8 * t)) ((t : Nat) : Int) 0 .acTick).1 ((t : Nat) : Int)).1.fg
    ((t : Nat) : Int) 0 d.head pay with hB
  have hBslot : B.slot = s := hslot
  refine ⟨8 * t + 2, B, ⟨Set.mem_univ _, rfl, ?_, ⟨⟨⟨true, hacc⟩, ?_⟩, rfl, ?_⟩, hBslot, ?_⟩, rfl⟩
  · intro k hk; exact absurd hk (tickRun_no_restart _ k)
  · change (8 * t + 2) % 8 ≠ 0; omega
  · rw [htk, hBslot]; exact hts
  · intro x hx hxs y _ j' hj'
    have hpool := acProposal_support _ _ hr x hx
    obtain ⟨σ, hσ⟩ := hpool
    have hmid : (Node.tickStep (fun _ => v0) dg1 v0
        ((tickRun N1 dg1).state v0 (8 * t)) ((t : Nat) : Int) 0
        .acTick).1 = (tickRun N1 dg1).state v0 (8 * t + 1) := by
      rw [tickRun_state_tick rfl v0 t, tickRun_state rfl v0 (8 * t + 1),
        show (8 * t + 1) / 8 = t by omega, show (8 * t + 1) % 8 = 1 by omega, tickMid_one]
      rfl
    rw [hmid] at hσ
    obtain ⟨jx, hjx, ℓ, hcall, e, he, hem⟩ := tickRun_votes (8 * t + 1) σ x hσ
    have hcAC : (tickRun N1 dg1).projAC.CallAt v0 jx ℓ := Compose.projAC_callAt.2 hcall
    have hrAC := (Compose.goldilocks_ac_projection sp1 ro1 dg1 Set.univ
      (tickRun N1 dg1) (fun _ => v0) hrun hnc).localRun
    obtain ⟨⟨Hd, hHdt, hHdr, -⟩, hjxt⟩ := Compose.cast_head_fcRoot hrAC (Set.mem_univ v0)
      ⟨hcAC, he⟩
    rw [Compose.frame_of_projAC hrun (Set.mem_univ v0) hcAC] at hHdt
    rw [hem] at hHdr hjxt
    have hslotHd := tree_slot_le hHdt.1
    have hΔ : sp1.Δ = 1 := rfl
    -- the vote was cast before `t_s`, so its head has a slot below `s`
    have hxs' : (x.slot : Int) = (s : Int) - 1 := by omega
    have htjx : (tickRun N1 dg1).time jx < sp1.ts (s : Int) := by
      have : sp1.ts (x.slot : Int) = sp1.ts (s : Int) - 4 := by
        rw [hxs']; simp only [SAParams.ts]; ring
      rw [this, hΔ] at hjxt
      change (tickRun N1 dg1).time jx ≤ _ at hjxt
      linarith
    have hsl : sp1.slot ((tickRun N1 dg1).time jx) < s := by
      by_contra hc
      have := (SA.ts_le_iff_le_slot sp1 (hrun.time_nonneg jx) (s : Int)).2 (by omega)
      linarith
    refine ⟨Hd, ?_, hHdr, by omega⟩
    have hj'jx : jx < j' := by
      by_contra hc
      have h1 := hrun.time_mono (show j' ≤ jx by omega)
      have h2 := hj'.1
      rw [hΔ] at h2
      linarith
    rw [eq_v0 rfl y]
    exact Compose.tree_mono hrun.toLocalRun (Set.mem_univ v0) hj'jx.le hHdt.1

/-- (a) **`Prop⁺(G_p)` holds on the tick run** for every `G_p ≥ 4Δ`: the next slot start after a
trigger has a ready proposal. -/
theorem tickRun_propPlus (g Gp : Time) (hGp : 4 ≤ Gp) :
    Healing.PropPlus (tickRun N1 dg1) Set.univ (fun _ => v0) g Gp := by
  intro τ hτ
  have h0 : 0 ≤ τ := le_trans (le_max_right g 0) hτ
  set s := sp1.slot τ + 1 with hs
  obtain ⟨k, B, hB, -⟩ := tickRun_readyProposal s (by omega)
  have hlt : τ < sp1.ts (s : Int) := by
    by_contra hc
    have := (SA.ts_le_iff_le_slot sp1 h0 (s : Int)).1 (not_lt.1 hc)
    omega
  have hle : sp1.ts (sp1.slot τ : Int) ≤ τ := (SA.ts_le_iff_le_slot sp1 h0 _).2 le_rfl
  refine ⟨s, k, B, by omega, hlt.le, ?_, hB⟩
  have : sp1.ts (s : Int) = sp1.ts (sp1.slot τ : Int) + 4 := by
    simp only [SAParams.ts, hs]; push_cast; ring
  change sp1.ts (s : Int) ≤ τ + Gp
  linarith

/-- (a) `Healthy(g)` holds on the tick run, for every `g` (with `Δ_F = 1`). -/
theorem tickRun_healthy (g : Time) : (tickRun N1 dg1).HealthyRun Set.univ 1 g :=
  ⟨tickRun_syncOn _ _ _ (fun τ => le_max_left τ g),
    fun _ _ t ht => (show (0 : Int) ≤ t from le_trans (le_max_right g 0) ht), by simp⟩

/-- (a) `Catch(κ)` holds on the tick run, for every `κ ≥ 0`. -/
theorem tickRun_catch (g κ : Time) (hκ : 0 ≤ κ) :
    Healing.CatchRun (tickRun N1 dg1) Set.univ g κ := by
  intro x _ i B hB hi y _ j hj _
  refine ⟨i, tickRun_lt_of_time (by linarith [hj.1]), ?_⟩
  rw [eq_v0 rfl x] at hB; rw [eq_v0 rfl y]; exact hB

/-- (a) The HS shared premises hold on the tick run, for every `g` (with `Δ_F = 1`). -/
theorem tickRun_hsShared (g : Time) : Healing.HSShared (tickRun N1 dg1) Set.univ dg1 g 1 where
  noColl := dg1_noColl _
  genesisRoot := dg1_genesis
  healthy := tickRun_healthy g
  noRestart _ _ k h := absurd h (tickRun_no_restart _ k)
  timeoutDelay := by decide

/-- **Non-vacuity of R.3's and R.6's healing premises, reduced to two facts of one run.** The
one-validator tick run (`n = 1`, `f = 0`, everyone awake, a tick at every time) is a Goldilocks
run (`tickRun_goldilocksRun`), and it meets outright the HS shared premises (`NoColl`, the
genesis root, `Healthy(g)`, no restart, the `δ_t` bound), `Catch(2Δ)`, `Prop⁺(G_p)` for
`G_p ≥ 4Δ` (`tickRun_propPlus`), `T_b ≥ 0` and `T ≥ T_heal`. The remaining fields of
`HealedPremises` are hypotheses here: the reset `a_z` (`IsReset`) and H.3 (c)'s bridge
(`BridgeAt`), facts about this run's attestations and AC invariant (consensus-lean#69, W3). With
`n = 1` and `f = 0` this shows the premises consistent, not met with faults. -/
theorem tickRun_healedPremises (g Gp a Tb T : Time) (hGp : 4 ≤ Gp)
    (hreset : Healing.IsReset (tickRun N1 dg1) Set.univ g a) (hTb : 0 ≤ Tb)
    (hbridge : Healing.BridgeAt (tickRun N1 dg1) Set.univ (fun _ => v0) g a Tb)
    (hT : Healing.T_heal sp1 g 1 Gp Tb ≤ T) :
    Regimes.HealedPremises (tickRun N1 dg1) Set.univ (fun _ => v0) dg1 g 1 Gp a Tb T :=
  ⟨tickRun_hsShared g, tickRun_catch g _ (by decide), tickRun_propPlus g Gp hGp, hreset, hTb,
    hbridge, hT⟩

/-- **Non-vacuity of node O.1's, C1.3's and R.4's pattern premises, reduced to one fact of one
run.** On the one-validator tick run, with `c_F = 2`, `k_F = 0` (so `c_F + k_F ≤ δ_t = 2`),
`W = 1`, `G_p ≥ 4Δ` and any `M ≥ M*`: the HS shared premises, `Catch(2Δ)`, `Prop⁺(G_p)`, the
window parameters and `W ≥ 1` hold outright; `UPat(1, M)` (a ready proposal at every slot `≥ 1`,
`tickRun_readyProposal`, with C1.2's retained inclusion) is a hypothesis here (W3). With `n = 1`
and `f = 0` this shows the premises consistent, not met with faults. -/
theorem tickRun_patternPremises (g Gp : Time) (M : Nat) (hGp : 4 ≤ Gp)
    (hpat : Healing.UPat (tickRun N1 dg1) Set.univ (fun _ => v0) g 1 M 2 0)
    (hM : Healing.Mstar sp1 1 Gp 2 0 ≤ M) :
    Healing.PatternPremises (tickRun N1 dg1) Set.univ (fun _ => v0) dg1 g 1 Gp 1 M 2 0 where
  shared := tickRun_hsShared g
  catchPremise := tickRun_catch g _ (by decide)
  prop := tickRun_propPlus g Gp hGp
  cF_lower := by decide
  cF_upper := by decide
  timeout := le_rfl
  one_le_W := le_rfl
  pattern := hpat
  long := hM

/-- **Non-vacuity of R.4's premises**, reduced to the facts of `tickRun_healedPremises` and
`tickRun_patternPremises` (with `T ≥ ḡ + T_rec`, arithmetic). -/
theorem tickRun_finalPremises (g Gp a Tb T : Time) (M : Nat) (hGp : 4 ≤ Gp)
    (hreset : Healing.IsReset (tickRun N1 dg1) Set.univ g a) (hTb : 0 ≤ Tb)
    (hbridge : Healing.BridgeAt (tickRun N1 dg1) Set.univ (fun _ => v0) g a Tb)
    (hT : Healing.T_heal sp1 g 1 Gp Tb ≤ T)
    (hpat : Healing.UPat (tickRun N1 dg1) Set.univ (fun _ => v0) g 1 M 2 0)
    (hM : Healing.Mstar sp1 1 Gp 2 0 ≤ M) (hrec : SA.gbar g + Healing.T_rec sp1 1 Gp 1 M ≤ T) :
    Regimes.FinalPremises (tickRun N1 dg1) Set.univ (fun _ => v0) dg1 g 1 Gp a Tb T 1 M 2 0 :=
  ⟨tickRun_healedPremises g Gp a Tb T hGp hreset hTb hbridge hT,
    tickRun_patternPremises g Gp M hGp hpat hM, hrec⟩


end One

end Consensus.Goldilocks.Witness

end
