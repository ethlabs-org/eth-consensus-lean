module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees

public section

/-! # Goldilocks runs: the AC projection is an AC trace with the contract (C0.5)

Over the AC projection of a run, inside the honest blocks of the run (coherent under `NoColl`):
each honest AC call executes the AC by the cut law, at the AC part of the run's state; and the
frame law holds at call boundaries. Between two AC calls of a node the frame `fg_to_ac(Σ)` stays
put (a processed attestation does not move it, the other FG cuts keep `Σ`), except at an
accepted block, whose FG cut is followed at once by the AC call of that block: so an AC call is
given the previous call's frame, or, for `ac_on_block(B)`, a frame step on `B` from it. The input
checks are the wire's, and for the own block requirement 5 at the proposal's state (reachable,
C0.5 (a)). Sleep and wake are the run's: a restart of the run is an AC restart, and an earlier
FG call after a sleep would follow a restart. -/

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}

/-- The frame of every honest state is a frame inside the honest blocks. -/
private theorem frameIn_state (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H)
    (k : Nat) : A.FrameIn (tr.HonestBlocks H) (frame (tr.state y k)) :=
  ⟨(Store.frame_realization P _ _ _ (fg_reachable h hy k)).1, fun _ hX => ⟨y, hy, k, hX.1⟩⟩

private theorem callAt_unique {y : Fin P.n} {i : Nat} {c c' : Cut A} (hc : tr.CallAt y i c)
    (hc' : tr.CallAt y i c') : c = c' :=
  Option.some.inj (hc.2.symm.trans hc'.2)

/-- Without AC calls of `y` in `[a, b)`, its frame at `b` is the frame at `a`, or the cut before
`b` accepts a block, at the frame of `a`. -/
private theorem frame_flat (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {a b : Nat}
    (hab : a ≤ b) (hno : ∀ k, a ≤ k → k < b → ∀ ℓ : ACLabel A, ¬ tr.CallAt y k (.ac ℓ)) :
    frame (tr.state y b) = frame (tr.state y a) ∨ ∃ b', b = b' + 1 ∧ a ≤ b' ∧
      (∃ B, tr.CallAt y b' (.fg (.block B true))) ∧
        frame (tr.state y b') = frame (tr.state y a) := by
  induction b, hab using Nat.le_induction with
  | base => exact Or.inl rfl
  | succ b hab ih =>
    rcases ih fun k hk hkb => hno k hk (by omega) with heq | ⟨b', rfl, hab', ⟨B, hB⟩, -⟩
    · by_cases hc : ∃ c, tr.CallAt y b c
      · obtain ⟨c, hc⟩ := hc
        have hlaw := h.cutLaw y hy b c hc
        rw [tr.state_succ_of_call hc]
        cases c with
        | ac ℓ => exact absurd hc (hno b hab (by omega) ℓ)
        | fg ℓ =>
          cases ℓ with
          | block B acc =>
            cases acc with
            | true => exact Or.inr ⟨b, rfl, hab, ⟨B, hc⟩, heq⟩
            | false => exact Or.inl (hlaw.2 ▸ heq)
          | attestation a =>
            left
            change (tr.post b).fg.toFrame = _
            rw [hlaw.1, (Store.accept_is_frame_step P _ _ _ (fg_reachable h hy b)).2 a]
            exact heq
          | attest C s =>
            cases s with
            | none => exact Or.inl (hlaw.2 ▸ heq)
            | some a =>
              left
              change (tr.post b).fg.toFrame = _
              rw [hlaw.2.1]
              exact heq
      · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
        exact Or.inl heq
    · obtain ⟨ℓ, hℓ, -⟩ := accept_next h hy hB
      exact absurd hℓ (hno (b' + 1) (by omega) (by omega) ℓ)

/-- The call law for an AC call of `y` at `i` after the frame of `a`, without AC calls of `y`
in `[a, i)` and without an accepting cut of `y` just before `a`. -/
private theorem callOK_from (hq : A.Requirements) (h : Node.LocalRun dg H sg tr) {y : Fin P.n}
    (hy : y ∈ H) {a i : Nat} {ℓ : ACLabel A} (hc : tr.CallAt y i (.ac ℓ)) (hai : a ≤ i)
    (hno : ∀ k, a ≤ k → k < i → ∀ ℓ' : ACLabel A, ¬ tr.CallAt y k (.ac ℓ'))
    (ha : ∀ k B, k + 1 = a → ¬ tr.CallAt y k (.fg (.block B true))) :
    A.CallOK (tr.HonestBlocks H) (frame (tr.state y a)) (tr.time i) ℓ.call ℓ.frame := by
  have hfr : ℓ.frame = frame (tr.state y i) := (h.cutLaw y hy i _ hc).1
  -- the frame is the frame of `a` unless the call is of a block
  have same (hnb : ∀ B, ℓ.call ≠ .block B) : ℓ.frame = frame (tr.state y a) := by
    rcases frame_flat h hy hai hno with heq | ⟨b', rfl, -, ⟨B, hB⟩, -⟩
    · exact hfr.trans heq
    · obtain ⟨ℓ', hℓ', hb, -⟩ := accept_next h hy hB
      cases callAt_unique hc hℓ'
      exact absurd hb (hnb B)
  refine ⟨hfr ▸ frameIn_state h hy i, ?_⟩
  obtain ⟨c, Φ, es⟩ := ℓ
  cases c with
  | block B =>
    obtain ⟨i', rfl, hacc, hti⟩ := acBlock_prev h hy hc rfl
    have hai' : a ≤ i' := by
      by_contra hlt
      exact ha i' B (by omega) hacc
    have hfr' : frame (tr.state y i') = frame (tr.state y a) := by
      rcases frame_flat h hy hai' fun k hk hki => hno k hk (by omega) with heq | ⟨b', rfl, -,
        ⟨B', hB'⟩, -⟩
      · exact heq
      · obtain ⟨ℓ', hℓ', -⟩ := accept_next h hy hB'
        cases callAt_unique hacc hℓ'
    have hlaw := h.cutLaw y hy i' _ hacc
    refine ⟨?_, ?_, hti ▸ hlaw.1⟩
    · rw [← hfr', hfr, tr.state_succ_of_call hacc]
      exact (Store.accept_is_frame_step P _ _ _ (fg_reachable h hy i')).1 B _ hlaw.2.1
    -- the payload: from the wire, or requirement 5 at the proposal's state
    rcases blockCall_cases h hy hacc with hg | ⟨j, x, -, hg, hp, d, p, hdp, rfl, -⟩
    · exact (h.wire y hy i' _ _ hg).2.2
    obtain ⟨cfg, hreach, hst, hstep⟩ := group_step h hy hg
    obtain ⟨hcoh, t₀, ht₀, hR⟩ := ac_states_reachable dg y hq cfg hreach
    have hfg := fg_states_reachable dg y cfg hreach
    have hR' := ACInterface.ReachableAt.step .tick hR (ht₀.trans hstep.1)
      ⟨⟨(Store.frame_realization P _ _ _ hfg).1, fun _ hX => hX.1⟩, rfl⟩
    rw [← hst] at hdp
    have hts : tr.time i' = P.slotTime (P.slotOf (tr.time i')) := hp.2.1
    refine hq.payload y _ hcoh _ _ _ hR' (P.slotOf (tr.time i')) hts.le d p ?_ _ rfl rfl
    rw [← hts]
    exact hdp
  | message m =>
    obtain ⟨j, hg⟩ := msgCall_group h hy hc rfl
    exact ⟨same (fun _ hb => by cases hb), h.wire y hy j _ _ hg⟩
  | _ => exact same fun _ hb => by cases hb

/-- **C0.5, the AC projection.** -/
theorem ac_projection : ACProjection := by
  intro P A dg H sg tr hq h hnc
  classical
  refine
    { coherent := honest_blocks_coherent h hnc
      init := fun y hy => by simp [RunTrace.projAC, h.init y hy, Node.init]
      exec := fun i ℓ hl hH => ?_
      frameLaw := fun y hy i ℓ hc => ?_
      time_nonneg := h.time_nonneg
      time_mono := h.time_mono
      awake_of_call := fun y hy i ℓ hc => h.awake_of_call y hy i ⟨_, projAC_callAt.1 hc⟩
      restart_of_sleep := fun y hy i ℓ u hc hu hui hs hb => ?_
      restart_at_wake := fun y hy u v hu huv hs hw => ?_
      sleep_of_restart := fun y hy i ℓ hc hr => ?_ }
  · have hc : tr.CallAt (tr.node i) i (.ac ℓ) := projAC_callAt.1 ⟨rfl, hl⟩
    change A.step (tr.node i) _ ℓ.frame (tr.time i) ℓ.call = ((tr.post i).ac, ℓ.emits)
    rw [projAC_state h hH]
    exact (h.cutLaw _ hH i _ hc).2.1
  · have hc := projAC_callAt.1 hc
    by_cases hex : ∃ j < i, ∃ ℓ' : ACLabel A, tr.CallAt y j (.ac ℓ')
    · -- the previous AC call
      set j := Nat.findGreatest (fun j => ∃ ℓ' : ACLabel A, tr.CallAt y j (.ac ℓ')) (i - 1)
      obtain ⟨j₀, hj₀, hj₀c⟩ := hex
      obtain ⟨ℓ', hj⟩ : ∃ ℓ' : ACLabel A, tr.CallAt y j (.ac ℓ') :=
        Nat.findGreatest_spec (P := fun j => ∃ ℓ' : ACLabel A, tr.CallAt y j (.ac ℓ'))
          (m := j₀) (by omega) hj₀c
      have hji : j < i := by
        have := Nat.findGreatest_le (P := fun j => ∃ ℓ' : ACLabel A, tr.CallAt y j (.ac ℓ'))
          (i - 1)
        have : j₀ ≤ j := Nat.le_findGreatest (by omega) hj₀c
        omega
      have hno : ∀ k, j + 1 ≤ k → k < i → ∀ ℓ'' : ACLabel A, ¬ tr.CallAt y k (.ac ℓ'') :=
        fun k hk hki ℓ'' hk' => Nat.findGreatest_is_greatest
          (P := fun j => ∃ ℓ' : ACLabel A, tr.CallAt y j (.ac ℓ')) (n := i - 1) (k := k)
          (by omega) (by omega) ⟨ℓ'', hk'⟩
      have hfr : frame (tr.state y (j + 1)) = ℓ'.frame := by
        rw [tr.state_succ_of_call hj, (h.cutLaw y hy j _ hj).1]
        exact congrArg Store.toFrame (h.cutLaw y hy j _ hj).2.2.1
      refine Or.inr ⟨j, ℓ', hji, projAC_callAt.2 hj, fun k hk hki ℓ'' hk' =>
        hno k hk hki ℓ'' (projAC_callAt.1 hk'), ?_⟩
      rw [← hfr]
      exact callOK_from hq h hy hc hji hno fun k B hk hk' => by
        cases callAt_unique hj (show k = j by omega ▸ hk')
    · push Not at hex
      have hno : ∀ k, 0 ≤ k → k < i → ∀ ℓ'' : ACLabel A, ¬ tr.CallAt y k (.ac ℓ'') :=
        fun k _ hki ℓ'' => hex k hki ℓ''
      have h₀ : tr.state y 0 = Node.init A := h.init y hy
      refine Or.inl ⟨fun k _ hki ℓ'' hk' => hex k hki ℓ'' (projAC_callAt.1 hk'), _,
        h₀ ▸ init_initialFrame, frameIn_state h hy 0,
        callOK_from hq h hy hc (Nat.zero_le i) hno fun k B hk => by omega⟩
  · -- the earlier calls of `y` were all before `u`, else a restart after the sleep precedes
    have hc := projAC_callAt.1 hc
    have hall : ∀ j < i, tr.IsCall y j → tr.time j < u := by
      by_contra hne
      push Not at hne
      have hex : ∃ j, j < i ∧ tr.IsCall y j ∧ u ≤ tr.time j := by
        obtain ⟨j, hj, hjc, hju⟩ := hne
        exact ⟨j, hj, hjc, hju⟩
      obtain ⟨hji, hjc, hju⟩ := Nat.find_spec hex
      have hmin := fun k (hk : k < Nat.find hex) => Nat.find_min hex hk
      have hlt : u < tr.time (Nat.find hex) := lt_of_le_of_ne hju fun he =>
        hs (he ▸ h.awake_of_call y hy _ hjc)
      obtain ⟨ℓ', hℓ', -⟩ := h.restart_of_sleep y hy _ u hjc hu hlt hs fun k hk hkc => by
        by_contra hku
        exact hmin k hk ⟨by omega, hkc, not_lt.1 hku⟩
      exact absurd (hb _ hji ℓ' (projAC_callAt.2 hℓ')) (not_lt.2 hju)
    obtain ⟨ℓ', hℓ', hr⟩ := h.restart_of_sleep y hy i u ⟨_, hc⟩ hu hui hs hall
    cases callAt_unique hc hℓ'
    exact hr
  · obtain ⟨k, ⟨ℓ, hℓ, hr⟩, hk⟩ := h.restart_at_wake y hy u v hu huv hs hw
    exact ⟨k, ⟨ℓ, projAC_callAt.2 hℓ, hr⟩, hk⟩
  · obtain ⟨u, hu, hui, hs, hb⟩ := h.sleep_of_restart y hy i ⟨ℓ, projAC_callAt.1 hc, hr⟩
    exact ⟨u, hu, hui, hs, fun j hj ℓ' hj' => hb j hj ⟨_, projAC_callAt.1 hj'⟩⟩

end Consensus.Goldilocks.Compose

end
