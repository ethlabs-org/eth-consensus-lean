module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Reachable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Reach
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo

public section

/-! # Shadow P-U: the AC projection of a shadow run (C0.5)

Copies of stock `Compose/Run/ACProjection` (`ac_projection`) and of the projection theorem of
`Compose/Run/GoldilocksAC` over the shadow run laws (`Node.LocalRun'`, `GoldilocksRun'`). The
shadow node is the stock AC with the shadow frame `Node.frame'`, so the conclusions are the stock
AC trace contract `ACLocalRun` and the stock `AC.ACRun`, at the frames `fg_to_ac'`.

**Reused, not copied:** `ACLocalRun`, `AC.ACRun`, `projAC`, `projAC_callAt`, `Trace.state_succ_*`
(generic); `Compose.projAC_state'` (Shadow/PU/Node), `Coherence.accept_next'` and
`Coherence.honest_blocks_coherent'` (Shadow/PU/Coherence);
`Compose.frameOK_state'` and `Compose.own_block_payload'` (Shadow/PU/Run). -/

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {proposer : Nat → Fin P.n} {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}
  {ini : Fin P.n → A.State}

/-- **An AC block call follows the FG cut that accepts the block** (a copy of `acBlock_prev`). -/
private theorem acBlock_prev (h : Node.LocalRun proposer dg H sg tr ini) {y : Fin P.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel A} {B : A.Blk} (hc : tr.CallAt y i (.ac ℓ))
    (hb : ℓ.call = .block B) :
    ∃ i', i = i' + 1 ∧ tr.CallAt y i' (.fg (.block B true)) ∧ tr.time i' = tr.time i := by
  obtain ⟨j, e, k, hg, rfl, hk⟩ := Coherence.call_in_group h hy hc
  obtain ⟨k', rfl, hk'⟩ := Coherence.exec_acBlock_prev proposer dg y _ _ e hk hb
  obtain ⟨hc', ht⟩ := group_cut hg hk'
  exact ⟨j + k', rfl, hc', ht⟩

/-! ### The frame between AC calls -/

/-- The frame of every honest state is a frame inside the honest blocks. -/
private theorem frameIn_state (h : Node.LocalRun proposer dg H sg tr ini) {y : Fin P.n}
    (hy : y ∈ H) (k : Nat) : A.FrameIn (tr.HonestBlocks H) (frame (tr.state y k)) := by
  refine ⟨frameOK_state' h hy k, fun X hX => ⟨y, hy, k, ?_⟩⟩
  rw [frame_eq, Store.toFrame_tree] at hX
  exact hX.1

private theorem callAt_unique {y : Fin P.n} {i : Nat} {c c' : Cut A} (hc : tr.CallAt y i c)
    (hc' : tr.CallAt y i c') : c = c' :=
  Option.some.inj (hc.2.symm.trans hc'.2)

/-- Without AC calls of `y` in `[a, b)`, its shadow frame at `b` is the frame at `a`, or the cut
before `b` accepts a block, at the frame of `a` (a copy of `frame_flat`). -/
private theorem frame_flat (h : Node.LocalRun proposer dg H sg tr ini) {y : Fin P.n}
    (hy : y ∈ H) {a b : Nat}
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
            | false => exact Or.inl (((cutStep_block_false _ _ _ _ _).1 hlaw).2 ▸ heq)
          | attestation a =>
            left
            rw [frame_eq, ((cutStep_attestation _ _ _ _ _).1 hlaw).1,
              (Store.accept_is_frame_step' _ _ (fg_reachable_at h hy b)).2 a, ← frame_eq]
            exact heq
          | attest C s =>
            cases s with
            | none => exact Or.inl (((cutStep_attest_none _ _ _ _ _).1 hlaw).2 ▸ heq)
            | some a =>
              left
              rw [frame_eq, ((cutStep_attest_some _ _ _ _ _ _).1 hlaw).2.1, ← frame_eq]
              exact heq
      · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
        exact Or.inl heq
    · obtain ⟨ℓ, hℓ, -⟩ := Coherence.accept_next h hy hB
      exact absurd hℓ (hno (b' + 1) (by omega) (by omega) ℓ)

/-- The call law for an AC call of `y` at `i` after the frame of `a`, without AC calls of `y`
in `[a, i)` and without an accepting cut of `y` just before `a` (a copy of `callOK_from`). -/
private theorem callOK_from (hpay : ∀ y ∈ H, A.ReqPayloadFrom (ini y) y)
    (h : Node.LocalRun proposer dg H sg tr ini) {y : Fin P.n}
    (hy : y ∈ H) {a i : Nat} {ℓ : ACLabel A} (hc : tr.CallAt y i (.ac ℓ)) (hai : a ≤ i)
    (hno : ∀ k, a ≤ k → k < i → ∀ ℓ' : ACLabel A, ¬ tr.CallAt y k (.ac ℓ'))
    (ha : ∀ k B, k + 1 = a → ¬ tr.CallAt y k (.fg (.block B true))) :
    A.CallOK (tr.HonestBlocks H) (frame (tr.state y a)) (tr.time i) ℓ.call ℓ.frame := by
  have hfr : ℓ.frame = frame (tr.state y i) := ((cutStep_ac _ _ _ _ _).1 (h.cutLaw y hy i _ hc)).1
  have same (hnb : ∀ B, ℓ.call ≠ .block B) : ℓ.frame = frame (tr.state y a) := by
    rcases frame_flat h hy hai hno with heq | ⟨b', rfl, -, ⟨B, hB⟩, -⟩
    · exact hfr.trans heq
    · obtain ⟨ℓ', hℓ', hb, -⟩ := Coherence.accept_next h hy hB
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
      · obtain ⟨ℓ', hℓ', -⟩ := Coherence.accept_next h hy hB'
        cases callAt_unique hacc hℓ'
    have hlaw := (cutStep_block_true _ _ _ _ _).1 (h.cutLaw y hy i' _ hacc)
    refine ⟨?_, own_block_payload hpay h hy hacc, hti ▸ hlaw.1⟩
    rw [← hfr', hfr, tr.state_succ_of_call hacc, frame_eq, frame_eq]
    exact (Store.accept_is_frame_step' _ _ (fg_reachable_at h hy i')).1 B _ hlaw.2.1
  | message m =>
    obtain ⟨j, hg⟩ := msgCall_group' h hy hc rfl
    exact ⟨same (fun _ hb => by cases hb), h.wire y hy j _ _ hg⟩
  | _ => exact same fun _ hb => by cases hb

/-- **C0.5, the AC projection of a shadow run**, from the run's AC starts `ini` (a copy of
`ac_projection`; the conclusion is the stock AC trace contract). -/
theorem ac_projection' (hpay : ∀ y ∈ H, A.ReqPayloadFrom (ini y) y)
    (h : Node.LocalRun proposer dg H sg tr ini) (hnc : NoCollRun dg tr) :
    ACLocalRun A H (tr.HonestBlocks H) tr.projAC ini := by
  classical
  refine
    { coherent := Coherence.honest_blocks_coherent h hnc
      init := fun y hy => by simp [RunTrace.projAC, h.init y hy, Node.initWith]
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
    rw [projAC_state' h hH]
    exact ((cutStep_ac _ _ _ _ _).1 (h.cutLaw _ hH i _ hc)).2.1
  · have hc := projAC_callAt.1 hc
    by_cases hex : ∃ j < i, ∃ ℓ' : ACLabel A, tr.CallAt y j (.ac ℓ')
    · set j := Nat.findGreatest (fun j => ∃ ℓ' : ACLabel A, tr.CallAt y j (.ac ℓ')) (i - 1)
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
        have hlaw := (cutStep_ac _ _ _ _ _).1 (h.cutLaw y hy j _ hj)
        rw [tr.state_succ_of_call hj, hlaw.1, frame_eq, frame_eq, hlaw.2.2.1]
      refine Or.inr ⟨j, ℓ', hji, projAC_callAt.2 hj, fun k hk hki ℓ'' hk' =>
        hno k hk hki ℓ'' (projAC_callAt.1 hk'), ?_⟩
      rw [← hfr]
      exact callOK_from hpay h hy hc hji hno fun k B hk hk' => by
        cases callAt_unique hj (show k = j by omega ▸ hk')
    · push Not at hex
      have hno : ∀ k, 0 ≤ k → k < i → ∀ ℓ'' : ACLabel A, ¬ tr.CallAt y k (.ac ℓ'') :=
        fun k _ hki ℓ'' => hex k hki ℓ''
      have h₀ : tr.state y 0 = Node.initWith A (ini y) := h.init y hy
      refine Or.inl ⟨fun k _ hki ℓ'' hk' => hex k hki ℓ'' (projAC_callAt.1 hk'), _,
        h₀ ▸ init_initialFrame', frameIn_state h hy 0,
        callOK_from hpay h hy hc (Nat.zero_le i) hno fun k B hk => by omega⟩
  · have hc := projAC_callAt.1 hc
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

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Payload Vote Blk goldilocksAC)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- The frame of an honest AC call is inside the node's tree (a copy of `frame_tree`). -/
private theorem frame_tree (hrun : GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ℓ)
    {B : Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree) :
    B ∈ (tr.state y i).fg.tree := by
  have hf := ((Node.cutStep_ac _ _ _ _ _).1 (hrun.cutLaw y hy i _ (projAC_callAt.1 hc))).1
  rw [hf, Node.frame_eq, Store.toFrame_tree] at hB
  exact hB.1

/-- An emission of the run is a vote of the AC projection. -/
private theorem emit_voteAt {x : Fin sp.n} {j : Nat} {v : Vote sp.n} (h : tr.EmitAt x j v) :
    ∃ e, AC.VoteAt tr.projAC x j e ∧ e.msg = v := by
  obtain ⟨ℓ, hc, e, he, rfl⟩ := h
  exact ⟨e, ⟨ℓ, projAC_callAt.2 hc, he⟩, rfl⟩

private theorem message_vote (hrun : GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {v : Vote sp.n}
    (hc : tr.projAC.CallAt y i ℓ) (hm : ℓ.call = .message v) (hval : v.val ∈ H) :
    ∃ j < i, ∃ e, AC.VoteAt tr.projAC v.val j e ∧ e.msg = v := by
  obtain ⟨j, hj, he⟩ := hrun.msg_unforgeable y hy i v ⟨ℓ, projAC_callAt.1 hc, hm⟩ hval
  exact ⟨j, hj, emit_voteAt he⟩

/-- The pool form and capacity invariant of a shadow run (a copy of `state_pool_cap`). -/
theorem state_pool_cap' (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    ∀ σ, (∀ m ∈ (tr.projAC.state y i).pool σ, m.slot = σ) ∧
      ∀ x : Fin sp.n, (((tr.projAC.state y i).pool σ).filter
        (fun m => m.val = x)).dedup.length ≤ 2 := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    rcases tr.projAC.noCall_or_lastCall y i with hn | ⟨k, hk, ℓ, hc, hn⟩
    · rw [tr.projAC.state_of_noCall hn]
      simp [RunTrace.projAC, hrun.init y hy, Node.initWith, (hrun.vstart y).pool]
    · rw [tr.projAC.state_of_lastCall hc hk hn]
      have hex := ((Node.cutStep_ac _ _ _ _ _).1
        (hrun.cutLaw y hy k _ (projAC_callAt.mp hc))).2.1
      rw [← projAC_state' hrun.toLocalRun hy] at hex
      have h := AC.step_pool_cap ro y (tr.projAC.state y k) ℓ.frame (tr.time k)
        ℓ.call (ih k hk)
      rw [hex] at h
      exact h

/-- Honest votes in a stored pool of a shadow run have an earlier emission, from starts up to
the vote permission (a copy of `pool_vote_emitted`; the pool insertions are read from the public
`step_pool_insertion_source`). -/
theorem pool_vote_emitted' (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) (i σ : Nat) (v : Vote sp.n)
    (hv : v ∈ (tr.projAC.state y i).pool σ) (hval : v.val ∈ H) :
    ∃ j < i, ∃ e, AC.VoteAt tr.projAC v.val j e ∧ e.msg = v := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    rcases tr.projAC.noCall_or_lastCall y i with hn | ⟨k, hk, ℓ, hc, hn⟩
    · rw [tr.projAC.state_of_noCall hn] at hv
      simp [RunTrace.projAC, hrun.init y hy, Node.initWith, (hrun.vstart y).pool] at hv
    · rw [tr.projAC.state_of_lastCall hc hk hn] at hv
      have hlaw := (Node.cutStep_ac _ _ _ _ _).1 (hrun.cutLaw y hy k _ (projAC_callAt.mp hc))
      have hΦ : FrameOK ℓ.frame := hlaw.1 ▸ frameOK_state' hrun.toLocalRun hy k
      have hex := hlaw.2.1
      rw [← projAC_state' hrun.toLocalRun hy] at hex
      by_cases hr : ℓ.call = .restart
      · have hs := AC.restart_state sp _ ro y (tr.projAC.state y k) ℓ.frame
          (tr.time k) hΦ (hrun.time_nonneg k)
        have hp : (AC.acRestart sp ro y (tr.projAC.state y k) ℓ.frame (tr.time k)).1 =
            tr.projAC.post k := by
          simpa [hr, ACInterface.step, RunTrace.projAC] using congrArg Prod.fst hex
        rw [← hp, hs.2.2.2.2.2.2.2.2.1 σ] at hv
        exact absurd hv List.not_mem_nil
      · have hv' : v ∈ ((goldilocksAC sp _ ro).step y (tr.projAC.state y k) ℓ.frame (tr.time k)
            ℓ.call).1.pool σ := by
          rw [hex]; exact hv
        have hσ : v.slot = σ := by
          have hcap := AC.step_pool_cap ro y (tr.projAC.state y k) ℓ.frame (tr.time k) ℓ.call
            (state_pool_cap' hrun hy k)
          exact (hcap σ).1 v hv'
        subst hσ
        by_cases hold : v ∈ (tr.projAC.state y k).pool v.slot
        · obtain ⟨j, hj, he⟩ := ih k hk hold
          exact ⟨j, hj.trans hk, he⟩
        rcases step_pool_insertion_source (ro := ro) y _ ℓ.frame (tr.time k) ℓ.call hr v hold
          hv' with hm | ⟨e, he, hev⟩
        · obtain ⟨j, hj, he⟩ := message_vote hrun hy hc hm hval
          exact ⟨j, hj.trans hk, he⟩
        · have hs := AC.step_emission_signer y _ _ _ _ hΦ (hrun.time_nonneg k) he
          have hvy : v.val = y := hev ▸ hs
          rw [hex] at he
          exact ⟨k, hk, e, hvy.symm ▸ ⟨ℓ, hc, he⟩, hev⟩

/-- A block of an honest frame is genesis or was accepted by an honest node (a copy of
`frame_block_cases`). -/
private theorem frame_block_cases (hrun : GoldilocksRun proposer dg H tr ini)
    {B : Blk sp.n (List (FG.Att sp.n))} (hB : AC.HonestFrameBlock tr.projAC H B) :
    B = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload ∨
      ∃ y ∈ H, ∃ k, tr.AcceptAt y k B := by
  obtain ⟨y, hy, i, ℓ, hc, hB⟩ := hB
  rcases Coherence.tree_accepted hrun.toLocalRun hy (frame_tree hrun hy hc hB) with
    h | ⟨k, -, hk⟩
  · exact Or.inl h
  · exact Or.inr ⟨y, hy, k, hk⟩

/-- An accepted block of an honest proposer is its own proposal, at the third cut of its tick at
the start of the block's slot, which is not slot `0` (a copy of `own_tick`). -/
private theorem own_tick (hrun : GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat}
    {B : Blk sp.n (List (FG.Att sp.n))} (hk : tr.AcceptAt y k B) (hp : B.proposer ∈ H) :
    ∃ j₀ acc, tr.TickAt proposer dg B.proposer j₀ (tr.time (j₀ + 2)) ∧
      tr.CallAt B.proposer (j₀ + 2) (.fg (.block B acc)) ∧ 0 < B.slot ∧
      tr.time (j₀ + 2) = sp.toParams.slotTime B.slot := by
  obtain ⟨j, -, ⟨acc, hc⟩, hpos⟩ := hrun.block_unforgeable y hy k B ⟨true, hk⟩ hp
  rcases Coherence.blockCall_cases hrun.toLocalRun hp hc with
    hg | ⟨j₀, x, f, rfl, ht, hP, d, p, -,
    hB, -⟩
  · have hg := (RunTrace.groupAt_iff _ _ _ _ _ _ _).1 hg
    exact absurd (by simpa using (hg.2.1 0 (List.length_pos_of_ne_nil hg.1)).2.2.2.1) hpos
  · have hs : B.slot = sp.toParams.slotOf (tr.time (j₀ + 2)) := by rw [hB]; rfl
    exact ⟨j₀, acc, (RunTrace.tickAt_iff _ _ _ _ _ _).2 ⟨x, f, ht⟩, hc, hs ▸ hP.1, hs ▸ hP.2.1⟩

private theorem one_block (hrun : GoldilocksRun proposer dg H tr ini)
    {B B' : Blk sp.n (List (FG.Att sp.n))}
    (hB : AC.HonestFrameBlock tr.projAC H B) (hB' : AC.HonestFrameBlock tr.projAC H B')
    (hp : B.proposer ∈ H) (hpr : B.proposer = B'.proposer) (hs : B.slot = B'.slot) : B = B' := by
  have hp' : B'.proposer ∈ H := hpr ▸ hp
  rcases frame_block_cases hrun hB with rfl | ⟨y, hy, k, hk⟩ <;>
    rcases frame_block_cases hrun hB' with rfl | ⟨y', hy', k', hk'⟩
  · rfl
  · obtain ⟨-, -, -, -, h, -⟩ := own_tick hrun hy' hk' hp'
    exact absurd hs (by simp [Params.genesisBlock]; omega)
  · obtain ⟨-, -, -, -, h, -⟩ := own_tick hrun hy hk hp
    exact absurd hs (by simp [Params.genesisBlock]; omega)
  · obtain ⟨j₀, acc, ht, hc, -, htime⟩ := own_tick hrun hy hk hp
    obtain ⟨j₀', acc', ht', hc', -, htime'⟩ := own_tick hrun hy' hk' hp'
    rw [hpr, htime, hs, ← htime'] at ht
    rw [hpr] at hc
    obtain rfl := hrun.tick_unique _ hp' j₀ j₀' _ ht ht'
    have := hc.2.symm.trans hc'.2
    simp only [Option.some.injEq, Cut.fg.injEq, FGLabel.block.injEq] at this
    exact this.1

/-- **The honest-object facts of a shadow run's AC projection**, from starts up to the vote
permission (a copy of `goldilocks_ac_projection_from`; the conclusion is the stock `AC.ACRun`, the
AC being the stock one). -/
theorem goldilocks_ac_projection_from' (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) :
    AC.ACRun proposer tr.projAC H (tr.HonestBlocks H) ini := by
  have hloc := ac_projection'
    (fun y _ U _ s Φ t₀ h => AC.proposal_payload_valid_from _ (hrun.vstart y).pool y U s Φ t₀ h)
    hrun.toLocalRun hnc
  refine ⟨hloc, ⟨fun y hy => pool_vote_emitted' hrun hy,
    fun y hy i ℓ v hc hm hval => message_vote hrun hy hc hm hval, fun B hB hr => ?_,
    fun B B' hB hB' hp hpr hs => one_block hrun hB hB' hp hpr hs⟩, hrun.vstart⟩
  rcases frame_block_cases hrun hB with rfl | ⟨y, hy, k, hk⟩
  · exact absurd rfl hr
  · exact (Coherence.accept_facts hrun.toLocalRun hy hk).2.1

end Consensus.Goldilocks.Compose

namespace Consensus.Goldilocks.Compose.Growing

variable {sp : AC.ACParams} {ro : AC.ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- **The honest-object facts of a shadow run's AC projection under growing faults** (a copy of
`Growing.goldilocks_ac_projection_from` and of the growing `ac_projection` inlined, by
retention through `Growing.GoldilocksRun'.upTo`; the conclusion is the stock `AC.Growing.ACRun`). -/
theorem goldilocks_ac_projection_from'
    (h : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) :
    AC.Growing.ACRun proposer tr.projAC H (tr.HonestBlocksAt H) ini := by
  have hpay {H' : Set (Fin sp.n)} :
      ∀ y ∈ H', (goldilocksNode sp ro).ReqPayloadFrom (ini y) y :=
    fun y _ U _ s Φ t₀ h' => AC.proposal_payload_valid_from _ (h.vstart y).pool y U s Φ t₀ h'
  have retained (i : Nat) :=
    Compose.goldilocks_ac_projection_from' (h.upTo (h.time_nonneg i)) (hnc.upTo _)
  have retainedLocal (i : Nat) := Compose.ac_projection' hpay
    (h.upTo (h.time_nonneg i)).toLocalRun (hnc.upTo (tr.time i))
  have call {y i ℓ} (hc : tr.projAC.CallAt y i ℓ) :
      (tr.upTo (tr.time i)).projAC.CallAt y i ℓ := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  have frame {i Φ} (hf : (goldilocksNode sp ro).FrameIn ((tr.upTo (tr.time i)).HonestBlocks
      (H (tr.time i))) Φ) : (goldilocksNode sp ro).FrameIn (tr.HonestBlocksAt H) Φ :=
    ⟨hf.1, fun _ hx => RunTrace.honestBlocks_upTo_subset h.time_mono (h.time_nonneg i)
      (hf.2 hx)⟩
  have lawful {i Φ Φ' c} (hc : (goldilocksNode sp ro).CallOK ((tr.upTo (tr.time i)).HonestBlocks
      (H (tr.time i))) Φ (tr.time i) c Φ') :
      (goldilocksNode sp ro).CallOK (tr.HonestBlocksAt H) Φ (tr.time i) c Φ' :=
    ⟨frame hc.1, hc.2⟩
  have emission {i v} (hv : ∃ j < i, ∃ e,
      AC.VoteAt (tr.upTo (tr.time i)).projAC v.val j e ∧ e.msg = v) :
      ∃ j < i, ∃ e, AC.VoteAt tr.projAC v.val j e ∧ e.msg = v := by
    obtain ⟨j, hj, e, he, hev⟩ := hv
    rw [RunTrace.upTo_projAC] at he
    exact ⟨j, hj, e, (AC.upTo_voteAt.mp he).2, hev⟩
  have hloc : Consensus.Goldilocks.Growing.ACLocalRun (goldilocksNode sp ro) H
      (tr.HonestBlocksAt H) tr.projAC ini := by
    refine
      { antitone := h.antitone
        coherent := Coherence.honestBlocksAt_coherent h hnc
        init := fun y hy => by simp only [RunTrace.projAC]; rw [h.init y hy]; rfl
        exec := fun i ℓ hl hy => ?_
        frameLaw := fun y i ℓ hy hc => ?_
        time_nonneg := h.time_nonneg
        time_mono := h.time_mono
        awake_of_call := fun y i ℓ hy hc =>
          h.awake_of_call y i hy ⟨_, Compose.projAC_callAt.mp hc⟩
        restart_of_sleep := fun y i ℓ u hy hc hu hui hs hb => ?_
        restart_at_wake := fun y u v hy hu huv hs hw => ?_
        sleep_of_restart := fun y i ℓ hy hc hr => ?_ }
    · have he := (retainedLocal i).exec i ℓ (call ⟨rfl, hl⟩).2 hy
      rw [RunTrace.upTo_projAC, Trace.upTo_node, Trace.upTo_post,
        Trace.upTo_state tr.projAC (tr.projAC.node i) (i := i)
          (fun k hk => h.time_mono hk.le)] at he
      exact he
    · have back {j ℓ'} (hc' : (tr.upTo (tr.time i)).projAC.CallAt y j ℓ') := by
        rw [RunTrace.upTo_projAC] at hc'
        exact ((Trace.upTo_callAt _).mp hc').2
      have nocall {a} (hn : (tr.upTo (tr.time i)).projAC.NoCallBetween y a i) :
          tr.projAC.NoCallBetween y a i := by
        intro j haj hji ℓ' hc'
        apply hn j haj hji ℓ'
        rw [RunTrace.upTo_projAC]
        exact (Trace.upTo_callAt _).mpr ⟨h.time_mono hji.le, hc'⟩
      rcases (retainedLocal i).frameLaw y hy i ℓ (call hc) with
        ⟨hn, Φ, hi, hf, hok⟩ | ⟨j, ℓ', hj, hc', hn, hok⟩
      · exact Or.inl ⟨nocall hn, Φ, hi, frame hf, lawful hok⟩
      · exact Or.inr ⟨j, ℓ', hj, back hc', nocall hn, lawful hok⟩
    · apply (retainedLocal i).restart_of_sleep y hy i ℓ u (call hc) hu hui
        (fun hw => hs hw.1)
      intro j hj ℓ' hc'
      rw [RunTrace.upTo_projAC] at hc'
      exact hb j hj ℓ' ((Trace.upTo_callAt _).mp hc').2
    · have hr := Compose.ac_projection' hpay (h.upTo (hu.trans huv.le)).toLocalRun
        (hnc.upTo v)
      obtain ⟨k, ⟨ℓ, hc, hrestart⟩, huk, hkv⟩ :=
        hr.restart_at_wake y hy u v hu huv (fun hw => hs hw.1) ⟨hw, le_rfl⟩
      rw [RunTrace.upTo_projAC] at hc
      exact ⟨k, ⟨ℓ, ((Trace.upTo_callAt _).mp hc).2, hrestart⟩, huk, hkv⟩
    · obtain ⟨u, hu, hui, hs, hb⟩ := (retainedLocal i).sleep_of_restart y hy i ℓ (call hc) hr
      refine ⟨u, hu, hui, fun hw => hs ⟨hw, hui.le⟩, fun j hj ℓ' hc' => ?_⟩
      apply hb j hj ℓ'
      rw [RunTrace.upTo_projAC]
      exact (Trace.upTo_callAt _).mpr ⟨h.time_mono hj.le, hc'⟩
  refine ⟨hloc,
    { pool_vote := fun y i σ hy v hv hval => ?_
      message_vote := fun y i ℓ v hy hc hm hv =>
        emission ((retained i).honest.message_vote y hy i ℓ v (call hc) hm hv)
      proposer := fun B hB hng => ?_
      one_block := fun y i ℓ B y' i' ℓ' B' hy hc hB hy' hc' hB' hp hprop hslot => ?_ },
    h.vstart⟩
  · apply emission
    apply (retained i).honest.pool_vote y hy i σ v
    · simpa only [RunTrace.upTo_projAC,
        Trace.upTo_state tr.projAC y (i := i) (fun k hk => h.time_mono hk.le)] using hv
    · exact hval
  · obtain ⟨y, i, ℓ, hy, hc, hB⟩ := hB
    exact (retained i).honest.proposer B ⟨y, hy, i, ℓ, call hc, hB⟩ hng
  · -- Each reader retains its own prefix; only the proposer is retained at both horizons.
    have hpi := h.antitone (le_max_left _ _) hp
    have hpi' := h.antitone (le_max_right _ _) hp
    have frame_cases {y i ℓ B} (hy : y ∈ H (tr.time i))
        (hc : tr.projAC.CallAt y i ℓ) (hB : B ∈ ℓ.frame.tree) :
        B = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload ∨
          ∃ k < i, tr.AcceptAt y k B := by
      have ht : B ∈ ((tr.upTo (tr.time i)).state y i).fg.tree :=
        frame_tree (h.upTo (h.time_nonneg i)) hy (call hc) hB
      rcases Coherence.tree_accepted (h.upTo (h.time_nonneg i)).toLocalRun hy ht with
        hg | ⟨k, hk, ha⟩
      · exact Or.inl hg
      · exact Or.inr ⟨k, hk, ((RunTrace.upTo_acceptAt _).mp ha).2⟩
    have own {y i ℓ B} (hy : y ∈ H (tr.time i)) (hc : tr.projAC.CallAt y i ℓ)
        (hB : B ∈ ℓ.frame.tree) (hp : B.proposer ∈ H (tr.time i))
        (hng : B ≠ sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload) :
        ∃ j acc, tr.CallAt B.proposer j (.fg (.block B acc)) ∧
          ∃ j₀, tr.TickAt proposer dg B.proposer j₀ (sp.toParams.slotTime B.slot) ∧
            j = j₀ + 2 ∧ 0 < B.slot ∧ sp.toParams.slotTime B.slot ≤ tr.time i := by
      obtain ⟨k, hk, ha⟩ := (frame_cases hy hc hB).resolve_left hng
      have ha' := (RunTrace.upTo_acceptAt _).mpr ⟨h.time_mono hk.le, ha⟩
      obtain ⟨j, hjk, ⟨acc, hj⟩, hpos⟩ :=
        (h.upTo (h.time_nonneg i)).block_unforgeable y hy k B ⟨true, ha'⟩ hp
      rcases Coherence.blockCall_cases (h.upTo (h.time_nonneg i)).toLocalRun hp hj with
        hg | ⟨j₀, x, f, rfl, ht, hP, d, p, _, hBdef, _⟩
      · have hg := (RunTrace.groupAt_iff _ _ _ _ _ _ _).1 hg
        exact absurd (by simpa using (hg.2.1 0 (List.length_pos_of_ne_nil hg.1)).2.2.2.1) hpos
      · have hs : B.slot = sp.toParams.slotOf (tr.time (j₀ + 2)) := by rw [hBdef]; rfl
        have htime : sp.toParams.slotTime B.slot = tr.time (j₀ + 2) := hs ▸ hP.2.1.symm
        refine ⟨j₀ + 2, acc, ((Trace.upTo_callAt _).mp hj).2, j₀, ?_, rfl, hs ▸ hP.1,
          htime ▸ (h.time_mono (hjk.trans hk.le))⟩
        have ht' := (RunTrace.upTo_tickAt' tr h.time_mono).mp
          ((RunTrace.tickAt_iff _ _ _ _ _ _).2 ⟨x, f, ht⟩)
        have ht'' : tr.TickAt proposer dg B.proposer j₀ (tr.time (j₀ + 2)) := ht'.2
        rw [← htime] at ht''
        exact ht''
    by_cases hg : B = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload
    · by_cases hg' : B' = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload
      · exact hg.trans hg'.symm
      · obtain ⟨_, _, _, _, _, _, hs, _⟩ := own hy' hc' hB' (hprop ▸ hpi') hg'
        simp only [hg, Params.genesisBlock] at hslot
        omega
    · obtain ⟨j, acc, hj, j₀, ht, hje, hs, htime⟩ := own hy hc hB hpi hg
      by_cases hg' : B' = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload
      · simp only [hg', Params.genesisBlock] at hslot
        omega
      · obtain ⟨j', acc', hj', j₀', ht', hje', _, _⟩ := own hy' hc' hB' (hprop ▸ hpi') hg'
        have hpstart := h.antitone htime hpi
        rw [hslot] at hpstart
        rw [hprop, hslot] at ht
        have he := h.tick_unique B'.proposer j₀ j₀' _ (hprop ▸ hpstart) ht ht'
        rw [hje, he, ← hje', hprop] at hj
        exact (Cut.fg.inj (Option.some.inj (hj.2.symm.trans hj'.2)) |> FGLabel.block.inj).1

end Consensus.Goldilocks.Compose.Growing

end
