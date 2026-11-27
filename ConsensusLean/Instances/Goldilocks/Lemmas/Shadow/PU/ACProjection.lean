module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Reach
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC

public section

/-! # Shadow P-U: the AC projection of a shadow run (C0.5)

Copies of stock `Compose/Run/ACProjection` (`ac_projection`) and of the projection theorem of
`Compose/Run/GoldilocksAC` over the shadow run laws (`Node.LocalRun'`, `GoldilocksRun'`). The
shadow node is the stock AC with the shadow frame `Node.frame'`, so the conclusions are the stock
AC trace contract `ACLocalRun` and the stock `AC.ACRun`, at the frames `fg_to_ac'`.

**Reused, not copied:** `ACLocalRun`, `AC.ACRun`, `projAC`, `projAC_callAt`, `Trace.state_succ_*`
(generic); `Compose.projAC_state'`, `accept_next'`, `honest_blocks_coherent'` (Shadow/PU/Node);
`Compose.frameOK_state'` (Shadow/PU/Run, from the shadow cache invariant).

**Pending suppliers.** The private `*_pending` theorems below are placeholders, each with the
exact type of a supplier owned by another lane; each is replaced by an import when it lands:
`Store.accept_is_frame_step'`, `acBlock_prev'`, `msgCall_group'` (Frame,
Handlers), `own_block_payload'` (Reach), `tree_cases'`, `accept_facts'`, `blockCall_cases'`
(Coherence). -/

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {proposer : Nat → Fin P.n} {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}
  {ini : Fin P.n → A.State}

/-! ### Pending suppliers (placeholders with the suppliers' exact types) -/

/-- Placeholder for `Store.accept_is_frame_step'` (Frame): accepting a block is a frame step of
the shadow frame, and a processed attestation leaves it unchanged. -/
private theorem accept_is_frame_step_pending {ACP : Type} (acp₀ : ACP) (st : Store P ACP)
    (hr : st.Reachable' acp₀) :
    (∀ B st', st.onBlock' B = some st' → FrameStep st.toFrame' B st'.toFrame') ∧
      ∀ a, (st.onAttestation a).toFrame' = st.toFrame' := by
  sorry

/-- Placeholder for `acBlock_prev'` (Handlers). -/
private theorem acBlock_prev_pending (h : Node.LocalRun' proposer dg H sg tr ini) {y : Fin P.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel A} {B : A.Blk} (hc : tr.CallAt y i (.ac ℓ))
    (hb : ℓ.call = .block B) :
    ∃ i', i = i' + 1 ∧ tr.CallAt y i' (.fg (.block B true)) ∧ tr.time i' = tr.time i := by
  sorry

/-- Placeholder for `msgCall_group'` (Handlers). -/
private theorem msgCall_group_pending (h : Node.LocalRun' proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel A} {m : A.Msg}
    (hc : tr.CallAt y i (.ac ℓ)) (hm : ℓ.call = .message m) :
    ∃ j, tr.GroupAt' proposer dg y j (tr.time i) (.message m) := by
  sorry

/-- Placeholder for `own_block_payload'` (Reach): every block an honest node accepts passes
`ac_valid_payload` (from the wire, or requirement 5 at its own proposal). -/
private theorem own_block_payload_pending (hpay : ∀ y ∈ H, A.ReqPayloadFrom (ini y) y)
    (h : Node.LocalRun' proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    {i : Nat} {B : A.Blk} (hacc : tr.CallAt y i (.fg (.block B true))) : A.validPayload B := by
  sorry

/-! ### The frame between AC calls -/

/-- The frame of every honest state is a frame inside the honest blocks. -/
private theorem frameIn_state' (h : Node.LocalRun' proposer dg H sg tr ini) {y : Fin P.n}
    (hy : y ∈ H) (k : Nat) : A.FrameIn (tr.HonestBlocks H) (frame' (tr.state y k)) := by
  refine ⟨frameOK_state' h hy k, fun X hX => ⟨y, hy, k, ?_⟩⟩
  rw [frame'_eq, Store.toFrame'_tree] at hX
  exact hX.1

private theorem callAt_unique {y : Fin P.n} {i : Nat} {c c' : Cut A} (hc : tr.CallAt y i c)
    (hc' : tr.CallAt y i c') : c = c' :=
  Option.some.inj (hc.2.symm.trans hc'.2)

/-- Without AC calls of `y` in `[a, b)`, its shadow frame at `b` is the frame at `a`, or the cut
before `b` accepts a block, at the frame of `a` (a copy of `frame_flat`). -/
private theorem frame_flat' (h : Node.LocalRun' proposer dg H sg tr ini) {y : Fin P.n}
    (hy : y ∈ H) {a b : Nat}
    (hab : a ≤ b) (hno : ∀ k, a ≤ k → k < b → ∀ ℓ : ACLabel A, ¬ tr.CallAt y k (.ac ℓ)) :
    frame' (tr.state y b) = frame' (tr.state y a) ∨ ∃ b', b = b' + 1 ∧ a ≤ b' ∧
      (∃ B, tr.CallAt y b' (.fg (.block B true))) ∧
        frame' (tr.state y b') = frame' (tr.state y a) := by
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
            | false => exact Or.inl (((cutStep'_block_false _ _ _ _ _).1 hlaw).2 ▸ heq)
          | attestation a =>
            left
            rw [frame'_eq, ((cutStep'_attestation _ _ _ _ _).1 hlaw).1,
              (accept_is_frame_step_pending _ _ (fg_reachable_at' h hy b)).2 a, ← frame'_eq]
            exact heq
          | attest C s =>
            cases s with
            | none => exact Or.inl (((cutStep'_attest_none _ _ _ _ _).1 hlaw).2 ▸ heq)
            | some a =>
              left
              rw [frame'_eq, ((cutStep'_attest_some _ _ _ _ _ _).1 hlaw).2.1, ← frame'_eq]
              exact heq
      · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
        exact Or.inl heq
    · obtain ⟨ℓ, hℓ, -⟩ := accept_next' h hy hB
      exact absurd hℓ (hno (b' + 1) (by omega) (by omega) ℓ)

/-- The call law for an AC call of `y` at `i` after the frame of `a`, without AC calls of `y`
in `[a, i)` and without an accepting cut of `y` just before `a` (a copy of `callOK_from`). -/
private theorem callOK_from' (hpay : ∀ y ∈ H, A.ReqPayloadFrom (ini y) y)
    (h : Node.LocalRun' proposer dg H sg tr ini) {y : Fin P.n}
    (hy : y ∈ H) {a i : Nat} {ℓ : ACLabel A} (hc : tr.CallAt y i (.ac ℓ)) (hai : a ≤ i)
    (hno : ∀ k, a ≤ k → k < i → ∀ ℓ' : ACLabel A, ¬ tr.CallAt y k (.ac ℓ'))
    (ha : ∀ k B, k + 1 = a → ¬ tr.CallAt y k (.fg (.block B true))) :
    A.CallOK (tr.HonestBlocks H) (frame' (tr.state y a)) (tr.time i) ℓ.call ℓ.frame := by
  have hfr : ℓ.frame = frame' (tr.state y i) := ((cutStep'_ac _ _ _ _ _).1 (h.cutLaw y hy i _ hc)).1
  have same (hnb : ∀ B, ℓ.call ≠ .block B) : ℓ.frame = frame' (tr.state y a) := by
    rcases frame_flat' h hy hai hno with heq | ⟨b', rfl, -, ⟨B, hB⟩, -⟩
    · exact hfr.trans heq
    · obtain ⟨ℓ', hℓ', hb, -⟩ := accept_next' h hy hB
      cases callAt_unique hc hℓ'
      exact absurd hb (hnb B)
  refine ⟨hfr ▸ frameIn_state' h hy i, ?_⟩
  obtain ⟨c, Φ, es⟩ := ℓ
  cases c with
  | block B =>
    obtain ⟨i', rfl, hacc, hti⟩ := acBlock_prev_pending h hy hc rfl
    have hai' : a ≤ i' := by
      by_contra hlt
      exact ha i' B (by omega) hacc
    have hfr' : frame' (tr.state y i') = frame' (tr.state y a) := by
      rcases frame_flat' h hy hai' fun k hk hki => hno k hk (by omega) with heq | ⟨b', rfl, -,
        ⟨B', hB'⟩, -⟩
      · exact heq
      · obtain ⟨ℓ', hℓ', -⟩ := accept_next' h hy hB'
        cases callAt_unique hacc hℓ'
    have hlaw := (cutStep'_block_true _ _ _ _ _).1 (h.cutLaw y hy i' _ hacc)
    refine ⟨?_, own_block_payload_pending hpay h hy hacc, hti ▸ hlaw.1⟩
    rw [← hfr', hfr, tr.state_succ_of_call hacc, frame'_eq, frame'_eq]
    exact (accept_is_frame_step_pending _ _ (fg_reachable_at' h hy i')).1 B _ hlaw.2.1
  | message m =>
    obtain ⟨j, hg⟩ := msgCall_group_pending h hy hc rfl
    exact ⟨same (fun _ hb => by cases hb), h.wire y hy j _ _ hg⟩
  | _ => exact same fun _ hb => by cases hb

/-- **C0.5, the AC projection of a shadow run**, from the run's AC starts `ini` (a copy of
`ac_projection`; the conclusion is the stock AC trace contract). -/
theorem ac_projection' (hpay : ∀ y ∈ H, A.ReqPayloadFrom (ini y) y)
    (h : Node.LocalRun' proposer dg H sg tr ini) (hnc : NoCollRun dg tr) :
    ACLocalRun A H (tr.HonestBlocks H) tr.projAC ini := by
  classical
  refine
    { coherent := honest_blocks_coherent' h hnc
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
    exact ((cutStep'_ac _ _ _ _ _).1 (h.cutLaw _ hH i _ hc)).2.1
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
      have hfr : frame' (tr.state y (j + 1)) = ℓ'.frame := by
        have hlaw := (cutStep'_ac _ _ _ _ _).1 (h.cutLaw y hy j _ hj)
        rw [tr.state_succ_of_call hj, hlaw.1, frame'_eq, frame'_eq, hlaw.2.2.1]
      refine Or.inr ⟨j, ℓ', hji, projAC_callAt.2 hj, fun k hk hki ℓ'' hk' =>
        hno k hk hki ℓ'' (projAC_callAt.1 hk'), ?_⟩
      rw [← hfr]
      exact callOK_from' hpay h hy hc hji hno fun k B hk hk' => by
        cases callAt_unique hj (show k = j by omega ▸ hk')
    · push Not at hex
      have hno : ∀ k, 0 ≤ k → k < i → ∀ ℓ'' : ACLabel A, ¬ tr.CallAt y k (.ac ℓ'') :=
        fun k _ hki ℓ'' => hex k hki ℓ''
      have h₀ : tr.state y 0 = Node.initWith A (ini y) := h.init y hy
      refine Or.inl ⟨fun k _ hki ℓ'' hk' => hex k hki ℓ'' (projAC_callAt.1 hk'), _,
        h₀ ▸ init_initialFrame', frameIn_state' h hy 0,
        callOK_from' hpay h hy hc (Nat.zero_le i) hno fun k B hk => by omega⟩
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

/-! ### Pending suppliers from Coherence -/

/-- Placeholder for `tree_cases'` (Coherence; a copy of `tree_cases`). -/
private theorem tree_cases_pending (h : Node.LocalRun' proposer dg H sg tr ini) {y : Fin P.n}
    (hy : y ∈ H) {i : Nat} {X : A.Blk} (hX : X ∈ (tr.state y i).fg.tree) :
    X = P.genesisBlock A.genesisPayload ∨ ∃ k < i, tr.AcceptAt y k X := by
  sorry

/-- Placeholder for `accept_facts'` (Coherence; a copy of `accept_facts`). -/
private theorem accept_facts_pending (h : Node.LocalRun' proposer dg H sg tr ini) {y : Fin P.n}
    (hy : y ∈ H) {k : Nat} {X : A.Blk} (hk : tr.AcceptAt y k X) :
    X.RootOk dg ∧ X.proposer = proposer X.slot ∧ (tr.state y k).fg.blocks X.root = none ∧
      X.root ≠ P.genesisRoot := by
  sorry

/-- Placeholder for `blockCall_cases'` (Coherence; a copy of `blockCall_cases` over the shadow
groups and handlers). -/
private theorem blockCall_cases_pending (h : Node.LocalRun' proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {i : Nat} {B : A.Blk} {acc : Bool}
    (hc : tr.CallAt y i (.fg (.block B acc))) :
    tr.GroupAt' proposer dg y i (tr.time i) (.block B) ∨
    ∃ j x fgDue, i = j + 2 ∧ tr.GroupAt' proposer dg y j (tr.time i) (.tick x fgDue) ∧
      Proposes proposer y (tr.time i) ∧ ∃ d p,
      (acProposal' (tickStep' proposer dg y (tr.state y j) (tr.time i) x .acTick).1
        (tr.time i)).2.2 = some (d, p) ∧
      B = mkBlock dg y (tr.state y j).fg (tr.time i) x d.head p ∧
      (acc = true ↔ ∃ fg', (tr.state y j).fg.onBlock' B = some fg') ∧
      (∃ ℓ : ACLabel A, tr.CallAt y j (.ac ℓ)) ∧ (∃ ℓ : ACLabel A, tr.CallAt y (j + 1) (.ac ℓ)) ∧
      (tr.state y i).fg = (tr.state y j).fg := by
  sorry

end Consensus.Goldilocks.Compose

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Payload Vote Blk goldilocksAC)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace' sp ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode' sp ro).State}

/-- The frame of an honest AC call is inside the node's tree (a copy of `frame_tree`). -/
private theorem frame_tree' (hrun : GoldilocksRun' proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode' sp ro)} (hc : tr.projAC.CallAt y i ℓ)
    {B : Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree) :
    B ∈ (tr.state y i).fg.tree := by
  have hf := ((Node.cutStep'_ac _ _ _ _ _).1 (hrun.cutLaw y hy i _ (projAC_callAt.1 hc))).1
  rw [hf, Node.frame'_eq, Store.toFrame'_tree] at hB
  exact hB.1

/-- An emission of the run is a vote of the AC projection. -/
private theorem emit_voteAt' {x : Fin sp.n} {j : Nat} {v : Vote sp.n} (h : tr.EmitAt x j v) :
    ∃ e, AC.VoteAt tr.projAC x j e ∧ e.msg = v := by
  obtain ⟨ℓ, hc, e, he, rfl⟩ := h
  exact ⟨e, ⟨ℓ, projAC_callAt.2 hc, he⟩, rfl⟩

private theorem message_vote' (hrun : GoldilocksRun' proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksNode' sp ro)} {v : Vote sp.n}
    (hc : tr.projAC.CallAt y i ℓ) (hm : ℓ.call = .message v) (hval : v.val ∈ H) :
    ∃ j < i, ∃ e, AC.VoteAt tr.projAC v.val j e ∧ e.msg = v := by
  obtain ⟨j, hj, he⟩ := hrun.msg_unforgeable y hy i v ⟨ℓ, projAC_callAt.1 hc, hm⟩ hval
  exact ⟨j, hj, emit_voteAt' he⟩

/-- The pool form and capacity invariant of a shadow run (a copy of `state_pool_cap`). -/
theorem state_pool_cap' (hrun : GoldilocksRun' proposer dg H tr ini)
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
      have hex := ((Node.cutStep'_ac _ _ _ _ _).1
        (hrun.cutLaw y hy k _ (projAC_callAt.mp hc))).2.1
      rw [← projAC_state' hrun.toLocalRun' hy] at hex
      have h := AC.step_pool_cap ro y (tr.projAC.state y k) ℓ.frame (tr.time k)
        ℓ.call (ih k hk)
      rw [hex] at h
      exact h

/-- Honest votes in a stored pool of a shadow run have an earlier emission, from starts up to
the vote permission (a copy of `pool_vote_emitted`; the pool insertions are read from the public
`step_pool_insertion_source`). -/
theorem pool_vote_emitted' (hrun : GoldilocksRun' proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) (i σ : Nat) (v : Vote sp.n)
    (hv : v ∈ (tr.projAC.state y i).pool σ) (hval : v.val ∈ H) :
    ∃ j < i, ∃ e, AC.VoteAt tr.projAC v.val j e ∧ e.msg = v := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    rcases tr.projAC.noCall_or_lastCall y i with hn | ⟨k, hk, ℓ, hc, hn⟩
    · rw [tr.projAC.state_of_noCall hn] at hv
      simp [RunTrace.projAC, hrun.init y hy, Node.initWith, (hrun.vstart y).pool] at hv
    · rw [tr.projAC.state_of_lastCall hc hk hn] at hv
      have hlaw := (Node.cutStep'_ac _ _ _ _ _).1 (hrun.cutLaw y hy k _ (projAC_callAt.mp hc))
      have hΦ : FrameOK ℓ.frame := hlaw.1 ▸ frameOK_state' hrun.toLocalRun' hy k
      have hex := hlaw.2.1
      rw [← projAC_state' hrun.toLocalRun' hy] at hex
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
        · obtain ⟨j, hj, he⟩ := message_vote' hrun hy hc hm hval
          exact ⟨j, hj.trans hk, he⟩
        · have hs := AC.step_emission_signer y _ _ _ _ hΦ (hrun.time_nonneg k) he
          have hvy : v.val = y := hev ▸ hs
          rw [hex] at he
          exact ⟨k, hk, e, hvy.symm ▸ ⟨ℓ, hc, he⟩, hev⟩

/-- A block of an honest frame is genesis or was accepted by an honest node (a copy of
`frame_block_cases`). -/
private theorem frame_block_cases' (hrun : GoldilocksRun' proposer dg H tr ini)
    {B : Blk sp.n (List (FG.Att sp.n))} (hB : AC.HonestFrameBlock tr.projAC H B) :
    B = sp.toParams.genesisBlock (goldilocksNode' sp ro).genesisPayload ∨
      ∃ y ∈ H, ∃ k, tr.AcceptAt y k B := by
  obtain ⟨y, hy, i, ℓ, hc, hB⟩ := hB
  rcases tree_cases_pending hrun.toLocalRun' hy (frame_tree' hrun hy hc hB) with h | ⟨k, -, hk⟩
  · exact Or.inl h
  · exact Or.inr ⟨y, hy, k, hk⟩

/-- An accepted block of an honest proposer is its own proposal, at the third cut of its tick at
the start of the block's slot, which is not slot `0` (a copy of `own_tick`). -/
private theorem own_tick' (hrun : GoldilocksRun' proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat}
    {B : Blk sp.n (List (FG.Att sp.n))} (hk : tr.AcceptAt y k B) (hp : B.proposer ∈ H) :
    ∃ j₀ acc, tr.TickAt' proposer dg B.proposer j₀ (tr.time (j₀ + 2)) ∧
      tr.CallAt B.proposer (j₀ + 2) (.fg (.block B acc)) ∧ 0 < B.slot ∧
      tr.time (j₀ + 2) = sp.toParams.slotTime B.slot := by
  obtain ⟨j, -, ⟨acc, hc⟩, hpos⟩ := hrun.block_unforgeable y hy k B ⟨true, hk⟩ hp
  rcases blockCall_cases_pending hrun.toLocalRun' hp hc with hg | ⟨j₀, x, f, rfl, ht, hP, d, p, -,
    hB, -⟩
  · have hg := (RunTrace.groupAt'_iff _ _ _ _ _ _ _).1 hg
    exact absurd (by simpa using (hg.2.1 0 (List.length_pos_of_ne_nil hg.1)).2.2.2.1) hpos
  · have hs : B.slot = sp.toParams.slotOf (tr.time (j₀ + 2)) := by rw [hB]; rfl
    exact ⟨j₀, acc, (RunTrace.tickAt'_iff _ _ _ _ _ _).2 ⟨x, f, ht⟩, hc, hs ▸ hP.1, hs ▸ hP.2.1⟩

private theorem one_block' (hrun : GoldilocksRun' proposer dg H tr ini)
    {B B' : Blk sp.n (List (FG.Att sp.n))}
    (hB : AC.HonestFrameBlock tr.projAC H B) (hB' : AC.HonestFrameBlock tr.projAC H B')
    (hp : B.proposer ∈ H) (hpr : B.proposer = B'.proposer) (hs : B.slot = B'.slot) : B = B' := by
  have hp' : B'.proposer ∈ H := hpr ▸ hp
  rcases frame_block_cases' hrun hB with rfl | ⟨y, hy, k, hk⟩ <;>
    rcases frame_block_cases' hrun hB' with rfl | ⟨y', hy', k', hk'⟩
  · rfl
  · obtain ⟨-, -, -, -, h, -⟩ := own_tick' hrun hy' hk' hp'
    exact absurd hs (by simp [Params.genesisBlock]; omega)
  · obtain ⟨-, -, -, -, h, -⟩ := own_tick' hrun hy hk hp
    exact absurd hs (by simp [Params.genesisBlock]; omega)
  · obtain ⟨j₀, acc, ht, hc, -, htime⟩ := own_tick' hrun hy hk hp
    obtain ⟨j₀', acc', ht', hc', -, htime'⟩ := own_tick' hrun hy' hk' hp'
    rw [hpr, htime, hs, ← htime'] at ht
    rw [hpr] at hc
    obtain rfl := hrun.tick_unique _ hp' j₀ j₀' _ ht ht'
    have := hc.2.symm.trans hc'.2
    simp only [Option.some.injEq, Cut.fg.injEq, FGLabel.block.injEq] at this
    exact this.1

/-- **The honest-object facts of a shadow run's AC projection**, from starts up to the vote
permission (a copy of `goldilocks_ac_projection_from`; the conclusion is the stock `AC.ACRun`, the
AC being the stock one). -/
theorem goldilocks_ac_projection_from' (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : NoCollRun dg tr) :
    AC.ACRun proposer tr.projAC H (tr.HonestBlocks H) ini := by
  have hloc := ac_projection'
    (fun y _ U _ s Φ t₀ h => AC.proposal_payload_valid_from _ (hrun.vstart y).pool y U s Φ t₀ h)
    hrun.toLocalRun' hnc
  refine ⟨hloc, ⟨fun y hy => pool_vote_emitted' hrun hy,
    fun y hy i ℓ v hc hm hval => message_vote' hrun hy hc hm hval, fun B hB hr => ?_,
    fun B B' hB hB' hp hpr hs => one_block' hrun hB hB' hp hpr hs⟩, hrun.vstart⟩
  rcases frame_block_cases' hrun hB with rfl | ⟨y, hy, k, hk⟩
  · exact absurd rfl hr
  · exact (accept_facts_pending hrun.toLocalRun' hy hk).2.1

end Consensus.Goldilocks.Compose

namespace Consensus.Goldilocks.Compose.Growing

variable {sp : AC.ACParams} {ro : AC.ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace' sp ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode' sp ro).State}

/-- **The honest-object facts of a shadow run's AC projection under growing faults** (a copy of
`Growing.goldilocks_ac_projection_from`; the conclusion is the stock growing `AC.Growing.ACRun`). -/
theorem goldilocks_ac_projection_from'
    (h : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : NoCollRun dg tr) :
    AC.Growing.ACRun proposer tr.projAC H (tr.HonestBlocksAt H) ini := by
  sorry

end Consensus.Goldilocks.Compose.Growing

end
