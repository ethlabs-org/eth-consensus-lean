module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.ACProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts

public section

/-! # Goldilocks runs: the AC projection of a Goldilocks run is an AC AC run

The AC projection of a Goldilocks run satisfies the AC trace contract (`ac_projection`, with the
AC's requirements) and the honest-object facts: honest votes in a pool or received were emitted
earlier (message unforgeability; a pooled vote was admitted from a message or emitted by the
node itself: a block admits no vote and a restart empties the pools); a frame block other than
genesis was accepted, so it has its slot's proposer; and an
honest proposer's frame blocks of one slot are its own proposal at that slot's tick, of which
there is one. -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams Payload Vote ACState Blk Frm admitVote blockReceipt
  tryVote optimisticConfirmation updateConfirmation acOnTick acProposal acToFG goldilocksAC)

/-! ### The votes an AC call adds to the pools -/

section Adds

variable {sp : ACParams} {FGP : Type}

/-- The pools of `A'` hold only the votes of the pools of `A` and the votes `S`. -/
private def Adds (A A' : ACState sp.n) (S : Vote sp.n → Prop) : Prop :=
  ∀ σ, ∀ x ∈ A'.pool σ, x ∈ A.pool σ ∨ S x

private theorem Adds.of_eq {A A' : ACState sp.n} {S : Vote sp.n → Prop} (h : A'.pool = A.pool) :
    Adds A A' S :=
  fun _ _ hx => Or.inl (h ▸ hx)

private theorem Adds.trans {A₁ A₂ A₃ : ACState sp.n} {S T U : Vote sp.n → Prop}
    (h₁ : Adds A₁ A₂ S) (h₂ : Adds A₂ A₃ T) (hS : ∀ x, S x → U x) (hT : ∀ x, T x → U x) :
    Adds A₁ A₃ U := by
  intro σ x hx
  rcases h₂ σ x hx with h | h
  · exact (h₁ σ x h).imp_right (hS x)
  · exact Or.inr (hT x h)

private theorem Adds.trans_eq {A₁ A₂ A₃ : ACState sp.n} {S : Vote sp.n → Prop}
    (h : Adds A₁ A₂ S) (he : A₃.pool = A₂.pool) : Adds A₁ A₃ S :=
  fun σ x hx => h σ x (he ▸ hx)

private theorem Adds.mono {A A' : ACState sp.n} {S T : Vote sp.n → Prop} (h : Adds A A' S)
    (hST : ∀ x, S x → T x) : Adds A A' T :=
  fun σ x hx => (h σ x hx).imp_right (hST x)

private theorem adds_admitVote (A : ACState sp.n) (t : Time) (v : Vote sp.n) :
    Adds A (admitVote sp A t v) (· = v) := by
  intro σ x hx
  unfold admitVote at hx
  split_ifs at hx
  · exact Or.inl hx
  · exact Or.inl hx
  · simp only [Function.update_apply] at hx
    split_ifs at hx with hσ
    · rcases List.mem_append.1 hx with h | h
      · exact Or.inl (hσ ▸ h)
      · exact Or.inr (List.mem_singleton.1 h)
    · exact Or.inl hx

/-- A block receipt only stamps the block: it adds no vote. -/
private theorem adds_blockReceipt (A : ACState sp.n) (t : Time) (B : Blk sp.n FGP) :
    Adds A (blockReceipt sp A t B) (fun _ => False) :=
  Adds.of_eq rfl

private theorem adds_tryVote (x : Fin sp.n) (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    Adds A (tryVote sp x A Φ t).1 (fun v => ∃ e ∈ (tryVote sp x A Φ t).2, e.msg = v) := by
  unfold tryVote
  lift_lets
  extract_lets s V A₁ dom H A₂ vote A₃
  have hA₂ : A₂.pool = A.pool := by simp only [A₂, A₁]; split <;> rfl
  split_ifs with h₁ h₂ h₃
  · exact Adds.of_eq rfl
  · exact Adds.of_eq rfl
  · intro σ v hv
    simp only [A₃, h₃, ↓reduceIte, AC.optimistic_pool_eq] at hv
    rcases adds_admitVote _ _ _ σ v hv with h | h
    · exact Or.inl (hA₂ ▸ h)
    · exact Or.inr ⟨_, List.mem_singleton_self _, h.symm⟩
  · exact Adds.of_eq (by simpa only [A₃, h₃, Bool.false_eq_true, ↓reduceIte] using hA₂)

/-- An emitted own vote enters its pool when no vote of its signer was present
at the `tryVote` input. In particular, the two-vote cap cannot reject it. -/
theorem tryVote_emission_mem_pool (x : Fin sp.n) (A : ACState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (e : AC.Em sp FGP)
    (he : e ∈ (tryVote sp x A Φ t).2)
    (hf : ∀ m ∈ A.pool e.msg.slot, m.val ≠ x) :
    e.msg ∈ (tryVote sp x A Φ t).1.pool e.msg.slot := by
  revert he
  unfold tryVote
  lift_lets
  extract_lets s V A₁ dom H A₂ vote A₃
  split_ifs with h₁ h₂ h₃ <;> intro he <;>
    simp only [List.not_mem_nil, List.mem_singleton] at he
  subst e
  simp only [A₃, h₃, ↓reduceIte, AC.optimistic_pool_eq, A₂, A₁, vote, s]
  split
  all_goals
    have hfilter : (A.pool (sp.slot t)).filter (fun m => m.val = x) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro m hm
      simpa only [decide_eq_true_eq] using hf m hm
    have hn : ∀ h, (⟨x, sp.slot t, h⟩ : Vote sp.n) ∉ A.pool (sp.slot t) := by
      intro h hm
      exact hf _ hm rfl
    have hslot : ¬ ((sp.slot t : Int) < (sp.slot t : Int) - 1) := by omega
    simp [admitVote, hn, hfilter, hslot]

/-- A call other than a restart adds to the pools only its message and its emissions (a block
call admits none of its declared head votes). -/
private theorem adds_step (self : Fin sp.n) (A : ACState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (c : (goldilocksAC sp FGP).Call) (hc : c ≠ .restart) :
    Adds A ((goldilocksAC sp FGP).step self A Φ t c).1 (fun v => c = .message v ∨
      ∃ e ∈ ((goldilocksAC sp FGP).step self A Φ t c).2, e.msg = v) := by
  cases c with
  | tick =>
    change Adds A (acOnTick sp self A Φ t).1
      (fun v => _ ∨ ∃ e ∈ (acOnTick sp self A Φ t).2, e.msg = v)
    unfold acOnTick
    dsimp only
    split_ifs
    · exact ((adds_tryVote _ _ _ _).trans_eq (AC.updateConfirmation_pool_eq _ _ _ _)).mono
        fun _ h => Or.inr h
    · exact Adds.of_eq (AC.updateConfirmation_pool_eq _ _ _ _)
    · exact (adds_tryVote _ _ _ _).mono fun _ h => Or.inr h
    · exact Adds.of_eq rfl
    · exact Adds.of_eq rfl
  | proposal =>
    change Adds A (acProposal sp A Φ t).1 _
    unfold acProposal
    dsimp only
    split_ifs <;> exact Adds.of_eq rfl
  | toFG =>
    change Adds A (acToFG sp A Φ t).1 _
    unfold acToFG
    split_ifs <;> exact Adds.of_eq rfl
  | message m =>
    exact ((adds_admitVote A t m).trans_eq (AC.optimistic_pool_eq _ _ _)).trans
      (adds_tryVote _ _ _ _) (fun _ h => Or.inl (h ▸ rfl)) (fun _ h => Or.inr h)
  | block B =>
    exact ((adds_blockReceipt A t B).trans_eq (AC.optimistic_pool_eq _ _ _)).trans
      (adds_tryVote _ _ _ _) (fun _ h => h.elim) (fun _ h => Or.inr h)
  | restart => exact absurd rfl hc

/-- A fresh non-restart pool insertion is a message or an own emission (a block call admits
no vote). This is the exact candidate set used by the forwarding queue. -/
theorem step_pool_insertion_source (self : Fin sp.n)
    (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (c : (goldilocksAC sp FGP).Call) (hc : c ≠ .restart) (m : Vote sp.n)
    (hold : m ∉ A.pool m.slot)
    (hnew : m ∈ ((goldilocksAC sp FGP).step self A Φ t c).1.pool m.slot) :
    c = .message m ∨ ∃ e ∈ ((goldilocksAC sp FGP).step self A Φ t c).2, e.msg = m :=
  (adds_step self A Φ t c hc m.slot m hnew).resolve_left hold

end Adds

/-! ### In the run -/

/-- The Goldilocks node's AC started at a start up to the vote permission meets the interface
requirements 1–5 (A0.6, A0.9), at the states reachable from that start. -/
theorem requirements_from (sp : ACParams)
    {s₀ : AC.ACState sp.n} (h₀ : AC.VoteStart sp.genesisRoot s₀) :
    ({ goldilocksNode sp with initial := s₀ } : NodeAC sp.toParams).Requirements :=
  have h := AC.interface_requirements_from sp (List (FG.Att sp.n)) h₀
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, fun self U _ s Φ t₀ hr =>
    AC.proposal_payload_valid_from sp h₀.pool self U s Φ t₀ (ACInterface.reachableAtFrom_iff.2 hr)⟩

/-- The Goldilocks node's AC meets the interface requirements 1–5 (A0.6, A0.9):
`requirements_from` at the initial state. -/
theorem requirements (sp : ACParams) :
    (goldilocksNode sp).Requirements :=
  requirements_from sp (s₀ := AC.ACState.initial sp.genesisRoot) (AC.voteStart_initial _)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp).State}

/-- Every projected send/admission has precisely one of the forwarding supplier's
sources: an emission, or a fresh message insertion. Restart replay is excluded. -/
theorem sendOrAdmit_forward_source (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {m : Vote sp.n}
    (h : tr.projAC.SendOrAdmit y k m) :
    tr.EmitAt y k m ∨
      (tr.MsgCallAt y k m ∧
        m ∉ (tr.state y k).ac.pool m.slot ∧ m ∈ (tr.post k).ac.pool m.slot) := by
  obtain ⟨ℓ, hc, he | ⟨hnr, hold, hnew⟩⟩ := h
  · exact Or.inl ⟨ℓ, projAC_callAt.mp hc, he⟩
  · have hex := (hrun.cutLaw y hy k _ (projAC_callAt.mp hc)).2.1
    rw [← projAC_state hrun.toLocalRun hy] at hex
    have ha := adds_step y (tr.projAC.state y k) ℓ.frame (tr.time k) ℓ.call hnr
    rw [hex] at ha
    have hold' : m ∉ (tr.projAC.state y k).pool m.slot := hold
    have hnew' : m ∈ (tr.post k).ac.pool m.slot := hnew
    rcases ha m.slot m hnew' with hm | hm | ⟨e, he, hm⟩
    · exact False.elim (hold' hm)
    · exact Or.inr ⟨⟨ℓ, projAC_callAt.mp hc, hm⟩,
        by rwa [projAC_state hrun.toLocalRun hy] at hold', hnew'⟩
    · exact Or.inl ⟨ℓ, projAC_callAt.mp hc, e, he, hm⟩

/-- The frame of an honest AC call is inside the node's tree. -/
private theorem frame_tree (hrun : GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y i ℓ)
    {B : Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree) :
    B ∈ (tr.state y i).fg.tree := by
  obtain ⟨hf, -⟩ := hrun.cutLaw y hy i _ (projAC_callAt.1 hc)
  rw [hf] at hB
  exact hB.1

/-- An emission of the run is a vote of the AC projection. -/
private theorem emit_voteAt {x : Fin sp.n} {j : Nat} {v : Vote sp.n} (h : tr.EmitAt x j v) :
    ∃ e, AC.VoteAt tr.projAC x j e ∧ e.msg = v := by
  obtain ⟨ℓ, hc, e, he, rfl⟩ := h
  exact ⟨e, ⟨ℓ, projAC_callAt.2 hc, he⟩, rfl⟩

/-- Honest emissions at different cuts have different slots without assuming `NoCollRun`.
Individual FG stores supply well-formed frames; no global block-root injection is needed. -/
theorem emitted_vote_slots_ne (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {i j : Nat} (hij : i < j) {v w : Vote sp.n}
    (hv : tr.EmitAt y i v) (hw : tr.EmitAt y j w) : v.slot ≠ w.slot := by
  obtain ⟨e, he, rfl⟩ := emit_voteAt hv
  obtain ⟨e', he', rfl⟩ := emit_voteAt hw
  apply AC.vote_slot_ne_of_exec hrun.time_nonneg hrun.time_mono ?_ ?_ hy hij he he'
  · intro x hx k ℓ hc
    rw [projAC_state hrun.toLocalRun hx]
    exact (hrun.cutLaw x hx k _ (projAC_callAt.mp hc)).2.1
  · intro x hx k ℓ hc
    have hf := (hrun.cutLaw x hx k _ (projAC_callAt.mp hc)).1
    exact hf ▸ (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hx k)).1

/-- Before an honest emission, no wire message processed by an honest node is a vote of that
signer and slot. This includes the emitting cut. -/
theorem emitted_slot_not_received (hrun : GoldilocksRun proposer dg H tr ini)
    {y x : Fin sp.n} (hy : y ∈ H) (hx : x ∈ H) {i k : Nat} (hki : k ≤ i)
    {v m : Vote sp.n} (hv : tr.EmitAt y i v) (hm : m.val = y) (hs : m.slot = v.slot) :
    ¬ tr.MsgCallAt x k m := by
  intro hc
  have he : ∃ j < k, tr.EmitAt y j m := by
    simpa only [hm] using hrun.msg_unforgeable x hx k m hc (hm ▸ hy)
  obtain ⟨j, hj, he⟩ := he
  exact emitted_vote_slots_ne hrun hy (hj.trans_le hki) he hv hs

private theorem message_vote (hrun : GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksNode sp)} {v : Vote sp.n}
    (hc : tr.projAC.CallAt y i ℓ) (hm : ℓ.call = .message v) (hval : v.val ∈ H) :
    ∃ j < i, ∃ e, AC.VoteAt tr.projAC v.val j e ∧ e.msg = v := by
  obtain ⟨j, hj, he⟩ := hrun.msg_unforgeable y hy i v ⟨ℓ, projAC_callAt.1 hc, hm⟩ hval
  exact ⟨j, hj, emit_voteAt he⟩

/-- Honest votes in a stored pool have an earlier emission, from starts up to the vote permission
(whose pools are empty; a restart empties the pools and a block admits no vote). Only individual
frame well-formedness is needed, not `NoCollRun`. -/
theorem pool_vote_emitted (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) (i σ : Nat) (v : Vote sp.n)
    (hv : v ∈ (tr.projAC.state y i).pool σ) (hval : v.val ∈ H) :
    ∃ j < i, ∃ e, AC.VoteAt tr.projAC v.val j e ∧ e.msg = v := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    rcases tr.projAC.noCall_or_lastCall y i with hn | ⟨k, hk, ℓ, hc, hn⟩
    · rw [tr.projAC.state_of_noCall hn] at hv
      simp [RunTrace.projAC, hrun.init y hy, Node.initWith, (hrun.vstart y).pool] at hv
    · rw [tr.projAC.state_of_lastCall hc hk hn] at hv
      have hf := (hrun.cutLaw y hy k _ (projAC_callAt.mp hc)).1
      have hΦ : FrameOK ℓ.frame :=
        hf ▸ (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy k)).1
      have hex := (hrun.cutLaw y hy k _ (projAC_callAt.mp hc)).2.1
      rw [← projAC_state hrun.toLocalRun hy] at hex
      by_cases hr : ℓ.call = .restart
      · have hs := AC.restart_state sp _ y (tr.projAC.state y k) ℓ.frame
          (tr.time k) hΦ (hrun.time_nonneg k)
        have hp : (AC.acRestart sp y (tr.projAC.state y k) ℓ.frame (tr.time k)).1 =
            tr.projAC.post k := by
          simpa [hr, ACInterface.step, RunTrace.projAC] using congrArg Prod.fst hex
        rw [← hp, hs.2.2.2.2.2.2.2.1 σ] at hv
        exact absurd hv List.not_mem_nil
      · have ha := adds_step y (tr.projAC.state y k) ℓ.frame (tr.time k) ℓ.call hr
        rw [hex] at ha
        rcases ha σ v hv with hv | hm | ⟨e, he, hev⟩
        · obtain ⟨j, hj, he⟩ := ih k hk hv
          exact ⟨j, hj.trans hk, he⟩
        · obtain ⟨j, hj, he⟩ := message_vote hrun hy hc hm hval
          exact ⟨j, hj.trans hk, he⟩
        · have he' : e ∈ ((goldilocksAC sp _).step y (tr.projAC.state y k)
              ℓ.frame (tr.time k) ℓ.call).2 := by rw [hex]; exact he
          have hs := AC.step_emission_signer y _ _ _ _ hΦ (hrun.time_nonneg k) he'
          have hvy : v.val = y := hev ▸ hs
          exact ⟨k, hk, e, hvy.symm ▸ ⟨ℓ, hc, he⟩, hev⟩

/-- The pool form and capacity invariant needs no global block-root injectivity. -/
theorem state_pool_cap (hrun : GoldilocksRun proposer dg H tr ini)
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
      have hex := (hrun.cutLaw y hy k _ (projAC_callAt.mp hc)).2.1
      rw [← projAC_state hrun.toLocalRun hy] at hex
      have h := AC.step_pool_cap y (tr.projAC.state y k) ℓ.frame (tr.time k)
        ℓ.call (ih k hk)
      rw [hex] at h
      exact h

/-- Non-restart pool retention uses the local step law only, not a coherent
global block universe. The restart-free interval is explicit. -/
theorem pool_mono (hrun : GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {a b : Nat} (hab : a ≤ b)
    (hnr : ∀ k, a ≤ k → k < b → ¬ tr.RestartAt y k) (σ : Nat) :
    (tr.projAC.state y a).pool σ ⊆ (tr.projAC.state y b).pool σ := by
  induction b, hab using Nat.le_induction with
  | base => exact List.Subset.refl _
  | succ b hab ih =>
    intro v hv
    have hp := ih (fun k hk hkb => hnr k hk (hkb.trans (Nat.lt_succ_self b))) hv
    by_cases hn : tr.projAC.node b = y ∧ tr.projAC.label b ≠ none
    · obtain ⟨ℓ, hl⟩ := Option.ne_none_iff_exists'.mp hn.2
      have hc : tr.projAC.CallAt y b ℓ := ⟨hn.1, hl⟩
      rw [tr.projAC.state_succ_of_call hc]
      have hex := (hrun.cutLaw y hy b _ (projAC_callAt.mp hc)).2.1
      rw [← projAC_state hrun.toLocalRun hy] at hex
      have hg := AC.step_pool_subset y (tr.projAC.state y b) ℓ.frame (tr.time b)
        ℓ.call (fun hr => hnr b hab (Nat.lt_succ_self b) ⟨ℓ, projAC_callAt.mp hc, hr⟩) σ hp
      rw [hex] at hg
      exact hg
    · rw [tr.projAC.state_succ_of_not (fun ℓ hc => hn ⟨hc.1, by simp [hc.2]⟩)]
      exact hp

/-- Before an honest emission, no honest stored pool contains a vote of its signer and slot. -/
theorem emitted_slot_not_pooled (hrun : GoldilocksRun proposer dg H tr ini)
    {y x : Fin sp.n} (hy : y ∈ H) (hx : x ∈ H) {i k : Nat} (hki : k ≤ i)
    {v m : Vote sp.n} (hv : tr.EmitAt y i v) (hm : m.val = y) (hs : m.slot = v.slot)
    (σ : Nat) : m ∉ (tr.projAC.state x k).pool σ := by
  intro hp
  obtain ⟨j, hj, e, ⟨ℓ, hc, he⟩, hev⟩ := pool_vote_emitted hrun hx k σ m hp (hm ▸ hy)
  have hem : tr.EmitAt y j m := hm ▸ ⟨ℓ, projAC_callAt.mp hc, e, he, hev⟩
  exact emitted_vote_slots_ne hrun hy (hj.trans_le hki) hem hv hs

/-- An honest emission really enters the post-call pool, without a collision
assumption. Incoming votes of this signer and slot cannot precede its emission. -/
theorem emitted_vote_mem_post (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {v : Vote sp.n}
    (hv : tr.EmitAt y i v) : v ∈ (tr.post i).ac.pool v.slot := by
  obtain ⟨ℓ, hc, e, he, rfl⟩ := hv
  have hv : tr.EmitAt y i e.msg := ⟨ℓ, hc, e, he, rfl⟩
  have hex := (hrun.cutLaw y hy i _ hc).2.1
  rw [← projAC_state hrun.toLocalRun hy] at hex
  have hem : e ∈ ((goldilocksAC sp _).step y (tr.projAC.state y i)
      ℓ.frame (tr.time i) ℓ.call).2 := by rw [hex]; exact he
  have hcap := state_pool_cap hrun hy i
  have hf : ∀ m ∈ (tr.projAC.state y i).pool e.msg.slot, m.val ≠ y := by
    intro m hm hmy
    exact emitted_slot_not_pooled hrun hy hy le_rfl hv hmy
      ((hcap _).1 m hm) _ hm
  have hrecv := fun (m : Vote sp.n) (hm : m.val = y) (hs : m.slot = e.msg.slot) =>
    emitted_slot_not_received hrun hy hy le_rfl hv hm hs
  have hΦ : FrameOK ℓ.frame := (hrun.cutLaw y hy i _ hc).1 ▸
    (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).1
  have hgoal : e.msg ∈ ((goldilocksAC sp _).step y (tr.projAC.state y i)
      ℓ.frame (tr.time i) ℓ.call).1.pool e.msg.slot := by
    cases hcall : ℓ.call with
    | tick =>
      rw [hcall] at hem
      change e ∈ (acOnTick sp y _ ℓ.frame _).2 at hem
      change e.msg ∈ (acOnTick sp y _ ℓ.frame _).1.pool e.msg.slot
      unfold acOnTick at hem ⊢
      dsimp only at hem ⊢
      split_ifs at hem ⊢ <;> try simp at hem
      all_goals
        try rw [AC.updateConfirmation_pool_eq]
        exact tryVote_emission_mem_pool y _ _ _ e hem hf
    | message m =>
      rw [hcall] at hem
      apply tryVote_emission_mem_pool y _ _ _ e hem
      intro w hw hwy
      rw [AC.optimistic_pool_eq] at hw
      have hs := (AC.receipt_pool_slot (FGP := List (FG.Att sp.n)) _ (tr.time i) hcap).1 m _ w hw
      rcases adds_admitVote _ _ _ _ w hw with hw | rfl
      · exact hf w hw hwy
      · exact hrecv _ hwy hs ⟨ℓ, hc, hcall⟩
    | block B =>
      rw [hcall] at hem
      apply tryVote_emission_mem_pool y _ _ _ e hem
      intro w hw hwy
      rw [AC.optimistic_pool_eq] at hw
      rcases adds_blockReceipt _ _ _ _ w hw with hold | hblock
      · exact hf w hold hwy
      · exact hblock.elim
    | proposal => simp [hcall, ACInterface.step] at hem
    | toFG => simp [hcall, ACInterface.step] at hem
    | restart =>
      rw [hcall] at hem
      have hn := (AC.restart_state sp _ y (tr.projAC.state y i) ℓ.frame (tr.time i) hΦ
        (hrun.time_nonneg i)).1
      change e ∈ (AC.acRestart sp y _ ℓ.frame (tr.time i)).2 at hem
      rw [hn] at hem
      exact False.elim (List.not_mem_nil hem)
  rw [hex] at hgoal
  exact hgoal

/-- A block of an honest frame is genesis or was accepted by an honest node. -/
private theorem frame_block_cases (hrun : GoldilocksRun proposer dg H tr ini)
    {B : Blk sp.n (List (FG.Att sp.n))} (hB : AC.HonestFrameBlock tr.projAC H B) :
    B = sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload ∨
      ∃ y ∈ H, ∃ k, tr.AcceptAt y k B := by
  obtain ⟨y, hy, i, ℓ, hc, hB⟩ := hB
  rcases tree_cases hrun.toLocalRun hy (frame_tree hrun hy hc hB) with h | ⟨k, -, hk⟩
  · exact Or.inl h
  · exact Or.inr ⟨y, hy, k, hk⟩

/-- An accepted block of an honest proposer is its own proposal, at the third cut of its tick at
the start of the block's slot, which is not slot `0`. -/
private theorem own_tick (hrun : GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat}
    {B : Blk sp.n (List (FG.Att sp.n))} (hk : tr.AcceptAt y k B) (hp : B.proposer ∈ H) :
    ∃ j₀ acc, tr.TickAt proposer dg B.proposer j₀ (tr.time (j₀ + 2)) ∧
      tr.CallAt B.proposer (j₀ + 2) (.fg (.block B acc)) ∧ 0 < B.slot ∧
      tr.time (j₀ + 2) = sp.toParams.slotTime B.slot := by
  obtain ⟨j, -, ⟨acc, hc⟩, hpos⟩ := hrun.block_unforgeable y hy k B ⟨true, hk⟩ hp
  rcases blockCall_cases hrun.toLocalRun hp hc with hg | ⟨j₀, x, f, rfl, ht, hP, d, p, -, hB, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_of_ne_nil hg.1)).2.2.2.1) hpos
  · have hs : B.slot = sp.toParams.slotOf (tr.time (j₀ + 2)) := by rw [hB]; rfl
    exact ⟨j₀, acc, ⟨x, f, ht⟩, hc, hs ▸ hP.1, hs ▸ hP.2.1⟩

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

/-- **The honest-object facts of the Goldilocks run's AC projection**, from starts up to the
vote permission: the AC run from the run's starts (`ac_projection`, its requirement 5 from
those starts by `AC.proposal_payload_valid_from`, their pools being empty). -/
theorem goldilocks_ac_projection_from (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) :
    AC.ACRun proposer tr.projAC H (tr.HonestBlocks H) ini := by
  have hloc := ac_projection _ _ dg H _ tr proposer
    (fun y _ U _ s Φ t₀ h => AC.proposal_payload_valid_from _ (hrun.vstart y).pool y U s Φ t₀ h)
    hrun.toLocalRun hnc
  refine ⟨hloc, ⟨fun y hy => pool_vote_emitted hrun hy,
    fun y hy i ℓ v hc hm hval => message_vote hrun hy hc hm hval, fun B hB hr => ?_,
    fun B B' hB hB' hp hpr hs => one_block hrun hB hB' hp hpr hs⟩, hrun.vstart⟩
  rcases frame_block_cases hrun hB with rfl | ⟨y, hy, k, hk⟩
  · exact absurd rfl hr
  · exact (accept_facts hrun.toLocalRun hy hk).2.1

/-- **The honest-object facts of the Goldilocks run's AC projection**:
`goldilocks_ac_projection_from` at the initial starts. -/
theorem goldilocks_ac_projection : GoldilocksACProjection :=
  fun _ _ _ _ _ hrun hnc =>
    goldilocks_ac_projection_from hrun hnc

end Consensus.Goldilocks.Compose

end
