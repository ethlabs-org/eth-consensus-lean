module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.ACProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts

public section

/-! # Goldilocks runs: the AC projection of a Goldilocks run is an SA AC run

The AC projection of a Goldilocks run satisfies the AC trace contract (`ac_projection`, with the
SA's requirements) and the honest-object facts: honest votes in a pool, received, or carried by a
frame block were emitted earlier (message and carried-vote unforgeability; a pooled vote was
admitted from one of these, emitted by the node itself, or put back by a restart from a frame
block); a frame block other than genesis was accepted, so it has its slot's proposer; and an
honest proposer's frame blocks of one slot are its own proposal at that slot's tick, of which
there is one. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote SAState Blk Frm blockVotes admitVote blockReceipt
  tryVote optimisticConfirmation updateConfirmation acOnTick acProposal acToFG goldilocksSA)

/-! ### The votes an SA call adds to the pools -/

section Adds

variable {sp : SAParams} {FGP : Type}

/-- The pools of `A'` hold only the votes of the pools of `A` and the votes `S`. -/
private def Adds (A A' : SAState sp.n) (S : Vote sp.n → Prop) : Prop :=
  ∀ σ, ∀ x ∈ A'.pool σ, x ∈ A.pool σ ∨ S x

private theorem Adds.of_eq {A A' : SAState sp.n} {S : Vote sp.n → Prop} (h : A'.pool = A.pool) :
    Adds A A' S :=
  fun _ _ hx => Or.inl (h ▸ hx)

private theorem Adds.trans {A₁ A₂ A₃ : SAState sp.n} {S T U : Vote sp.n → Prop}
    (h₁ : Adds A₁ A₂ S) (h₂ : Adds A₂ A₃ T) (hS : ∀ x, S x → U x) (hT : ∀ x, T x → U x) :
    Adds A₁ A₃ U := by
  intro σ x hx
  rcases h₂ σ x hx with h | h
  · exact (h₁ σ x h).imp_right (hS x)
  · exact Or.inr (hT x h)

private theorem Adds.trans_eq {A₁ A₂ A₃ : SAState sp.n} {S : Vote sp.n → Prop}
    (h : Adds A₁ A₂ S) (he : A₃.pool = A₂.pool) : Adds A₁ A₃ S :=
  fun σ x hx => h σ x (he ▸ hx)

private theorem Adds.mono {A A' : SAState sp.n} {S T : Vote sp.n → Prop} (h : Adds A A' S)
    (hST : ∀ x, S x → T x) : Adds A A' T :=
  fun σ x hx => (h σ x hx).imp_right (hST x)

private theorem adds_admitVote (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
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

private theorem adds_foldl (A : SAState sp.n) (t : Time) (S : Vote sp.n → Prop) :
    ∀ (l : List (Vote sp.n)) (A' : SAState sp.n), Adds A A' S → (∀ v ∈ l, S v) →
      Adds A (l.foldl (fun A v => admitVote sp A t v) A') S
  | [], _, h, _ => h
  | v :: l, A', h, hl =>
    adds_foldl A t S l _ (h.trans (adds_admitVote A' t v) (fun _ h => h)
      (fun _ h => h ▸ hl v List.mem_cons_self)) (fun w hw => hl w (List.mem_cons_of_mem _ hw))

private theorem adds_blockReceipt (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    Adds A (blockReceipt sp A t B) (· ∈ blockVotes B) :=
  adds_foldl A t _ _ _ (Adds.of_eq rfl) (fun _ h => h)

private theorem optimistic_pool (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).pool = A.pool := by
  unfold optimisticConfirmation SA.updateLatestConfirmed
  split
  · rfl
  · split_ifs <;> rfl

private theorem updateConfirmation_pool (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) : (updateConfirmation sp A Φ t s).pool = A.pool := by
  unfold updateConfirmation SA.updateLatestConfirmed
  dsimp only
  split
  · rfl
  · split_ifs <;> rfl

private theorem adds_tryVote (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    Adds A (tryVote sp x A Φ t).1 (fun v => ∃ e ∈ (tryVote sp x A Φ t).2, e.msg = v) := by
  unfold tryVote
  dsimp only
  split_ifs
  · exact Adds.of_eq rfl
  · exact Adds.of_eq rfl
  all_goals
    intro σ v hv
    rw [optimistic_pool] at hv
    rcases adds_admitVote _ _ _ σ v hv with h | h
    · exact Or.inl h
    · exact Or.inr ⟨_, List.mem_singleton_self _, h.symm⟩

/-- An emitted own vote enters its pool when no vote of its signer was present
at the `tryVote` input. In particular, the two-vote cap cannot reject it. -/
theorem tryVote_emission_mem_pool (x : Fin sp.n) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (e : SA.Em sp FGP)
    (he : e ∈ (tryVote sp x A Φ t).2)
    (hf : ∀ m ∈ A.pool e.msg.slot, m.val ≠ x) :
    e.msg ∈ (tryVote sp x A Φ t).1.pool e.msg.slot := by
  unfold tryVote at he ⊢
  dsimp only at he ⊢
  split_ifs at he ⊢ <;> simp only [List.not_mem_nil, List.mem_singleton] at he
  all_goals
    subst e
    rw [optimistic_pool]
    have hfilter : (A.pool (sp.slot t)).filter (fun m => m.val = x) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro m hm
      simpa only [decide_eq_true_eq] using hf m hm
    have hn : ∀ h, (⟨x, sp.slot t, h⟩ : Vote sp.n) ∉ A.pool (sp.slot t) := by
      intro h hm
      exact hf _ hm rfl
    have hslot : ¬ ((sp.slot t : Int) < (sp.slot t : Int) - 1) := by omega
    simp [admitVote, hn, hfilter, hslot]

/-- A call other than a restart adds to the pools only its message, the votes of its block, and
its emissions. -/
private theorem adds_step {ro : ReplayOrder sp FGP} (self : Fin sp.n) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (c : (goldilocksSA sp FGP ro).Call) (hc : c ≠ .restart) :
    Adds A ((goldilocksSA sp FGP ro).step self A Φ t c).1 (fun v => c = .message v ∨
      (∃ B, c = .block B ∧ v ∈ blockVotes B) ∨
      ∃ e ∈ ((goldilocksSA sp FGP ro).step self A Φ t c).2, e.msg = v) := by
  cases c with
  | tick =>
    change Adds A (acOnTick sp self A Φ t).1
      (fun v => _ ∨ _ ∨ ∃ e ∈ (acOnTick sp self A Φ t).2, e.msg = v)
    unfold acOnTick
    dsimp only
    split_ifs
    · exact ((adds_tryVote _ _ _ _).trans_eq (updateConfirmation_pool _ _ _ _)).mono
        fun _ h => Or.inr (Or.inr h)
    · exact Adds.of_eq (updateConfirmation_pool _ _ _ _)
    · exact (adds_tryVote _ _ _ _).mono fun _ h => Or.inr (Or.inr h)
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
    dsimp only
    split_ifs
    · split
      · exact Adds.of_eq rfl
      · split_ifs <;> exact Adds.of_eq rfl
    · exact Adds.of_eq rfl
  | message m =>
    exact ((adds_admitVote A t m).trans_eq (optimistic_pool _ _ _)).trans
      (adds_tryVote _ _ _ _) (fun _ h => Or.inl (h ▸ rfl)) (fun _ h => Or.inr (Or.inr h))
  | block B =>
    exact ((adds_blockReceipt A t B).trans_eq (optimistic_pool _ _ _)).trans
      (adds_tryVote _ _ _ _) (fun _ h => Or.inr (Or.inl ⟨B, rfl, h⟩))
      (fun _ h => Or.inr (Or.inr h))
  | restart => exact absurd rfl hc

end Adds

/-! ### In the run -/

/-- The Goldilocks node's AC meets the interface requirements 1–5 (A0.6, A0.9). -/
private theorem requirements (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n))) :
    (goldilocksNode sp ro).Requirements :=
  have h := SA.interface_requirements sp (List (FG.Att sp.n)) ro
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, SA.proposal_payload_valid sp _ ro⟩

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- Every projected send/admission has precisely one of the forwarding supplier's
sources: an emission, or a fresh message/payload insertion. Restart replay is excluded. -/
theorem sendOrAdmit_forward_source (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {m : Vote sp.n}
    (h : tr.projAC.SendOrAdmit y k m) :
    tr.EmitAt y k m ∨
      ((tr.MsgCallAt y k m ∨ ∃ ℓ B, tr.CallAt y k (.ac ℓ) ∧ ℓ.call = .block B ∧
          m ∈ blockVotes B) ∧
        m ∉ (tr.state y k).ac.pool m.slot ∧ m ∈ (tr.post k).ac.pool m.slot) := by
  obtain ⟨ℓ, hc, he | ⟨hnr, hold, hnew⟩⟩ := h
  · exact Or.inl ⟨ℓ, projAC_callAt.mp hc, he⟩
  · have hex := (hrun.cutLaw y hy k _ (projAC_callAt.mp hc)).2.1
    rw [← projAC_state hrun.toLocalRun hy] at hex
    have ha := adds_step (ro := ro) y (tr.projAC.state y k) ℓ.frame (tr.time k) ℓ.call hnr
    rw [hex] at ha
    have hold' : m ∉ (tr.projAC.state y k).pool m.slot := hold
    have hnew' : m ∈ (tr.post k).ac.pool m.slot := hnew
    rcases ha m.slot m hnew' with hm | hm | ⟨B, hb, hm⟩ | ⟨e, he, hm⟩
    · exact False.elim (hold' hm)
    · exact Or.inr ⟨Or.inl ⟨ℓ, projAC_callAt.mp hc, hm⟩,
        by rwa [projAC_state hrun.toLocalRun hy] at hold', hnew'⟩
    · exact Or.inr ⟨Or.inr ⟨ℓ, B, projAC_callAt.mp hc, hb, hm⟩,
        by rwa [projAC_state hrun.toLocalRun hy] at hold', hnew'⟩
    · exact Or.inl ⟨ℓ, projAC_callAt.mp hc, e, he, hm⟩

/-- The frame of an honest AC call is inside the node's tree. -/
private theorem frame_tree (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ℓ)
    {B : Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree) :
    B ∈ (tr.state y i).fg.tree := by
  obtain ⟨hf, -⟩ := hrun.cutLaw y hy i _ (projAC_callAt.1 hc)
  rw [hf] at hB
  exact hB.1

/-- An emission of the run is a vote of the AC projection. -/
private theorem emit_voteAt {x : Fin sp.n} {j : Nat} {v : Vote sp.n} (h : tr.EmitAt x j v) :
    ∃ e, SA.VoteAt tr.projAC x j e ∧ e.msg = v := by
  obtain ⟨ℓ, hc, e, he, rfl⟩ := h
  exact ⟨e, ⟨ℓ, projAC_callAt.2 hc, he⟩, rfl⟩

/-- Honest emissions at different cuts have different slots without assuming `NoCollRun`.
Individual FG stores supply well-formed frames; no global block-root injection is needed. -/
theorem emitted_vote_slots_ne (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) {i j : Nat} (hij : i < j) {v w : Vote sp.n}
    (hv : tr.EmitAt y i v) (hw : tr.EmitAt y j w) : v.slot ≠ w.slot := by
  obtain ⟨e, he, rfl⟩ := emit_voteAt hv
  obtain ⟨e', he', rfl⟩ := emit_voteAt hw
  apply SA.vote_slot_ne_of_exec hrun.time_nonneg hrun.time_mono ?_ ?_ hy hij he he'
  · intro x hx k ℓ hc
    rw [projAC_state hrun.toLocalRun hx]
    exact (hrun.cutLaw x hx k _ (projAC_callAt.mp hc)).2.1
  · intro x hx k ℓ hc
    have hf := (hrun.cutLaw x hx k _ (projAC_callAt.mp hc)).1
    exact hf ▸ (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hx k)).1

/-- Before an honest emission, neither a wire message nor a block payload processed by an
honest node can contain a vote of that signer and slot. This includes the emitting cut. -/
theorem emitted_slot_not_received (hrun : GoldilocksRun proposer dg H tr)
    {y x : Fin sp.n} (hy : y ∈ H) (hx : x ∈ H) {i k : Nat} (hki : k ≤ i)
    {v m : Vote sp.n} (hv : tr.EmitAt y i v) (hm : m.val = y) (hs : m.slot = v.slot) :
    ¬ (tr.MsgCallAt x k m ∨ ∃ B, tr.BlockCallAt x k B ∧ m ∈ blockVotes B) := by
  intro hc
  have he : ∃ j < k, tr.EmitAt y j m := by
    rcases hc with hc | ⟨B, hc, hmem⟩
    · simpa only [hm] using hrun.msg_unforgeable x hx k m hc (hm ▸ hy)
    · simpa only [hm] using hrun.carried_vote_unforgeable x hx k B hc m hmem (hm ▸ hy)
  obtain ⟨j, hj, he⟩ := he
  exact emitted_vote_slots_ne hrun hy (hj.trans_le hki) he hv hs

private theorem message_vote (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {v : Vote sp.n}
    (hc : tr.projAC.CallAt y i ℓ) (hm : ℓ.call = .message v) (hval : v.val ∈ H) :
    ∃ j < i, ∃ e, SA.VoteAt tr.projAC v.val j e ∧ e.msg = v := by
  obtain ⟨j, hj, he⟩ := hrun.msg_unforgeable y hy i v ⟨ℓ, projAC_callAt.1 hc, hm⟩ hval
  exact ⟨j, hj, emit_voteAt he⟩

private theorem carried_vote (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ℓ)
    {B : Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree) {v : Vote sp.n}
    (hv : v ∈ blockVotes B) (hval : v.val ∈ H) :
    ∃ j < i, ∃ e, SA.VoteAt tr.projAC v.val j e ∧ e.msg = v := by
  rcases tree_cases hrun.toLocalRun hy (frame_tree hrun hy hc hB) with rfl | ⟨k, hk, hacc⟩
  · exact absurd hv List.not_mem_nil
  · obtain ⟨j, hj, he⟩ := hrun.carried_vote_unforgeable y hy k B ⟨true, hacc⟩ v hv hval
    exact ⟨j, hj.trans hk, emit_voteAt he⟩

/-- Honest votes in a stored pool have an earlier emission, including votes replayed at
restart. Only individual frame well-formedness is needed, not `NoCollRun`. -/
theorem pool_vote_emitted (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    (hy : y ∈ H) (i σ : Nat) (v : Vote sp.n)
    (hv : v ∈ (tr.projAC.state y i).pool σ) (hval : v.val ∈ H) :
    ∃ j < i, ∃ e, SA.VoteAt tr.projAC v.val j e ∧ e.msg = v := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    rcases tr.projAC.noCall_or_lastCall y i with hn | ⟨k, hk, ℓ, hc, hn⟩
    · rw [tr.projAC.state_of_noCall hn] at hv
      simp [RunTrace.projAC, hrun.init y hy, Node.init, SA.SAState.initial] at hv
    · rw [tr.projAC.state_of_lastCall hc hk hn] at hv
      have hf := (hrun.cutLaw y hy k _ (projAC_callAt.mp hc)).1
      have hΦ : FrameOK ℓ.frame :=
        hf ▸ (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy k)).1
      have hex := (hrun.cutLaw y hy k _ (projAC_callAt.mp hc)).2.1
      rw [← projAC_state hrun.toLocalRun hy] at hex
      by_cases hr : ℓ.call = .restart
      · have hs := SA.restart_state sp _ ro y (tr.projAC.state y k) ℓ.frame
          (tr.time k) hΦ (hrun.time_nonneg k)
        have hp : (SA.acRestart sp ro y (tr.projAC.state y k) ℓ.frame (tr.time k)).1 =
            tr.projAC.post k := by
          simpa [hr, ACInterface.step, RunTrace.projAC] using congrArg Prod.fst hex
        rw [← hp] at hv
        obtain ⟨B, hB, hvB⟩ := (hs.2.2.2.2.2.2.2.2.1 σ v hv).2
        obtain ⟨j, hj, he⟩ := carried_vote hrun hy hc hB hvB hval
        exact ⟨j, hj.trans hk, he⟩
      · have ha := adds_step (ro := ro) y (tr.projAC.state y k) ℓ.frame (tr.time k) ℓ.call hr
        rw [hex] at ha
        rcases ha σ v hv with hv | hm | ⟨B, hb, hvB⟩ | ⟨e, he, hev⟩
        · obtain ⟨j, hj, he⟩ := ih k hk hv
          exact ⟨j, hj.trans hk, he⟩
        · obtain ⟨j, hj, he⟩ := message_vote hrun hy hc hm hval
          exact ⟨j, hj.trans hk, he⟩
        · obtain ⟨k', rfl, hacc, -⟩ := acBlock_prev hrun.toLocalRun hy (projAC_callAt.mp hc) hb
          obtain ⟨j, hj, he⟩ := hrun.carried_vote_unforgeable y hy k' B ⟨true, hacc⟩ v hvB hval
          exact ⟨j, by omega, emit_voteAt he⟩
        · have he' : e ∈ ((goldilocksSA sp _ ro).step y (tr.projAC.state y k)
              ℓ.frame (tr.time k) ℓ.call).2 := by rw [hex]; exact he
          have hs := SA.step_emission_signer y _ _ _ _ hΦ (hrun.time_nonneg k) he'
          have hvy : v.val = y := hev ▸ hs
          exact ⟨k, hk, e, hvy.symm ▸ ⟨ℓ, hc, he⟩, hev⟩

/-- The pool form and capacity invariant needs no global block-root injectivity. -/
theorem state_pool_cap (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    ∀ σ, (∀ m ∈ (tr.projAC.state y i).pool σ, m.slot = σ) ∧
      ∀ x : Fin sp.n, (((tr.projAC.state y i).pool σ).filter
        (fun m => m.val = x)).dedup.length ≤ 2 := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    rcases tr.projAC.noCall_or_lastCall y i with hn | ⟨k, hk, ℓ, hc, hn⟩
    · rw [tr.projAC.state_of_noCall hn]
      simp [RunTrace.projAC, hrun.init y hy, Node.init, SA.SAState.initial]
    · rw [tr.projAC.state_of_lastCall hc hk hn]
      have hex := (hrun.cutLaw y hy k _ (projAC_callAt.mp hc)).2.1
      rw [← projAC_state hrun.toLocalRun hy] at hex
      have h := SA.step_pool_cap ro y (tr.projAC.state y k) ℓ.frame (tr.time k)
        ℓ.call (ih k hk)
      rw [hex] at h
      exact h

/-- Non-restart pool retention uses the local step law only, not a coherent
global block universe. The restart-free interval is explicit. -/
theorem pool_mono (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
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
      have hg := SA.step_pool_subset y (tr.projAC.state y b) ℓ.frame (tr.time b)
        ℓ.call (fun hr => hnr b hab (Nat.lt_succ_self b) ⟨ℓ, projAC_callAt.mp hc, hr⟩) σ hp
      rw [hex] at hg
      exact hg
    · rw [tr.projAC.state_succ_of_not (fun ℓ hc => hn ⟨hc.1, by simp [hc.2]⟩)]
      exact hp

/-- Before an honest emission, no honest stored pool contains a vote of its signer and slot,
even if a restart has replayed previously accepted blocks. -/
theorem emitted_slot_not_pooled (hrun : GoldilocksRun proposer dg H tr)
    {y x : Fin sp.n} (hy : y ∈ H) (hx : x ∈ H) {i k : Nat} (hki : k ≤ i)
    {v m : Vote sp.n} (hv : tr.EmitAt y i v) (hm : m.val = y) (hs : m.slot = v.slot)
    (σ : Nat) : m ∉ (tr.projAC.state x k).pool σ := by
  intro hp
  obtain ⟨j, hj, e, ⟨ℓ, hc, he⟩, hev⟩ := pool_vote_emitted hrun hx k σ m hp (hm ▸ hy)
  have hem : tr.EmitAt y j m := hm ▸ ⟨ℓ, projAC_callAt.mp hc, e, he, hev⟩
  exact emitted_vote_slots_ne hrun hy (hj.trans_le hki) hem hv hs

/-- An honest emission really enters the post-call pool, without a collision
assumption. Incoming votes of this signer and slot cannot precede its emission. -/
theorem emitted_vote_mem_post (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {v : Vote sp.n}
    (hv : tr.EmitAt y i v) : v ∈ (tr.post i).ac.pool v.slot := by
  obtain ⟨ℓ, hc, e, he, rfl⟩ := hv
  have hv : tr.EmitAt y i e.msg := ⟨ℓ, hc, e, he, rfl⟩
  have hex := (hrun.cutLaw y hy i _ hc).2.1
  rw [← projAC_state hrun.toLocalRun hy] at hex
  have hem : e ∈ ((goldilocksSA sp _ ro).step y (tr.projAC.state y i)
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
  have hgoal : e.msg ∈ ((goldilocksSA sp _ ro).step y (tr.projAC.state y i)
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
        try rw [updateConfirmation_pool]
        exact tryVote_emission_mem_pool y _ _ _ e hem hf
    | message m =>
      rw [hcall] at hem
      apply tryVote_emission_mem_pool y _ _ _ e hem
      intro w hw hwy
      rw [optimistic_pool] at hw
      have hs := (SA.receipt_pool_slot (FGP := List (FG.Att sp.n)) _ (tr.time i) hcap).1 m _ w hw
      rcases adds_admitVote _ _ _ _ w hw with hw | rfl
      · exact hf w hw hwy
      · exact hrecv _ hwy hs (Or.inl ⟨ℓ, hc, hcall⟩)
    | block B =>
      rw [hcall] at hem
      apply tryVote_emission_mem_pool y _ _ _ e hem
      intro w hw hwy
      rw [optimistic_pool] at hw
      have hs := (SA.receipt_pool_slot _ (tr.time i) hcap).2 B _ w hw
      rcases adds_blockReceipt _ _ _ _ w hw with hold | hblock
      · exact hf w hold hwy
      · obtain ⟨k, rfl, hacc, -⟩ := acBlock_prev hrun.toLocalRun hy hc hcall
        exact emitted_slot_not_received hrun hy hy (Nat.le_succ k) hv hwy hs
          (Or.inr ⟨B, ⟨true, hacc⟩, hblock⟩)
    | proposal => simp [hcall, ACInterface.step] at hem
    | toFG => simp [hcall, ACInterface.step] at hem
    | restart =>
      rw [hcall] at hem
      have hn := (SA.restart_state sp _ ro y (tr.projAC.state y i) ℓ.frame (tr.time i) hΦ
        (hrun.time_nonneg i)).1
      change e ∈ (SA.acRestart sp ro y _ ℓ.frame (tr.time i)).2 at hem
      rw [hn] at hem
      exact False.elim (List.not_mem_nil hem)
  rw [hex] at hgoal
  exact hgoal

/-- A block of an honest frame is genesis or was accepted by an honest node. -/
private theorem frame_block_cases (hrun : GoldilocksRun proposer dg H tr)
    {B : Blk sp.n (List (FG.Att sp.n))} (hB : SA.HonestFrameBlock tr.projAC H B) :
    B = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload ∨
      ∃ y ∈ H, ∃ k, tr.AcceptAt y k B := by
  obtain ⟨y, hy, i, ℓ, hc, hB⟩ := hB
  rcases tree_cases hrun.toLocalRun hy (frame_tree hrun hy hc hB) with h | ⟨k, -, hk⟩
  · exact Or.inl h
  · exact Or.inr ⟨y, hy, k, hk⟩

/-- An accepted block of an honest proposer is its own proposal, at the third cut of its tick at
the start of the block's slot, which is not slot `0`. -/
private theorem own_tick (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat}
    {B : Blk sp.n (List (FG.Att sp.n))} (hk : tr.AcceptAt y k B) (hp : B.proposer ∈ H) :
    ∃ j₀ acc, tr.TickAt proposer dg B.proposer j₀ (tr.time (j₀ + 2)) ∧
      tr.CallAt B.proposer (j₀ + 2) (.fg (.block B acc)) ∧ 0 < B.slot ∧
      tr.time (j₀ + 2) = sp.toParams.slotTime B.slot := by
  obtain ⟨j, -, ⟨acc, hc⟩, hpos⟩ := hrun.block_unforgeable y hy k B ⟨true, hk⟩ hp
  rcases blockCall_cases hrun.toLocalRun hp hc with hg | ⟨j₀, x, rfl, ht, hP, d, p, -, hB, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_of_ne_nil hg.1)).2.2.2.1) hpos
  · have hs : B.slot = sp.toParams.slotOf (tr.time (j₀ + 2)) := by rw [hB]; rfl
    exact ⟨j₀, acc, ⟨x, ht⟩, hc, hs ▸ hP.1, hs ▸ hP.2.1⟩

private theorem one_block (hrun : GoldilocksRun proposer dg H tr)
    {B B' : Blk sp.n (List (FG.Att sp.n))}
    (hB : SA.HonestFrameBlock tr.projAC H B) (hB' : SA.HonestFrameBlock tr.projAC H B')
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

/-- **The honest-object facts of the Goldilocks run's AC projection.** -/
theorem goldilocks_ac_projection : GoldilocksACProjection := by
  intro sp ro dg H tr proposer hrun hnc
  have hloc := ac_projection _ _ dg H _ tr proposer (requirements sp ro) hrun.toLocalRun hnc
  refine ⟨hloc, fun y hy => pool_vote_emitted hrun hy,
    fun y hy i ℓ v hc hm hval => message_vote hrun hy hc hm hval,
    fun y hy i ℓ hc B hB v hv hval => carried_vote hrun hy hc hB hv hval, fun B hB hr => ?_,
    fun B B' hB hB' hp hpr hs => one_block hrun hB hB' hp hpr hs⟩
  rcases frame_block_cases hrun hB with rfl | ⟨y, hy, k, hk⟩
  · exact absurd rfl hr
  · exact (accept_facts hrun.toLocalRun hy hk).2.1

end Consensus.Goldilocks.Compose

end
