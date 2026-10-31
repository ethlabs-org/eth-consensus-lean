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

private theorem pool_vote (hrun : GoldilocksRun proposer dg H tr)
    (hloc : ACLocalRun (goldilocksNode sp ro) H (tr.HonestBlocks H) tr.projAC) {y : Fin sp.n}
    (hy : y ∈ H) (i σ : Nat) (v : Vote sp.n) (hv : v ∈ (tr.projAC.state y i).pool σ)
    (hval : v.val ∈ H) : ∃ j < i, ∃ e, SA.VoteAt tr.projAC v.val j e ∧ e.msg = v := by
  obtain rfl := SA.state_pool_slot _ hloc hy i σ v hv
  have own : ∀ k < i, ∀ ℓ, tr.projAC.CallAt y k ℓ → ∀ e ∈ ℓ.emits, e.msg = v →
      ∃ j < i, ∃ e, SA.VoteAt tr.projAC v.val j e ∧ e.msg = v := by
    rintro k hk ℓ hc e he rfl
    have hy' := (SA.castAt_spec hloc hy ⟨hc, he⟩).1
    exact ⟨k, hk, e, hy' ▸ ⟨ℓ, hc, he⟩, rfl⟩
  rcases SA.pool_origin hloc hy i v hv with
    ⟨k, hk, ⟨ℓ, hc, ⟨e, he, hev⟩ | ⟨hnr, hn, hh⟩⟩, -⟩ | ⟨k, hk, ℓ, hc, -, -, B, hB, hvB⟩
  · exact own k hk ℓ hc e he hev
  · have hex := hloc.exec k ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1] at hex
    have ha := adds_step (ro := ro) y (tr.projAC.state y k) ℓ.frame (tr.projAC.time k) ℓ.call hnr
    rw [hex] at ha
    rcases ha v.slot v hh with h | hm | ⟨B, hb, hvB⟩ | ⟨e, he, hev⟩
    · exact absurd h hn
    · obtain ⟨j, hj, h⟩ := message_vote hrun hy hc hm hval
      exact ⟨j, hj.trans hk, h⟩
    · obtain ⟨k', rfl, hacc, -⟩ := acBlock_prev hrun.toLocalRun hy (projAC_callAt.1 hc) hb
      obtain ⟨j, hj, he⟩ := hrun.carried_vote_unforgeable y hy k' B ⟨true, hacc⟩ v hvB hval
      exact ⟨j, by omega, emit_voteAt he⟩
    · exact own k hk ℓ hc e he hev
  · obtain ⟨j, hj, h⟩ := carried_vote hrun hy hc hB hvB hval
    exact ⟨j, hj.trans hk, h⟩

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
  refine ⟨hloc, fun y hy => pool_vote hrun hloc hy,
    fun y hy i ℓ v hc hm hval => message_vote hrun hy hc hm hval,
    fun y hy i ℓ hc B hB v hv hval => carried_vote hrun hy hc hB hv hval, fun B hB hr => ?_,
    fun B B' hB hB' hp hpr hs => one_block hrun hB hB' hp hpr hs⟩
  rcases frame_block_cases hrun hB with rfl | ⟨y, hy, k, hk⟩
  · exact absurd rfl hr
  · exact (accept_facts hrun.toLocalRun hy hk).2.1

end Consensus.Goldilocks.Compose

end
