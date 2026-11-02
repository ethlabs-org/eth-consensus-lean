module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance

public section

/-! # Goldilocks SA: the locks at a vote's read point

The read point of an honest slot-`s` vote is the state after `try_vote`'s unlocking against the
merged view (`readPoint_locks`). A lock there of slot `s − 1` or later sits below (inside `U`) a
block that an optimistic confirmation of the voter selected, at a cut no later than the vote's,
with three quarters of the committee as optimistic voters, every honest one of which voted at an
earlier cut (`lock_origin_readPoint`): locks only move back (A0.4 (c)), a restart keeps them
(A0.7), the updates that write locks of slot `s − 1` or later run after the vote
(`t_s + 2Δ`), and the pool's honest votes were emitted before (the honest-object facts). A1.3's
lock analysis reads both. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

/-! ## The SA functions -/

/-- Before an honest vote, no honest receiver already pools any vote of that signer and
slot. Otherwise unforgeability supplies an earlier vote, contradicting one vote per slot. -/
theorem vote_slot_absent_before (hrun : ACRun proposer tr H U)
    {y x : Fin sp.n} (hy : y ∈ H) (hx : x ∈ H) {i : Nat} {e : Em sp FGP}
    (he : VoteAt tr y i e) {m : Vote sp.n} (hm : m.val = y)
    (hs : m.slot = e.msg.slot) (σ : Nat) : m ∉ (tr.state x i).pool σ := by
  intro hp
  obtain ⟨j, hj, e', hv, hmsg⟩ := hrun.honest.pool_vote x hx i σ m hp (hm ▸ hy)
  rw [hm] at hv
  have hslots : e'.msg.slot = e.msg.slot := by rw [hmsg, hs]
  have hij := (one_vote_per_slot sp FGP ro H U tr hrun.localRun y hy j i e' e hv he hslots).1
  exact (Nat.ne_of_lt hj) hij

private theorem optimistic_pool (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).pool = A.pool := by
  unfold optimisticConfirmation updateLatestConfirmed
  split
  · rfl
  · split_ifs <;> rfl

private theorem admit_pool_mem {A : SAState sp.n} {t : Time} {m v : Vote sp.n} {σ : Nat}
    (h : v ∈ (admitVote sp A t m).pool σ) : v ∈ A.pool σ ∨ v = m ∧ m.slot = σ := by
  unfold admitVote at h
  split_ifs at h
  · exact Or.inl h
  · exact Or.inl h
  · simp only [Function.update_apply] at h
    split_ifs at h with hs
    · subst hs
      rcases List.mem_append.1 h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨List.mem_singleton.1 h, rfl⟩
    · exact Or.inl h

private theorem receipt_pool_mem {A : SAState sp.n} {t : Time} {B : Blk sp.n FGP} {v : Vote sp.n}
    {σ : Nat} (h : v ∈ (blockReceipt sp A t B).pool σ) :
    v ∈ A.pool σ ∨ v ∈ blockVotes B ∧ v.slot = σ := by
  have key : ∀ (l : List (Vote sp.n)) (A₀ : SAState sp.n),
      v ∈ (l.foldl (fun A v => admitVote sp A t v) A₀).pool σ →
        v ∈ A₀.pool σ ∨ v ∈ l ∧ v.slot = σ := by
    intro l
    induction l with
    | nil => exact fun _ h => Or.inl h
    | cons x l ih =>
      intro A₀ h
      rcases ih _ h with h | h
      · rcases admit_pool_mem h with h | ⟨rfl, hs⟩
        · exact Or.inl h
        · exact Or.inr ⟨List.mem_cons_self, hs⟩
      · exact Or.inr ⟨List.mem_cons_of_mem _ h.1, h.2⟩
  unfold blockReceipt at h
  exact (key _ _ h :)

/-- The emission of `try_vote`: its slot is the call's, it is cast by `t_s + Δ`, its read point
holds the input's pool and the input's locks unlocked against the merged view (for `s > 0`),
whose view is the input's. -/
private theorem tryVote_em {x : Fin sp.n} {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {e : Em sp FGP} (he : e ∈ (tryVote sp x A Φ t).2) :
    e.msg.slot = sp.slot t ∧ t ≤ sp.ts (sp.slot t) + sp.Δ ∧
      e.readPoint.locks = (if 0 < sp.slot t then
        unlock sp A.locks Φ t ((sp.slot t : Int) - 1) (mergedVoteView sp A Φ (sp.slot t))
        else A.locks) ∧
      mergedVoteView sp e.readPoint Φ (sp.slot t) = mergedVoteView sp A Φ (sp.slot t) := by
  unfold tryVote at he
  dsimp only at he
  split_ifs at he with h1 h2 h3
  · simp at he
  · simp at he
  all_goals
    rw [List.mem_singleton] at he
    subst he
    refine ⟨rfl, not_lt.1 (not_or.1 (not_or.1 h1).2).2, ?_, rfl⟩
    split_ifs
    rfl

/-! ## Over an SA trace -/

/-- The input of the `try_vote` that emits an honest vote: the state before the call (a tick),
or the optimistic check after the receipt of a message or a block, which keeps the locks. -/
private theorem emits_tryVote (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    ∃ P, e ∈ (tryVote sp y P ℓ.frame (tr.time i)).2 ∧ (P = tr.state y i ∨
      ∃ A, ((∃ m, ℓ.call = .message m ∧ A = admitVote sp (tr.state y i) (tr.time i) m) ∨
          ∃ B, ℓ.call = .block B ∧ A = blockReceipt sp (tr.state y i) (tr.time i) B) ∧
        P = optimisticConfirmation sp A ℓ.frame (tr.time i) ∧ A.locks = (tr.state y i).locks) := by
  obtain ⟨hc, he⟩ := hc
  have hΦ := (frameIn_of_callAt hr hy hc).1
  have hx := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at hx
  have he' : e ∈ ((goldilocksSA sp FGP ro).step y (tr.state y i) ℓ.frame (tr.time i)
      ℓ.call).2 := by
    rw [hx]
    exact he
  clear hx he
  cases hcall : ℓ.call with
  | tick =>
    rw [hcall] at he'
    change e ∈ (acOnTick sp y _ ℓ.frame _).2 at he'
    unfold acOnTick at he'
    dsimp only at he'
    split_ifs at he' <;> first | exact ⟨_, he', Or.inl rfl⟩ | simp at he'
  | proposal =>
    rw [hcall] at he'
    simp [ACInterface.step] at he'
  | toFG =>
    rw [hcall] at he'
    simp [ACInterface.step] at he'
  | message m =>
    rw [hcall] at he'
    exact ⟨_, he', Or.inr ⟨_, Or.inl ⟨m, rfl, rfl⟩, rfl, admitVote_locks_eq _ _ _⟩⟩
  | block B =>
    rw [hcall] at he'
    exact ⟨_, he', Or.inr ⟨_, Or.inr ⟨B, rfl, rfl⟩, rfl, blockReceipt_locks _ _ _⟩⟩
  | restart =>
    rw [hcall] at he'
    change e ∈ (acRestart sp ro y _ ℓ.frame (tr.time i)).2 at he'
    rw [((restart_state sp) FGP ro y _ ℓ.frame (tr.time i) hΦ (hr.time_nonneg i)).1] at he'
    simp at he'

/-- The locks at the read point of a vote of slot `s > 0` are an `unlock` against the merged
view, of slot `s − 1`. -/
theorem readPoint_locks (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : 0 < e.msg.slot) :
    ∃ L, e.readPoint.locks = unlock sp L ℓ.frame (tr.time i) ((e.msg.slot : Int) - 1)
      (mergedVoteView sp e.readPoint ℓ.frame e.msg.slot) := by
  obtain ⟨P, he, -⟩ := emits_tryVote hr hy hc
  obtain ⟨hes, -, hlocks, hview⟩ := tryVote_em he
  rw [hes] at hs ⊢
  rw [hlocks, hview]
  split_ifs
  exact ⟨_, rfl⟩

/-- Every vote of an honest validator in the pools of `A` has its pool's slot and was emitted
before cut `i`. -/
private def PoolOK (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (A : SAState sp.n) (i : Nat) :
    Prop :=
  ∀ σ, ∀ v ∈ A.pool σ, v.val ∈ H → v.slot = σ ∧ ∃ j < i, ∃ e', VoteAt tr v.val j e' ∧ e'.msg = v

/-- The state the call leaves after an own vote's optimistic check holds that check's pools. -/
private theorem point_post (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x j ℓ)
    {e : Em sp FGP} (he : e ∈ ℓ.emits) :
    (tr.state x (j + 1)).pool = (admitVote sp e.readPoint (tr.time j) e.msg).pool := by
  rw [show tr.state x (j + 1) = tr.post j by simp [Trace.state, hc.1, hc.2],
    post_of_castAt hr hx ⟨hc, he⟩, optimistic_pool]

/-- **The slots at an optimistic point.** The slot-`σ` pool of a state at which an honest node
runs the optimistic check holds only slot-`σ` votes. -/
theorem optimisticPoint_pool_slot (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {A : SAState sp.n} (hp : OptimisticPoint tr x j ℓ A) {σ : Nat} {v : Vote sp.n}
    (hv : v ∈ A.pool σ) : v.slot = σ := by
  obtain ⟨hc, ⟨m, -, rfl⟩ | ⟨B, -, rfl⟩ | ⟨e, he, rfl⟩⟩ := hp
  · rcases admit_pool_mem hv with hv | ⟨rfl, hs⟩
    · exact state_pool_slot sp hr hx j σ v hv
    · exact hs
  · rcases receipt_pool_mem hv with hv | ⟨-, hs⟩
    · exact state_pool_slot sp hr hx j σ v hv
    · exact hs
  · rw [← point_post hr hx hc he] at hv
    exact state_pool_slot sp hr hx _ σ v hv

/-- The honest votes after the receipt of a message or a block at cut `j` were emitted before
`j`. -/
private theorem receipt_poolOK (hrun : ACRun proposer tr H U) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ℓ) {A : SAState sp.n}
    (h : (∃ m, ℓ.call = .message m ∧ A = admitVote sp (tr.state y j) (tr.time j) m) ∨
      ∃ B, ℓ.call = .block B ∧ A = blockReceipt sp (tr.state y j) (tr.time j) B) :
    PoolOK tr H A j := by
  intro σ v hv hvH
  refine ⟨optimisticPoint_pool_slot hrun.localRun hy ⟨hc, h.imp_right Or.inl⟩ hv, ?_⟩
  rcases h with ⟨m, hm, rfl⟩ | ⟨B, hB, rfl⟩
  · rcases admit_pool_mem hv with hv | ⟨rfl, -⟩
    · exact hrun.honest.pool_vote y hy j σ v hv hvH
    · exact hrun.honest.message_vote y hy j ℓ _ hc hm hvH
  · rcases receipt_pool_mem hv with hv | ⟨hv, -⟩
    · exact hrun.honest.pool_vote y hy j σ v hv hvH
    · exact hrun.honest.carried_vote y hy j ℓ hc B
        ((accept_new sp hrun.localRun hy ⟨ℓ, hc, hB⟩).1 ℓ hc) v hv hvH

/-- The input of the actual `tryVote` contains no vote of the emitting signer and slot,
even when this call first admits a wire message or block payload. -/
theorem tryVote_input_fresh (hrun : ACRun proposer tr H U) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    ∃ A, e ∈ (tryVote sp y A ℓ.frame (tr.time i)).2 ∧
      ∀ σ m, m.val = y → m.slot = e.msg.slot → m ∉ A.pool σ := by
  obtain ⟨A, he, hA⟩ := emits_tryVote hrun.localRun hy hc
  refine ⟨A, he, ?_⟩
  intro σ m hm hs hp
  rcases hA with rfl | ⟨R, hR, rfl, _⟩
  · exact vote_slot_absent_before hrun hy hy ⟨ℓ, hc⟩ hm hs σ hp
  · rw [optimistic_pool] at hp
    obtain ⟨_, j, hj, e', hv, hmsg⟩ := receipt_poolOK hrun hy hc.1 hR σ m hp (hm ▸ hy)
    rw [hm] at hv
    have hij := (one_vote_per_slot sp FGP ro H U tr hrun.localRun y hy j i e' e
      hv ⟨ℓ, hc⟩ (by rw [hmsg, hs])).1
    exact (Nat.ne_of_lt hj) hij

/-- Every reachable honest emission is a fresh pool insertion, including after incoming
message/payload handling; the two-vote cap cannot refuse its own vote. -/
theorem emitted_vote_fresh (hrun : ACRun proposer tr H U) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    e.msg ∉ (tr.state y i).pool e.msg.slot ∧
      e.msg ∈ (tr.post i).pool e.msg.slot := by
  have hv := (castAt_spec hrun.localRun hy hc).1
  refine ⟨vote_slot_absent_before hrun hy hy ⟨ℓ, hc⟩ hv rfl _, ?_⟩
  obtain ⟨A, he, hf⟩ := tryVote_input_fresh hrun hy hc
  have hpool : e.readPoint.pool = A.pool := by
    unfold tryVote at he
    dsimp only at he
    split_ifs at he <;> simp only [List.mem_singleton, List.not_mem_nil] at he
    all_goals subst e; rfl
  have hn : e.msg ∉ e.readPoint.pool e.msg.slot := by
    rw [hpool]; exact hf _ _ hv rfl
  have hfilter : (e.readPoint.pool e.msg.slot).filter (fun m => m.val = e.msg.val) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro m hm
    simp only [decide_eq_true_eq]
    intro hmval
    have hs := state_pool_slot sp hrun.localRun hy (i + 1) _ m
      (readPoint_pool hrun.localRun hy hc hm).1
    exact hf _ m (hmval.trans hv) hs (hpool ▸ hm)
  rw [post_of_castAt hrun.localRun hy hc, optimistic_pool]
  have hs := (castAt_spec hrun.localRun hy hc).2.1
  have hbad : ¬ ((e.msg.slot : Int) < (sp.slot (tr.time i) : Int) - 1 ∨
      sp.slot (tr.time i) < e.msg.slot ∨ e.msg ∈ e.readPoint.pool e.msg.slot) := by
    rintro (h | h | h)
    · omega
    · omega
    · exact hn h
  simp [admitVote, hbad, hfilter]

/-- **The honest votes at an optimistic point.** A vote of an honest validator in a pool of a
state at which an honest node runs the optimistic check at cut `j` has its pool's slot and was
emitted at a cut no later than `j` (at `j`: the node's own vote). -/
theorem optimisticPoint_pool_vote (hrun : ACRun proposer tr H U)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {A : SAState sp.n} (hp : OptimisticPoint tr x j ℓ A)
    {σ : Nat} {v : Vote sp.n} (hv : v ∈ A.pool σ) (hvH : v.val ∈ H) :
    v.slot = σ ∧ ∃ j' ≤ j, ∃ e', VoteAt tr v.val j' e' ∧ e'.msg = v := by
  refine ⟨optimisticPoint_pool_slot hrun.localRun hx hp hv, ?_⟩
  obtain ⟨hc, h | h | ⟨e', he', rfl⟩⟩ := hp
  · obtain ⟨-, j', hj', h⟩ := receipt_poolOK hrun hx hc (Or.inl h) σ v hv hvH
    exact ⟨j', hj'.le, h⟩
  · obtain ⟨-, j', hj', h⟩ := receipt_poolOK hrun hx hc (Or.inr h) σ v hv hvH
    exact ⟨j', hj'.le, h⟩
  · rw [← point_post hrun.localRun hx hc he'] at hv
    obtain ⟨j', hj', h⟩ := hrun.honest.pool_vote x hx _ _ v hv hvH
    exact ⟨j', Nat.lt_succ_iff.1 hj', h⟩

/-- **The honest votes at a receipt's optimistic point** (after an `on_message` admission or an
`on_block` receipt, before any own vote of the call) were emitted at earlier cuts. -/
theorem receipt_pool_vote (hrun : ACRun proposer tr H U) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ℓ) {A : SAState sp.n}
    (h : (∃ m, ℓ.call = .message m ∧ A = admitVote sp (tr.state y j) (tr.time j) m) ∨
      ∃ B, ℓ.call = .block B ∧ A = blockReceipt sp (tr.state y j) (tr.time j) B)
    {σ : Nat} {v : Vote sp.n} (hv : v ∈ A.pool σ) (hvH : v.val ∈ H) :
    ∃ j' < j, ∃ e', VoteAt tr v.val j' e' ∧ e'.msg = v :=
  (receipt_poolOK hrun hy hc h σ v hv hvH).2

/-- Every read-point lock has a genuine optimistic or update write, including an
optimistic receipt in the vote's own call. Unlock and live remaps preserve its label
and move its block only to ancestors of the selected block. -/
theorem lock_write_readPoint (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ell e) (hpos : 0 < e.msg.slot)
    {l : Lock} (hl : l ∈ e.readPoint.locks) :
    ∃ a ≤ i, ∃ D,
      ((∃ CV, OptimisticLockAt tr y a l.slot D CV) ∨ ∃ ell', UpdateAt tr y a l.slot ell') ∧
      ∃ L ∈ U, L.root = l.block ∧ Anc U L D := by
  have hPhi := frameIn_of_callAt hr hy hc.1
  have transfer : ∀ {L L' : Set Lock}, MovesBack sp ell.frame L L' →
      (∀ l ∈ L, ∃ a ≤ i, ∃ D,
        ((∃ CV, OptimisticLockAt tr y a l.slot D CV) ∨ ∃ ell', UpdateAt tr y a l.slot ell') ∧
        ∃ B ∈ U, B.root = l.block ∧ Anc U B D) →
      ∀ l ∈ L', ∃ a ≤ i, ∃ D,
        ((∃ CV, OptimisticLockAt tr y a l.slot D CV) ∨ ∃ ell', UpdateAt tr y a l.slot ell') ∧
        ∃ B ∈ U, B.root = l.block ∧ Anc U B D := by
    intro L L' hm ho l hl
    obtain ⟨l₀, hl₀, hs, -, B, hB, hBr, B', hB', hB'r, hBB⟩ := hm l hl
    obtain ⟨a, hai, D, hd, C, hC, hCr, hCD⟩ := ho l₀ hl₀
    obtain rfl : C = B := hr.coherent.1 hC (hPhi.2 hB) (hCr.trans hBr.symm)
    exact ⟨a, hai, D, hs ▸ hd, B', hPhi.2 hB', hB'r, (hBB.mono hPhi.2).trans hCD⟩
  obtain ⟨P, he, hP⟩ := emits_tryVote hr hy hc
  have hs := (castAt_spec hr hy hc).2.1
  have hstored : ∀ l ∈ (tr.state y i).locks, ∃ a ≤ i, ∃ D,
      ((∃ CV, OptimisticLockAt tr y a l.slot D CV) ∨ ∃ ell', UpdateAt tr y a l.slot ell') ∧
      ∃ L ∈ U, L.root = l.block ∧ Anc U L D := by
    intro l hl
    obtain ⟨a, hai, D, ho, hb⟩ := lock_provenance hr hy i l hl
    exact ⟨a, hai.le, D, ho, hb⟩
  have hinput : ∀ l ∈ P.locks, ∃ a ≤ i, ∃ D,
      ((∃ CV, OptimisticLockAt tr y a l.slot D CV) ∨ ∃ ell', UpdateAt tr y a l.slot ell') ∧
      ∃ L ∈ U, L.root = l.block ∧ Anc U L D := by
    rcases hP with rfl | ⟨A, hA, rfl, hAl⟩
    · exact hstored
    unfold optimisticConfirmation
    rcases hsel : optimisticSelect sp A ell.frame (tr.time i) with _ | D
    · exact hAl ▸ hstored
    rw [updateLatestConfirmed_locks_eq]
    apply transfer (((locks_move_back sp) FGP ell.frame A.locks (tr.time i) hPhi.1).2.1 _ _)
    rintro l (hl | ⟨p, hp, rfl⟩)
    · exact hstored l (hAl ▸ hl)
    rw [Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨i, le_rfl, D, Or.inl ⟨_, ell, A, ⟨hc.1, hA.imp_right Or.inl⟩,
      rfl, hsel, rfl⟩, D, ?_, rfl, .refl⟩
    unfold optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    exact hPhi.2 (deepest_mem hsel).1.1
  rw [(tryVote_em he).2.2.1, ite_eq_left (hs ▸ hpos)] at hl
  exact transfer (((locks_move_back sp) FGP ell.frame P.locks (tr.time i) hPhi.1).2.2 _ _)
    hinput l hl

/-- A read-point lock not older than the vote is current-slot optimistic. Its
write may be the receipt before the vote in the very same call. -/
theorem current_lock_write_readPoint (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ell e) (hpos : 0 < e.msg.slot)
    {l : Lock} (hl : l ∈ e.readPoint.locks) (hs : e.msg.slot ≤ l.slot) :
    l.slot = e.msg.slot ∧ ∃ a ≤ i, ∃ D CV,
      OptimisticLockAt tr y a e.msg.slot D CV ∧
      sp.ts e.msg.slot ≤ tr.time a ∧
      (∃ L ∈ U, L.root = l.block ∧ Anc U L D) := by
  obtain ⟨a, hai, D, ho, hb⟩ := lock_write_readPoint hr hy hc hpos hl
  have hslot := (castAt_spec hr hy hc).2.1
  have ht := vote_time_le hr hy ⟨ell, hc⟩
  have htime := hr.time_mono hai
  rcases ho with ⟨CV, ell₀, A, hp, hs₀, hsel, heq⟩ | ⟨ell₀, hu⟩
  · have hle := slot_mono sp (hr.time_nonneg a) htime
    have hsame : l.slot = e.msg.slot := by omega
    refine ⟨hsame, a, hai, D, CV, ?_, ?_, hb⟩
    · exact hsame ▸ ⟨ell₀, A, hp, hs₀, hsel, heq⟩
    · apply (ts_le_iff_le_slot sp (hr.time_nonneg a) _).mpr
      rw [hs₀, hsame]
  · have hts := (ts_le_iff sp).mpr
      (show (sp.slot (tr.time i) : Int) + 1 ≤ (l.slot : Int) + 1 by omega)
    have hupdate := hu.2.2.1
    simp only [SAParams.ts] at ht hts hupdate
    have := sp.toParams.hΔ
    exfalso
    linarith

/-- The optimistic write's actual counted pool, threshold, timing and honest-vote
provenance. This retains the consumer content of `OptimisticLockAt`. -/
theorem optimisticLockAt_spec (hrun : ACRun proposer tr H U)
    {y : Fin sp.n} (hy : y ∈ H) {i s : Nat} {D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (ho : OptimisticLockAt tr y i s D CV) :
    tr.time i < sp.ts s + 2 * sp.Δ ∧ 3 * sp.n ≤ 4 * (voters CV).ncard ∧
      ∃ ell A, OptimisticPoint tr y i ell A ∧ D ∈ ell.frame.tree ∧
        (∀ v ∈ CV, v ∈ A.pool s ∧ v.slot = s ∧ AncR ell.frame D v.head) ∧
        (∀ v ∈ CV, v.val ∈ H → ∃ a ≤ i, ∃ e, VoteAt tr v.val a e ∧ e.msg = v) := by
  obtain ⟨ell, A, hp, hs, hsel, rfl⟩ := ho
  unfold optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel with hn
  obtain ⟨⟨hD, hcount, -⟩, -⟩ := deepest_mem hsel
  have hv : voters {v | v ∈ A.pool s ∧ AncR ell.frame D v.head} =
      optimisticVoters sp A ell.frame s D := by
    ext x
    constructor
    · rintro ⟨v, ⟨hv, ha⟩, he⟩; exact ⟨v, hv, he, ha⟩
    · rintro ⟨v, hv, he, ha⟩; exact ⟨v, ⟨hv, ha⟩, he⟩
  refine ⟨?_, ?_, ell, A, hp, hD, ?_, ?_⟩
  · exact lt_of_not_ge (fun ht => hn (Or.inr (Or.inr (hs ▸ ht))))
  · rw [hv]; exact hs ▸ hcount
  · intro v hv
    exact ⟨hv.1, (optimisticPoint_pool_slot hrun.localRun hy hp hv.1), hv.2⟩
  · intro v hv hh
    exact (optimisticPoint_pool_vote hrun hy hp hv.1 hh).2

/-- The conclusion of `lock_origin_readPoint` for the lock `l`, before cut `i`. -/
private def Good (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (y : Fin sp.n) (i : Nat) (l : Lock) : Prop :=
  ∃ (Φ : Frm sp.n FGP) (A : SAState sp.n) (D : Blk sp.n FGP), FrameOK Φ ∧ Φ.tree ⊆ U ∧
    D ∈ Φ.tree ∧ 3 * sp.n ≤ 4 * (optimisticVoters sp A Φ l.slot D).ncard ∧
    (∀ v ∈ A.pool l.slot, v.val ∈ H → v.slot = l.slot ∧
      ∃ j < i, ∃ e', VoteAt tr v.val j e' ∧ e'.msg = v) ∧
    (∃ k ≤ i, A.pool l.slot ⊆ (tr.state y (k + 1)).pool l.slot) ∧
    ∃ L ∈ U, L.root = l.block ∧ Anc U L D

private theorem Good.below (hU : Coherent U) {y : Fin sp.n} {i : Nat} {l l' : Lock}
    (h : Good tr H U y i l)
    (hs : l'.slot = l.slot) {L' L : Blk sp.n FGP} (hL' : L' ∈ U) (hL'r : L'.root = l'.block)
    (hL : L ∈ U) (hLr : L.root = l.block) (hA : Anc U L' L) : Good tr H U y i l' := by
  unfold Good at h ⊢
  rw [hs]
  obtain ⟨Φ, A, D, h1, h2, h3, h4, h5, h6, M, hM, hMr, hMD⟩ := h
  obtain rfl : L = M := hU.1 hL hM (hLr.trans hMr.symm)
  exact ⟨Φ, A, D, h1, h2, h3, h4, h5, h6, L', hL', hL'r, hA.trans hMD⟩

private theorem good_movesBack (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦU : Φ.tree ⊆ U)
    {L L' : Set Lock} (hm : MovesBack sp Φ L L') {y : Fin sp.n} {i : Nat} {s : Int}
    (h : ∀ l ∈ L, s ≤ l.slot → Good tr H U y i l) :
    ∀ l ∈ L', s ≤ l.slot → Good tr H U y i l := by
  intro l' hl' hs
  obtain ⟨l, hl, hsl, -, B, hB, hBr, B', hB', hB'r, hA⟩ := hm l' hl'
  exact (h l hl (hsl ▸ hs)).below hU hsl (hΦU hB') hB'r (hΦU hB) hBr (hA.mono hΦU)

/-- The block an optimistic check selects is in the tree, and a lock of its slot below it is
`Good` when the check's pool is. -/
private theorem good_of_select {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {A : SAState sp.n} {t : Time} {D : Blk sp.n FGP} (hsel : optimisticSelect sp A Φ t = some D)
    {y : Fin sp.n} {i : Nat} (hpool : PoolOK tr H A i)
    (hpost : ∃ k ≤ i, ∀ σ, A.pool σ ⊆ (tr.state y (k + 1)).pool σ) :
    D ∈ Φ.tree ∧ ∀ l : Lock, l.slot = sp.slot t → (∃ L ∈ U, L.root = l.block ∧ Anc U L D) →
      Good tr H U y i l := by
  unfold optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  obtain ⟨⟨hD, hn, -⟩, -⟩ := deepest_mem hsel
  obtain ⟨k, hk, hsub⟩ := hpost
  exact ⟨hD, fun l hl hb => ⟨Φ, A, D, hΦ, hΦU, hD, hl ▸ hn, fun v hv hvH => hpool _ v hv hvH,
    ⟨k, hk, hsub _⟩, hb⟩⟩

private theorem good_optimistic (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {A : SAState sp.n} {t : Time} {y : Fin sp.n} {i : Nat} {s : Int}
    (h : ∀ l ∈ A.locks, s ≤ l.slot → Good tr H U y i l)
    (hnew : ∀ D, optimisticSelect sp A Φ t = some D →
      Good tr H U y i ⟨D.root, sp.slot t, true⟩) :
    ∀ l ∈ (optimisticConfirmation sp A Φ t).locks, s ≤ l.slot → Good tr H U y i l := by
  unfold optimisticConfirmation
  rcases hD : optimisticSelect sp A Φ t with _ | D
  · exact h
  · rw [updateLatestConfirmed_locks_eq]
    refine good_movesBack hU hΦU (((locks_move_back sp) FGP Φ A.locks t hΦ).2.1 _ _) ?_
    rintro l (hl | ⟨p, hp, rfl⟩) hs
    · exact h l hl hs
    · rw [Set.mem_singleton_iff] at hp
      subst hp
      exact hnew D hD

/-- **Lock origin at a vote.** A lock of slot `s − 1` or later at the read point of an honest
slot-`s` vote sits below a block `D` that three quarters of the committee vote for in a pool
whose honest votes were all emitted before the vote's cut. -/
theorem lock_origin_readPoint (hrun : ACRun proposer tr H U) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e) :
    ∀ l ∈ e.readPoint.locks, (e.msg.slot : Int) - 1 ≤ l.slot →
      ∃ (Φ : Frm sp.n FGP) (A : SAState sp.n) (D : Blk sp.n FGP), FrameOK Φ ∧ Φ.tree ⊆ U ∧
        D ∈ Φ.tree ∧ 3 * sp.n ≤ 4 * (optimisticVoters sp A Φ l.slot D).ncard ∧
        (∀ v ∈ A.pool l.slot, v.val ∈ H → v.slot = l.slot ∧
          ∃ j < i, ∃ e', VoteAt tr v.val j e' ∧ e'.msg = v) ∧
        (∃ k ≤ i, A.pool l.slot ⊆ (tr.state y (k + 1)).pool l.slot) ∧
        ∃ L ∈ U, L.root = l.block ∧ Anc U L D := by
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc.1
  obtain ⟨P, he, hP⟩ := emits_tryVote hr hy hc
  obtain ⟨hes, ht, hlocks, -⟩ := tryVote_em he
  rw [hes]
  -- the locks before the call: an earlier optimistic check (an update of their slot runs later)
  have hS : ∀ l ∈ (tr.state y i).locks, (sp.slot (tr.time i) : Int) - 1 ≤ l.slot →
      Good tr H U y i l := by
    intro l hl hsl
    obtain ⟨j, hj, B, horig, hb⟩ := lock_provenance hr hy i l hl
    rcases horig with ⟨CV, ℓ', A, hpt, hslot, hsel, -⟩ | ⟨ℓ', -, -, htj, -⟩
    · have hΦ' := frameIn_of_callAt hr hy hpt.1
      refine (good_of_select hΦ'.1 hΦ'.2 hsel (fun σ v hv hvH => ?_)
        ⟨j, hj.le, optimisticPoint_pool_post hr hy hpt⟩).2 l hslot.symm hb
      obtain ⟨hs, j', hj', h⟩ := optimisticPoint_pool_vote hrun hy hpt hv hvH
      exact ⟨hs, j', hj'.trans_lt hj, h⟩
    · have hji := hr.time_mono hj.le
      have hΔ := sp.toParams.hΔ
      have hsl' : ((sp.slot (tr.time i) : Nat) : Time) - 1 ≤ (l.slot : Time) := by
        exact_mod_cast hsl
      simp only [SAParams.ts] at htj ht
      nlinarith
  -- the locks at `try_vote`'s input: also the optimistic check of the receipt
  have hPl : ∀ l ∈ P.locks, (sp.slot (tr.time i) : Int) - 1 ≤ l.slot → Good tr H U y i l := by
    rcases hP with rfl | ⟨A, hA, rfl, hAl⟩
    · exact hS
    · refine good_optimistic hU hΦ hΦU (hAl ▸ hS) fun D hD => ?_
      obtain ⟨hDt, hg⟩ := good_of_select hΦ hΦU hD (receipt_poolOK hrun hy hc.1 hA)
        ⟨i, le_rfl, optimisticPoint_pool_post hr hy ⟨hc.1, hA.imp_right Or.inl⟩⟩
      exact hg _ rfl ⟨D, hΦU hDt, rfl, Relation.ReflTransGen.refl⟩
  rw [hlocks]
  split_ifs
  · exact good_movesBack hU hΦU (((locks_move_back sp) FGP _ _ _ hΦ).2.2 _ _) hPl
  · exact hPl

/-- A current-label read lock is below the common head of the strictly earlier
honest casts. The strict cut comes from the read point, not from an arbitrary
optimistic write (which may include its own post-cast admission). This is the
local causal step; it does not assume future unanimity or close the induction. -/
theorem current_read_lock_below_of_earlier_heads (hrun : ACRun proposer tr H U)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ell e) {l : Lock} (hl : l ∈ e.readPoint.locks)
    (hs : l.slot = e.msg.slot) {P : Blk sp.n FGP} (hP : P ∈ U)
    (hIH : ∀ x ∈ H, ∀ k < i, ∀ e', VoteAt tr x k e' →
      e'.msg.slot = e.msg.slot → e'.msg.head = P.root)
    {B : Blk sp.n FGP} (hB : B ∈ U) (hBr : B.root = l.block) : Anc U B P := by
  obtain ⟨Φ, A, D, -, hΦU, -, hcnt, hpool, -, L, hL, hLr, hLD⟩ :=
    lock_origin_readPoint hrun hy hc l hl (by omega)
  obtain rfl : L = B := hrun.localRun.coherent.1 hL hB (hLr.trans hBr.symm)
  obtain ⟨z, ⟨v, hv, rfl, R, hR, hRr, hDR⟩, hz⟩ :
      ∃ z ∈ optimisticVoters sp A Φ l.slot D, z ∈ H := by
    by_contra hn
    push Not at hn
    have hsub : optimisticVoters sp A Φ l.slot D ⊆ Hᶜ := fun z hz => hn z hz
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    omega
  obtain ⟨hvs, k, hki, e', he', hmsg⟩ := hpool v hv hz
  have hhead := hIH v.val hz k hki e' he' (by rw [hmsg, hvs, hs])
  have hRP : R = P := hrun.localRun.coherent.1 (hΦU hR) hP
    (hRr.trans (by rw [← hmsg]; exact hhead))
  exact hLD.trans (hRP ▸ hDR.mono hΦU)

end Consensus.Goldilocks.SA

end
