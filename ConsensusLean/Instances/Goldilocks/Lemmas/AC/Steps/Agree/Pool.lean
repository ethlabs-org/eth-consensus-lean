module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission

public section

/-! # Goldilocks SA: where the votes of an honest node's pools come from

Between restarts an honest node's pools only grow, and a vote's stamp is written once, when the
node admits it (`SendOrAdmit`), with the time of the admission, of a slot at most the slot of that
time. A vote that a restart put in the pools is a vote of a block of the restart's frame. A1.1
reads this to forward a voter's early votes to the proposer under `Sync`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-! ## The pools across one SA function -/

/-- From `A` to `A'` at `t`, the pools grow, a held vote keeps its stamp, and a new vote is
stamped `t` and is of a slot at most `slot(t)`. -/
private def Grow (t : Time) (A A' : SAState sp.n) : Prop :=
  (∀ σ, A.pool σ ⊆ A'.pool σ) ∧ ∀ x : Vote sp.n,
    (x ∈ A.pool x.slot → A'.voteStamp x = A.voteStamp x) ∧
    (x ∈ A'.pool x.slot → x ∉ A.pool x.slot → A'.voteStamp x = ETime.of t ∧ x.slot ≤ sp.slot t)

private theorem Grow.of_eq {t : Time} {A A' : SAState sp.n} (hp : A'.pool = A.pool)
    (hs : A'.voteStamp = A.voteStamp) : Grow t A A' :=
  ⟨fun _ => hp ▸ List.Subset.refl _, fun _ => ⟨fun _ => hs ▸ rfl, fun h h' => absurd (hp ▸ h) h'⟩⟩

private theorem Grow.trans {t : Time} {A₁ A₂ A₃ : SAState sp.n} (h₁ : Grow t A₁ A₂)
    (h₂ : Grow t A₂ A₃) : Grow t A₁ A₃ := by
  refine ⟨fun σ _ h => h₂.1 σ (h₁.1 σ h), fun x => ⟨fun hx => ?_, fun hx hx' => ?_⟩⟩
  · rw [(h₂.2 x).1 (h₁.1 _ hx), (h₁.2 x).1 hx]
  · by_cases h : x ∈ A₂.pool x.slot
    · rw [(h₂.2 x).1 h]
      exact (h₁.2 x).2 h hx'
    · exact (h₂.2 x).2 hx h

private theorem grow_admitVote (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    Grow t A (admitVote sp A t v) := by
  unfold admitVote
  split_ifs with h₁ h₂
  · exact Grow.of_eq rfl rfl
  · exact Grow.of_eq rfl rfl
  · refine ⟨fun σ x hx => ?_, fun x => ⟨fun hx => ?_, fun hx hx' => ?_⟩⟩
    · simp only [Function.update_apply]
      split_ifs with hσ
      · exact List.mem_append_left _ (hσ ▸ hx)
      · exact hx
    · simp only [Function.update_apply]
      split_ifs with hxv
      · subst hxv; exact absurd hx (fun h => h₁ (Or.inr (Or.inr h)))
      · rfl
    · by_cases hxv : x = v
      · subst hxv
        exact ⟨Function.update_self .., Nat.le_of_not_lt fun h => h₁ (Or.inr (Or.inl h))⟩
      · refine absurd ?_ hx'
        simp only [Function.update_apply] at hx
        split_ifs at hx with hσ
        · rcases List.mem_append.1 hx with h | h
          · exact hσ ▸ h
          · exact absurd (List.mem_singleton.1 h) hxv
        · exact hx

private theorem grow_blockReceipt (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    Grow t A (blockReceipt sp A t B) := by
  unfold blockReceipt
  generalize hA' : ({ A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) } :
    SAState sp.n) = A'
  have h₀ : Grow t A A' := Grow.of_eq (by rw [← hA']) (by rw [← hA'])
  clear hA'
  induction (blockVotes B) generalizing A' with
  | nil => exact h₀
  | cons v l ih => exact ih _ (h₀.trans (grow_admitVote _ _ _))

private theorem grow_optimistic (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    Grow t A (optimisticConfirmation sp A Φ t) := by
  unfold optimisticConfirmation updateLatestConfirmed
  split
  · exact Grow.of_eq rfl rfl
  · split_ifs <;> exact Grow.of_eq rfl rfl

private theorem grow_updateConfirmation (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) : Grow t A (updateConfirmation sp A Φ t s) := by
  unfold updateConfirmation updateLatestConfirmed
  dsimp only
  split
  · exact Grow.of_eq rfl rfl
  · split_ifs <;> exact Grow.of_eq rfl rfl

private theorem grow_tryVote (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    Grow t A (tryVote sp x A Φ t).1 := by
  unfold tryVote
  dsimp only
  split_ifs
  · exact Grow.of_eq rfl rfl
  · exact Grow.of_eq rfl rfl
  all_goals
    refine Grow.trans ?_ ((grow_admitVote _ _ _).trans (grow_optimistic _ _ _))
    first
    | exact Grow.of_eq rfl rfl

/-- A call other than a restart grows the pools (`Grow`). -/
private theorem grow_step {ro : ReplayOrder sp FGP} (self : Fin sp.n) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (c : (goldilocksSA sp FGP ro).Call)
    (hc : c ≠ .restart) : Grow t A ((goldilocksSA sp FGP ro).step self A Φ t c).1 := by
  cases c with
  | tick =>
    change Grow t A (acOnTick sp self A Φ t).1
    unfold acOnTick
    dsimp only
    split_ifs
    · exact (grow_tryVote _ _ _ _).trans (grow_updateConfirmation _ _ _ _)
    · exact grow_updateConfirmation _ _ _ _
    · exact grow_tryVote _ _ _ _
    · exact Grow.of_eq rfl rfl
    · exact Grow.of_eq rfl rfl
  | proposal =>
    change Grow t A (acProposal sp A Φ t).1
    unfold acProposal
    dsimp only
    split_ifs <;> exact Grow.of_eq rfl rfl
  | toFG =>
    change Grow t A (acToFG sp A Φ t).1
    unfold acToFG
    dsimp only
    split_ifs
    · split
      · exact Grow.of_eq rfl rfl
      · split_ifs <;> exact Grow.of_eq rfl rfl
    · exact Grow.of_eq rfl rfl
  | message m =>
    exact ((grow_admitVote _ _ _).trans (grow_optimistic _ _ _)).trans (grow_tryVote _ _ _ _)
  | block B =>
    exact ((grow_blockReceipt _ _ _).trans (grow_optimistic _ _ _)).trans (grow_tryVote _ _ _ _)
  | restart => exact absurd rfl hc

/-- Admitting a vote of the slot of `t` or the previous one leaves it in its pool, or two other
votes of its validator there. -/
private theorem admitVote_held (A : SAState sp.n) {t : Time} {v : Vote sp.n}
    (h₁ : (sp.slot t : Int) - 1 ≤ v.slot) (h₂ : v.slot ≤ sp.slot t) :
    v ∈ (admitVote sp A t v).pool v.slot ∨
      v.val ∈ equivocators {w | w ∈ (admitVote sp A t v).pool v.slot} := by
  unfold admitVote
  split_ifs with ha hb
  · left
    rcases ha with ha | ha | ha
    · omega
    · omega
    · exact ha
  · right
    generalize hL : ((A.pool v.slot).filter (fun x => x.val = v.val)).dedup = L at hb
    have hnd : L.Nodup := hL ▸ List.nodup_dedup _
    rcases L with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at hb
    · simp at hb
    have hmem : ∀ c ∈ a :: b :: l, c ∈ A.pool v.slot ∧ c.val = v.val := fun c hc => by
      rw [← hL, List.mem_dedup, List.mem_filter] at hc
      exact ⟨hc.1, of_decide_eq_true hc.2⟩
    obtain ⟨ha, hav⟩ := hmem a List.mem_cons_self
    obtain ⟨hb', hbv⟩ := hmem b (List.mem_cons_of_mem _ List.mem_cons_self)
    refine ⟨a, ha, b, hb', ?_, hav, hbv⟩
    rintro rfl
    exact (List.nodup_cons.1 hnd).1 List.mem_cons_self
  · left
    simp

/-- After a vote's receipt (an `on_message` call) or its emission, at a time of its slot or the
next, the node holds it, or two other votes of its validator. -/
private theorem held_after (A A' : SAState sp.n) {t : Time} {v : Vote sp.n}
    (h₁ : (sp.slot t : Int) - 1 ≤ v.slot) (h₂ : v.slot ≤ sp.slot t)
    (h : Grow t (admitVote sp A t v) A') :
    v ∈ A'.pool v.slot ∨ v.val ∈ equivocators {w | w ∈ A'.pool v.slot} := by
  rcases admitVote_held A h₁ h₂ with hv | ⟨a, ha, b, hb, hab, hav, hbv⟩
  · exact Or.inl (h.1 _ hv)
  · exact Or.inr ⟨a, h.1 _ ha, b, h.1 _ hb, hab, hav, hbv⟩

/-! ## Over an SA trace -/

variable {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
  {tr : SATrace sp FGP ro}

private theorem frameOK_of_call (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FrameOK ℓ.frame := by
  rcases hr.frameLaw x hx i ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1.1

private theorem state_succ_of_call {y : Fin sp.n} {k : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y k ℓ) : tr.state y (k + 1) = tr.post k := by
  rw [Trace.state]
  split_ifs with h
  · rfl
  · exact absurd ⟨hc.1, by simp [hc.2]⟩ h

private theorem state_succ_of_not {y : Fin sp.n} {k : Nat}
    (hn : ¬ (tr.node k = y ∧ tr.label k ≠ none)) : tr.state y (k + 1) = tr.state y k := by
  rw [Trace.state]
  split_ifs
  rfl

/-- A call other than a restart grows the pools. -/
private theorem grow_call (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y k ℓ)
    (hnr : ℓ.call ≠ .restart) : Grow (tr.time k) (tr.state y k) (tr.post k) := by
  have he := hr.exec k ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at he
  have h := grow_step (ro := ro) y (tr.state y k) ℓ.frame (tr.time k) ℓ.call hnr
  rwa [he] at h

/-- **Where a held vote comes from.** A vote that an honest node holds before cut `c` (in the
pool of its slot) was admitted by it at an earlier cut, at a time of slot at least the vote's,
which is its stamp; or a restart at an earlier cut put it there, from a block of the restart's
frame. -/
theorem pool_origin (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) (c : Nat) (x : Vote sp.n) (hx : x ∈ (tr.state y c).pool x.slot) :
    (∃ k < c, tr.SendOrAdmit y k x ∧ (tr.state y c).voteStamp x = ETime.of (tr.time k) ∧
      x.slot ≤ sp.slot (tr.time k)) ∨
    ∃ k < c, ∃ ℓ, tr.CallAt y k ℓ ∧ ℓ.call = .restart ∧
      (tr.state y c).voteStamp x = ETime.of (tr.time k) ∧ ∃ B ∈ ℓ.frame.tree, x ∈ blockVotes B := by
  induction c with
  | zero =>
    change x ∈ (tr.init y).pool x.slot at hx
    rw [hr.init y hy] at hx
    simp [SAState.initial] at hx
  | succ c ih =>
    by_cases hn : tr.node c = y ∧ tr.label c ≠ none
    · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hn.2
      have hc : tr.CallAt y c ℓ := ⟨hn.1, hℓ⟩
      rw [state_succ_of_call hc] at hx ⊢
      by_cases hrs : ℓ.call = .restart
      · have he := hr.exec c ℓ hℓ (hn.1 ▸ hy)
        rw [hn.1, hrs] at he
        have hR := (restart_state sp) FGP ro y (tr.state y c) ℓ.frame (tr.time c)
          (frameOK_of_call hr hy hc) (hr.time_nonneg c)
        change (acRestart sp ro y (tr.state y c) ℓ.frame (tr.time c)) = _ at he
        rw [he] at hR
        obtain ⟨hs, B, hB, hxB⟩ := hR.2.2.2.2.2.2.2.2.1 _ x hx
        exact Or.inr ⟨c, Nat.lt_succ_self c, ℓ, hc, hrs, hs, B, hB, hxB⟩
      · have hg := grow_call hr hy hc hrs
        by_cases hx' : x ∈ (tr.state y c).pool x.slot
        · rw [(hg.2 x).1 hx']
          rcases ih hx' with ⟨k, hk, h⟩ | ⟨k, hk, h⟩
          · exact Or.inl ⟨k, hk.trans (Nat.lt_succ_self c), h⟩
          · exact Or.inr ⟨k, hk.trans (Nat.lt_succ_self c), h⟩
        · obtain ⟨hs, hsl⟩ := (hg.2 x).2 hx hx'
          exact Or.inl ⟨c, Nat.lt_succ_self c, ⟨ℓ, hc, Or.inr ⟨hrs, hx', hx⟩⟩, hs, hsl⟩
    · rw [state_succ_of_not hn] at hx ⊢
      rcases ih hx with ⟨k, hk, h⟩ | ⟨k, hk, h⟩
      · exact Or.inl ⟨k, hk.trans (Nat.lt_succ_self c), h⟩
      · exact Or.inr ⟨k, hk.trans (Nat.lt_succ_self c), h⟩

/-- Between restarts, an honest node's pools only grow. -/
theorem pool_mono (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {a b : Nat} (hab : a ≤ b) (hnr : ∀ k, a ≤ k → k < b → ¬ tr.RestartAt y k)
    (σ : Nat) : (tr.state y a).pool σ ⊆ (tr.state y b).pool σ := by
  induction b, hab using Nat.le_induction with
  | base => exact List.Subset.refl _
  | succ b hab ih =>
    intro v hv
    have hv := ih (fun k hk hkb => hnr k hk (hkb.trans (Nat.lt_succ_self b))) hv
    by_cases hn : tr.node b = y ∧ tr.label b ≠ none
    · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hn.2
      have hc : tr.CallAt y b ℓ := ⟨hn.1, hℓ⟩
      rw [state_succ_of_call hc]
      exact (grow_call hr hy hc fun h => hnr b hab (Nat.lt_succ_self b) ⟨ℓ, hc, h⟩).1 σ hv
    · rw [state_succ_of_not hn]
      exact hv

/-- **An honest node holds a vote it processed.** When an honest node processes a vote (receives
it, or emits it) at a time of the vote's slot or the next, the node holds it after that cut, or
two other votes of its validator. -/
theorem held_of_processAt (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {v : Vote sp.n} (hp : tr.ProcessAt y k v)
    (h₁ : (sp.slot (tr.time k) : Int) - 1 ≤ v.slot) (h₂ : v.slot ≤ sp.slot (tr.time k)) :
    v ∈ (tr.state y (k + 1)).pool v.slot ∨
      v.val ∈ equivocators {w | w ∈ (tr.state y (k + 1)).pool v.slot} := by
  obtain ⟨ℓ, hc, hm | ⟨e, he, rfl⟩⟩ := hp
  · rw [state_succ_of_call hc]
    have he := hr.exec k ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1, hm] at he
    have h := (grow_optimistic (admitVote sp (tr.state y k) (tr.time k) v) ℓ.frame
      (tr.time k)).trans (grow_tryVote y _ ℓ.frame (tr.time k))
    change Grow _ _ (acOnMessage sp y (tr.state y k) ℓ.frame (tr.time k) v).1 at h
    change acOnMessage sp y (tr.state y k) ℓ.frame (tr.time k) v = _ at he
    rw [he] at h
    exact held_after _ _ h₁ h₂ h
  · rw [state_succ_of_call hc, post_of_castAt hr hy ⟨hc, he⟩]
    exact held_after _ _ h₁ h₂ (grow_optimistic _ _ _)

private theorem lastWake_eq_coe {y : Fin sp.n} {w : Time} :
    ∀ {c : Nat}, tr.lastWake y c = (w : WithBot Time) →
      ∃ k ≤ c, tr.RestartAt y k ∧ tr.time k = w
  | 0, h => by
    unfold ACTrace.lastWake at h
    split_ifs at h with hr
    · exact ⟨0, le_rfl, hr, WithBot.coe_injective h⟩
    · simp at h
  | c + 1, h => by
    unfold ACTrace.lastWake at h
    split_ifs at h with hr
    · exact ⟨c + 1, le_rfl, hr, WithBot.coe_injective h⟩
    · obtain ⟨k, hk, h'⟩ := lastWake_eq_coe h
      exact ⟨k, hk.trans (Nat.le_succ c), h'⟩

/-- With every restart up to cut `c` at or before `τ`, the deadline of `τ` is `τ + Δ`. -/
private theorem deadline_eq {y : Fin sp.n} {c : Nat} {τ : Time}
    (h : ∀ k ≤ c, tr.RestartAt y k → tr.time k ≤ τ) : tr.deadline y c τ = τ + sp.Δ := by
  unfold ACTrace.deadline
  rcases hw : tr.lastWake y c with _ | w
  · rfl
  · obtain ⟨k, hk, hrk, rfl⟩ := lastWake_eq_coe hw
    simp [Option.elim, max_eq_left (h k hk hrk)]

/-- **Forwarding under `Sync`.** A vote that an honest `y` sends or admits at a cut `k` inside
the window of `Sync` is held, at a later call of an honest `X` at least `Δ` after it, by `X`, or
`X` holds two other votes of its validator; when every restart of `X` up to that call is at or
before the time of `k`, and the vote's slot is the slot, or the previous one, of every time in
`[t_k, t_k + Δ)`. -/
theorem sync_forward (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {a b : Time}
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U a b tr) {y X : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {v : Vote sp.n} (hsend : tr.SendOrAdmit y k v) (ha : a ≤ tr.time k)
    (hb : tr.time k ≤ b) (hX : X ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt X i ℓ) (hrs : ∀ k' ≤ i, tr.RestartAt X k' → tr.time k' ≤ tr.time k)
    (hdl : tr.time k + sp.Δ ≤ tr.time i)
    (hslot : ∀ t, tr.time k ≤ t → t < tr.time k + sp.Δ →
      (sp.slot t : Int) - 1 ≤ v.slot ∧ v.slot ≤ sp.slot t) :
    v ∈ (tr.state X i).pool v.slot ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i).pool v.slot} := by
  have hd : ∀ c ≤ i, tr.deadline X c (tr.time k) = tr.time k + sp.Δ := fun c hc =>
    deadline_eq fun k' hk' hr' => hrs k' (hk'.trans hc) hr'
  obtain ⟨k', hk'i, hkk', hproc, hk'dl⟩ := hsync.1 y hy k v hsend ha hb X hX i ℓ hc
    (by rw [hd i le_rfl]; exact hdl)
  rw [hd k' hk'i] at hk'dl
  have hk'lt : k' < i := lt_of_le_of_ne hk'i (by rintro rfl; linarith)
  obtain ⟨h₁, h₂⟩ := hslot _ hkk' hk'dl
  have hmono := pool_mono hr hX (Nat.succ_le_of_lt hk'lt) (fun k'' hk'' hk''i hrk'' => by
    obtain ⟨ℓ'', hc'', hcall''⟩ := hrk''
    obtain ⟨u, -, hu, -, hprev⟩ := hr.sleep_of_restart X hX k'' ℓ'' hc'' hcall''
    obtain ⟨ℓ', hc', -⟩ := hproc
    have := hprev k' (by omega) ℓ' hc'
    have := hrs k'' hk''i.le ⟨ℓ'', hc'', hcall''⟩
    linarith) v.slot
  rcases held_of_processAt hr hX hproc h₁ h₂ with h | ⟨a, ha, b, hb, hab, hav, hbv⟩
  · exact Or.inl (hmono h)
  · exact Or.inr ⟨a, hmono ha, b, hmono hb, hab, hav, hbv⟩

/-- The state a cast leaves holds the votes of the vote's read point, with their stamps. -/
theorem readPoint_pool (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y j ℓ e) {x : Vote sp.n} {σ : Nat} (hx : x ∈ e.readPoint.pool σ) :
    x ∈ (tr.state y (j + 1)).pool σ ∧
      (x.slot = σ → (tr.state y (j + 1)).voteStamp x = e.readPoint.voteStamp x) := by
  rw [state_succ_of_call hc.1, post_of_castAt hr hy hc]
  have hg := (grow_admitVote e.readPoint (tr.time j) e.msg).trans
    (grow_optimistic _ ℓ.frame (tr.time j))
  exact ⟨hg.1 _ hx, fun h => (hg.2 x).1 (h ▸ hx)⟩

/-- A cast leaves the restart time of its read point. -/
theorem restartTime_of_castAt (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y j ℓ e) : (tr.post j).restartTime = e.readPoint.restartTime := by
  have h₁ : ∀ (A : SAState sp.n) t v, (admitVote sp A t v).restartTime = A.restartTime := by
    intro A t v; unfold admitVote; split_ifs <;> rfl
  have h₂ : ∀ (A : SAState sp.n) (Φ : Frm sp.n FGP) t,
      (optimisticConfirmation sp A Φ t).restartTime = A.restartTime := by
    intro A Φ t; unfold optimisticConfirmation updateLatestConfirmed; split
    · rfl
    · split_ifs <;> rfl
  rw [post_of_castAt hr hy hc, h₂, h₁]

end Consensus.Goldilocks.SA

end
