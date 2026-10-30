module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool

public section

/-! # Goldilocks SA: the writer's pool holds the voter's slot-`s` votes (A1.2, A1.8 (d))

Under `Sync[t_s, τ]`, every slot-`s` vote that an honest voter `y` of slot `s + 1` holds up to its
vote at `τ ≤ t_s + 5Δ` was admitted (and so forwarded) at a time in `[t_s, τ]`, and an honest
writer `X` whose update of slot `s` runs at `t_s + 6Δ` (joined) processed it before: it is in
`X`'s pool, or `X`'s two-vote cap refused it and the pool holds two distinct votes of its
validator (`writer_pool`). A slot-`s` vote of `y`'s merged view is in `y`'s pool, or carried by a
slot-`(s+1)` block that `y` accepted before its vote, whose receipt admitted the vote or refused
it for two other held votes of its validator (`writer_merged`, A1.8's condition (d)). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}

/-! ## The SA functions -/

private theorem admitVote_restartTime (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).restartTime = A.restartTime := by
  unfold admitVote
  split_ifs <;> rfl

private theorem optimistic_restartTime (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).restartTime = A.restartTime := by
  unfold optimisticConfirmation updateLatestConfirmed
  split
  · rfl
  · split_ifs <;> rfl

private theorem tryVote_restartTime (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : (tryVote sp x A Φ t).1.restartTime = A.restartTime := by
  unfold tryVote
  dsimp only
  split_ifs <;> simp only [optimistic_restartTime, admitVote_restartTime]

private theorem updateConfirmation_restartTime (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) : (updateConfirmation sp A Φ t s).restartTime = A.restartTime := by
  unfold updateConfirmation updateLatestConfirmed
  dsimp only
  split
  · rfl
  · split_ifs <;> rfl

/-- A tick leaves the restart time. -/
private theorem onTick_restartTime (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : (acOnTick sp x A Φ t).1.restartTime = A.restartTime := by
  unfold acOnTick
  dsimp only
  split_ifs <;> simp only [updateConfirmation_restartTime, tryVote_restartTime]

private theorem mem_admitVote_pool {A : SAState sp.n} {t : Time} {v x : Vote sp.n} {σ : Nat}
    (h : x ∈ A.pool σ) : x ∈ (admitVote sp A t v).pool σ := by
  unfold admitVote
  split_ifs
  · exact h
  · exact h
  · simp only [Function.update_apply]
    split_ifs with he
    · subst he; exact List.mem_append_left _ h
    · exact h

private theorem optimistic_pool (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).pool = A.pool := by
  unfold optimisticConfirmation updateLatestConfirmed
  split
  · rfl
  · split_ifs <;> rfl

private theorem tryVote_pool (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (σ : Nat) : A.pool σ ⊆ (tryVote sp x A Φ t).1.pool σ := by
  unfold tryVote
  dsimp only
  split_ifs
  · exact List.Subset.refl _
  · exact List.Subset.refl _
  all_goals
    intro w hw
    rw [optimistic_pool]
    exact mem_admitVote_pool hw

private theorem foldl_admit_pool {t : Time} {σ : Nat} :
    ∀ (l : List (Vote sp.n)) (A : SAState sp.n),
      A.pool σ ⊆ (l.foldl (fun A v => admitVote sp A t v) A).pool σ
  | [], _ => List.Subset.refl _
  | _ :: l, _ => fun _ hw => foldl_admit_pool l _ (mem_admitVote_pool hw)

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

/-- The receipt of a block admits each of its votes of the slot of `t` or the previous one: the
node holds it after the receipt, or two other votes of its validator. -/
private theorem blockReceipt_held (A : SAState sp.n) {t : Time} {B : Blk sp.n FGP}
    {v : Vote sp.n} (hv : v ∈ blockVotes B) (h₁ : (sp.slot t : Int) - 1 ≤ v.slot)
    (h₂ : v.slot ≤ sp.slot t) :
    v ∈ (blockReceipt sp A t B).pool v.slot ∨
      v.val ∈ equivocators {w | w ∈ (blockReceipt sp A t B).pool v.slot} := by
  unfold blockReceipt
  generalize ({ A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) } :
    SAState sp.n) = A'
  generalize blockVotes B = l at hv
  induction l generalizing A' with
  | nil => simp at hv
  | cons x l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hv with rfl | hv
    · have hs := foldl_admit_pool (t := t) (σ := v.slot) l (admitVote sp A' t v)
      rcases admitVote_held A' h₁ h₂ with h | ⟨a, ha, b, hb, hab, hav, hbv⟩
      · exact Or.inl (hs h)
      · exact Or.inr ⟨a, hs ha, b, hs hb, hab, hav, hbv⟩
    · exact ih _ hv

/-! ## Over an SA trace -/

private theorem state_succ_of_call {y : Fin sp.n} {k : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y k ℓ) : tr.state y (k + 1) = tr.post k := by
  rw [Trace.state]
  split_ifs with h
  · rfl
  · exact absurd ⟨hc.1, by simp [hc.2]⟩ h

/-- An honest vote is cast at most `Δ` after the start of its slot (`try_vote`'s guard). -/
private theorem cast_time_le (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) : tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ := by
  have hv : ∀ (A : SAState sp.n) (t : Time), (tryVote sp y A ℓ.frame t).2 ≠ [] →
      t ≤ sp.ts (sp.slot t) + sp.Δ := by
    intro A t h
    unfold tryVote at h
    dsimp only at h
    split_ifs at h with h₁
    · exact absurd rfl h
    · exact absurd rfl h
    all_goals exact not_lt.1 (not_or.1 (not_or.1 h₁).2).2
  have hΦ : FrameOK ℓ.frame := by
    rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
      exact h.1.1
  obtain ⟨hc, he⟩ := hc
  have hx := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at hx
  have hne : ((goldilocksSA sp FGP ro).step y (tr.state y i) ℓ.frame (tr.time i)
      ℓ.call).2 ≠ [] := by
    rw [hx]; exact List.ne_nil_of_mem he
  generalize tr.state y i = A at hne
  generalize ℓ.call = c at hne
  cases c with
  | tick =>
    change (acOnTick sp y A ℓ.frame (tr.time i)).2 ≠ [] at hne
    unfold acOnTick at hne
    dsimp only at hne
    split_ifs at hne <;> first | exact absurd rfl hne | exact hv _ _ hne
  | proposal => exact absurd rfl hne
  | toFG => exact absurd rfl hne
  | message m => exact hv _ _ hne
  | block B => exact hv _ _ hne
  | restart =>
    change (acRestart sp ro y A ℓ.frame (tr.time i)).2 ≠ [] at hne
    exact absurd ((restart_state sp) FGP ro y A ℓ.frame (tr.time i) hΦ (hr.time_nonneg i)).1
      hne

/-- Every block of an honest node's frame at a call is of slot `0` (genesis), or the node
accepted it at that call or an earlier one. -/
private theorem frame_accepted (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
    ∀ B ∈ ℓ.frame.tree, B.slot = 0 ∨ ∃ k ≤ i, tr.AcceptAt y k B := by
  induction i using Nat.strong_induction_on generalizing ℓ with
  | _ i ih =>
    have step : ∀ Φ : Frm sp.n FGP,
        (goldilocksSA sp FGP ro).CallOK U Φ (tr.time i) ℓ.call ℓ.frame →
        (∀ B ∈ Φ.tree, B.slot = 0 ∨ ∃ k ≤ i, tr.AcceptAt y k B) →
        ∀ B ∈ ℓ.frame.tree, B.slot = 0 ∨ ∃ k ≤ i, tr.AcceptAt y k B := by
      intro Φ hok hv X hX
      obtain ⟨-, hm⟩ := hok
      generalize hcall : ℓ.call = c at hm
      cases c with
      | block B =>
        rw [hm.1.tree_eq] at hX
        rcases hX.1 with rfl | hX
        · exact Or.inr ⟨i, le_rfl, ℓ, hc, hcall⟩
        · exact hv X hX
      | message m => exact hv X (hm.1 ▸ hX)
      | tick => exact hv X (hm ▸ hX)
      | proposal => exact hv X (hm ▸ hX)
      | toFG => exact hv X (hm ▸ hX)
      | restart => exact hv X (hm ▸ hX)
    rcases hr.frameLaw y hy i ℓ hc with
      ⟨-, Φ₀, ⟨htree, -, hslot, -, -⟩, -, hok⟩ | ⟨j, ℓ', hj, hc', -, hok⟩
    · refine step Φ₀ hok fun B hB => ?_
      rw [htree, Set.mem_singleton_iff] at hB
      subst hB
      exact Or.inl hslot
    · exact step _ hok fun B hB =>
        (ih j hj hc' B hB).imp_right fun ⟨k, hk, h⟩ => ⟨k, hk.trans hj.le, h⟩

/-- **The writer's pool, for the voter's pool.** -/
theorem writer_pool (hrun : ACRun tr H U) {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat}
    {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ s ℓX) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr) {k : Nat}
    (hk : k ≤ i) :
    ∀ v ∈ (tr.state y (k + 1)).pool s, v ∈ (tr.state X i₀).pool s ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s} := by
  have hr := hrun.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : ∀ m : Nat, sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := fun m => by
    simp only [SAParams.ts]; push_cast; ring
  have hts₂ : sp.ts (s + 2 : Nat) = sp.ts s + 8 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hcast : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  obtain ⟨-, hys, hyj, -⟩ := castAt_spec hr hy hc
  have hsi : sp.slot (tr.time i) = s + 1 := by omega
  -- the restarts of the voter up to its vote, and of the writer up to its update, are at or
  -- before `t_s`
  have hrsy : ∀ k ≤ i, tr.RestartAt y k → tr.time k ≤ sp.ts s := by
    have hj' : joined sp (tr.post i) (tr.time i) := by
      unfold joined; rw [restartTime_of_castAt hr hy hc]; exact hyj
    intro k hk hrk
    have := ((joined_awake sp) FGP ro H U tr hr y hy i ℓ hc.1 hj').2 k hk hrk
    rwa [hsi, hcast] at this
  have hrsX : ∀ k ≤ i₀, tr.RestartAt X k → tr.time k ≤ sp.ts s := by
    obtain ⟨hcX, htick, hti₀, hjX⟩ := hupd
    have he := hr.exec i₀ ℓX hcX.2 (hcX.1 ▸ hX)
    rw [hcX.1, htick] at he
    have hj' : joined sp (tr.post i₀) (tr.time i₀) := by
      have hpost : tr.post i₀ = (acOnTick sp X (tr.state X i₀) ℓX.frame (tr.time i₀)).1 :=
        (congrArg Prod.fst he).symm
      unfold joined; rw [hpost, onTick_restartTime]; exact hjX
    have hsl : sp.slot (tr.time i₀) = s + 1 := by
      rw [hti₀]
      exact slot_of_mem sp (s + 1) (by rw [hts]; linarith) (by rw [hts₂]; linarith)
    intro k hk hrk
    have := ((joined_awake sp) FGP ro H U tr hr X hX i₀ ℓX hcX hj').2 k hk hrk
    rwa [hsl, hcast] at this
  intro v hv
  have hvs : v.slot = s := state_pool_slot sp hr hy (k + 1) s v hv
  rcases pool_origin hr hy (k + 1) v (hvs ▸ hv) with
    ⟨k', hk', hsend, -, hsl⟩ | ⟨k', hk', ℓk, hck, hrk, -, B, hB, hvB⟩
  · have hsk : sp.ts s ≤ tr.time k' :=
      (ts_le_iff_le_slot sp (hr.time_nonneg k') s).2 (by rw [← hvs]; exact_mod_cast hsl)
    have hti : tr.time i ≤ sp.ts s + 5 * sp.Δ := by
      have := cast_time_le hr hy hc
      rw [hsi, hts] at this; linarith
    have hki : tr.time k' ≤ tr.time i := hr.time_mono (by omega)
    have := sync_forward hr hsync hy hsend hsk hki hX hupd.1
      (fun k'' hk'' hr'' => (hrsX k'' hk'' hr'').trans hsk) (by rw [hupd.2.2.1]; linarith)
      fun t h₁ h₂ => by
        have ht : 0 ≤ t := (hr.time_nonneg k').trans h₁
        have ha := (ts_le_iff_le_slot sp ht s).1 (hsk.trans h₁)
        have hb : ¬ ((s + 2 : Nat) : Int) ≤ sp.slot t := fun h => by
          have := (ts_le_iff_le_slot sp ht _).2 h
          rw [hts₂] at this; linarith
        rw [hvs]; omega
    rwa [hvs] at this
  · -- a restart's vote is of a block of slot at most `s`, so of slot below `s`
    have hBv := (frame_validPayload sp hr hy hck B hB).1 v hvB
    have hBs := frame_slot_le sp hr hy hck B hB
    have htk := hrsy k' (by omega) ⟨ℓk, hck, hrk⟩
    have : ¬ ((s + 1 : Nat) : Int) ≤ sp.slot (tr.time k') := fun h => by
      have := (ts_le_iff_le_slot sp (hr.time_nonneg k') _).2 h
      rw [hts] at this; linarith
    omega

/-- **The writer-pool condition** (A1.8 (d)) from `Sync[t_s, τ]`. -/
theorem writer_merged (hrun : ACRun tr H U) {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat}
    {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ s ℓX) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr) :
    ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s} := by
  have hr := hrun.localRun
  rintro v (hv | ⟨B, hB, hBs, hvB⟩) hvs
  · have hv : v ∈ e.readPoint.poolAt ((s + 1 : Nat) - 1 : Int) := (List.mem_filter.1 hv).1
    simp only [SAState.poolAt] at hv
    split_ifs at hv with hneg
    · simp at hv
    exact writer_pool hrun hX hupd hy hc hs hsync le_rfl v
      (readPoint_pool hr hy hc (by simpa using hv)).1
  -- a vote of a slot-`(s+1)` block of the tree, which `y` accepted at a cut `k ≤ i`
  obtain ⟨-, hys, -, -⟩ := castAt_spec hr hy hc
  rcases frame_accepted hr hy hc.1 B hB with h0 | ⟨k, hki, ℓk, hck, hcall⟩
  · omega
  have hBk : B.slot ≤ sp.slot (tr.time k) := by
    rcases hr.frameLaw y hy k ℓk hck with ⟨-, Φ₀, -, -, hok⟩ | ⟨j, ℓ', -, -, -, hok⟩ <;>
    · rw [hcall] at hok
      obtain ⟨-, -, -, h⟩ := hok
      exact h
  have hki' := slot_mono sp (hr.time_nonneg k) (hr.time_mono hki)
  have he := hr.exec k ℓk hck.2 (hck.1 ▸ hy)
  rw [hck.1, hcall] at he
  have hpost : tr.post k = (tryVote sp y (optimisticConfirmation sp
      (blockReceipt sp (tr.state y k) (tr.time k) B) ℓk.frame (tr.time k)) ℓk.frame
      (tr.time k)).1 := (congrArg Prod.fst he).symm
  have hsub : ∀ w ∈ (blockReceipt sp (tr.state y k) (tr.time k) B).pool s,
      w ∈ (tr.state y (k + 1)).pool s := fun w hw => by
    rw [state_succ_of_call hck, hpost]
    exact tryVote_pool _ _ _ _ _ (by rw [optimistic_pool]; exact hw)
  have hw := writer_pool hrun hX hupd hy hc hs hsync hki
  rcases blockReceipt_held (tr.state y k) hvB (t := tr.time k) (by omega) (by omega) with
    h | ⟨a, ha, b, hb, hab, hav, hbv⟩
  · rw [hvs] at h
    exact hw v (hsub v h)
  · rw [hvs] at ha hb
    rcases hw a (hsub a ha) with ha' | ha'
    · rcases hw b (hsub b hb) with hb' | hb'
      · exact Or.inr ⟨a, ha', b, hb', hab, hav, hbv⟩
      · exact Or.inr (hbv ▸ hb')
    · exact Or.inr (hav ▸ ha')

end Consensus.Goldilocks.SA

end
