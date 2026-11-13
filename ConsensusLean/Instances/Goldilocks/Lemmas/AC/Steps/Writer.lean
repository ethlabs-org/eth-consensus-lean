module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ReceiptCover
import ConsensusLean.Lemmas.Tactic.Linarith

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

variable {wm : SA.WriteMode}

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

/-! ## The SA functions -/

theorem admitVote_restartTime (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).restartTime = A.restartTime := by
  unfold admitVote
  split_ifs <;> rfl

private theorem optimistic_restartTime (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).restartTime = A.restartTime := by
  unfold optimisticConfirmation updateLatestConfirmed
  split
  · rfl
  · split_ifs <;> rfl

/-- `tryVote_restartTime` with the unlock given. -/
theorem tryVote_restartTimeWith
    {L : Set Lock} (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : (tryVoteWithM sp wm x L A Φ t).1.restartTime = A.restartTime := by
  unfold tryVoteWithM
  dsimp only
  split_ifs <;>
    simp only [optimisticConfirmationM_keep _ optimistic_restartTime,
      admitVote_restartTime]

theorem tryVote_restartTime (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : (tryVote sp x A Φ t).1.restartTime = A.restartTime :=
  tryVote_restartTimeWith (wm := WriteMode.parent sp) (x := x) (A := A) (Φ := Φ) (t := t)

theorem updateConfirmation_restartTime (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) : (updateConfirmation sp A Φ t s).restartTime = A.restartTime := by
  unfold updateConfirmation updateLatestConfirmed
  dsimp only
  split
  · rfl
  · split_ifs <;> rfl

/-- `onTick_restartTime` with the unlock given. -/
theorem onTick_restartTimeWith
    {L : Set Lock} (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : (acOnTickWithM sp wm x L A Φ t).1.restartTime = A.restartTime := by
  unfold acOnTickWithM
  dsimp only
  split
  · rfl
  · split
    · rw [updateConfirmationM_field SAState.restartTime (fun _ _ => rfl),
        updateConfirmation_restartTime]
      split <;> first | exact tryVote_restartTimeWith _ _ _ _ | rfl
    · split <;> first | exact tryVote_restartTimeWith _ _ _ _ | rfl

/-- A tick leaves the restart time. -/
theorem onTick_restartTime (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : (acOnTick sp x A Φ t).1.restartTime = A.restartTime :=
  onTick_restartTimeWith (wm := WriteMode.parent sp) (x := x) (A := A) (Φ := Φ) (t := t)

theorem optimistic_pool (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).pool = A.pool := by
  unfold optimisticConfirmation updateLatestConfirmed
  split
  · rfl
  · split_ifs <;> rfl

/-! ## Over an SA trace -/

/-- `cast_time_le` with the unlock given. -/
private theorem cast_time_leU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) : tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ := by
  have hv : ∀ (A : SAState sp.n) (t : Time), (tryVoteWithM sp wm y (u i) A ℓ.frame t).2 ≠ [] →
      t ≤ sp.ts (sp.slot t) + sp.Δ := by
    intro A t h
    by_contra ht
    have hguard : ¬ joined sp A t ∨ A.votedSlot = sp.slot t ∨
        sp.ts (sp.slot t) + sp.Δ < t := Or.inr (Or.inr (lt_of_not_ge ht))
    simp only [tryVoteWithM, hguard, ite_true] at h
    exact h rfl
  have hΦ : FrameOK ℓ.frame := by
    rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
      exact h.1.1
  obtain ⟨hc, he⟩ := hc
  have hx := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at hx
  have hne : (stepWithM sp ro wm y (u i) (tr.state y i) ℓ.frame (tr.time i)
      ℓ.call).2 ≠ [] := by
    rw [hx]; exact List.ne_nil_of_mem he
  generalize tr.state y i = A at hne
  generalize ℓ.call = c at hne
  cases c with
  | tick =>
    change (acOnTickWithM sp wm y (u i) A ℓ.frame (tr.time i)).2 ≠ [] at hne
    unfold acOnTickWithM at hne
    dsimp only at hne
    split at hne
    · exact absurd rfl hne
    · change (if tr.time i = sp.ts (sp.slot (tr.time i)) + sp.Δ then
        tryVoteWithM sp wm y (u i) A ℓ.frame (tr.time i) else (A, [])).2 ≠ [] at hne
      split at hne
      · exact hv _ _ hne
      · exact absurd rfl hne
  | proposal => exact absurd rfl hne
  | toFG => exact absurd rfl hne
  | message m => exact hv _ _ hne
  | block B => exact hv _ _ hne
  | restart =>
    change (acRestart sp ro y A ℓ.frame (tr.time i)).2 ≠ [] at hne
    exact absurd ((restart_state sp) FGP ro y A ℓ.frame (tr.time i) hΦ (hr.time_nonneg i)).1
      hne

/-- An honest vote is cast at most `Δ` after the start of its slot (`try_vote`'s guard). -/
private theorem cast_time_le (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) : tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ :=
  cast_time_leU (hr := hr.toU) (y := y) (hy := hy) (i := i) (ℓ := ℓ) (e := e) (hc := hc)

/-- `writer_pool_of_sync` with the unlock given. -/
private theorem writer_pool_of_syncU
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U) {X : Fin sp.n}
    (hX : X ∈ H) {i₀ s : Nat}
    {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ s ℓX) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr ∨
      ServiceWindowBefore H U (sp.ts s) (tr.time i₀) tr) {k : Nat}
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
  obtain ⟨-, hys, hyj, -⟩ := castAt_specU hr hy hc
  have hsi : sp.slot (tr.time i) = s + 1 := by omega
  -- the restarts of the voter up to its vote, and of the writer up to its update, are at or
  -- before `t_s`
  have hrsy : ∀ k ≤ i, tr.RestartAt y k → tr.time k ≤ sp.ts s := by
    have hj' : joined sp (tr.post i) (tr.time i) := by
      unfold joined; rw [restartTime_of_castAtU hr hy hc]; exact hyj
    intro k hk hrk
    have := ((joined_awakeU sp) FGP ro H U tr hr y hy i ℓ hc.1 hj').2 k hk hrk
    rwa [hsi, hcast] at this
  have hrsX : ∀ k ≤ i₀, tr.RestartAt X k → tr.time k ≤ sp.ts s := by
    obtain ⟨hcX, htick, hti₀, hjX⟩ := hupd
    have he := hr.exec i₀ ℓX hcX.2 (hcX.1 ▸ hX)
    rw [hcX.1, htick] at he
    have hj' : joined sp (tr.post i₀) (tr.time i₀) := by
      have hpost : tr.post i₀ = (acOnTickWithM sp wm X (u i₀)
          (tr.state X i₀) ℓX.frame (tr.time i₀)).1 :=
        (congrArg Prod.fst he).symm
      unfold joined; rw [hpost, onTick_restartTimeWith]; exact hjX
    have hsl : sp.slot (tr.time i₀) = s + 1 := by
      rw [hti₀]
      exact slot_of_mem sp (s + 1) (by rw [hts]; linarith) (by rw [hts₂]; linarith)
    intro k hk hrk
    have := ((joined_awakeU sp) FGP ro H U tr hr X hX i₀ ℓX hcX hj').2 k hk hrk
    rwa [hsl, hcast] at this
  intro v hv
  have hvs : v.slot = s := state_pool_slotU sp hr hy (k + 1) s v hv
  rcases pool_originU hr hy (k + 1) v (hvs ▸ hv) with
    ⟨k', hk', hsend, -, hsl⟩ | ⟨k', hk', ℓk, hck, hrk, -, B, hB, hvB⟩
  · have hsk : sp.ts s ≤ tr.time k' :=
      (ts_le_iff_le_slot sp (hr.time_nonneg k') s).2 (by rw [← hvs]; exact_mod_cast hsl)
    have hti : tr.time i ≤ sp.ts s + 5 * sp.Δ := by
      have := cast_time_leU hr hy hc
      rw [hsi, hts] at this; linarith only [this]
    have hki : tr.time k' ≤ tr.time i := hr.time_mono ((Nat.le_of_lt_succ hk').trans hk)
    have hrs : ∀ k'' ≤ i₀, tr.RestartAt X k'' → tr.time k'' ≤ tr.time k' :=
      fun k'' hk'' hr'' => (hrsX k'' hk'' hr'').trans hsk
    have hdl : tr.time k' + sp.Δ ≤ tr.time i₀ := by
      rw [hupd.2.2.1]; linarith only [hki, hti]
    have hslot : ∀ t, tr.time k' ≤ t → t < tr.time k' + sp.Δ →
        (sp.slot t : Int) - 1 ≤ v.slot ∧ v.slot ≤ sp.slot t := by
      rw [hvs]; exact slot_window_of_forward (hr.time_nonneg k') hsk hki hti
    have hheld := hsync.elim
      (fun h => sync_forwardU hr h hy hsend hsk hki hX hupd.1 hrs hdl hslot)
      (fun h => sync_window_before_forwardU hr h hy hsend hsk hdl hX hupd.1 hrs hdl hslot)
    rwa [hvs] at hheld
  · -- a restart's vote is of a block of slot at most `s`, so of slot below `s`
    have hBv := (frame_validPayloadU sp hr hy hck B hB).1 v hvB
    have hBs := frame_slot_leU sp hr hy hck B hB
    have htk := hrsy k' ((Nat.le_of_lt_succ hk').trans hk) ⟨ℓk, hck, hrk⟩
    have : ¬ ((s + 1 : Nat) : Int) ≤ sp.slot (tr.time k') := fun h => by
      have := (ts_le_iff_le_slot sp (hr.time_nonneg k') _).2 h
      rw [hts] at this; linarith only [this, htk, hΔ]
    clear * - this hBv hBs hvs
    omega

private theorem writer_pool_of_sync (hrun : ACRun proposer tr H U) {X : Fin sp.n}
    (hX : X ∈ H) {i₀ s : Nat}
    {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ s ℓX) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr ∨
      ServiceWindowBefore H U (sp.ts s) (tr.time i₀) tr) {k : Nat}
    (hk : k ≤ i) :
    ∀ v ∈ (tr.state y (k + 1)).pool s, v ∈ (tr.state X i₀).pool s ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s} :=
  writer_pool_of_syncU (hrun := hrun.toU) (X := X) (hX := hX) (i₀ := i₀) (s := s) (ℓX := ℓX)
      (hupd := hupd) (y := y) (hy := hy) (i := i) (ℓ := ℓ) (e := e) (hc := hc) (hs := hs)
          (hsync := hsync) (k := k) (hk := hk)

/-- `writer_merged_of_sync` with the unlock given. -/
private theorem writer_merged_of_syncU
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U) {X : Fin sp.n}
    (hX : X ∈ H) {i₀ s : Nat}
    {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ s ℓX) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr ∨
      ServiceWindowBefore H U (sp.ts s) (tr.time i₀) tr) :
    ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s} := by
  have hr := hrun.localRun
  rintro v (hv | ⟨B, hB, hBs, hvB⟩) hvs
  · have hv : v ∈ e.readPoint.poolAt ((s + 1 : Nat) - 1 : Int) := (List.mem_filter.1 hv).1
    simp only [SAState.poolAt] at hv
    split_ifs at hv with hneg
    · simp at hv
    exact writer_pool_of_syncU hrun hX hupd hy hc hs hsync le_rfl v
      (readPoint_poolU hr hy hc (by simpa using hv)).1
  -- a vote of a slot-`(s+1)` block of the tree, which `y` accepted at a cut `k ≤ i`
  obtain ⟨-, hys, -, -⟩ := castAt_specU hr hy hc
  rcases frame_genesis_or_acceptedU sp hr hy hc.1 B hB with h0 | ⟨k, hki, ℓk, hck, hcall⟩
  · omega
  have hBk : B.slot ≤ sp.slot (tr.time k) := by
    rcases hr.frameLaw y hy k ℓk hck with ⟨-, Φ₀, -, -, hok⟩ | ⟨j, ℓ', -, -, -, hok⟩ <;>
    · rw [hcall] at hok
      obtain ⟨-, -, -, h⟩ := hok
      exact h
  have hki' := slot_mono sp (hr.time_nonneg k) (hr.time_mono hki)
  have he := hr.exec k ℓk hck.2 (hck.1 ▸ hy)
  rw [hck.1, hcall] at he
  have hpost : tr.post k = (tryVoteWithM sp wm y (u k) (optimisticConfirmationM sp wm
      (blockReceipt sp (tr.state y k) (tr.time k) B) ℓk.frame (tr.time k)) ℓk.frame
      (tr.time k)).1 := (congrArg Prod.fst he).symm
  exact receipt_vote_covered (L := u k) (t := tr.time k) y (tr.state y k) ℓk.frame hvB hvs
    (by omega) (by omega) fun w hw => writer_pool_of_syncU hrun hX hupd hy hc hs hsync hki w
      (by rw [state_succ_of_call hck, hpost]; exact hw)

private theorem writer_merged_of_sync (hrun : ACRun proposer tr H U) {X : Fin sp.n}
    (hX : X ∈ H) {i₀ s : Nat}
    {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ s ℓX) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr ∨
      ServiceWindowBefore H U (sp.ts s) (tr.time i₀) tr) :
    ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s} :=
  writer_merged_of_syncU (hrun := hrun.toU) (X := X) (hX := hX) (i₀ := i₀) (s := s) (ℓX := ℓX)
      (hupd := hupd) (y := y) (hy := hy) (i := i) (ℓ := ℓ) (e := e) (hc := hc) (hs := hs)
          (hsync := hsync)

/-- `writer_pool` with the unlock given. -/
theorem writer_poolU
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U) {X : Fin sp.n} (hX : X ∈ H)
    {i₀ s : Nat}
    {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ s ℓX) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr) {k : Nat}
    (hk : k ≤ i) :
    ∀ v ∈ (tr.state y (k + 1)).pool s, v ∈ (tr.state X i₀).pool s ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s} :=
  writer_pool_of_syncU hrun hX hupd hy hc hs (Or.inl hsync) hk

/-- **The writer's pool, for the voter's pool.** -/
theorem writer_pool (hrun : ACRun proposer tr H U) {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat}
    {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ s ℓX) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr) {k : Nat}
    (hk : k ≤ i) :
    ∀ v ∈ (tr.state y (k + 1)).pool s, v ∈ (tr.state X i₀).pool s ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s} :=
  writer_poolU (hrun := hrun.toU) (X := X) (hX := hX) (i₀ := i₀) (s := s) (ℓX := ℓX)
      (hupd := hupd) (y := y) (hy := hy) (i := i) (ℓ := ℓ) (e := e) (hc := hc) (hs := hs)
          (hsync := hsync) (k := k) (hk := hk)

/-- `writer_merged` with the unlock given. -/
theorem writer_mergedU
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U) {X : Fin sp.n} (hX : X ∈ H)
    {i₀ s : Nat}
    {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ s ℓX) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr) :
    ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s} :=
  writer_merged_of_syncU hrun hX hupd hy hc hs (Or.inl hsync)

/-- **The writer-pool condition** (A1.8 (d)) from `Sync[t_s, τ]`. -/
theorem writer_merged (hrun : ACRun proposer tr H U) {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat}
    {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ s ℓX) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr) :
    ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s} :=
  writer_mergedU (hrun := hrun.toU) (X := X) (hX := hX) (i₀ := i₀) (s := s) (ℓX := ℓX)
      (hupd := hupd) (y := y) (hy := hy) (i := i) (ℓ := ℓ) (e := e) (hc := hc) (hs := hs)
          (hsync := hsync)

/-- Writer-pool comparison uses only sources at or after the result slot's start. -/
theorem writer_pool_window_before (hrun : ACRun proposer tr H U) {a b : Time}
    (hsync : ServiceWindowBefore H U a b tr) {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat}
    (ha : a ≤ sp.ts s)
    {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ s ℓX)
    (hi₀ : tr.time i₀ ≤ b) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1) {k : Nat} (hk : k ≤ i) :
    ∀ v ∈ (tr.state y (k + 1)).pool s, v ∈ (tr.state X i₀).pool s ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s} := by
  exact writer_pool_of_sync hrun hX hupd hy hc hs (Or.inr {
    message := fun x hx k m hm h0 z hz j ℓ hc hd ht =>
      hsync.message x hx k m hm (ha.trans h0) z hz j ℓ hc (hd.trans hi₀) ht
    relay := fun x hx k B hB h0 z hz j ℓ hc hd ht hanc =>
      hsync.relay x hx k B hB (ha.trans h0) z hz j ℓ hc (hd.trans hi₀) ht hanc }) hk

/-- A1.8 (d) with an inclusive source window and the writer's update cutoff. -/
theorem writer_merged_window_before (hrun : ACRun proposer tr H U) {a b : Time}
    (hsync : ServiceWindowBefore H U a b tr) {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat}
    (ha : a ≤ sp.ts s)
    {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ s ℓX)
    (hi₀ : tr.time i₀ ≤ b) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1) :
    ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s} := by
  exact writer_merged_of_sync hrun hX hupd hy hc hs (Or.inr {
    message := fun x hx k m hm h0 z hz j ℓ hc hd ht =>
      hsync.message x hx k m hm (ha.trans h0) z hz j ℓ hc (hd.trans hi₀) ht
    relay := fun x hx k B hB h0 z hz j ℓ hc hd ht hanc =>
      hsync.relay x hx k B hB (ha.trans h0) z hz j ℓ hc (hd.trans hi₀) ht hanc })

end Consensus.Goldilocks.SA

end
