module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served

public section

/-! # Goldilocks Healing, HR.4: relay after the GST and the writers of fast locks

`hr4-boot-carry.md` §§4–6 (workbench#23): the relay of a counted vote and its head to a next
voter under `Sync` on a window `[a₀, b]` instead of `Sync[0, b]` (`carryAt_of_writer_window`,
main's Sleepy `carryAt_of_writer` with the extra premise that the head was accepted at or after
`a₀`), and what a writer of a fast lock did with its counted votes before `t_s + 2Δ`
(`fastLock_writer`, main's Sleepy `result_writer` / `optimistic_writer` for both origins of a fast
lock, the fast test's selected block instead of the result), with the counted votes nonempty
(`fastLock_counted_nonempty`). The private helpers of `Compose/Sleepy/Transport.lean` are
repeated here (they are private there). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Vote Payload)
open Compose

/-! ### Deadlines -/

section Deadline

variable {P : Params} {FGP : Type} {A : ACInterface P FGP} {T : ACTrace A}

private theorem lastWake_coe {y : Fin P.n} {w : Time} :
    ∀ {c : Nat}, T.lastWake y c = (w : WithBot Time) → ∃ k ≤ c, T.RestartAt y k ∧ T.time k = w
  | 0, h => by
    unfold ACTrace.lastWake at h
    split_ifs at h with hr
    · exact ⟨0, le_rfl, hr, WithBot.coe_injective h⟩
    · simp at h
  | c + 1, h => by
    unfold ACTrace.lastWake at h
    split_ifs at h with hr
    · exact ⟨c + 1, le_rfl, hr, WithBot.coe_injective h⟩
    · obtain ⟨k, hk, h'⟩ := lastWake_coe h
      exact ⟨k, hk.trans (Nat.le_succ c), h'⟩

/-- With every restart up to cut `c` at or before `a`, the deadline of `τ` is at most
`max(τ, a) + Δ`. -/
private theorem deadline_le {y : Fin P.n} {c : Nat} {a : Time}
    (h : ∀ k ≤ c, T.RestartAt y k → T.time k ≤ a) (τ : Time) :
    T.deadline y c τ ≤ max τ a + P.Δ := by
  unfold ACTrace.deadline
  rcases hw : T.lastWake y c with _ | w
  · change τ + P.Δ ≤ max τ a + P.Δ
    linarith [le_max_left τ a]
  · obtain ⟨k, hk, hrk, rfl⟩ := lastWake_coe hw
    change max τ (T.time k) + P.Δ ≤ max τ a + P.Δ
    linarith [max_le_max (le_refl τ) (h k hk hrk)]

end Deadline

/-! ### One honest node over an SA trace -/

section Node

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (SA.Blk sp.n FGP)} {T : SA.SATrace sp FGP ro}

private theorem etime_lt {t t' : Time} : SA.ETime.of t < SA.ETime.of t' ↔ t < t' := by
  simp [SA.ETime.of]

private theorem etime_le {t t' : Time} : SA.ETime.of t ≤ SA.ETime.of t' ↔ t ≤ t' := by
  simp [SA.ETime.of]

/-- **A stamp is not earlier than the acceptance** (main's Sleepy `stamp_ge_of_accept`). -/
private theorem stamp_ge_of_accept (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {B : SA.Blk sp.n FGP} (hk : T.AcceptAt y k B)
    (hB : B.root ≠ sp.genesisRoot) :
    ∀ c, k + 1 ≤ c → SA.ETime.of (T.time k) ≤ (T.state y c).blockStamp B.root := by
  have hpost : ∀ c (ℓ : ACLabel (SA.goldilocksSA sp FGP ro)), T.CallAt y c ℓ → k ≤ c →
      (ℓ.call = .block B ∨ SA.ETime.of (T.time k) ≤ (T.state y c).blockStamp B.root) →
      SA.ETime.of (T.time k) ≤ (T.post c).blockStamp B.root := by
    intro c ℓ hc hkc hpre
    have hΦ : FrameOK ℓ.frame := by
      rcases hr.frameLaw y hy c ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1.1
    have he := hr.exec c ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1] at he
    have hp : T.post c =
        ((SA.goldilocksSA sp FGP ro).step y (T.state y c) ℓ.frame (T.time c) ℓ.call).1 := by
      rw [he]
    have htk : SA.ETime.of (T.time k) ≤ SA.ETime.of (T.time c) := etime_le.2 (hr.time_mono hkc)
    obtain ⟨hblk, -, hoth⟩ :=
      SA.step_blockStamp_eq ro y (T.state y c) hΦ (hr.time_nonneg c) ℓ.call
    rw [hp]
    generalize ℓ.call = cl at hpre hblk hoth ⊢
    cases cl with
    | block B' =>
      rw [hblk B' rfl, Function.update_apply]
      split_ifs with h
      · exact htk
      · rcases hpre with hpre | hpre
        · cases hpre
          exact absurd rfl h
        · exact hpre
    | restart =>
      change _ ≤ (SA.acRestart sp ro y (T.state y c) ℓ.frame (T.time c)).1.blockStamp B.root
      rcases ((SA.restart_state sp) FGP ro y (T.state y c) ℓ.frame (T.time c) hΦ
        (hr.time_nonneg c)).2.2.2.2.2.2.2.2.2.2 B.root with h | ⟨h, -⟩
      · rw [h]; simp [SA.SAState.initial, hB]
      · rw [h]; exact htk
    | tick => rw [hoth (fun _ => by simp) (by simp)]; exact hpre.resolve_left (by simp)
    | message m => rw [hoth (fun _ => by simp) (by simp)]; exact hpre.resolve_left (by simp)
    | proposal => rw [hoth (fun _ => by simp) (by simp)]; exact hpre.resolve_left (by simp)
    | toFG => rw [hoth (fun _ => by simp) (by simp)]; exact hpre.resolve_left (by simp)
  intro c hc
  induction c, hc using Nat.le_induction with
  | base =>
    obtain ⟨ℓ, hcl, hcall⟩ := hk
    rw [Trace.state_succ_of_call T hcl]
    exact hpost k ℓ hcl le_rfl (Or.inl hcall)
  | succ c hkc ih =>
    by_cases hn : ∃ ℓ, T.CallAt y c ℓ
    · obtain ⟨ℓ, hcl⟩ := hn
      rw [Trace.state_succ_of_call T hcl]
      exact hpost c ℓ hcl (by omega) (Or.inr ih)
    · rw [Trace.state_succ_of_not T fun ℓ hcl => hn ⟨ℓ, hcl⟩]
      exact ih

/-- At an honest vote, the pool of a slot other than the vote's, and the stamps of its votes,
are those of the state after the vote's call (main's Sleepy `readPoint_slot`). -/
private theorem readPoint_slot (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)}
    {e : SA.Em sp FGP} (hc : SA.CastAt T y i ℓ e) {σ : Nat} (hσ : e.msg.slot ≠ σ) :
    (T.state y (i + 1)).pool σ = e.readPoint.pool σ ∧
      ∀ u : Vote sp.n, u.slot = σ → (T.state y (i + 1)).voteStamp u = e.readPoint.voteStamp u := by
  rw [Trace.state_succ_of_call T hc.1, SA.post_of_castAt hr hy hc]
  have hopt : ∀ A : SA.SAState sp.n,
      (SA.optimisticConfirmation sp A ℓ.frame (T.time i)).pool = A.pool ∧
        (SA.optimisticConfirmation sp A ℓ.frame (T.time i)).voteStamp = A.voteStamp := by
    intro A
    unfold SA.optimisticConfirmation SA.updateLatestConfirmed
    split
    · exact ⟨rfl, rfl⟩
    · split_ifs <;> exact ⟨rfl, rfl⟩
  rw [(hopt _).1, (hopt _).2]
  unfold SA.admitVote
  split_ifs
  · exact ⟨rfl, fun _ _ => rfl⟩
  · exact ⟨rfl, fun _ _ => rfl⟩
  · exact ⟨Function.update_of_ne (Ne.symm hσ) _ _,
      fun u hu => Function.update_of_ne (by rintro rfl; exact hσ hu) _ _⟩

/-- **`Carry_y` from a writer, after the GST** (`hr4-boot-carry.md` §4; main's Sleepy
`carryAt_of_writer` with `Sync[a₀, b]` instead of `Sync[0, b]`). For an honest `y` casting its
slot-`(s+1)` vote, with `a₀ ≤ t_s` and `t_s + 2Δ ≤ b`: if each counted vote is of slot `s`, was
sent or admitted by an honest writer `w` at a time in `[t_s, t_s + 2Δ)`, and has a head above `y`'s
`Σ.F` that is genesis or that `w` accepted in `[a₀, t_s + 2Δ)`, then `Carry_y(s, ·, ·)` holds for
the counted votes. -/
theorem carryAt_of_writer_window (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
    {a₀ b : Time} (hsync : SyncAC (SA.goldilocksSA sp FGP ro) H U a₀ b T) {s : Nat}
    (ha₀ : a₀ ≤ sp.ts s) (hb : sp.ts s + 2 * sp.Δ ≤ b) {w : Fin sp.n} (hw : w ∈ H) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt T y i ℓ e) (hs : e.msg.slot = s + 1) {CV : Set (Vote sp.n)}
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ k, T.SendOrAdmit w k v ∧ sp.ts s ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U ℓ.frame.F Hv ∧
        (Hv.root = sp.genesisRoot ∨
          ∃ k, T.AcceptAt w k Hv ∧ a₀ ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ)) :
    SA.CarryAt T U y i e s CV := by
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  obtain ⟨-, hys, hyj, -⟩ := SA.castAt_spec hr hy hc
  have hsi : sp.slot (T.time i) = s + 1 := by omega
  have hti : sp.ts s + 4 * sp.Δ ≤ T.time i := by
    have := (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) ((s + 1 : Nat) : Int)).2 (by rw [hsi])
    rwa [hts] at this
  have hrsy : ∀ k ≤ i, T.RestartAt y k → T.time k ≤ sp.ts s := by
    have hj' : SA.joined sp (T.post i) (T.time i) := by
      unfold SA.joined; rw [SA.restartTime_of_castAt hr hy hc]; exact hyj
    intro k hk hrk
    have := ((SA.joined_awake sp) FGP ro H U T hr y hy i ℓ hc.1 hj').2 k hk hrk
    rwa [hsi, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by push_cast; ring] at this
  have hdl : ∀ k ≤ i, ∀ τ, τ < sp.ts s + 2 * sp.Δ → T.deadline y k τ < sp.ts s + 3 * sp.Δ := by
    intro k hk τ hτ
    have h₁ := deadline_le (fun k' hk' hr' => hrsy k' (hk'.trans hk) hr') τ
    have h₂ := max_lt hτ (show sp.ts s < sp.ts s + 2 * sp.Δ by linarith)
    change T.deadline y k τ ≤ max τ (sp.ts s) + sp.Δ at h₁
    linarith
  obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hy i ℓ hc.1
  refine ⟨hr.awake_of_call y hy i ℓ hc.1, hyj, fun v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨-, -, Hv, hHv, hHvr, hFHv, hacc⟩ := hW v hv
    refine ⟨Hv, hHv, hHvr, fun X hX => ?_⟩
    rcases hacc with hg | ⟨kw, hkw, hkwa, hkwt⟩
    · left
      obtain rfl : Hv = G := hU.1 hHv hGU (hg.trans hGr.symm)
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hX with rfl | ⟨Q, -, hQ⟩
      · exact hGr
      · exact absurd (hQ.2.2.symm.trans hGp) (Option.some_ne_none _)
    obtain ⟨ky, hky, ⟨ℓk, hck, hcall⟩, hkyt⟩ := hsync.2 w hw kw Hv hkw hkwa
      (by linarith) y hy i ℓ hc.1 (by linarith [hdl i le_rfl _ hkwt]) hFHv
    have hkyt' : T.time ky < sp.ts s + 3 * sp.Δ := hkyt.trans (hdl ky hky _ hkwt)
    rcases frame_anc_accepted hr hy ky ℓk hck Hv
      ((SA.accept_new sp hr hy ⟨ℓk, hck, hcall⟩).1 ℓk hck) X hX with hg | ⟨k, hk, hkX⟩
    · exact Or.inl hg
    · exact Or.inr ⟨k, hkX, lt_of_le_of_lt (hr.time_mono hk) hkyt'⟩
  · obtain ⟨hvs, ⟨k, hsend, hk1, hk2⟩, -⟩ := hW v hv
    obtain ⟨k', hk'i, hkk', hp, hk'dl⟩ := hsync.1 w hw k v hsend (ha₀.trans hk1)
      (by linarith) y hy i ℓ hc.1 (by linarith [hdl i le_rfl _ hk2])
    have hk'lt : T.time k' < sp.ts s + 3 * sp.Δ := hk'dl.trans (hdl k' hk'i _ hk2)
    obtain ⟨ℓ', hc', -⟩ := id hp
    have hnr : ∀ r, k' + 1 ≤ r → r < i + 1 → ¬ T.RestartAt y r := by
      rintro r hr1 hr2 ⟨ℓr, hcr, hrr⟩
      obtain ⟨u, -, hu, -, hprev⟩ := hr.sleep_of_restart y hy r ℓr hcr hrr
      have h₁ := hprev k' (by omega) ℓ' hc'
      have h₂ := hrsy r (by omega) ⟨ℓr, hcr, hrr⟩
      linarith
    have hsk' : sp.slot (T.time k') = s :=
      SA.slot_of_mem sp s (hk1.trans hkk') (by rw [hts]; linarith)
    have hheld : ∀ u ∈ (T.state y (k' + 1)).pool s,
        SA.HeldBefore e.readPoint u (sp.ts s + 3 * sp.Δ) := by
      intro u hu
      have hus : u.slot = s := SA.state_pool_slot sp hr hy (k' + 1) s u hu
      obtain ⟨hpool, hstamp⟩ := readPoint_slot hr hy hc (σ := s) (by omega)
      have hu' := SA.pool_mono hr hy (show k' + 1 ≤ i + 1 by omega) hnr s hu
      refine ⟨by rw [hus, ← hpool]; exact hu', ?_⟩
      rw [← hstamp u hus]
      rcases SA.pool_origin hr hy (i + 1) u (by rw [hus]; exact hu') with
        ⟨k₁, hk₁, hsend₁, hst₁, -⟩ | ⟨k₁, hk₁, ℓ₁, hc₁, hr₁, hst₁, -⟩
      · rw [hst₁, etime_lt]
        by_cases hk₁k' : k₁ ≤ k'
        · exact lt_of_le_of_lt (hr.time_mono hk₁k') hk'lt
        · obtain ⟨ℓ₁, hc₁, ⟨e₁, he₁, rfl⟩ | ⟨-, hn₁, -⟩⟩ := hsend₁
          · have h := (cast_head_fcRoot hr hy ⟨hc₁, he₁⟩).2
            rw [hus] at h
            linarith
          · exact absurd (SA.pool_mono hr hy (show k' + 1 ≤ k₁ by omega)
              (fun r h₁ h₂ => hnr r h₁ (by omega)) _ (by rw [hus]; exact hu)) hn₁
      · rw [hst₁, etime_lt]
        have := hrsy k₁ (by omega) ⟨ℓ₁, hc₁, hr₁⟩
        linarith
    by_cases hv' : v ∈ (T.state y (k' + 1)).pool s
    · exact Or.inl (hheld v hv')
    · rcases SA.held_of_processAt hr hy hp (by rw [hvs, hsk']; omega) (by rw [hvs, hsk']) with
        h | ⟨a, ha, c, hc'', hac, hav, hcv⟩
      · rw [hvs] at h
        exact absurd h hv'
      · have ha' : a ∈ (T.state y (k' + 1)).pool s := by rw [← hvs]; exact ha
        have hc' : c ∈ (T.state y (k' + 1)).pool s := by rw [← hvs]; exact hc''
        refine Or.inr ⟨a, c, hac, ?_, ?_, hav, hcv, SA.state_pool_slot sp hr hy _ s a ha',
          SA.state_pool_slot sp hr hy _ s c hc', hheld a ha', hheld c hc'⟩
        · rintro rfl; exact hv' ha'
        · rintro rfl; exact hv' hc'

private theorem admitVote_fields (A : SA.SAState sp.n) (t : Time) (v : Vote sp.n) :
    (SA.admitVote sp A t v).blockStamp = A.blockStamp ∧
      (SA.admitVote sp A t v).restartTime = A.restartTime := by
  unfold SA.admitVote
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem optimistic_fields (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time) :
    (SA.optimisticConfirmation sp A Φ t).blockStamp = A.blockStamp ∧
      (SA.optimisticConfirmation sp A Φ t).restartTime = A.restartTime := by
  unfold SA.optimisticConfirmation SA.updateLatestConfirmed
  split
  · exact ⟨rfl, rfl⟩
  · split_ifs <;> exact ⟨rfl, rfl⟩

private theorem blockReceipt_blockStamp (A : SA.SAState sp.n) (t : Time) (B : SA.Blk sp.n FGP) :
    (SA.blockReceipt sp A t B).blockStamp =
      Function.update A.blockStamp B.root (SA.ETime.of t) := by
  unfold SA.blockReceipt
  generalize SA.blockVotes B = l
  suffices h : ∀ A' : SA.SAState sp.n,
      (l.foldl (fun A v => SA.admitVote sp A t v) A').blockStamp = A'.blockStamp from h _
  induction l with
  | nil => exact fun _ => rfl
  | cons v l ih => exact fun A' => (ih _).trans (admitVote_fields _ _ _).1

private theorem tryVote_readPoint (x : Fin sp.n) (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP)
    (t : Time) : ∀ e ∈ (SA.tryVote sp x A Φ t).2, e.readPoint.blockStamp = A.blockStamp := by
  unfold SA.tryVote
  dsimp only
  split_ifs <;> simp

private theorem onTick_readPoint (x : Fin sp.n) (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP)
    (t : Time) : ∀ e ∈ (SA.acOnTick sp x A Φ t).2, e.readPoint.blockStamp = A.blockStamp := by
  unfold SA.acOnTick
  dsimp only
  split_ifs
  all_goals first | exact tryVote_readPoint x A Φ t | simp

/-- The read point of an honest vote has the block stamps of the state before its call, except
for the block that an `on_block` call receives (main's private `SA.readPoint_blockStamp`). -/
private theorem readPoint_blockStamp (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)}
    {e : SA.Em sp FGP} (hc : SA.CastAt T y i ℓ e) {r : Nat}
    (hrB : ∀ B, ℓ.call = .block B → r ≠ B.root) :
    e.readPoint.blockStamp r = (T.state y i).blockStamp r := by
  obtain ⟨hc, he⟩ := hc
  have hΦ : FrameOK ℓ.frame := (SA.frameIn_of_callAt hr hy hc).1
  have hx := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at hx
  have he' : e ∈ ((SA.goldilocksSA sp FGP ro).step y (T.state y i) ℓ.frame (T.time i)
      ℓ.call).2 := by
    rw [hx]; exact he
  clear hx he
  generalize T.state y i = A at he' ⊢
  revert hrB he'
  cases ℓ.call with
  | tick => exact fun _ he' => by rw [onTick_readPoint y A _ _ e he']
  | proposal => intro _ he'; simp [ACInterface.step] at he'
  | toFG => intro _ he'; simp [ACInterface.step] at he'
  | message m =>
    intro _ he'
    rw [tryVote_readPoint y _ _ _ e he', (optimistic_fields _ _ _).1, (admitVote_fields _ _ _).1]
  | block B =>
    intro hrB he'
    rw [tryVote_readPoint y _ _ _ e he', (optimistic_fields _ _ _).1, blockReceipt_blockStamp,
      Function.update_of_ne (hrB B rfl)]
  | restart =>
    intro _ he'
    change e ∈ (SA.acRestart sp ro y A ℓ.frame (T.time i)).2 at he'
    rw [((SA.restart_state sp) FGP ro y A ℓ.frame (T.time i) hΦ (hr.time_nonneg i)).1] at he'
    simp at he'

/-- **Head-only relay to a voter, after the GST** (`hr4-boot-carry.md` §4, §7): a block `W`
above the voter's `Σ.F` that an honest writer accepted in `[a₀, t_s + 2Δ)`, under `Sync[a₀, b]`
with `t_s + 2Δ ≤ b`, is in the voter block tree of every honest vote of a slot `> s` (relayed to
the voter, joined at its vote, before `t_{s} + 3Δ`, at or before its vote freeze). -/
theorem relay_mem_voterBlockTree (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
    {a₀ b : Time} (hsync : SyncAC (SA.goldilocksSA sp FGP ro) H U a₀ b T) {w : Fin sp.n}
    (hw : w ∈ H) {kw : Nat} {W : SA.Blk sp.n FGP} (hkw : T.AcceptAt w kw W)
    (ha₀ : a₀ ≤ T.time kw) {s : Nat} (hkwt : T.time kw < sp.ts s + 2 * sp.Δ)
    (hb : sp.ts s + 2 * sp.Δ ≤ b) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP} (hc : SA.CastAt T y i ℓ e)
    (hs : s + 1 ≤ e.msg.slot) (hF : Anc U ℓ.frame.F W) :
    W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot := by
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨-, hys, hyj, -⟩ := SA.castAt_spec hr hy hc
  have hm : sp.ts ((e.msg.slot : Int) - 1) + 4 * sp.Δ = sp.ts e.msg.slot := by
    simp only [SAParams.ts]; ring
  have hti : sp.ts e.msg.slot ≤ T.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by rw [hys])
  have hsm : sp.ts s ≤ sp.ts ((e.msg.slot : Int) - 1) := (SA.ts_le_iff sp).2 (by omega)
  have hrsy : ∀ k ≤ i, T.RestartAt y k → T.time k ≤ sp.ts ((e.msg.slot : Int) - 1) := by
    have hj' : SA.joined sp (T.post i) (T.time i) := by
      unfold SA.joined; rw [SA.restartTime_of_castAt hr hy hc]; exact hyj
    intro k hk hrk
    have := ((SA.joined_awake sp) FGP ro H U T hr y hy i ℓ hc.1 hj').2 k hk hrk
    rwa [← hys] at this
  have hdl : ∀ k ≤ i, T.deadline y k (T.time kw) < sp.ts ((e.msg.slot : Int) - 1) + 3 * sp.Δ := by
    intro k hk
    have h₁ := deadline_le (fun k' hk' hr' => hrsy k' (hk'.trans hk) hr') (T.time kw)
    have h₂ := max_lt (show T.time kw < sp.ts ((e.msg.slot : Int) - 1) + 2 * sp.Δ by linarith)
      (show sp.ts ((e.msg.slot : Int) - 1) < sp.ts ((e.msg.slot : Int) - 1) + 2 * sp.Δ by
        linarith)
    change T.deadline y k (T.time kw) ≤ max (T.time kw) (sp.ts ((e.msg.slot : Int) - 1)) + sp.Δ
      at h₁
    linarith
  obtain ⟨ky, hky, hacc, hkyt⟩ := hsync.2 w hw kw W hkw ha₀ (by linarith) y hy i ℓ hc.1
    (by linarith [hdl i le_rfl]) hF
  have hkyt' : T.time ky < SA.freeze sp e.msg.slot := by
    have := hdl ky hky
    unfold SA.freeze
    linarith
  have hfz : SA.freeze sp e.msg.slot ≤ T.time i := by unfold SA.freeze; linarith
  have hWt := SA.mem_tree_of_acceptAt sp hr hy hacc hky hc.1 hF
  have hbs := SA.blockStamp_lt_of_acceptedBefore sp hr hy hc.1 hWt (Or.inr ⟨ky, hacc, hkyt'⟩)
    (fun k hk hrk => lt_of_le_of_lt (hrsy k hk hrk) (by unfold SA.freeze; linarith))
    (Or.inl hfz)
  have hne : ∀ B, ℓ.call = .block B → W.root ≠ B.root := by
    intro B₀ hcall hB
    have hB₀ := (SA.accept_new sp hr hy ⟨ℓ, hc.1, hcall⟩).1 ℓ hc.1
    obtain rfl : B₀ = W := hU.1 ((SA.frameIn_of_callAt hr hy hc.1).2 hB₀)
      ((SA.frameIn_of_callAt hr hy hc.1).2 hWt) hB.symm
    have heq := SA.accept_unique sp hr hy hacc ⟨ℓ, hc.1, hcall⟩
    rw [heq] at hkyt'
    linarith
  rw [← readPoint_blockStamp hr hy hc hne] at hbs
  exact ⟨hWt, Or.inl hbs⟩

/-- **What the writer of a fast lock did with its counted votes** (main's Sleepy
`result_writer` and `optimistic_writer`, for the selected block): each was admitted (or sent) by
the writer at a time in `[t_s, t_s + 2Δ)`, and its head extends the selected block and is genesis
or was accepted by the writer before `t_s + 2Δ`. -/
theorem fastLock_writer (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
    {x : Fin sp.n} (hx : x ∈ H) {i₀ s : Nat} {D : SA.Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt T x i₀ s D CV) :
    ∀ v ∈ CV, v.slot = s ∧
      (∃ k, T.SendOrAdmit x k v ∧ sp.ts s ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U D Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, T.AcceptAt x k Hv ∧ T.time k < sp.ts s + 2 * sp.Δ) := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  rcases hfl with ⟨ℓX, C, ⟨hcX, htick, -, -⟩, -, -, -, rfl⟩ | ⟨ℓx, A, hp, hsl, hsel, rfl⟩
  · have hΦXU : ℓX.frame.tree ⊆ U := (SA.frameIn_of_callAt hr hx hcX).2
    rintro v ⟨hvp, -, hvres, R, hR, hRr, hCR⟩
    have hvs : v.slot = s := SA.state_pool_slot sp hr hx i₀ s v hvp
    obtain ⟨hvst, hbst⟩ : (T.state x i₀).voteStamp v < SA.ETime.of (sp.ts s + 2 * sp.Δ) ∧
        (T.state x i₀).blockStamp v.head < SA.ETime.of (sp.ts s + 2 * sp.Δ) := by
      unfold SA.resolutionTime at hvres
      split at hvres
      · exact absurd hvres (by simp [SA.ETime.of])
      · split_ifs at hvres
        · exact absurd hvres (by simp [SA.ETime.of])
        · exact max_lt_iff.1 hvres
    refine ⟨hvs, ?_, R, hΦXU hR, hRr, Anc.mono hΦXU hCR, ?_⟩
    · rcases SA.pool_origin hr hx i₀ v (by rw [hvs]; exact hvp) with
        ⟨k, -, hsend, hst, hsl⟩ | ⟨k, -, ℓk, hck, -, hst, B, hB, hvB⟩
      · rw [hst, etime_lt] at hvst
        exact ⟨k, hsend, (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2
          (by rw [← hvs]; exact_mod_cast hsl), hvst⟩
      · exfalso
        rw [hst, etime_lt] at hvst
        have hBv := (SA.frame_validPayload sp hr hx hck B hB).1 v hvB
        have hBs := SA.frame_slot_le sp hr hx hck B hB
        have : ¬ ((s + 1 : Nat) : Int) ≤ sp.slot (T.time k) := fun h => by
          have := (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).2 h
          rw [hts] at this; linarith
        omega
    · rcases frame_anc_accepted hr hx i₀ ℓX hcX R hR R Relation.ReflTransGen.refl with
        hg | ⟨k, hk, hacc⟩
      · exact Or.inl hg
      · refine Or.inr ⟨k, hacc, not_le.1 fun hge => ?_⟩
        have hki : k < i₀ := by
          refine lt_of_le_of_ne hk ?_
          rintro rfl
          obtain ⟨ℓ', hc', hcall⟩ := hacc
          rw [Option.some.inj (hc'.2.symm.trans hcX.2), htick] at hcall
          cases hcall
        rw [← hRr] at hbst
        have h := (stamp_ge_of_accept hr hx hacc (SA.accept_ne_genesis sp hr hx hacc) i₀
          hki).trans_lt hbst
        rw [etime_lt] at h
        linarith
  · have hc := hp.1
    have hti : T.time i₀ < sp.ts (sp.slot (T.time i₀)) + 2 * sp.Δ := by
      unfold SA.optimisticSelect at hsel
      dsimp only at hsel
      split_ifs at hsel with h
      all_goals first
        | cases hsel
        | exact not_le.1 fun h' => h (Or.inr (Or.inr h'))
    rw [hsl] at hti
    have hΦU : ℓx.frame.tree ⊆ U := (SA.frameIn_of_callAt hr hx hc).2
    rintro v ⟨hvA, R, hR, hRr, hCR⟩
    have hv1 := SA.optimisticPoint_pool_post hr hx hp s hvA
    have hvs : v.slot = s := SA.state_pool_slot sp hr hx (i₀ + 1) s v hv1
    refine ⟨hvs, ?_, R, hΦU hR, hRr, Anc.mono hΦU hCR, ?_⟩
    · rcases SA.pool_origin hr hx (i₀ + 1) v (by rw [hvs]; exact hv1) with
        ⟨k, hk, hsend, -, hsl'⟩ | ⟨k, hk, ℓk, hck, -, -, B, hB, hvB⟩
      · exact ⟨k, hsend, (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2
          (by rw [← hvs]; exact_mod_cast hsl'), lt_of_le_of_lt (hr.time_mono (by omega)) hti⟩
      · exfalso
        have hBv := (SA.frame_validPayload sp hr hx hck B hB).1 v hvB
        have hBs := SA.frame_slot_le sp hr hx hck B hB
        have := SA.slot_mono sp (hr.time_nonneg k) (hr.time_mono (show k ≤ i₀ by omega))
        omega
    · rcases frame_anc_accepted hr hx i₀ ℓx hc R hR R Relation.ReflTransGen.refl with
        hg | ⟨k, hk, hacc⟩
      · exact Or.inl hg
      · exact Or.inr ⟨k, hacc, lt_of_le_of_lt (hr.time_mono hk) hti⟩

/-- **A fast lock counts a vote**: the fast test passes with half of the committee (`n ≥ 1`), the
optimistic test with three quarters, and each counted validator has a counted vote. -/
theorem fastLock_counted_nonempty {x : Fin sp.n} {i₀ s : Nat} {D : SA.Blk sp.n FGP}
    {CV : Set (Vote sp.n)} (hfl : SA.FastLockAt T x i₀ s D CV) : CV.Nonempty := by
  have hn := sp.toParams.hn
  have hn' : sp.n = sp.toParams.n := rfl
  rcases hfl with ⟨ℓX, C, -, -, -, hsel, rfl⟩ | ⟨ℓx, A, -, hsl, hsel, rfl⟩
  · obtain ⟨⟨-, hfast⟩, -⟩ := SA.deepest_mem hsel
    unfold SA.FastTest SA.confirmationScore at hfast
    dsimp only at hfast
    generalize hS : SA.supporters _ _ _ _ = S at hfast
    obtain ⟨i, hi⟩ := Set.nonempty_of_ncard_ne_zero (s := S) (by omega)
    rw [← hS] at hi
    obtain ⟨hi, v, ⟨hvp, hvres⟩, rfl, -, hv⟩ := hi
    exact ⟨v, hvp, hi, hvres, hv⟩
  · unfold SA.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    obtain ⟨⟨-, hq, -⟩, -⟩ := SA.deepest_mem hsel
    generalize hS : SA.optimisticVoters _ _ _ _ _ = S at hq
    obtain ⟨i, hi⟩ := Set.nonempty_of_ncard_ne_zero (s := S) (by omega)
    rw [← hS] at hi
    obtain ⟨v, hv, -, hvD⟩ := hi
    exact ⟨v, hsl ▸ hv, hvD⟩

end Node

end Consensus.Goldilocks.Healing

end
