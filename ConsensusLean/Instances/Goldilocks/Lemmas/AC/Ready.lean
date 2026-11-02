module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance

public section

/-! # Goldilocks SA: what an honest vote's call shows

The read point of an honest vote has the block stamps of the state its call leaves
(`readPoint_blockStamp_eq`), and a vote cast before `t_s + Δ` is ready: its frame holds a block
of its slot (`cast_ready`, the `vote_ready` branch of `try_vote`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}

private theorem bs_admitVote (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).blockStamp = A.blockStamp := by
  unfold admitVote; split_ifs <;> rfl

private theorem bs_optimistic (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).blockStamp = A.blockStamp := by
  unfold optimisticConfirmation updateLatestConfirmed; split
  · rfl
  · split_ifs <;> rfl

/-- The read point of an honest vote has the block stamps of the state its call leaves. -/
theorem readPoint_blockStamp_eq (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) :
    e.readPoint.blockStamp = (tr.post i).blockStamp := by
  rw [post_of_castAt hr hy hc, bs_optimistic, bs_admitVote]

/-- A block already held in an earlier frame has an early read-point stamp. The
stamp cases include restart replay; unique acceptance forbids a later overwrite. -/
theorem readPoint_blockStamp_lt_of_earlier_frame
    (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H)
    {a i : Nat} {ell₀ ell : ACLabel (goldilocksSA sp FGP ro)}
    (ha : tr.CallAt y a ell₀) {e : Em sp FGP} (hc : CastAt tr y i ell e)
    {Q : Blk sp.n FGP} (hQa : Q ∈ ell₀.frame.tree) (hQi : Q ∈ ell.frame.tree)
    (hat : tr.time a < freeze sp e.msg.slot)
    (hrs : ∀ r ≤ i, tr.RestartAt y r → tr.time r < freeze sp e.msg.slot) :
    e.readPoint.blockStamp Q.root < ETime.of (freeze sp e.msg.slot) := by
  rw [readPoint_blockStamp_eq hr hy hc]
  rcases stamp_cases sp hr hy i ell hc.1 Q hQi with h | ⟨k, -, hk, h⟩ | ⟨r, hri, hrst, h⟩
  · rw [h]; exact WithBot.bot_lt_coe _
  · have hka : k ≤ a := by
      by_contra hn
      exact (accept_new sp hr hy hk).2 a (by omega) ell₀ ha hQa
    rw [h]
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ((hr.time_mono hka).trans_lt hat))
  · rw [h]
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (hrs r hri hrst))

private theorem tryVote_ready (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    {e : Em sp FGP} (he : e ∈ (tryVote sp x A Φ t).2) (ht : t < sp.ts (sp.slot t) + sp.Δ) :
    voteReady sp Φ (sp.slot t) := by
  unfold tryVote at he
  dsimp only at he
  split_ifs at he with h1 h2
  · simp at he
  · simp at he
  all_goals
    by_contra hn
    exact h2 ⟨ht, Or.inr hn⟩

private theorem step_ready (self : Fin sp.n) (A : SAState sp.n) {Φ : Frm sp.n FGP} {t : Time}
    (hΦ : FrameOK Φ) (ht0 : 0 ≤ t) (c : (goldilocksSA sp FGP ro).Call) {e : Em sp FGP}
    (he : e ∈ ((goldilocksSA sp FGP ro).step self A Φ t c).2)
    (ht : t < sp.ts (sp.slot t) + sp.Δ) : voteReady sp Φ (sp.slot t) := by
  cases c with
  | tick =>
    change e ∈ (acOnTick sp self A Φ t).2 at he
    have htt : t = sp.ts (sp.slot t) + sp.Δ := by
      unfold acOnTick at he
      dsimp only at he
      split_ifs at he <;> first | assumption | simp at he
    linarith
  | message m => exact tryVote_ready self _ Φ t he ht
  | block B => exact tryVote_ready self _ Φ t he ht
  | proposal => simp [ACInterface.step] at he
  | toFG => simp [ACInterface.step] at he
  | restart =>
    change e ∈ (acRestart sp ro self A Φ t).2 at he
    rw [((restart_state sp) FGP ro self A Φ t hΦ ht0).1] at he
    simp at he

/-- **An early vote is ready**: an honest vote cast before `t_s + Δ` has a block of its slot in
its frame (`vote_ready`). -/
theorem cast_ready (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (ht : tr.time i < sp.ts e.msg.slot + sp.Δ) :
    voteReady sp ℓ.frame e.msg.slot := by
  obtain ⟨hcall, he⟩ := hc
  have hx := hr.exec i ℓ hcall.2 (hcall.1 ▸ hy)
  rw [hcall.1] at hx
  obtain ⟨hΦ, -⟩ := frameIn_of_callAt hr hy hcall
  have he' : e ∈ ((goldilocksSA sp FGP ro).step y (tr.state y i) ℓ.frame (tr.time i)
      ℓ.call).2 := by rw [hx]; exact he
  have hs := (castAt_spec hr hy ⟨hcall, he⟩).2.1
  rw [hs] at ht ⊢
  exact step_ready y _ hΦ (hr.time_nonneg i) ℓ.call he' ht

end Consensus.Goldilocks.SA

end
