module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockKeepStep

public section

/-! # Goldilocks SA: a kept lock is live at the read point of a vote

consensus-lean#135 (WI-16), r14 s1 L1.2. At an honest cast at cut `i`, a stored lock `l` on `B`
that the call keeps (no expiry, `B` its own viable ancestor, `unlock` at the call's view
`unlockView` does not move it) is a lock of the vote's read point
(`mem_readPoint_locks_of_keep`), so `B` is a live lock block there
(`mem_readPoint_liveLockBlocks_of_keep`). The `try_vote` that emits the vote unlocks against the
merged view of its input, which is `unlockView` of the call. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}

/-- `try_vote` keeps in its read point a lock of its input that `unlock` at the input's merged
view does not move. -/
private theorem mem_tryVote_readPoint_of_keep {x : Fin sp.n} {P : SAState sp.n}
    {Φ : Frm sp.n FGP} {t : Time} {e : Em sp FGP} (he : e ∈ (tryVote sp x P Φ t).2) {l : Lock}
    {B : Blk sp.n FGP} (hl : l ∈ P.locks) (hk : sp.slot t ≤ l.slot + sp.k) (hB : B ∈ Φ.tree)
    (hBr : B.root = l.block) (hva : Φ.viableAncestor B = B)
    (hu : (sp.slot t : Int) - 1 ≤ l.slot ∨
      unlockTarget sp Φ (mergedVoteView sp P Φ (sp.slot t)) ((sp.slot t : Int) - 1) B = B) :
    l ∈ e.readPoint.locks := by
  rw [tryVote_readPoint_locks_eq he]
  split_ifs
  · exact mem_unlock_of_keep hl hk hB hBr hva hu
  · exact hl

/-- **A kept lock is a lock of the read point.** -/
theorem mem_readPoint_locks_of_keep (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) {l : Lock} {B : Blk sp.n FGP} (hl : l ∈ (tr.state y i).locks)
    (hk : sp.slot (tr.time i) ≤ l.slot + sp.k) (hB : B ∈ ℓ.frame.tree) (hBr : B.root = l.block)
    (hva : ℓ.frame.viableAncestor B = B)
    (hu : (sp.slot (tr.time i) : Int) - 1 ≤ l.slot ∨
      unlockTarget sp ℓ.frame (unlockView (tr.state y i) ℓ.frame (tr.time i) ℓ.call)
        ((sp.slot (tr.time i) : Int) - 1) B = B) :
    l ∈ e.readPoint.locks := by
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
    rw [hcall] at he' hu
    rw [unlockView_tick] at hu
    change e ∈ (acOnTick sp y _ ℓ.frame _).2 at he'
    unfold acOnTick at he'
    dsimp only at he'
    split_ifs at he' <;>
      first
      | exact mem_tryVote_readPoint_of_keep he' hl hk hB hBr hva hu
      | simp at he'
  | proposal =>
    rw [hcall] at he'
    simp [ACInterface.step] at he'
  | toFG =>
    rw [hcall] at he'
    simp [ACInterface.step] at he'
  | message m =>
    rw [hcall] at he' hu
    rw [unlockView_message] at hu
    have hl' : l ∈ (admitVote sp (tr.state y i) (tr.time i) m).locks := by
      rw [admitVote_locks_eq]
      exact hl
    exact mem_tryVote_readPoint_of_keep he'
      (mem_optimisticConfirmation_of_keep hl' hk hB hBr hva) hk hB hBr hva hu
  | block C =>
    rw [hcall] at he' hu
    rw [unlockView_block] at hu
    have hl' : l ∈ (blockReceipt sp (tr.state y i) (tr.time i) C).locks := by
      rw [blockReceipt_locks]
      exact hl
    exact mem_tryVote_readPoint_of_keep he'
      (mem_optimisticConfirmation_of_keep hl' hk hB hBr hva) hk hB hBr hva hu
  | restart =>
    rw [hcall] at he'
    change e ∈ (acRestart sp ro y _ ℓ.frame (tr.time i)).2 at he'
    rw [((restart_state sp) FGP ro y _ ℓ.frame (tr.time i) hΦ (hr.time_nonneg i)).1] at he'
    simp at he'

/-- **A kept lock's block is a live lock block of the read point.** -/
theorem mem_readPoint_liveLockBlocks_of_keep (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) {l : Lock} {B : Blk sp.n FGP} (hl : l ∈ (tr.state y i).locks)
    (hk : sp.slot (tr.time i) ≤ l.slot + sp.k) (hB : B ∈ ℓ.frame.tree) (hBr : B.root = l.block)
    (hva : ℓ.frame.viableAncestor B = B)
    (hu : (sp.slot (tr.time i) : Int) - 1 ≤ l.slot ∨
      unlockTarget sp ℓ.frame (unlockView (tr.state y i) ℓ.frame (tr.time i) ℓ.call)
        ((sp.slot (tr.time i) : Int) - 1) B = B) :
    B ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i) :=
  ⟨hB, l, mem_liveLocks_of_keep (mem_readPoint_locks_of_keep hr hy hc hl hk hB hBr hva hu) hk hB
    hBr hva, hBr.symm⟩

end Consensus.Goldilocks.SA

end
