module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockRule
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.Unlock

public section

/-! # Candidate `evidence-release` as a lock rule

The candidate's unlock is an instance of the lock-rule interface (`Lemmas/AC/LockRule`). The store
`wlockStore` and the stage `evidenceStage` are defined in `Spec/WeightedLocks/Evidence`; here:

* `wlockStore_lawful`: the weighted locks form a lawful store;
* `evidenceKeep`: the release's keep premise at `Y`, that the evidence against `Y` lies in a set of
  fewer validators than the lock's weight at `Y`;
* `evidenceStage_lawful`: the stage is lawful with that premise, so every step property of the
  interface holds for the candidate;
* `unlockW_eq_unlockWith`: `unlockW` is the interface's unlock of that stage (by definition).

Idempotence (A0.4 (d)), `unlockW_idempotent`, is the interface's `unlockWith_idempotent`. The
stage fixes its own choice (`evidenceTarget_evidenceTarget`): either its choice was the deepest
keepable block below `T`, so it is the deepest keepable block below itself, or it is `Φ.F` by the
fallback, and no block below `Φ.F` is keepable either. Together with the parent's absorption
(`SA.unlockTarget_eq_self_of_anc_unlockTarget`: a block at or below the parent's target is its
own parent target) this gives idempotence of `E ∘ unlock`. -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable {sp : SAParams} {FGP : Type}

/-- The store of weighted locks is lawful. -/
theorem wlockStore_lawful : wlockStore.Lawful where
  lock_withBlock _ _ := rfl
  withBlock_withBlock _ _ _ := rfl
  withBlock_self _ := rfl

variable (sp) in
/-- The release's keep premise at `Y`: the evidence against `Y` lies in a set of fewer validators
than the lock's weight at `Y`. -/
def evidenceKeep : UnlockStage.Keep sp wlockStore Unit :=
  fun _ Φ V s w Y => ∃ O : Set (Fin sp.n), evidence sp Φ V s Y ⊆ O ∧ O.ncard < w.weight Y.root

theorem evidenceKeep_iff (c : Unit) (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (w : WLock)
    (Y : Blk sp.n FGP) :
    evidenceKeep sp c Φ V s w Y ↔
      ∃ O : Set (Fin sp.n), evidence sp Φ V s Y ⊆ O ∧ O.ncard < w.weight Y.root :=
  Iff.rfl

theorem evidenceStage_target (c : Unit) (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (w : WLock)
    (T : Blk sp.n FGP) : (evidenceStage sp).target c Φ V s w T = evidenceTarget sp Φ V s w T := by
  rfl

/-- The evidence stage fixes its own choice. -/
theorem evidenceTarget_evidenceTarget {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (V : View sp.n)
    (s : Int) (w : WLock) {T : Blk sp.n FGP} (hT : T ∈ Φ.tree) :
    evidenceTarget sp Φ V s w (evidenceTarget sp Φ V s w T) = evidenceTarget sp Φ V s w T := by
  have hsub : ∀ {X}, Φ.Anc X T → keepable sp Φ V s w X ⊆ keepable sp Φ V s w T :=
    fun hXT Y hY => mem_keepable.2 ⟨(mem_keepable.1 hY).1, (mem_keepable.1 hY).2.1.trans hXT,
      (mem_keepable.1 hY).2.2⟩
  rw [evidenceTarget_eq, evidenceTarget_eq]
  rcases hd : deepest Φ (keepable sp Φ V s w T) with _ | D
  · rw [Option.getD_none]
    have hempty : keepable sp Φ V s w T = ∅ := by
      by_contra hne
      obtain ⟨D, hD⟩ := exists_deepest hΦ (fun X hX => (mem_keepable.1 hX).1)
        (Set.nonempty_iff_ne_empty.2 hne)
      rw [hd] at hD
      cases hD
    rcases hd' : deepest Φ (keepable sp Φ V s w Φ.F) with _ | D'
    · rfl
    · have := hsub (hΦ.rooted.2 T hT) (deepest_mem hd').1
      rw [hempty] at this
      exact absurd this (Set.notMem_empty _)
  · rw [Option.getD_some]
    obtain ⟨hDt, hDT, hDw⟩ := mem_keepable.1 (deepest_mem hd).1
    have hDS : D ∈ keepable sp Φ V s w D := mem_keepable.2 ⟨hDt, .refl, hDw⟩
    have hsubT : keepable sp Φ V s w D ⊆ Φ.tree := fun X hX => (mem_keepable.1 hX).1
    obtain ⟨D', hD'⟩ := exists_deepest hΦ hsubT ⟨D, hDS⟩
    rw [hD', Option.getD_some]
    have h1 := (mem_keepable.1 (deepest_mem hD').1).2.1
    have h2 := anc_deepest hΦ hsubT
      (fun X hX C hC => anc_total hΦ.coherent (mem_keepable.1 hX).2.1 (mem_keepable.1 hC).2.1)
      hD' D hDS
    exact Anc.antisymm hΦ.coherent h1 h2

variable (sp) in
/-- **The evidence stage is lawful.** -/
theorem evidenceStage_lawful : (evidenceStage sp).Lawful (evidenceKeep sp) where
  target_withBlock _ _ _ _ w r T := by
    rw [evidenceStage_target, evidenceStage_target, evidenceTarget_eq, evidenceTarget_eq,
      keepable_weight (show (wlockStore.withBlock w r).weight = w.weight from rfl)]
  target_anc := by
    intro _ _ Φ V s w T hΦ hT
    rw [evidenceStage_target]
    exact evidenceTarget_anc hΦ V s w hT
  keeps := by
    intro _ _ Φ V s w T Y hΦ hY hYT hk
    obtain ⟨O, hO, hOw⟩ := (evidenceKeep_iff _ Φ V s w Y).1 hk
    rw [evidenceStage_target]
    exact evidenceTarget_keeps hΦ V s w hY hYT hO hOw
  target_target := by
    intro _ _ Φ V s w T hΦ hT
    simp only [evidenceStage_target]
    exact evidenceTarget_evidenceTarget hΦ V s w hT

/-- **The candidate's unlock is an instance**: `unlockW` is the interface's unlock with the
evidence stage. -/
theorem unlockW_eq_unlockWith (L : Set WLock) (Φ : Frm sp.n FGP) (t : Time) (s : Int)
    (V : View sp.n) :
    unlockW sp L Φ t s V = wlockStore.unlockWith sp (evidenceStage sp) () L Φ t s V := by
  rfl

/-- **A0.4 (d) for the candidate**: `unlockW` is idempotent. -/
theorem unlockW_idempotent {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (L : Set WLock) (t : Time)
    (s : Int) (V : View sp.n) :
    unlockW sp (unlockW sp L Φ t s V) Φ t s V = unlockW sp L Φ t s V := by
  simp only [unlockW_eq_unlockWith]
  exact LockStore.unlockWith_idempotent wlockStore_lawful (evidenceStage_lawful sp) () hΦ L t s V

end Consensus.Goldilocks.EvidenceRelease

end
