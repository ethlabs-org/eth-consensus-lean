module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Candidates.PreConfirmations.Statements
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.Rule
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.RelTrace

public section

/-! # The one release as a lock rule

The one release (`oneReleaseStage`, `Candidates/PreConfirmations/OneRelease`) is evidence-release's
target for the lock with its weight capped at `μ_r = ⌈n/2⌉`. Here:

* `oneReleaseKeep`: its keep premise at `Y`, that the evidence against `Y` lies in a set of fewer
  validators than `min(W(Y), μ_r)`;
* `oneReleaseStage_lawful`, `oneReleaseStage_fixes`: the stage is lawful with that premise and
  fixes its own choice for every lock (evidence-release's laws at the capped weight);
* `oneRelease_unlockRel`: the forgotten unlock of the stage satisfies the parent's unlock relation
  (`unlockRel_unlockWith`): every lock of a slot below `s` moves to an ancestor of its parent
  target (old-label provenance and moves-back; not retention);
* `oneReleaseScan`: the code's scan, the deepest `Y` with `Φ.F ⪯ Y ⪯ B` and
  `|evidence(Y)| < min(W(Y), μ_r)`, else `Φ.F`, is the stage's target from the parent's target of
  `B`: the opponents of `Y` are evidence against it (`opponents_subset_evidence`), so such a `Y`
  has `2·|opponents(Y)| < n` and lies at or above the parent's target. -/

namespace Consensus.Goldilocks.PreConfirmations

open SA EvidenceRelease

variable {sp : SAParams} {FGP : Type}

theorem oneReleaseStage_target (c : Unit) (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int)
    (w : WLock) (T : Blk sp.n FGP) :
    (oneReleaseStage sp).target c Φ V s w T =
      evidenceTarget sp Φ V s (capWeight (releaseMu sp) w) T :=
  rfl

theorem capWeight_weight (μ : Nat) (w : WLock) (r : Nat) :
    (capWeight μ w).weight r = min (w.weight r) μ :=
  rfl

variable (sp) in
/-- The one release's keep premise at `Y`: the evidence against `Y` lies in a set of fewer
validators than `min(W(Y), μ_r)`. -/
def oneReleaseKeep : UnlockStage.Keep sp wlockStore Unit :=
  fun _ Φ V s w Y => ∃ O : Set (Fin sp.n), evidence sp Φ V s Y ⊆ O ∧
    O.ncard < min (w.weight Y.root) (releaseMu sp)

theorem oneReleaseKeep_iff (c : Unit) (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (w : WLock)
    (Y : Blk sp.n FGP) :
    oneReleaseKeep sp c Φ V s w Y ↔ ∃ O : Set (Fin sp.n), evidence sp Φ V s Y ⊆ O ∧
      O.ncard < min (w.weight Y.root) (releaseMu sp) :=
  Iff.rfl

variable (sp) in
/-- **The one release is lawful.** -/
theorem oneReleaseStage_lawful : (oneReleaseStage sp).Lawful (oneReleaseKeep sp) where
  target_withBlock _ _ _ _ w r T := by
    rw [oneReleaseStage_target, oneReleaseStage_target, evidenceTarget_eq, evidenceTarget_eq,
      keepable_weight (show (capWeight (releaseMu sp) (wlockStore.withBlock w r)).weight =
        (capWeight (releaseMu sp) w).weight from rfl)]
  target_anc := by
    intro _ _ Φ V s w T hΦ hT
    rw [oneReleaseStage_target]
    exact evidenceTarget_anc hΦ V s _ hT
  keeps := by
    intro _ _ Φ V s w T Y hΦ hY hYT hk
    obtain ⟨O, hO, hOw⟩ := (oneReleaseKeep_iff _ Φ V s w Y).1 hk
    rw [oneReleaseStage_target]
    exact evidenceTarget_keeps hΦ V s _ hY hYT hO (by rw [capWeight_weight]; exact hOw)

variable (sp) in
/-- **The one release fixes its own choice**, for every lock. -/
theorem oneReleaseStage_fixes : (oneReleaseStage sp).Fixes fun _ _ => True where
  target_target := by
    intro _ _ Φ V s w T hΦ hT _
    simp only [oneReleaseStage_target]
    exact evidenceTarget_evidenceTarget hΦ V s _ hT

/-- **The old-label bound**: the forgotten unlock of the one release satisfies the parent's unlock
relation (provenance and moves-back of every lock; not retention). -/
theorem oneRelease_unlockRel {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (L : Set WLock) (t : Time)
    (s : Int) (V : View sp.n) :
    UnlockRel sp (WLock.lock '' L) Φ t s V
      (WLock.lock '' wlockStore.unlockWith sp (oneReleaseStage sp) () L Φ t s V) :=
  unlockRel_unlockWith wlockStore_lawful (oneReleaseStage_lawful sp) () hΦ L t s V

/-- The opponents of a block are evidence against it. -/
theorem opponents_subset_evidence (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int)
    (Y : Blk sp.n FGP) : opponents sp Φ V s Y ⊆ evidence sp Φ V s Y := by
  rintro i (hi | ⟨x, hx, hxi, hxs, H, hH, hHr, hc⟩)
  · exact Or.inl hi
  · exact Or.inr ⟨x, hx, hxi, hxs, H, hH, hHr, fun hYH => hc (Or.inr hYH)⟩

/-- **The one release reads the code's scan.** -/
theorem oneReleaseScan : OneReleaseScan sp FGP := by
  intro Φ hΦ V s w B hB
  set T := unlockTarget sp Φ V s B
  obtain ⟨hTt, hTB⟩ := unlockTarget_anc sp hΦ V s hB
  have hset : {Y | Y ∈ Φ.tree ∧ Φ.Anc Φ.F Y ∧ Φ.Anc Y B ∧
      (evidence sp Φ V s Y).ncard < min (w.weight Y.root) (releaseMu sp)} =
      keepable sp Φ V s (capWeight (releaseMu sp) w) T := by
    ext Y
    rw [mem_keepable, capWeight_weight]
    constructor
    · rintro ⟨hY, -, hYB, hev⟩
      refine ⟨hY, ?_, hev⟩
      -- `Y` passes the parent's test, so it is at or above the parent's target
      have hopp : 2 * (opponents sp Φ V s Y).ncard < sp.n := by
        have h1 := Set.ncard_le_ncard (opponents_subset_evidence Φ V s Y)
          (evidence sp Φ V s Y).toFinite
        have h2 : (evidence sp Φ V s Y).ncard < releaseMu sp :=
          lt_of_lt_of_le hev (min_le_right _ _)
        unfold releaseMu at h2
        omega
      set P := {B' | B' ∈ Φ.tree ∧ Φ.Anc B' B ∧ 2 * (opponents sp Φ V s B').ncard < sp.n}
      have hPt : P ⊆ Φ.tree := fun X hX => hX.1
      have hYP : Y ∈ P := ⟨hY, hYB, hopp⟩
      obtain ⟨D, hD⟩ := exists_deepest hΦ hPt ⟨Y, hYP⟩
      have hTD : T = D := by
        change (deepest Φ P).getD Φ.F = D
        rw [hD, Option.getD_some]
      rw [hTD]
      exact anc_deepest hΦ hPt
        (fun X hX C hC => anc_total hΦ.coherent hX.2.1 hC.2.1) hD Y hYP
    · rintro ⟨hY, hYT, hev⟩
      exact ⟨hY, hΦ.rooted.2 Y hY, hYT.trans hTB, hev⟩
  rw [hset]
  rfl

end Consensus.Goldilocks.PreConfirmations

end
