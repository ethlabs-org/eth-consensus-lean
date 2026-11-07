module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.LateCertificate.Stage
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.Write

public section

/-! # Candidate `cert-recovery` as a lock rule

The candidate's unlock (`certUnlock`) is the parent's unlock, then evidence-release's release,
then the late-certificate stage, on the same call: the lock-rule interface's unlock of the
composite stage `certStage = evidenceStageC.comp lateStage`, with the arrival record as context.

* `evidenceStageC`: evidence-release's stage on locks with formation slots (it reads the weight);
  `evidenceStageC_lawful`, and `evidenceStageC_fixesBelow`: it fixes every block of the tree at
  or below its choice for a lock whose weight is antitone along the chain in the frame
  (`WeightAntitone`), since the evidence grows along the chain (`evidence_anc`) and so the
  keepable blocks below the choice are closed downwards;
* `certStage_lawful` (keep premise: both stages' premises) and `certStage_fixes` (for locks with
  antitone weight), so the step properties hold: (B) `certUnlock_backward`, no removal
  `certUnlock_image`, (S) `certUnlock_slot_ge`, (K) `certUnlock_keeps`, A0.4 (c)
  `certUnlock_movesBack`, A0.4 (d) `certUnlock_idempotent` (for antitone weights);
* **against evidence-release**: forgetting the formation slots (`forgetA`), the first stage is
  `unlockW` (`image_unlockWith_evidenceStageC`); every lock of `certUnlock` is a lock of `unlockW`
  moved back (`certUnlock_backward_unlockW`); with no late certificate it is `unlockW`
  (`image_certUnlock_of_noCert`); and the writes with formation slots forget to evidence-release's
  (`image_addLocksWith_tagA`).

Written weights are antitone along the chain in the frame of the write
(`confirmationScore_antitone`, `optimisticVoters_antitone`); that they stay so in later frames is
a property of runs, which the idempotence takes as a hypothesis. -/

namespace Consensus.Goldilocks.LateCertificate

open SA EvidenceRelease

variable {sp : SAParams} {FGP : Type}

/-! ### Evidence-release's stage on locks with formation slots -/

variable (sp) in
/-- Evidence-release's stage, reading the weighted lock of a lock with formation slots. -/
noncomputable def evidenceStageC : UnlockStage sp clockStore Unit where
  target _ Φ V s c T := evidenceTarget sp Φ V s c.w T

theorem evidenceStageC_target (u : Unit) (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int)
    (c : CLock) (T : Blk sp.n FGP) :
    (evidenceStageC sp).target u Φ V s c T = evidenceTarget sp Φ V s c.w T := by
  rfl

variable (sp) in
/-- Evidence-release's keep premise, of the weighted lock. -/
def evidenceKeepC : UnlockStage.Keep sp clockStore Unit :=
  fun u Φ V s c Y => evidenceKeep sp u Φ V s c.w Y

theorem evidenceKeepC_iff (u : Unit) (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (c : CLock)
    (Y : Blk sp.n FGP) :
    evidenceKeepC sp u Φ V s c Y ↔
      ∃ O : Set (Fin sp.n), evidence sp Φ V s Y ⊆ O ∧ O.ncard < c.w.weight Y.root :=
  evidenceKeep_iff u Φ V s c.w Y

variable (sp) in
theorem evidenceStageC_lawful : (evidenceStageC sp).Lawful (evidenceKeepC sp) where
  target_withBlock u Φ V s c r T := by
    rw [evidenceStageC_target, evidenceStageC_target]
    exact (evidenceStage_lawful sp).target_withBlock u Φ V s c.w r T
  target_anc := by
    intro _ u Φ V s c T hΦ hT
    exact (evidenceStage_lawful sp).target_anc u V s c.w hΦ hT
  keeps := by
    intro _ u Φ V s c T Y hΦ hY hYT hk
    exact (evidenceStage_lawful sp).keeps u V s c.w hΦ hY hYT
      ((evidenceKeep_iff u Φ V s c.w Y).2 ((evidenceKeepC_iff u Φ V s c Y).1 hk))

/-- The evidence grows along the chain: a head that does not extend `Y` does not extend any
descendant of `Y`. -/
theorem evidence_anc {Φ : Frm sp.n FGP} (V : View sp.n) (s : Int) {Y D : Blk sp.n FGP}
    (hYD : Φ.Anc Y D) : evidence sp Φ V s Y ⊆ evidence sp Φ V s D := by
  rintro i (hi | ⟨x, hx, hxi, hs, H, hH, hHr, hn⟩)
  · exact Or.inl hi
  · exact Or.inr ⟨x, hx, hxi, hs, H, hH, hHr, fun hDH => hn (hYD.trans hDH)⟩

variable (sp) in
/-- The weight of a lock is antitone along the chains of the frame's tree. -/
def WeightAntitone (Φ : Frm sp.n FGP) (w : WLock) : Prop :=
  ∀ Y ∈ Φ.tree, ∀ D ∈ Φ.tree, Φ.Anc Y D → w.weight D.root ≤ w.weight Y.root

/-- **Evidence-release fixes every block at or below its choice**, for a lock whose weight is
antitone along the chain: such a block is keepable (less evidence, more weight). -/
theorem evidenceTarget_of_anc {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (V : View sp.n) (s : Int)
    {w : WLock} (hw : WeightAntitone sp Φ w) {T Y : Blk sp.n FGP} (hT : T ∈ Φ.tree)
    (hY : Y ∈ Φ.tree) (hYE : Φ.Anc Y (evidenceTarget sp Φ V s w T)) :
    evidenceTarget sp Φ V s w Y = Y := by
  rw [evidenceTarget_eq] at hYE
  rcases hd : deepest Φ (keepable sp Φ V s w T) with _ | D
  · rw [hd, Option.getD_none] at hYE
    obtain rfl : Y = Φ.F := Anc.antisymm hΦ.coherent hYE (hΦ.rooted.2 Y hY)
    have hempty : keepable sp Φ V s w T = ∅ := by
      by_contra hne
      obtain ⟨D, hD⟩ := exists_deepest hΦ (fun X hX => (mem_keepable.1 hX).1)
        (Set.nonempty_iff_ne_empty.2 hne)
      rw [hd] at hD
      cases hD
    rw [evidenceTarget_eq]
    rcases hd' : deepest Φ (keepable sp Φ V s w Φ.F) with _ | D'
    · rfl
    · obtain ⟨hD't, hD'F, hD'w⟩ := mem_keepable.1 (deepest_mem hd').1
      have : D' ∈ keepable sp Φ V s w T :=
        mem_keepable.2 ⟨hD't, hD'F.trans (hΦ.rooted.2 T hT), hD'w⟩
      rw [hempty] at this
      exact absurd this (Set.notMem_empty _)
  · rw [hd, Option.getD_some] at hYE
    obtain ⟨hDt, -, hDw⟩ := mem_keepable.1 (deepest_mem hd).1
    have hYk : Y ∈ keepable sp Φ V s w Y := by
      refine mem_keepable.2 ⟨hY, .refl, ?_⟩
      calc (evidence sp Φ V s Y).ncard ≤ (evidence sp Φ V s D).ncard :=
            Set.ncard_le_ncard (evidence_anc V s hYE) (Set.toFinite _)
        _ < w.weight D.root := hDw
        _ ≤ w.weight Y.root := hw Y hY D hDt hYE
    have hsub : keepable sp Φ V s w Y ⊆ Φ.tree := fun X hX => (mem_keepable.1 hX).1
    obtain ⟨D', hD'⟩ := exists_deepest hΦ hsub ⟨Y, hYk⟩
    rw [evidenceTarget_eq, hD', Option.getD_some]
    exact Anc.antisymm hΦ.coherent (mem_keepable.1 (deepest_mem hD').1).2.1
      (anc_deepest hΦ hsub
        (fun X hX C hC => anc_total hΦ.coherent (mem_keepable.1 hX).2.1 (mem_keepable.1 hC).2.1)
        hD' Y hYk)

variable (sp) in
/-- The locks with antitone weight, as a predicate for the fixed-point laws. -/
def antitoneLocks : UnlockStage.Pred sp clockStore :=
  fun Φ c => WeightAntitone sp Φ c.w

variable (sp) in
theorem evidenceStageC_fixesBelow : (evidenceStageC sp).FixesBelow (antitoneLocks sp) where
  target_of_anc := by
    intro _ u Φ V s c T Y hΦ hT hY hG hYE
    rw [evidenceStageC_target] at hYE ⊢
    exact evidenceTarget_of_anc hΦ V s hG hT hY hYE

/-! ### The composite -/

variable (sp) in
/-- The candidate's stage: evidence-release's release, then the late-certificate stage. -/
noncomputable def certStage : UnlockStage sp clockStore (Unit × CertCtx sp.n) :=
  (evidenceStageC sp).comp (lateStage sp)

variable (sp) in
/-- The candidate's keep premise: both stages'. -/
def certKeep : UnlockStage.Keep sp clockStore (Unit × CertCtx sp.n) :=
  UnlockStage.Keep.and (evidenceKeepC sp) (lateKeep sp)

variable (sp) in
/-- The candidate's predicate for the fixed point: an antitone weight. -/
def certGood : UnlockStage.Pred sp clockStore :=
  UnlockStage.Pred.and (antitoneLocks sp) fun _ _ => True

variable (sp) in
theorem certStage_lawful : (certStage sp).Lawful (certKeep sp) := by
  unfold certStage certKeep
  exact UnlockStage.comp_lawful (evidenceStageC_lawful sp) (lateStage_lawful sp)

variable (sp) in
theorem certStage_fixes : (certStage sp).Fixes (certGood sp) := by
  unfold certStage certGood
  exact UnlockStage.comp_fixes (evidenceStageC_lawful sp) (lateStage_lawful sp)
    (evidenceStageC_fixesBelow sp) (lateStage_fixes sp)

theorem certStage_target (ctx : CertCtx sp.n) (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int)
    (c : CLock) (T : Blk sp.n FGP) :
    (certStage sp).target ((), ctx) Φ V s c T =
      lateTarget sp ctx Φ c (evidenceTarget sp Φ V s c.w T) := by
  unfold certStage
  rw [UnlockStage.comp_target, lateStage_target, evidenceStageC_target]

variable (sp) in
/-- **The candidate's unlock**: the parent's unlock, then the release, then the late-certificate
stage, with the arrival record `ctx`. -/
noncomputable def certUnlock (ctx : CertCtx sp.n) (L : Set CLock) (Φ : Frm sp.n FGP) (t : Time)
    (s : Int) (V : View sp.n) : Set CLock :=
  clockStore.unlockWith sp (certStage sp) ((), ctx) L Φ t s V

theorem certUnlock_eq (ctx : CertCtx sp.n) (L : Set CLock) (Φ : Frm sp.n FGP) (t : Time)
    (s : Int) (V : View sp.n) :
    certUnlock sp ctx L Φ t s V = clockStore.unlockWith sp (certStage sp) ((), ctx) L Φ t s V := by
  rfl

/-! ### The step properties -/

/-- **(B)** against the parent's unlock of the forgotten locks. -/
theorem certUnlock_backward {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (ctx : CertCtx sp.n)
    (L : Set CLock) (t : Time) (s : Int) (V : View sp.n) :
    ∀ c' ∈ certUnlock sp ctx L Φ t s V, ∃ c ∈ L, (∃ r, c' = clockStore.withBlock c r) ∧
      ∃ l ∈ unlock sp (clockStore.lock '' L) Φ t s V, l.slot = c.w.lock.slot ∧
        l.fast = c.w.lock.fast ∧ l.expiry = c.w.lock.expiry ∧
        ∃ T ∈ Φ.tree, T.root = l.block ∧ ∃ Y ∈ Φ.tree, Y.root = c'.w.lock.block ∧
          Φ.Anc Y T :=
  LockStore.unlockWith_backward clockStore_lawful (certStage_lawful sp) ((), ctx) hΦ L t s V

/-- **No removal**: every live stored lock has an image, at an ancestor of its block. -/
theorem certUnlock_image {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (ctx : CertCtx sp.n)
    {L : Set CLock} {t : Time} (s : Int) (V : View sp.n) {c : CLock} (hc : c ∈ L)
    {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) (hBr : B.root = c.w.lock.block)
    (hlive : c.w.lock.LiveAt sp t) :
    ∃ Y ∈ Φ.tree, Φ.Anc Y B ∧ clockStore.withBlock c Y.root ∈ certUnlock sp ctx L Φ t s V :=
  LockStore.unlockWith_image clockStore_lawful (certStage_lawful sp) ((), ctx) hΦ s V hc hB hBr
    hlive

/-- **(S)**: a live lock of a slot at or above `s` keeps its place. -/
theorem certUnlock_slot_ge {ctx : CertCtx sp.n} {L : Set CLock} {Φ : Frm sp.n FGP} {t : Time}
    {s : Int} {V : View sp.n} {c : CLock} (hc : c ∈ clockStore.liveLocks sp L Φ t)
    (hs : s ≤ (c.w.lock.slot : Int)) {B : Blk sp.n FGP} (hB : B ∈ Φ.tree)
    (hBr : B.root = c.w.lock.block) : c ∈ certUnlock sp ctx L Φ t s V :=
  LockStore.unlockWith_slot_ge hc hs hB hBr

/-- **(K)**: a live lock whose parent target is at or above `Y` stays at or above `Y` when
the evidence and, for an eligible lock, each formation slot's late certificate against `Y` lie in
sets of fewer validators than its weight at `Y`. -/
theorem certUnlock_keeps {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (ctx : CertCtx sp.n)
    {L : Set CLock} {t : Time} {s : Int} {V : View sp.n} {c : CLock} (hc : c ∈ L)
    {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) (hBr : B.root = c.w.lock.block)
    (hlive : c.w.lock.LiveAt sp t) {Y : Blk sp.n FGP} (hY : Y ∈ Φ.tree)
    (hpar : Φ.Anc Y (unlockTarget sp Φ V s (Φ.viableAncestor B)))
    (hev : ∃ O : Set (Fin sp.n), evidence sp Φ V s Y ⊆ O ∧ O.ncard < c.w.weight Y.root)
    (hlate : lateKeep sp ctx Φ V s c Y) :
    ∃ Z ∈ Φ.tree, Φ.Anc Y Z ∧ clockStore.withBlock c Z.root ∈ certUnlock sp ctx L Φ t s V :=
  LockStore.unlockWith_keeps clockStore_lawful (certStage_lawful sp) ((), ctx) hΦ hc hB hBr hlive
    hY hpar (by
      unfold certKeep
      exact (UnlockStage.Keep.and_iff _ _ _ _ _ _ _ _).2
        ⟨(evidenceKeepC_iff () Φ V s c Y).2 hev, hlate⟩)

/-- **A0.4 (c)**: the forgotten locks only move back. -/
theorem certUnlock_movesBack {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (ctx : CertCtx sp.n)
    (L : Set CLock) (t : Time) (s : Int) (V : View sp.n) :
    MovesBack sp Φ (clockStore.lock '' L) (clockStore.lock '' certUnlock sp ctx L Φ t s V) :=
  LockStore.unlockWith_movesBack clockStore_lawful (certStage_lawful sp) ((), ctx) hΦ L t s V

/-- **A0.4 (d)**: for stored locks whose weights are antitone along the chains of the frame, the
candidate's unlocking is idempotent. -/
theorem certUnlock_idempotent {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (ctx : CertCtx sp.n)
    {L : Set CLock} (hL : ∀ c ∈ L, WeightAntitone sp Φ c.w) (t : Time) (s : Int)
    (V : View sp.n) :
    certUnlock sp ctx (certUnlock sp ctx L Φ t s V) Φ t s V = certUnlock sp ctx L Φ t s V :=
  LockStore.unlockWith_idempotent clockStore_lawful (certStage_lawful sp) (certStage_fixes sp)
    ((), ctx) hΦ (fun c hc => by
      unfold certGood
      exact (UnlockStage.Pred.and_iff _ _ _ _).2 ⟨hL c hc, trivial⟩) t s V

/-! ### Against evidence-release -/

/-- Forgetting the formation slots, the first stage's unlock is evidence-release's `unlockW`. -/
theorem image_unlockWith_evidenceStageC {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (L : Set CLock)
    (t : Time) (s : Int) (V : View sp.n) :
    forgetA.toFun '' clockStore.unlockWith sp (evidenceStageC sp) () L Φ t s V =
      unlockW sp (forgetA.toFun '' L) Φ t s V := by
  rw [unlockW_eq_unlockWith]
  exact forgetA.image_unlockWith () () hΦ (fun V s c T _ => by
    rw [evidenceStage_target, evidenceStageC_target, forgetA_apply]) L t s V

/-- **(B) against evidence-release**: every lock of `certUnlock`, its formation slot forgotten,
is a lock of `unlockW` of the forgotten locks moved to an ancestor of its block, in the tree. -/
theorem certUnlock_backward_unlockW {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (ctx : CertCtx sp.n)
    (L : Set CLock) (t : Time) (s : Int) (V : View sp.n) :
    ∀ c' ∈ certUnlock sp ctx L Φ t s V, ∃ w' ∈ unlockW sp (forgetA.toFun '' L) Φ t s V,
      ∃ r, c'.w = wlockStore.withBlock w' r ∧ ∃ Y ∈ Φ.tree, Y.root = r ∧ ∃ Z ∈ Φ.tree,
        Z.root = w'.lock.block ∧ Φ.Anc Y Z := by
  intro c' hc'
  obtain ⟨c'', hc'', r, rfl, Y, hY, hYr, Z, hZ, hZr, hYZ⟩ :=
    LockStore.unlockWith_comp_backward clockStore_lawful (evidenceStageC_lawful sp)
      (lateStage_lawful sp) ((), ctx) hΦ L t s V c' hc'
  refine ⟨c''.w, ?_, r, rfl, Y, hY, hYr, Z, hZ, hZr, hYZ⟩
  rw [← image_unlockWith_evidenceStageC hΦ]
  exact ⟨c'', hc'', forgetA_apply c''⟩

/-- **With no late certificate the candidate is evidence-release**: forgetting the formation
slots, `certUnlock` is `unlockW` of the forgotten locks. -/
theorem image_certUnlock_of_noCert {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {ctx : CertCtx sp.n}
    (h : ∀ i : Int, ¬ HasCert sp ctx Φ i) (L : Set CLock) (t : Time) (s : Int) (V : View sp.n) :
    forgetA.toFun '' certUnlock sp ctx L Φ t s V = unlockW sp (forgetA.toFun '' L) Φ t s V := by
  rw [unlockW_eq_unlockWith, certUnlock_eq]
  refine forgetA.image_unlockWith ((), ctx) () hΦ (fun V s c T hT => ?_) L t s V
  rw [certStage_target, forgetA_apply, evidenceStage_target]
  exact (lateTarget_of_noCert hΦ (fun i _ _ => h i) (evidenceTarget_anc hΦ V s c.w hT).1).symm

/-- **The writes forget to evidence-release's**: writing weighted locks with their formation
slots, then forgetting the slots, is evidence-release's write. -/
theorem image_addLocksWith_tagA (L : Set CLock) (N : Set WLock) (Φ : Frm sp.n FGP)
    (t : Time) :
    forgetA.toFun '' clockStore.addLocksWith sp L (tagA sp '' N) Φ t =
      wlockStore.addLocksWith sp (forgetA.toFun '' L) N Φ t := by
  rw [forgetA.image_addLocksWith, Set.image_image]
  simp only [forgetA_tagA, Set.image_id']

end Consensus.Goldilocks.LateCertificate

end
