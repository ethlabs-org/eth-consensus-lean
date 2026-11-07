module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.LateCertificate.RunInv
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.Handlers
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Trace

public section

/-! # The late-certificate SA: projection, unlock and the run invariant

The late-certificate SA (`Spec/WeightedLocks/LateCertificate`, `certRecoverySA`) is
evidence-release's state with an archive, and its handlers are evidence-release's stage-generic
handlers (`Spec/WeightedLocks/Actions`) at the candidate's stage `certStageW`, reading the archive.

* **The projection** (`acOnMessageC_er`, …, `acRestartC_er`): forgetting the archive, each handler
  is evidence-release's generic handler at `certStageW` with the archive as context, by `rfl`,
  and each emission is that handler's emission with the archive added (`acOnMessageC_emits`, …).
  With no late certificate the stage's unlock is `unlockW` (`unlockWith_certStageW_of_noCert`),
  so then a call is evidence-release's call (`acOnTickW_eq`, …, `Handlers`). The difference is the
  unlock only: a step correspondence, not an equivalence of runs.
* **The stage on weighted locks** is the composite stage `certStage` on locks with formation
  slots, through the map `tagW` that reads the first formation slot off the lock
  (`image_unlockWith_certStageW`). So its unlock only moves locks back
  (`unlockWith_certStageW_movesBack`), and it is idempotent for antitone weights
  (`unlockWith_certStageW_idempotent`).
* **The run invariant on the candidate's own runs**: every handler keeps evidence-release's weight
  invariant, for every stage (`EvidenceRelease.WeightInv`), so at every reachable state of the
  late-certificate SA every stored weight is antitone along the chain in the frame of the last call
  and every later frame (`weightAntitone_of_reachable_cert`), and the candidate's unlock there is
  idempotent with no further hypothesis (`unlockWith_certStageW_idempotent_of_reachable`).
* **The archive's obligation, as a named premise** (`HonestNotEarly`): no honest node receives an
  honest vote before its slot. Under it the archive's refusal of future-slot votes never applies
  to an honest vote (`archiveRecord_of_slot_le`), so its archived time is its first receipt. The
  SA's half is proved: every vote the SA emits is of its call's slot (`tryVoteE_emits_slot`), so
  an own vote is never refused. The run half (an honest vote is delivered after it is sent) is a
  node-level obligation, open here. -/

namespace Consensus.Goldilocks.LateCertificate

open SA EvidenceRelease

variable {sp : SAParams} {FGP : Type}

/-! ### The projection to evidence-release's state -/

/-- An emission with its archive forgotten. -/
def projC (e : EmC sp FGP) : EmW sp FGP := ⟨e.msg, e.readPoint.er, e.head⟩

theorem map_projC_liftEm (arr : Archive sp.n) (l : List (EmW sp FGP)) :
    (l.map (liftEm sp arr)).map projC = l := by
  rw [List.map_map]
  exact List.map_id'' (fun _ => rfl) l

theorem acOnMessageC_er (self : Fin sp.n) (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (v : Vote sp.n) :
    (acOnMessageC sp self X Φ t v).1.er = (acOnMessageE sp (certStageW sp)
      (certCtx (archiveRecord sp X.arch t v) X.er.ac) self X.er Φ t v).1 := by
  rfl

theorem acOnMessageC_emits (self : Fin sp.n) (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (v : Vote sp.n) :
    (acOnMessageC sp self X Φ t v).2.map projC = (acOnMessageE sp (certStageW sp)
      (certCtx (archiveRecord sp X.arch t v) X.er.ac) self X.er Φ t v).2 :=
  map_projC_liftEm _ _

theorem acOnBlockC_er (self : Fin sp.n) (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) :
    (acOnBlockC sp self X Φ t B).1.er = (acOnBlockE sp (certStageW sp)
      (certCtx (archiveAll sp X.arch t (blockVotes B)) X.er.ac) self X.er Φ t B).1 := by
  rfl

theorem acOnBlockC_emits (self : Fin sp.n) (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) :
    (acOnBlockC sp self X Φ t B).2.map projC = (acOnBlockE sp (certStageW sp)
      (certCtx (archiveAll sp X.arch t (blockVotes B)) X.er.ac) self X.er Φ t B).2 :=
  map_projC_liftEm _ _

theorem acOnTickC_er (self : Fin sp.n) (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acOnTickC sp self X Φ t).1.er =
      (acOnTickE sp (certStageW sp) (certCtx X.arch X.er.ac) self X.er Φ t).1 := by
  rfl

theorem acOnTickC_emits (self : Fin sp.n) (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acOnTickC sp self X Φ t).2.map projC =
      (acOnTickE sp (certStageW sp) (certCtx X.arch X.er.ac) self X.er Φ t).2 :=
  map_projC_liftEm _ _

theorem acProposalC_er (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    ((acProposalC sp X Φ t).1.er, (acProposalC sp X Φ t).2) =
      acProposalE sp (certStageW sp) (certCtx X.arch X.er.ac) X.er Φ t := by
  rfl

theorem acToFGC_er (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    ((acToFGC sp X Φ t).1.er, (acToFGC sp X Φ t).2) = acToFGW sp X.er Φ t := by
  rfl

theorem acRestartC_er (ro : ReplayOrder sp FGP) (self : Fin sp.n) (X : CState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    (acRestartC sp ro self X Φ t).1.er = (acRestartE sp (certStageW sp)
      ⟨Archive.arrival [], (t : WithBot Time)⟩ ro self X.er Φ t).1 := by
  rfl

theorem acRestartC_emits (ro : ReplayOrder sp FGP) (self : Fin sp.n) (X : CState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    (acRestartC sp ro self X Φ t).2.map projC = (acRestartE sp (certStageW sp)
      ⟨Archive.arrival [], (t : WithBot Time)⟩ ro self X.er Φ t).2 :=
  map_projC_liftEm _ _

/-! ### The stage on weighted locks is the composite stage on locks with formation slots -/

variable (sp) in
/-- Reading the first formation slot off a weighted lock. -/
def tagW : LockStore.Hom wlockStore clockStore where
  toFun w := ⟨w, firstSlot sp.k w.lock⟩
  lock_map _ := rfl
  map_withBlock _ _ := rfl

theorem tagW_apply (w : WLock) : (tagW sp).toFun w = ⟨w, firstSlot sp.k w.lock⟩ := by
  rfl

theorem tagW_injective : Function.Injective (tagW sp).toFun := fun _ _ h => by
  rw [tagW_apply, tagW_apply] at h
  exact congrArg CLock.w h

theorem certStageW_target (ctx : CertCtx sp.n) (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int)
    (w : WLock) (T : Blk sp.n FGP) :
    (certStageW sp).target ctx Φ V s w T =
      lateTarget sp ctx Φ (firstSlot sp.k w.lock) w (evidenceTarget sp Φ V s w T) := by
  rfl

/-- **The candidate's unlock on weighted locks** is `certUnlock` of the tagged locks. -/
theorem image_unlockWith_certStageW {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (ctx : CertCtx sp.n)
    (L : Set WLock) (t : Time) (s : Int) (V : View sp.n) :
    (tagW sp).toFun '' wlockStore.unlockWith sp (certStageW sp) ctx L Φ t s V =
      certUnlock sp ctx ((tagW sp).toFun '' L) Φ t s V := by
  rw [certUnlock_eq]
  exact (tagW sp).image_unlockWith ctx ((), ctx) hΦ (fun V s w T _ => by
    rw [certStage_target, tagW_apply, certStageW_target]) L t s V

/-- **A0.4 (c)**: the candidate's unlock on weighted locks moves the forgotten locks only back. -/
theorem unlockWith_certStageW_movesBack {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (ctx : CertCtx sp.n) (L : Set WLock) (t : Time) (s : Int) (V : View sp.n) :
    MovesBack sp Φ (WLock.lock '' L)
      (WLock.lock '' wlockStore.unlockWith sp (certStageW sp) ctx L Φ t s V) := by
  have hl : ∀ M : Set WLock, clockStore.lock '' ((tagW sp).toFun '' M) = WLock.lock '' M :=
    fun M => by
      rw [Set.image_image]
      simp only [tagW_apply]
  have h := certUnlock_movesBack hΦ ctx ((tagW sp).toFun '' L) t s V
  rwa [← image_unlockWith_certStageW hΦ, hl, hl] at h

/-- **A0.4 (d)** for stored weights antitone along the chains of the frame. -/
theorem unlockWith_certStageW_idempotent {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (ctx : CertCtx sp.n) {L : Set WLock} (hL : ∀ w ∈ L, WeightAntitone sp Φ w) (t : Time)
    (s : Int) (V : View sp.n) :
    wlockStore.unlockWith sp (certStageW sp) ctx
        (wlockStore.unlockWith sp (certStageW sp) ctx L Φ t s V) Φ t s V =
      wlockStore.unlockWith sp (certStageW sp) ctx L Φ t s V := by
  apply Set.image_injective.2 (tagW_injective (sp := sp))
  rw [image_unlockWith_certStageW hΦ, image_unlockWith_certStageW hΦ]
  refine certUnlock_idempotent hΦ ctx ?_ t s V
  rintro _ ⟨w, hw, rfl⟩
  rw [tagW_apply]
  exact hL w hw

/-- **With no late certificate the candidate's unlock is evidence-release's.** -/
theorem unlockWith_certStageW_of_noCert {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    {ctx : CertCtx sp.n} (h : ∀ i : Int, ¬ HasCert sp ctx Φ i) (L : Set WLock) (t : Time)
    (s : Int) (V : View sp.n) :
    wlockStore.unlockWith sp (certStageW sp) ctx L Φ t s V = unlockW sp L Φ t s V := by
  have hf : ∀ M : Set WLock, forgetA.toFun '' ((tagW sp).toFun '' M) = M := fun M => by
    rw [Set.image_image]
    simp only [tagW_apply, forgetA_apply, Set.image_id']
  have := image_certUnlock_of_noCert hΦ h ((tagW sp).toFun '' L) t s V
  rwa [← image_unlockWith_certStageW hΦ, hf, hf] at this

/-! ### The run invariant on the candidate's runs -/

variable {U : Set (Blk sp.n FGP)}

/-- **Evidence-release's weight invariant holds at every reachable state of the late-certificate
SA**, at the frame of its last call: the handlers are evidence-release's at another stage. -/
theorem weightInv_of_reachable_cert (hU : Coherent U) {ro : ReplayOrder sp FGP}
    {self : Fin sp.n} {X : (certRecoverySA sp FGP ro).State}
    {Φ : (certRecoverySA sp FGP ro).Frm} {t : Time}
    (h : (certRecoverySA sp FGP ro).ReachableAt self U X Φ t) :
    (FrameOK Φ ∧ Φ.tree ⊆ U) ∧ WeightInv sp U Φ X.er := by
  induction h with
  | init Φ _ hΦ => exact ⟨hΦ, weightInv_initial Φ _⟩
  | @step X Φ Φ' t t' c _ _ hc ih =>
    obtain ⟨⟨hΦ, hΦU⟩, hinv⟩ := ih
    have hF := callOK_F_anc hΦU hc
    obtain ⟨⟨hΦ', hΦ'U⟩, -⟩ := hc
    have h' := hinv.later hF
    refine ⟨⟨hΦ', hΦ'U⟩, ?_⟩
    cases c with
    | tick => exact weightInv_acOnTickE (certStageW sp) _ hU hΦ' hΦ'U h' self t'
    | proposal => exact weightInv_acProposalE (certStageW sp) _ h' t'
    | toFG => exact weightInv_acToFGW h' t'
    | message m => exact weightInv_acOnMessageE (certStageW sp) _ hΦ' hΦ'U h' self t' m
    | block B => exact weightInv_acOnBlockE (certStageW sp) _ hΦ' hΦ'U h' self t' B
    | restart => exact weightInv_acRestartE (certStageW sp) _ hΦ' hΦ'U h' ro self t'

/-- **Stored weights stay antitone along the chain on the candidate's runs**: at every reachable
state of the late-certificate SA inside a coherent `U`, in the frame of the last call and every
later frame of `U`. -/
theorem weightAntitone_of_reachable_cert (hU : Coherent U) {ro : ReplayOrder sp FGP}
    {self : Fin sp.n} {X : (certRecoverySA sp FGP ro).State}
    {Φ : (certRecoverySA sp FGP ro).Frm} {t : Time}
    (h : (certRecoverySA sp FGP ro).ReachableAt self U X Φ t) {Φ' : Frm sp.n FGP}
    (hΦ' : FrameOK Φ') (hΦ'U : Φ'.tree ⊆ U) (hF : Anc U Φ.F Φ'.F) :
    ∀ w ∈ X.er.wlocks, WeightAntitone sp Φ' w := fun w hw =>
  (weightAntitone_iff Φ' w).2 ((treeAntitone_iff Φ' _).1
    ((weightInv_of_reachable_cert hU h).2.treeAntitone hU hF hΦ' hΦ'U w hw))

/-- **Idempotence on the candidate's reachable states.** At a reachable state of the
late-certificate SA, the candidate's unlock of its stored locks in the frame of the last call, or
a later frame of `U`, is idempotent, for every arrival record. -/
theorem unlockWith_certStageW_idempotent_of_reachable (hU : Coherent U)
    {ro : ReplayOrder sp FGP} {self : Fin sp.n} {X : (certRecoverySA sp FGP ro).State}
    {Φ : (certRecoverySA sp FGP ro).Frm} {t₀ : Time}
    (h : (certRecoverySA sp FGP ro).ReachableAt self U X Φ t₀) {Φ' : Frm sp.n FGP}
    (hΦ' : FrameOK Φ') (hΦ'U : Φ'.tree ⊆ U) (hF : Anc U Φ.F Φ'.F) (ctx : CertCtx sp.n)
    (t : Time) (s : Int) (V : View sp.n) :
    wlockStore.unlockWith sp (certStageW sp) ctx
        (wlockStore.unlockWith sp (certStageW sp) ctx X.er.wlocks Φ' t s V) Φ' t s V =
      wlockStore.unlockWith sp (certStageW sp) ctx X.er.wlocks Φ' t s V :=
  unlockWith_certStageW_idempotent hΦ' ctx
    (weightAntitone_of_reachable_cert hU h hΦ' hΦ'U hF) t s V

/-! ### The archive's obligation -/

variable (sp) in
/-- **No honest vote is received before its slot** (a premise, not proved here): in an AC trace
of the late-certificate SA, every vote of an honest validator that an honest node receives, on its
own or in a block's payload, is of a slot that has begun at the receipt. -/
def HonestNotEarly (ro : ReplayOrder sp FGP) (tr : ACTrace (certRecoverySA sp FGP ro))
    (H : Set (Fin sp.n)) : Prop :=
  ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ → ∀ x : Vote sp.n, x.val ∈ H →
    (ℓ.call = .message x ∨ ∃ B, ℓ.call = .block B ∧ x ∈ blockVotes B) →
      x.slot ≤ sp.slot (tr.time i)

theorem honestNotEarly_iff (ro : ReplayOrder sp FGP) (tr : ACTrace (certRecoverySA sp FGP ro))
    (H : Set (Fin sp.n)) :
    HonestNotEarly sp ro tr H ↔ ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ → ∀ x : Vote sp.n, x.val ∈ H →
      (ℓ.call = .message x ∨ ∃ B, ℓ.call = .block B ∧ x ∈ blockVotes B) →
        x.slot ≤ sp.slot (tr.time i) :=
  Iff.rfl

/-- A receipt of a vote whose slot has begun is the first-receipt archive without the refusal. -/
theorem archiveRecord_of_slot_le (arr : Archive sp.n) {t : Time} {x : Vote sp.n}
    (h : x.slot ≤ sp.slot t) :
    archiveRecord sp arr t x =
      if x ∈ arr.map Prod.fst ∨
          2 ≤ (arr.filter fun p => p.1.val = x.val ∧ p.1.slot = x.slot).length then arr
      else arr ++ [(x, t)] := by
  unfold archiveRecord
  have hn : ¬ sp.slot t < x.slot := Nat.not_lt.2 h
  simp only [hn, false_or]

/-- **The SA's half**: every vote `try_vote` emits is of its call's slot, for every stage. -/
theorem tryVoteE_emits_slot {σ : Type} (E : UnlockStage sp wlockStore σ) (c : σ)
    (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    ∀ e ∈ (tryVoteE sp E c self X Φ t).2, e.msg.slot = sp.slot t := by
  unfold tryVoteE
  dsimp only
  split_ifs <;> simp

end Consensus.Goldilocks.LateCertificate

end
