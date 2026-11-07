module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.RelTrace
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.FastWeight
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.UnlockViewOpponents
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.OpponentsHonest
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace

public section

/-! # Evidence-release: the outage keep at the AC level

The parent's outage retention (`unlockKeeps_of_voteCompat`) keeps a frame block `P` against the
opponents of `P`, which lie in the faulty validators and the late wakers `W` when every other
honest vote of the view's slot is *compatible* with `P`. Evidence-release's release counts as
evidence against `P` every support head that does not *extend* `P` (`evidence`), so its keep needs
the votes to extend `P`, and the lock's weight at `P` to exceed the evidence:

* **the evidence bound** (`evidence_subset_compl` on a view, `evidence_subset_of_votesExtend` at
  an honest call of an evidence-release run): when every honest vote of the view's slot by a
  validator outside `W`, cast before the call, extends `P`, the evidence against `P` in the call's
  view lies in `Hᶜ ∪ W`;
* **the keep for a weight bound** (`unlockWith_keeps_of_weight`, for every lawful stage whose keep
  premise is the evidence bound, as evidence-release's and any rule with its release; and
  `unlockW_keeps_slow` for `unlockW`): a stored lock on `B ⪰ P`, whose parent unlock target is at or
  above `P`, stays at or above `P` when the evidence against `P` lies in a set `O` with
  `|O| < W(P)`. It reads nothing of the lock but its weight, so it covers slow locks;
* **the outage keep** (`unlockW_keeps_outage`): the two together, with `|Hᶜ ∪ W| < W(P)`.

The vote-extension premise is the outage route's own invariant (its late-waker classification,
strengthened from compatible to extending); the weight bound for the armed slow lock is
`SavedCounts` (`card_le_slowWeight`). Nothing here is stated over a composite run. -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable {sp : SAParams} {FGP : Type}

/-! ### The evidence bound -/

/-- **The evidence against `P` is outside `Hn`** when no validator of `Hn` has two votes in the
view and every slot-`s` support vote of `Hn` has only heads extending `P`. -/
theorem evidence_subset_compl {Φ : Frm sp.n FGP} {V : View sp.n} {s : Int} {P : Blk sp.n FGP}
    {Hn : Set (Fin sp.n)}
    (hne : ∀ x ∈ V.votes, ∀ y ∈ V.votes, x.val ∈ Hn → y.val = x.val → x = y)
    (hext : ∀ x ∈ V.support, x.val ∈ Hn → (x.slot : Int) = s →
      ∀ H ∈ Φ.tree, H.root = x.head → Φ.Anc P H) :
    evidence sp Φ V s P ⊆ Hnᶜ := by
  rintro i (⟨x, hx, y, hy, hxy, rfl, hyi⟩ | ⟨x, hx, rfl, hs, H, hH, hr, hn⟩) hi
  · exact hxy (hne x hx y hy hi hyi).symm.symm
  · exact hn (hext x hx hi hs H hH hr)

/-- `try_vote` with the locks after the unlock given only adds to the pools. -/
theorem grows_tryVoteWith (self : Fin sp.n) (L : Set Lock) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : Grows A (tryVoteWith sp self L A Φ t).1 := by
  unfold tryVoteWith
  dsimp only
  split_ifs
  · exact Grows.refl _
  · exact Grows.refl _
  all_goals
    refine Grows.trans ?_ (Grows.of_pool_eq (optimistic_pool_eq _ _ _))
    refine Grows.trans (Grows.of_pool_eq ?_) (grows_admitVote _ _ _)
    rfl

variable {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
  {tr : ACTrace (evidenceReleaseSA sp FGP ro)} {proposer : Nat → Fin sp.n}

private theorem projTrace_state_succ {y : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (evidenceReleaseSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
    (projTrace tr).state y (i + 1) = (projTrace tr).post i := by
  have h : (projTrace tr).node i = y ∧ (projTrace tr).label i ≠ none :=
    ⟨hc.1, by simp [hc.2]⟩
  simp only [Trace.state]
  rw [ite_eq_left h]

/-- The view of a call lies in a set `S` holding the pools before and after the call and the
votes of the frame's blocks, and holds only votes of slot `slot(t) − 1`. -/
private theorem callView_facts {S : Set (Vote sp.n)} {self : Fin sp.n} {L : Set Lock}
    {A A' : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time} (c : (goldilocksSA sp FGP ro).Call)
    (hpost : (stepWith sp ro self L A Φ t c).1 = A')
    (hSpre : ∀ τ, ∀ v ∈ A.pool τ, v ∈ S) (hSpost : ∀ τ, ∀ v ∈ A'.pool τ, v ∈ S)
    (hStree : ∀ C ∈ Φ.tree, ∀ v, v ∈ blockVotes C ∨ v ∈ blockSupport C → v ∈ S)
    (hsl : ∀ τ, ∀ v ∈ A.pool τ, v.slot = τ) (hsl' : ∀ τ, ∀ v ∈ A'.pool τ, v.slot = τ)
    (hpay : ∀ C ∈ Φ.tree, validPayload C) :
    ((callView sp A Φ t c).votes ⊆ S ∧ (callView sp A Φ t c).support ⊆ S) ∧
      ∀ v ∈ (callView sp A Φ t c).votes, (v.slot : Int) = (sp.slot t : Int) - 1 := by
  have key : ∀ B : SAState sp.n, (∀ τ, ∀ v ∈ B.pool τ, v ∈ S) →
      (∀ τ, ∀ v ∈ B.pool τ, v.slot = τ) →
      ((mergedVoteView sp B Φ (sp.slot t)).votes ⊆ S ∧
        (mergedVoteView sp B Φ (sp.slot t)).support ⊆ S) ∧
      ∀ v ∈ (mergedVoteView sp B Φ (sp.slot t)).votes, (v.slot : Int) = (sp.slot t : Int) - 1 :=
    fun B hB hBs => ⟨mergedVoteView_subset hB hStree, mergedVoteView_votes_slot _ hBs hpay⟩
  have hgrow : ∀ B : SAState sp.n, Grows B A' →
      ((mergedVoteView sp B Φ (sp.slot t)).votes ⊆ S ∧
        (mergedVoteView sp B Φ (sp.slot t)).support ⊆ S) ∧
      ∀ v ∈ (mergedVoteView sp B Φ (sp.slot t)).votes, (v.slot : Int) = (sp.slot t : Int) - 1 :=
    fun B hB => key B (fun τ v hv => hSpost τ v (hB.mem hv)) (fun τ v hv => hsl' τ v (hB.mem hv))
  cases c with
  | tick => exact key A hSpre hsl
  | toFG => exact key A hSpre hsl
  | restart => exact key A hSpre hsl
  | proposal =>
    exact ⟨voteViewList_subset hSpre, voteViewList_votes_slot hsl⟩
  | message m =>
    exact hgrow _ (hpost ▸ grows_tryVoteWith self L _ Φ t)
  | block B =>
    exact hgrow _ (hpost ▸ grows_tryVoteWith self L _ Φ t)

/-- **The evidence bound at an honest call** (Lemma O, the vote half): at an honest call of a run
of the evidence-release SA, when every honest vote of slot `slot(t) − 1` by a validator outside
`W`, cast at an earlier cut, extends `P ∈ Φ.tree`, the evidence against `P` in the call's view lies
in `Hᶜ ∪ W`. -/
theorem evidence_subset_of_votesExtend (hrun : ACLocalRun (evidenceReleaseSA sp FGP ro) H U tr)
    (hobj : HonestObjects proposer (projTrace tr) H) {W : Set (Fin sp.n)} {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (evidenceReleaseSA sp FGP ro)} (hc : tr.CallAt y i ℓ)
    {P : Blk sp.n FGP} (hP : P ∈ ℓ.frame.tree)
    (hext : ∀ x ∈ H, x ∉ W → ∀ k < i, ∀ e, VoteAt (projTrace tr) x k e →
      (e.msg.slot : Int) = (sp.slot (tr.time i) : Int) - 1 → VoteExtends U e.msg P) :
    evidence sp ℓ.frame (callView sp (tr.state y i).ac ℓ.frame (tr.time i) (projCall ro ℓ.call))
      ((sp.slot (tr.time i) : Int) - 1) P ⊆ Hᶜ ∪ W := by
  have hU := localRunU_projTrace hrun
  have hcP : (projTrace tr).CallAt y i (projLabel ℓ) := projTrace_callAt.2 ⟨ℓ, hc, rfl⟩
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hU hy hcP
  have hpay := frame_validPayloadU sp hU hy hcP
  have hpost : (stepWith sp ro y (erOracle tr i) ((projTrace tr).state y i) ℓ.frame (tr.time i)
      (projCall ro ℓ.call)).1 = (projTrace tr).state y (i + 1) := by
    have he := hU.exec i (projLabel ℓ) (by simp [hc.2]) (hc.1 ▸ hy)
    rw [hc.1] at he
    rw [projTrace_state_succ hc]
    exact congrArg Prod.fst he
  -- the honest votes held across the call were cast at a cut up to `i`
  let S : Set (Vote sp.n) :=
    {v | v.val ∈ H → ∃ j < i + 1, ∃ e, VoteAt (projTrace tr) v.val j e ∧ e.msg = v}
  have hSpre : ∀ τ, ∀ v ∈ ((projTrace tr).state y i).pool τ, v ∈ S := fun τ v hv hvH => by
    obtain ⟨j, hj, e, he, hm⟩ := hobj.pool_vote y hy i τ v hv hvH
    exact ⟨j, by omega, e, he, hm⟩
  have hSpost : ∀ τ, ∀ v ∈ ((projTrace tr).state y (i + 1)).pool τ, v ∈ S :=
    fun τ v hv hvH => hobj.pool_vote y hy (i + 1) τ v hv hvH
  have hStree : ∀ C ∈ ℓ.frame.tree, ∀ v, v ∈ blockVotes C ∨ v ∈ blockSupport C → v ∈ S := by
    intro C hC v hv hvH
    have hvC : v ∈ blockVotes C := hv.elim id fun h => (hpay C hC).2 v h
    obtain ⟨j, hj, e, he, hm⟩ := hobj.carried_vote y hy i (projLabel ℓ) hcP C hC v hvC hvH
    exact ⟨j, by omega, e, he, hm⟩
  obtain ⟨⟨hVv, hVs⟩, hVsl⟩ := callView_facts (projCall ro ℓ.call) hpost hSpre hSpost hStree
    (state_pool_slotU sp hU hy i) (state_pool_slotU sp hU hy (i + 1)) hpay
  rw [projTrace_state] at hVv hVs hVsl
  have hcomp : (H \ W)ᶜ = Hᶜ ∪ W := by
    ext x; simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_union, not_and, not_not]; tauto
  rw [← hcomp]
  refine evidence_subset_compl (fun x hx x' hx' hxH hval => ?_) (fun x hx hxH hs H' hH' hr => ?_)
  · obtain ⟨j, -, e, he, hm⟩ := hVv hx hxH.1
    obtain ⟨j', -, e', he', hm'⟩ := hVv hx' (hval ▸ hxH.1)
    rw [hval] at he'
    have hsx := hVsl x hx
    have hsx' := hVsl x' hx'
    have h := (one_vote_per_slotU sp FGP ro H U (projTrace tr) hU) x.val hxH.1 j j' e e' he he'
      (by rw [hm, hm']; omega)
    rw [← hm, ← hm', h.2]
  · obtain ⟨j, hj, e, he, hm⟩ := hVs hx hxH.1
    have hji : j < i := by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
      · exact h
      · exfalso
        obtain ⟨ℓ', hc', he'⟩ := he
        have := (castAt_specU hU hxH.1 ⟨hc', he'⟩).2.1
        rw [hm] at this
        change x.slot = sp.slot (tr.time j) at this
        omega
    obtain ⟨Hd, hHd, hHdr, hPHd⟩ := hext x.val hxH.1 hxH.2 j hji e he (by rw [hm]; exact hs)
    rw [hm] at hHdr
    obtain rfl : H' = Hd := hU.coherent.1 (hΦU hH') hHd (hr.trans hHdr.symm)
    exact anc_tree_of_anc_U hU.coherent hΦ hΦU hP hPHd hH'

/-! ### The keep for a weight bound -/

/-- **The keep for a weight bound**, for every lawful stage on weighted locks whose keep premise
is implied by the evidence bound (evidence-release's release, and any rule that reuses it): a
stored live lock on `B` whose parent unlock target is at or above `P` stays at or above `P` when
the evidence against `P` lies in a set `O` with `|O| < W(P)`. -/
theorem unlockWith_keeps_of_weight {σ : Type} {E : UnlockStage sp wlockStore σ}
    {K : UnlockStage.Keep sp wlockStore σ} (hE : E.Lawful K) (c : σ)
    (hK : ∀ (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (w : WLock) (Y : Blk sp.n FGP),
      (∃ O : Set (Fin sp.n), evidence sp Φ V s Y ⊆ O ∧ O.ncard < w.weight Y.root) →
        K c Φ V s w Y)
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {L : Set WLock} {w : WLock} (hw : w ∈ L)
    {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) (hBr : B.root = w.lock.block) {t : Time}
    (hlive : w.lock.LiveAt sp t) {s : Int} {V : View sp.n} {P : Blk sp.n FGP} (hP : P ∈ Φ.tree)
    (hpar : Φ.Anc P (unlockTarget sp Φ V s (Φ.viableAncestor B))) {O : Set (Fin sp.n)}
    (hO : evidence sp Φ V s P ⊆ O) (hOw : O.ncard < w.weight P.root) :
    ∃ Z ∈ Φ.tree, Φ.Anc P Z ∧ wlockStore.withBlock w Z.root ∈ wlockStore.unlockWith sp E c L Φ t s
        V :=
  LockStore.unlockWith_keeps wlockStore_lawful hE c hΦ hw hB hBr hlive hP hpar
    (hK Φ V s w P ⟨O, hO, hOw⟩)

/-- **The release keeps a lock against evidence below its weight** (`unlockW`; the whole keep of a
rule with only slow locks and evidence-release's release). -/
theorem unlockW_keeps_slow {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {L : Set WLock} {w : WLock}
    (hw : w ∈ L) {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) (hBr : B.root = w.lock.block) {t : Time}
    (hlive : w.lock.LiveAt sp t) {s : Int} {V : View sp.n} {P : Blk sp.n FGP} (hP : P ∈ Φ.tree)
    (hpar : Φ.Anc P (unlockTarget sp Φ V s (Φ.viableAncestor B))) {O : Set (Fin sp.n)}
    (hO : evidence sp Φ V s P ⊆ O) (hOw : O.ncard < w.weight P.root) :
    ∃ Z ∈ Φ.tree, Φ.Anc P Z ∧ wlockStore.withBlock w Z.root ∈ unlockW sp L Φ t s V := by
  rw [unlockW_eq_unlockWith]
  exact unlockWith_keeps_of_weight (evidenceStage_lawful sp) ()
    (fun Φ V s w Y h => (evidenceKeep_iff _ Φ V s w Y).2 h) hΦ hw hB hBr hlive hP hpar hO hOw

/-! ### The outage keep -/

/-- **The outage keep at an honest call** (Lemma O at the AC level): at an honest call of a run of
the evidence-release SA, a stored lock of the call's input on `B`, live at the call, whose parent
unlock target is at or above `P ∈ Φ.tree`, stays at or above `P` in the call's unlock (the locks
of `erOracle`), when every honest vote of slot `slot(t) − 1` by a validator outside `W`, cast
before the call, extends `P`, and `|Hᶜ ∪ W| < W(P)`.

It still assumes the strict weight margin `|Hᶜ ∪ W| < W(P)` and the parent target's retention
(the parent unlock target at or above `P`); it combines the evidence bound and the keep, not the
full derivation of the arming, the count and the cohort. -/
theorem unlockW_keeps_outage (hrun : ACLocalRun (evidenceReleaseSA sp FGP ro) H U tr)
    (hobj : HonestObjects proposer (projTrace tr) H) {W : Set (Fin sp.n)} {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (evidenceReleaseSA sp FGP ro)} (hc : tr.CallAt y i ℓ)
    {P : Blk sp.n FGP} (hP : P ∈ ℓ.frame.tree)
    (hext : ∀ x ∈ H, x ∉ W → ∀ k < i, ∀ e, VoteAt (projTrace tr) x k e →
      (e.msg.slot : Int) = (sp.slot (tr.time i) : Int) - 1 → VoteExtends U e.msg P)
    {w : WLock}
    (hw : w ∈ (callInputW sp (tr.state y i) ℓ.frame (tr.time i) (projCall ro ℓ.call)).wlocks)
    {B : Blk sp.n FGP} (hB : B ∈ ℓ.frame.tree) (hBr : B.root = w.lock.block)
    (hlive : w.lock.LiveAt sp (tr.time i))
    (hpar : ℓ.frame.Anc P (unlockTarget sp ℓ.frame
      (callView sp (tr.state y i).ac ℓ.frame (tr.time i) (projCall ro ℓ.call))
      ((sp.slot (tr.time i) : Int) - 1) (ℓ.frame.viableAncestor B)))
    (hcount : (Hᶜ ∪ W).ncard < w.weight P.root) :
    ∃ Z ∈ ℓ.frame.tree, ℓ.frame.Anc P Z ∧ wlockStore.withBlock w Z.root ∈
      wlockStore.unlockWith sp (evidenceStage sp) ()
        (callInputW sp (tr.state y i) ℓ.frame (tr.time i) (projCall ro ℓ.call)).wlocks ℓ.frame
        (tr.time i) ((sp.slot (tr.time i) : Int) - 1)
        (callView sp (tr.state y i).ac ℓ.frame (tr.time i) (projCall ro ℓ.call)) := by
  have hU := localRunU_projTrace hrun
  have hΦ := (frameIn_of_callAtU hU hy (projTrace_callAt.2 ⟨ℓ, hc, rfl⟩)).1
  rw [← unlockW_eq_unlockWith]
  exact unlockW_keeps_slow hΦ hw hB hBr hlive hP hpar
    (evidence_subset_of_votesExtend hrun hobj hy hc hP hext) hcount

end Consensus.Goldilocks.EvidenceRelease

end
