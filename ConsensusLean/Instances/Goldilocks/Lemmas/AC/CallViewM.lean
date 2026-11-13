module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.RelTrace
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WriteMode
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.UnlockViewOpponents
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.OpponentsHonest
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # The unlock view of a call at a write mode

* `grows_tryVoteWithM`: `try_vote` at a write mode, with the locks after the unlock given, only
  adds to the pools (the optimistic write keeps them);
* `callViewM_subset`: the unlock view of a call at a write mode (`callViewM`) lies in every set of
  votes holding the pools before and after the call and the votes of the frame's blocks, and
  holds only votes of slot `slot(t) − 1`. -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {wm : WriteMode}

/-- `try_vote` at mode `wm` with the locks after the unlock given only adds to the pools. -/
theorem grows_tryVoteWithM (wm : WriteMode) (self : Fin sp.n) (L : Set Lock) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : Grows A (tryVoteWithM sp wm self L A Φ t).1 := by
  unfold tryVoteWithM
  dsimp only
  split_ifs
  · exact Grows.refl _
  · exact Grows.refl _
  all_goals try exact Grows.of_pool_eq rfl
  all_goals
    refine Grows.trans ?_ (Grows.of_pool_eq
      (optimisticConfirmationM_keep SAState.pool optimistic_pool_eq wm _ _ _))
    refine Grows.trans ?_ (grows_admitVote _ _ _)
    exact Grows.of_pool_eq rfl

/-- The view of a call at mode `wm` lies in a set `S` holding the pools before and after the call
and the votes of the frame's blocks, and holds only votes of slot `slot(t) − 1`. -/
theorem callViewM_subset {S : Set (Vote sp.n)} {self : Fin sp.n} {L : Set Lock}
    {A A' : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time} (c : (goldilocksSA sp FGP ro).Call)
    (hpost : (stepWithM sp ro wm self L A Φ t c).1 = A')
    (hSpre : ∀ τ, ∀ v ∈ A.pool τ, v ∈ S) (hSpost : ∀ τ, ∀ v ∈ A'.pool τ, v ∈ S)
    (hStree : ∀ C ∈ Φ.tree, ∀ v, v ∈ blockVotes C ∨ v ∈ blockSupport C → v ∈ S)
    (hsl : ∀ τ, ∀ v ∈ A.pool τ, v.slot = τ) (hsl' : ∀ τ, ∀ v ∈ A'.pool τ, v.slot = τ)
    (hpay : ∀ C ∈ Φ.tree, validPayload C) :
    ((callViewM sp wm A Φ t c).votes ⊆ S ∧ (callViewM sp wm A Φ t c).support ⊆ S) ∧
      ∀ v ∈ (callViewM sp wm A Φ t c).votes, (v.slot : Int) = (sp.slot t : Int) - 1 := by
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
  | message v =>
    exact hgrow _ (hpost ▸ grows_tryVoteWithM wm self L _ Φ t)
  | block B =>
    exact hgrow _ (hpost ▸ grows_tryVoteWithM wm self L _ Φ t)

end Consensus.Goldilocks.SA

end
