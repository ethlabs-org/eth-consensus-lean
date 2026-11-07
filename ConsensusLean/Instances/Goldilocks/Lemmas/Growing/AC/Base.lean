module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Growing
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts

public section

/-! # Node-local AC facts at an honest cut

Retention suffices for these facts: each reads only the history of a node still honest at
the indicated cut. No assertion is made about that node after compromise.
-/

namespace Consensus.Goldilocks.SA.Growing

theorem joined_awake (sp : SAParams) : JoinedAwake sp := by
  intro FGP ro H U tr hr y i ℓ hy hc hj
  have hm := hr.time_mono
  have hpost : (tr.upTo (tr.time i)).post i = tr.post i := by
    rw [Trace.upTo_post]
  obtain ⟨ha, hb⟩ := SA.joined_awake sp FGP ro (H (tr.time i)) U
    (tr.upTo (tr.time i)) (hr.upTo (hr.time_nonneg i)) y hy i ℓ
    ((Trace.upTo_callAt tr).mpr ⟨le_rfl, hc⟩) (hpost.symm ▸ hj)
  exact ⟨fun u hu hi => (ha u hu hi).1, fun j hji hj => hb j hji
    ((ACTrace.upTo_restartAt (A := goldilocksSA sp FGP ro)).mpr ⟨hm hji, hj⟩)⟩

theorem joined_keeps_votes (sp : SAParams) : JoinedKeepsVotes sp := by
  intro FGP ro H U tr hr y i ℓ hy hc hj j hji hjr σ x hx
  have hm := hr.time_mono
  have hpost : (tr.upTo (tr.time i)).post i = tr.post i := by
    rw [Trace.upTo_post]
  have hs : (tr.upTo (tr.time i)).state y j = tr.state y j :=
    Trace.upTo_state tr y fun _ hk => hm (hk.le.trans hji)
  exact SA.joined_keeps_votes sp FGP ro (H (tr.time i)) U
    (tr.upTo (tr.time i)) (hr.upTo (hr.time_nonneg i)) y hy i ℓ
    ((Trace.upTo_callAt tr).mpr ⟨le_rfl, hc⟩) (hpost.symm ▸ hj) j hji
    ((ACTrace.upTo_restartAt (A := goldilocksSA sp FGP ro)).mpr ⟨hm hji, hjr⟩)
    σ x (hs.symm ▸ hx)

theorem one_vote_per_slot (sp : SAParams) : OneVotePerSlot sp := by
  intro FGP ro H U tr hr y i j e e' hy hv hv' he
  have hd : 0 ≤ max (tr.time i) (tr.time j) :=
    (hr.time_nonneg i).trans (le_max_left _ _)
  exact SA.one_vote_per_slot sp FGP ro (H (max (tr.time i) (tr.time j))) U
    (tr.upTo (max (tr.time i) (tr.time j))) (hr.upTo hd) y hy i j e e'
    (upTo_voteAt.mpr ⟨le_max_left _ _, hv⟩)
    (upTo_voteAt.mpr ⟨le_max_right _ _, hv'⟩) he

end Consensus.Goldilocks.SA.Growing

namespace Consensus.Goldilocks.Growing

theorem localRun_reachable : LocalRunReachable := by
  intro P FGP A H U tr hr y i ℓ hy hc
  have hpost : (tr.upTo (tr.time i)).post i = tr.post i := by
    rw [Trace.upTo_post]
  have h := Goldilocks.localRun_reachable P FGP A (H (tr.time i)) U
    (tr.upTo (tr.time i)) (hr.upTo (hr.time_nonneg i)) y hy i ℓ
    ((Trace.upTo_callAt tr).mpr ⟨le_rfl, hc⟩)
  simpa only [hpost, Trace.upTo_time] using h

end Consensus.Goldilocks.Growing

end
