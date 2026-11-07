module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo

public section

/-! # Retaining a generic node run at an honesty horizon -/

namespace Consensus.Goldilocks.Growing

/-- The generic node run laws hold statically for nodes retained at a nonnegative horizon. -/
theorem LocalRun.upTo {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
    {sg : A.Msg → Fin P.n} {tr : RunTrace A}
    (h : LocalRun proposer dg H sg tr) {d : Time} (hd : 0 ≤ d) :
    Node.LocalRun proposer dg (H d) sg (tr.upTo d) := by
  have hm := h.time_mono
  have anti : ∀ {t}, t ≤ d → H d ⊆ H t := fun ht => h.antitone ht
  refine
    { init := fun y hy => h.init y (anti hd hy)
      grouped := fun y hy i c hc => ?_
      cutLaw := fun y hy i c hc => ?_
      wire := fun y hy j t e he => ?_
      proposerCredential := fun y hy j t B hB => ?_
      time_nonneg := h.time_nonneg
      time_mono := hm
      finite := fun T => (h.finite T).subset fun i ⟨hl, hT⟩ => ⟨fun hn => hl (by
        simp [Trace.upTo_label, hn]), hT⟩
      phase_order := fun y hy y' hy' j j' t e e' he he' hjj => ?_
      tick_public := fun y hy j t ht => ?_
      tick_unique := fun y hy j j' t ht ht' => ?_
      tick_of_awake := fun y hy t ht hp ha => ?_
      awake_in_horizon := fun y hy t ha => ?_
      awake_of_call := fun y hy i hc => ?_
      restart_of_sleep := fun y hy i u hc hu hui hs hb => ?_
      restart_at_wake := fun y hy u v hu huv hs hv => ?_
      sleep_of_restart := fun y hy i hr => ?_
      block_unforgeable := fun y hy i B hB hp => ?_
      att_unforgeable := fun y hy i a ha hv => ?_
      msg_unforgeable := fun y hy i m hc hs => ?_ }
  · obtain ⟨hid, hc⟩ := (Trace.upTo_callAt _).mp hc
    obtain ⟨j, e, hg⟩ := h.grouped y i c hc (anti hid hy)
    exact ⟨j, e, RunTrace.upTo_inGroup hm hid hg⟩
  · obtain ⟨hid, hc⟩ := (Trace.upTo_callAt _).mp hc
    rw [RunTrace.upTo_state_of_le hm hid]
    exact h.cutLaw y i c hc (anti hid hy)
  · obtain ⟨htd, he⟩ := (RunTrace.upTo_groupAt hm).mp he
    exact h.wire y j t e (anti htd hy) he
  · obtain ⟨htd, hB⟩ := (RunTrace.upTo_groupAt hm).mp hB
    exact h.proposerCredential y j t B (anti htd hy) hB
  · obtain ⟨htd, he⟩ := (RunTrace.upTo_groupAt hm).mp he
    obtain ⟨-, he'⟩ := (RunTrace.upTo_groupAt hm).mp he'
    exact h.phase_order y y' j j' t e e' (anti htd hy) (anti htd hy') he he' hjj
  · obtain ⟨htd, ht⟩ := (RunTrace.upTo_tickAt hm).mp ht
    exact h.tick_public y j t (anti htd hy) ht
  · obtain ⟨htd, ht⟩ := (RunTrace.upTo_tickAt hm).mp ht
    obtain ⟨-, ht'⟩ := (RunTrace.upTo_tickAt hm).mp ht'
    exact h.tick_unique y j j' t (anti htd hy) ht ht'
  · obtain ⟨ha, htd⟩ := ha
    obtain ⟨j, hj⟩ := h.tick_of_awake y t (anti htd hy) ht hp ha
    exact ⟨j, (RunTrace.upTo_tickAt hm).mpr ⟨htd, hj⟩⟩
  · obtain ⟨ha, htd⟩ := ha
    exact RunTrace.upTo_inHorizon htd (h.awake_in_horizon y t (anti htd hy) ha)
  · obtain ⟨hid, hc⟩ := (RunTrace.upTo_isCall _).mp hc
    exact ⟨h.awake_of_call y i (anti hid hy) hc, hid⟩
  · obtain ⟨hid, hc⟩ := (RunTrace.upTo_isCall _).mp hc
    refine (RunTrace.upTo_restartAt _).mpr ⟨hid, h.restart_of_sleep y i u (anti hid hy) hc hu hui
      (fun ha => hs ⟨ha, hui.le.trans hid⟩) fun j hj hcj => hb j hj ?_⟩
    exact (RunTrace.upTo_isCall _).mpr ⟨(hm hj.le).trans hid, hcj⟩
  · obtain ⟨hv, hvd⟩ := hv
    obtain ⟨k, hk, huk, hkv⟩ := h.restart_at_wake y u v (anti hvd hy) hu huv
      (fun ha => hs ⟨ha, huv.le.trans hvd⟩) hv
    exact ⟨k, (RunTrace.upTo_restartAt _).mpr ⟨hkv.trans hvd, hk⟩, huk, hkv⟩
  · obtain ⟨hid, hr⟩ := (RunTrace.upTo_restartAt _).mp hr
    obtain ⟨u, hu, hui, hs, hb⟩ := h.sleep_of_restart y i (anti hid hy) hr
    refine ⟨u, hu, hui, fun ha => hs ha.1, fun j hj hcj => hb j hj ?_⟩
    exact ((RunTrace.upTo_isCall _).mp hcj).2
  · obtain ⟨hid, hB⟩ := (RunTrace.upTo_blockCallAt _).mp hB
    obtain ⟨j, hji, hj⟩ := h.block_unforgeable y i B (anti hid hy) hB (anti hid hp)
    exact ⟨j, hji, (RunTrace.upTo_ownBlockAt _).mpr ⟨(hm hji).trans hid, hj⟩⟩
  · have hid : tr.time i ≤ d := by
      rcases ha with ha | ⟨B, hB, _⟩
      exacts [((RunTrace.upTo_attCallAt _).mp ha).1, ((RunTrace.upTo_blockCallAt _).mp hB).1]
    have ha' : tr.AttCallAt y i a ∨ ∃ B, tr.BlockCallAt y i B ∧ a ∈ B.fgPayload := by
      rcases ha with ha | ⟨B, hB, haB⟩
      exacts [Or.inl ((RunTrace.upTo_attCallAt _).mp ha).2,
        Or.inr ⟨B, ((RunTrace.upTo_blockCallAt _).mp hB).2, haB⟩]
    obtain ⟨j, hji, hj⟩ := h.att_unforgeable y i a (anti hid hy) ha' (anti hid hv)
    exact ⟨j, hji, (RunTrace.upTo_signAt _).mpr ⟨(hm hji.le).trans hid, hj⟩⟩
  · obtain ⟨hid, hc⟩ := (RunTrace.upTo_msgCallAt _).mp hc
    obtain ⟨j, hji, hj⟩ := h.msg_unforgeable y i m (anti hid hy) hc (anti hid hs)
    exact ⟨j, hji, (RunTrace.upTo_emitAt _).mpr ⟨(hm hji.le).trans hid, hj⟩⟩

end Consensus.Goldilocks.Growing

end
