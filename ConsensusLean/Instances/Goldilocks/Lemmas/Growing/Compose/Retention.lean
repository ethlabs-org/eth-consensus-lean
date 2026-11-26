module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Const

public section

/-! # Retaining a generic node run on a prefix

The prefix through a nonnegative horizon `d` of a run under growing faults is a run under growing
faults for every antitone honest set `H'` below `H` on `[0, d]` (`LocalRun.upTo_of_subset`): every
law of the prefix is read at a time `≤ d`, where a node honest under `H'` is honest under `H`. At
`H' := H` the prefix keeps the run's growing faults; at the constant `H d` it is the static run
of the nodes retained at `d` (`LocalRun.upTo`). -/

namespace Consensus.Goldilocks.Growing

/-- **Retention of a growing-fault run at a smaller growing honest set.** -/
private theorem LocalRun.upTo_of_subset {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
    {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}
    (h : LocalRun proposer dg H sg tr ini) {d : Time} (hd : 0 ≤ d)
    {H' : Time → Set (Fin P.n)} (hanti : Antitone H') (hsub : ∀ t ≤ d, H' t ⊆ H t) :
    LocalRun proposer dg H' sg (tr.upTo d) ini := by
  have hm := h.time_mono
  refine
    { antitone := hanti
      init := fun y hy => h.init y (hsub 0 hd hy)
      grouped := fun y i c hc hy => ?_
      cutLaw := fun y i c hc hy => ?_
      wire := fun y j t e hy he => ?_
      proposerCredential := fun y j t B hy hB => ?_
      time_nonneg := h.time_nonneg
      time_mono := hm
      finite := fun T => (h.finite T).subset fun i ⟨hl, hT⟩ => ⟨fun hn => hl (by
        simp [Trace.upTo_label, hn]), hT⟩
      phase_order := fun y y' j j' t e e' hy hy' he he' hjj hop => ?_
      tick_public := fun y j t hy ht => ?_
      tick_unique := fun y j j' t hy ht ht' => ?_
      tick_of_awake := fun y t hy ht hp ha => ?_
      awake_in_horizon := fun y t hy ha => ?_
      awake_of_call := fun y i hy hc => ?_
      restart_of_sleep := fun y i u hy hc hu hui hs hb => ?_
      restart_at_wake := fun y u v hy hu huv hs hv => ?_
      sleep_of_restart := fun y i hy hr => ?_
      block_unforgeable := fun y i B hy hB hp => ?_
      att_unforgeable := fun y i a hy ha hv => ?_
      msg_unforgeable := fun y i m hy hc hs => ?_ }
  · obtain ⟨hid, hc⟩ := (Trace.upTo_callAt _).mp hc
    obtain ⟨j, e, hg⟩ := h.grouped y i c hc (hsub _ hid hy)
    exact ⟨j, e, RunTrace.upTo_inGroup hm hid hg⟩
  · obtain ⟨hid, hc⟩ := (Trace.upTo_callAt _).mp hc
    rw [RunTrace.upTo_state_of_le hm hid]
    exact h.cutLaw y i c hc (hsub _ hid hy)
  · obtain ⟨htd, he⟩ := (RunTrace.upTo_groupAt hm).mp he
    exact h.wire y j t e (hsub _ htd hy) he
  · obtain ⟨htd, hB⟩ := (RunTrace.upTo_groupAt hm).mp hB
    exact h.proposerCredential y j t B (hsub _ htd hy) hB
  · obtain ⟨htd, he⟩ := (RunTrace.upTo_groupAt hm).mp he
    obtain ⟨-, he'⟩ := (RunTrace.upTo_groupAt hm).mp he'
    exact h.phase_order y y' j j' t e e' (hsub _ htd hy) (hsub _ htd hy') he he' hjj
      (hop.imp_right fun hn hp => hn (RunTrace.upTo_ownPublicationAt hm htd hp))
  · obtain ⟨htd, ht⟩ := (RunTrace.upTo_tickAt hm).mp ht
    exact h.tick_public y j t (hsub _ htd hy) ht
  · obtain ⟨htd, ht⟩ := (RunTrace.upTo_tickAt hm).mp ht
    obtain ⟨-, ht'⟩ := (RunTrace.upTo_tickAt hm).mp ht'
    exact h.tick_unique y j j' t (hsub _ htd hy) ht ht'
  · obtain ⟨ha, htd⟩ := ha
    obtain ⟨j, hj⟩ := h.tick_of_awake y t (hsub _ htd hy) ht hp ha
    exact ⟨j, (RunTrace.upTo_tickAt hm).mpr ⟨htd, hj⟩⟩
  · obtain ⟨ha, htd⟩ := ha
    exact RunTrace.upTo_inHorizon htd (h.awake_in_horizon y t (hsub _ htd hy) ha)
  · obtain ⟨hid, hc⟩ := (RunTrace.upTo_isCall _).mp hc
    exact ⟨h.awake_of_call y i (hsub _ hid hy) hc, hid⟩
  · obtain ⟨hid, hc⟩ := (RunTrace.upTo_isCall _).mp hc
    refine (RunTrace.upTo_restartAt _).mpr ⟨hid, h.restart_of_sleep y i u (hsub _ hid hy) hc hu hui
      (fun ha => hs ⟨ha, hui.le.trans hid⟩) fun j hj hcj => hb j hj ?_⟩
    exact (RunTrace.upTo_isCall _).mpr ⟨(hm hj.le).trans hid, hcj⟩
  · obtain ⟨hv, hvd⟩ := hv
    obtain ⟨k, hk, huk, hkv⟩ := h.restart_at_wake y u v (hsub _ hvd hy) hu huv
      (fun ha => hs ⟨ha, huv.le.trans hvd⟩) hv
    exact ⟨k, (RunTrace.upTo_restartAt _).mpr ⟨hkv.trans hvd, hk⟩, huk, hkv⟩
  · obtain ⟨hid, hr⟩ := (RunTrace.upTo_restartAt _).mp hr
    obtain ⟨u, hu, hui, hs, hb⟩ := h.sleep_of_restart y i (hsub _ hid hy) hr
    refine ⟨u, hu, hui, fun ha => hs ha.1, fun j hj hcj => hb j hj ?_⟩
    exact ((RunTrace.upTo_isCall _).mp hcj).2
  · obtain ⟨hid, hB⟩ := (RunTrace.upTo_blockCallAt _).mp hB
    obtain ⟨j, hji, hj⟩ := h.block_unforgeable y i B (hsub _ hid hy) hB (hsub _ hid hp)
    exact ⟨j, hji, (RunTrace.upTo_ownBlockAt _).mpr ⟨(hm hji).trans hid, hj⟩⟩
  · have hid : tr.time i ≤ d := by
      rcases ha with ha | ⟨B, hB, _⟩
      exacts [((RunTrace.upTo_attCallAt _).mp ha).1, ((RunTrace.upTo_blockCallAt _).mp hB).1]
    have ha' : tr.AttCallAt y i a ∨ ∃ B, tr.BlockCallAt y i B ∧ a ∈ B.fgPayload := by
      rcases ha with ha | ⟨B, hB, haB⟩
      exacts [Or.inl ((RunTrace.upTo_attCallAt _).mp ha).2,
        Or.inr ⟨B, ((RunTrace.upTo_blockCallAt _).mp hB).2, haB⟩]
    obtain ⟨j, hji, hj⟩ := h.att_unforgeable y i a (hsub _ hid hy) ha' (hsub _ hid hv)
    exact ⟨j, hji, (RunTrace.upTo_signAt _).mpr ⟨(hm hji.le).trans hid, hj⟩⟩
  · obtain ⟨hid, hc⟩ := (RunTrace.upTo_msgCallAt _).mp hc
    obtain ⟨j, hji, hj⟩ := h.msg_unforgeable y i m (hsub _ hid hy) hc (hsub _ hid hs)
    exact ⟨j, hji, (RunTrace.upTo_emitAt _).mpr ⟨(hm hji.le).trans hid, hj⟩⟩

/-- The generic node run laws hold statically for nodes retained at a nonnegative horizon: the
constant instance of `LocalRun.upTo_of_subset` at `H d`. -/
theorem LocalRun.upTo {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
    {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}
    (h : LocalRun proposer dg H sg tr ini) {d : Time} (hd : 0 ≤ d) :
    Node.LocalRun proposer dg (H d) sg (tr.upTo d) ini :=
  LocalRun.const_iff.1 (h.upTo_of_subset hd antitone_const fun _ ht => h.antitone ht)

end Consensus.Goldilocks.Growing

end
