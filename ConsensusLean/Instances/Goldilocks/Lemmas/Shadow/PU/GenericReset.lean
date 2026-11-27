module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Proposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves

public section

/-! # Reset suppliers for shadow execution

The reset witness is the first high signing cut. Its minimality is by cut index,
so signatures imported by an earlier block suffice without a same-tick ordering argument.
-/

namespace Consensus.Goldilocks.Generic.Shadow

open Node

private theorem local_prefix {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
    {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}
    (h : Consensus.Goldilocks.Growing.LocalRun' proposer dg H sg tr ini)
    {d : Time} (hd : 0 ≤ d) : Node.LocalRun' proposer dg (H d) sg (tr.upTo d) ini := by
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
      phase_order := fun y hy y' hy' j j' t e e' he he' hjj hop => ?_
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
    exact ⟨j, e, RunTrace.upTo_inGroup' _ hm hid hg⟩
  · obtain ⟨hid, hc⟩ := (Trace.upTo_callAt _).mp hc
    rw [RunTrace.upTo_state_of_le hm hid]
    exact h.cutLaw y i c hc (anti hid hy)
  · obtain ⟨htd, he⟩ := (RunTrace.upTo_groupAt' _ hm).mp he
    exact h.wire y j t e (anti htd hy) he
  · obtain ⟨htd, hB⟩ := (RunTrace.upTo_groupAt' _ hm).mp hB
    exact h.proposerCredential y j t B (anti htd hy) hB
  · obtain ⟨htd, he⟩ := (RunTrace.upTo_groupAt' _ hm).mp he
    obtain ⟨-, he'⟩ := (RunTrace.upTo_groupAt' _ hm).mp he'
    exact h.phase_order y y' j j' t e e' (anti htd hy) (anti htd hy') he he' hjj
      (hop.imp_right fun hn hp => hn (RunTrace.upTo_ownPublicationAt' _ hm htd hp))
  · obtain ⟨htd, ht⟩ := (RunTrace.upTo_tickAt' _ hm).mp ht
    exact h.tick_public y j t (anti htd hy) ht
  · obtain ⟨htd, ht⟩ := (RunTrace.upTo_tickAt' _ hm).mp ht
    obtain ⟨-, ht'⟩ := (RunTrace.upTo_tickAt' _ hm).mp ht'
    exact h.tick_unique y j j' t (anti htd hy) ht ht'
  · obtain ⟨ha, htd⟩ := ha
    obtain ⟨j, hj⟩ := h.tick_of_awake y t (anti htd hy) ht hp ha
    exact ⟨j, (RunTrace.upTo_tickAt' _ hm).mpr ⟨htd, hj⟩⟩
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

private theorem exists_honest_att_of_lt' {P : Params} {ACP : Type} {acp₀ : ACP}
    {st : Store P ACP} (hr : st.Reachable' acp₀) {H : Set (Fin P.n)}
    (hq : Hᶜ.ncard < P.fg.q) {X : NodeBlock P ACP} (hX : X ∈ st.tree) :
    ∀ h, 1 ≤ h → h < (st.σ X.root).h →
      ∃ Y, st.Anc Y X ∧ ∃ a ∈ Y.fgPayload, a.val ∈ H ∧ a.h = h := by
  let hu := Store.finalitySpec_updateFinality' (P := P) (ACP := ACP)
  have hR := hr.reachableWith
  suffices key : (∀ v ∈ (st.σ X.root).prog ∪ (st.σ X.root).target,
      ∃ Y, st.Anc Y X ∧ ∃ a ∈ Y.fgPayload, a.val = v ∧ a.h = (st.σ X.root).h) ∧
      ∀ h, 1 ≤ h → h < (st.σ X.root).h →
        ∃ Y, st.Anc Y X ∧ ∃ a ∈ Y.fgPayload, a.val ∈ H ∧ a.h = h from key.2
  have hg := (Store.accepted_tree_with hu hR).2.2.2 X hX
  clear hX
  induction hg with
  | refl =>
    change (∀ v ∈ (st.σ P.genesisRoot).prog ∪ (st.σ P.genesisRoot).target, _) ∧
      ∀ h, 1 ≤ h → h < (st.σ P.genesisRoot).h → _
    rw [Store.σ_genesis_with hu hR]
    refine ⟨fun v hv => ?_, fun h h1 h2 => ?_⟩
    · rcases Finset.mem_union.1 hv with hv | hv <;>
        exact absurd hv (Finset.notMem_empty _)
    simp only [FG.ChainState.init] at h2
    omega
  | @tail W' W _ hpar ih =>
    obtain ⟨hW', hW, hp⟩ := hpar
    obtain ⟨-, -, -, ht⟩ := Store.step_σ_with hu hR hW hp
    have hanc : st.Anc W' W := .single ⟨hW', hW, hp⟩
    have old : ∀ v, v ∈ (st.σ W'.root).prog ∪ (st.σ W'.root).target ∨
        (∃ a ∈ W.fgView.atts, a.val = v ∧ a.h = (st.σ W'.root).h) →
        ∃ Y, st.Anc Y W ∧ ∃ a ∈ Y.fgPayload, a.val = v ∧ a.h = (st.σ W'.root).h := by
      rintro v (hv | ⟨a, ha, hav, hah⟩)
      · obtain ⟨Y, hY, hYa⟩ := ih.1 v hv
        exact ⟨Y, hY.trans hanc, hYa⟩
      · exact ⟨W, .refl, a, ha, hav, hah⟩
    rcases Healing.stateTransition_bits ht with ⟨he, hbits⟩ | ⟨he, hnil, S, hS, hSv⟩
    · refine ⟨fun v hv => he ▸ old v (hbits v hv), fun h h1 h2 => ?_⟩
      obtain ⟨Y, hY, hYa⟩ := ih.2 h h1 (he ▸ h2)
      exact ⟨Y, hY.trans hanc, hYa⟩
    · obtain ⟨S, hS, hSv⟩ : ∃ S : Finset (Fin P.n), P.fg.q ≤ S.card ∧ ∀ v ∈ S,
          v ∈ (st.σ W'.root).prog ∪ (st.σ W'.root).target ∨
            ∃ a ∈ W.fgView.atts, a.val = v ∧ a.h = (st.σ W'.root).h := ⟨S, hS, hSv⟩
      refine ⟨fun v hv => absurd hv (Finset.eq_empty_iff_forall_notMem.1 hnil v),
        fun h h1 h2 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 (he ▸ h2) with h2 | rfl
      · obtain ⟨Y, hY, hYa⟩ := ih.2 h h1 h2
        exact ⟨Y, hY.trans hanc, hYa⟩
      · obtain ⟨v, hvS, hvH⟩ : ∃ v ∈ S, v ∈ H := by
          by_contra hc
          have hsub : (↑S : Set (Fin P.n)) ⊆ Hᶜ := fun v hv h => hc ⟨v, hv, h⟩
          have hc' := Set.ncard_le_ncard hsub (Set.toFinite _)
          rw [Set.ncard_coe_finset] at hc'
          omega
        obtain ⟨Y, hY, a, ha, rfl, hah⟩ := old v (hSv v hvS)
        exact ⟨Y, hY, a, ha, hvH, hah⟩

/-- A high signing yields the first signing at the reset height in a shadow run. -/
theorem reset_of_height_advance_at_from {P : Params} {A : NodeAC P}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H : Time → Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}
    {ini : Fin P.n → A.State} {g : Time} {y : Fin P.n} {k : Nat} {att : FG.Att P.n}
    (hrun : Consensus.Goldilocks.Growing.LocalRun' proposer dg H sg tr ini)
    (hq : (H (max (Healing.cutZ P g) (tr.time k)))ᶜ.ncard < P.fg.q)
    (hyz : y ∈ H (max (Healing.cutZ P g) (tr.time k)))
    (hs : tr.SignAt y k att) (hh : Healing.Growing.HZ tr H g + 1 ≤ att.h) :
    ∃ a, Healing.Growing.IsReset tr H g a ∧ a ≤ tr.time k := by
  classical
  have hr := local_prefix hrun (hrun.time_nonneg k)
  have hy := hrun.antitone (le_max_right _ _) hyz
  have hs' := (RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩
  have hex₀ : ∃ j z a, z ∈ H (max (Healing.cutZ P g) (tr.time j)) ∧ tr.SignAt z j a ∧
      a.h = Healing.Growing.HZ tr H g + 1 ∧ tr.time j ≤ tr.time k := by
    rcases hh.lt_or_eq with hlt | heq
    · obtain ⟨src, hc⟩ := hs'
      have hR := Node.fg_reachable_at' hr hy k
      have hcl := hr.cutLaw y hy k _ hc
      rw [Node.cutStep'_attest_some] at hcl
      obtain ⟨E, hE, _, hEh⟩ := Store.exists_entry_of_createAtt_with
        Store.finalitySpec_updateFinality' hR.reachableWith hcl.1
      obtain ⟨Y, hYE, a, ha, haH, hah⟩ := exists_honest_att_of_lt' hR hq hE
        (Healing.Growing.HZ tr H g + 1) (by omega) (by omega)
      have hY : Y ∈ ((tr.upTo (tr.time k)).state y k).fg.tree := by
        by_cases he : Y = E
        · exact he ▸ hE
        · exact (Anc.mem hYE he).1
      rcases Coherence.tree_accepted' hr hy hY with rfl | ⟨i, hik, hA⟩
      · cases ha
      obtain ⟨j, hji, hj⟩ := hr.att_unforgeable y hy i a
        (Or.inr ⟨Y, ⟨true, hA⟩, ha⟩) (hrun.antitone (le_max_right _ _) haH)
      obtain ⟨hjt, hj⟩ := (RunTrace.upTo_signAt tr).mp hj
      exact ⟨j, a.val, a, hrun.antitone (max_le_max le_rfl hjt) haH, hj, hah, hjt⟩
    · exact ⟨k, y, att, hyz, hs, heq.symm, le_rfl⟩
  obtain ⟨j, z, att, hz, hs, hh, hjk⟩ := hex₀
  have hex : ∃ j z att, z ∈ H (max (Healing.cutZ P g) (tr.time j)) ∧ tr.SignAt z j att ∧
      att.h = Healing.Growing.HZ tr H g + 1 := ⟨j, z, att, hz, hs, hh⟩
  obtain ⟨v, c, hv, hc, hch⟩ := Nat.find_spec hex
  have hR : Healing.Growing.IsReset tr H g (tr.time (Nat.find hex)) :=
    ⟨⟨v, Nat.find hex, c, hv, hc, hch, rfl⟩, by
      intro v i c hv hc hch
      exact hrun.time_mono (Nat.find_min' hex ⟨v, c, hv, hc, hch⟩)⟩
  exact ⟨_, hR, (hR.2 z j att hz hs hh).trans hjk⟩

private theorem createAtt_record {n : Nat} {Λ Λ' : FG.Record} {v : Fin n}
    {σe : FG.ChainState n} {a : FG.Att n} (h : Λ.createAtt v σe = some (a, Λ')) :
    Λ' = Λ.recordAtt a := by
  unfold FG.Record.createAtt at h
  split at h
  · cases h
  · dsimp only at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

private theorem record_step {P : Params} {A : NodeAC P}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}
    {ini : Fin P.n → A.State} (hrun : Node.LocalRun' proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) (i : Nat) :
    (tr.state y (i + 1)).record = (tr.state y i).record ∨
      ∃ att, tr.SignAt y i att ∧
        (tr.state y (i + 1)).record = (tr.state y i).record.recordAtt att := by
  by_cases hc : ∃ c, tr.CallAt y i c
  · obtain ⟨c, hc⟩ := hc
    have hlaw := hrun.cutLaw y hy i c hc
    have hsucc := tr.state_succ_of_call hc
    cases c with
    | ac ℓ =>
      rw [Node.cutStep'_ac] at hlaw
      exact Or.inl (by rw [hsucc]; exact hlaw.2.2.2)
    | fg ℓ =>
      rcases ℓ with ⟨B, _ | _⟩ | a' | ⟨C, _ | a'⟩
      · rw [Node.cutStep'_block_false] at hlaw
        exact Or.inl (by rw [hsucc, hlaw.2])
      · rw [Node.cutStep'_block_true] at hlaw
        exact Or.inl (by rw [hsucc]; exact hlaw.2.2.2)
      · rw [Node.cutStep'_attestation] at hlaw
        exact Or.inl (by rw [hsucc]; exact hlaw.2.2)
      · rw [Node.cutStep'_attest_none] at hlaw
        exact Or.inl (by rw [hsucc, hlaw.2])
      · rw [Node.cutStep'_attest_some] at hlaw
        exact Or.inr ⟨a', ⟨C, hc⟩, hsucc ▸ createAtt_record hlaw.1⟩
  · exact Or.inl (by rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩])

private theorem record_lock_origin {P : Params} {A : NodeAC P}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}
    {ini : Fin P.n → A.State} (hrun : Node.LocalRun' proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) (h r : Nat) : ∀ i,
    (tr.state y i).record.lock h = some r →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.fin = some (h, r)
  | 0, hx => by
    rw [Trace.state, hrun.init y hy] at hx
    simp [Node.initWith, FG.Record.empty] at hx
  | i + 1, hx => by
    have ih := record_lock_origin hrun hy h r i
    rcases record_step hrun hy i with he | ⟨a', hs, he⟩ <;> rw [he] at hx
    · obtain ⟨k, hk, att, h'⟩ := ih hx
      exact ⟨k, by omega, att, h'⟩
    · dsimp only [FG.Record.recordAtt] at hx
      rcases hf : a'.fin with _ | ⟨p₁, p₂⟩
      · rw [hf] at hx
        dsimp only at hx
        obtain ⟨k, hk, att, h'⟩ := ih hx
        exact ⟨k, by omega, att, h'⟩
      · rw [hf] at hx
        dsimp only at hx
        rw [Function.update_apply] at hx
        split_ifs at hx with hh
        · cases Option.some.inj hx
          exact ⟨i, by omega, a', hs, by rw [hf, hh]⟩
        · obtain ⟨k, hk, att, h'⟩ := ih hx
          exact ⟨k, by omega, att, h'⟩

private theorem sent_origin {P : Params} {A : NodeAC P}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}
    {ini : Fin P.n → A.State} (hrun : Node.LocalRun' proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {b : FG.Content} : ∀ i,
    b ∈ (tr.state y i).record.sent → ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.content = b
  | 0, hb => by
    rw [Trace.state, hrun.init y hy] at hb
    simp [Node.initWith, FG.Record.empty] at hb
  | i + 1, hb => by
    rcases record_step hrun hy i with he | ⟨att, hs, he⟩ <;> rw [he] at hb
    · obtain ⟨k, hk, h⟩ := sent_origin hrun hy i hb
      exact ⟨k, by omega, h⟩
    · rcases List.mem_append.1 hb with hb | hb
      · obtain ⟨k, hk, h⟩ := sent_origin hrun hy i hb
        exact ⟨k, by omega, h⟩
      · exact ⟨i, by omega, att, hs, (List.mem_singleton.1 hb).symm⟩

private theorem sign_wellFormed {P : Params} {A : NodeAC P}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}
    {ini : Fin P.n → A.State} (hrun : Node.LocalRun' proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {k : Nat} {att : FG.Att P.n}
    (hs : tr.SignAt y k att) : att.WellFormed := by
  obtain ⟨src, hc⟩ := hs
  have hcl := hrun.cutLaw y hy k _ hc
  rw [Node.cutStep'_attest_some] at hcl
  obtain ⟨hcl, _⟩ := hcl
  have hr := (Node.fg_reachable_at' hrun hy k).reachableWith
  let hu := Store.finalitySpec_updateFinality' (P := P) (ACP := A.Payload)
  change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
    ((tr.state y k).fg.σ src.root).Th) = some (att, _) at hcl
  rcases hsrc : (tr.state y k).fg.blocks src.root with _ | X
  · have hg : ((tr.state y k).fg.σ src.root).Th = P.genesisRoot := by
      rw [Store.σ_of_blocks_none_with hu hr hsrc]; rfl
    rw [hg, Store.σ_genesis_with hu hr] at hcl
    exact Compose.createAtt_wellFormed le_rfl Nat.one_pos (by simp [FG.ChainState.init]) hcl
  · have hXr := Store.blocks_root_with hu hr hsrc
    have hX : X ∈ (tr.state y k).fg.tree := by
      change (tr.state y k).fg.blocks X.root = some X
      rw [hXr]; exact hsrc
    obtain ⟨⟨E, hE, hEr, -⟩, -⟩ := Store.entry_state_of_source_with hu hr X hX
    obtain ⟨c, -, -, -, hcs⟩ := Store.chain_state_of_chain_with hu hr E hE
    obtain ⟨h1, -, h3, -, -, -, -, h8, -⟩ := FG.chain_invariants P.fg _ _ hcs
    rw [hXr] at hEr
    rw [← hEr] at hcl
    exact Compose.createAtt_wellFormed h1 h3 (fun p hp => (h8 p hp).2.trans_lt h3) hcl

/-- A high source yields a reset even when the shadow client suppresses its signature. -/
theorem reset_of_high_source_at_from {P : Params} {A : NodeAC P}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H : Time → Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}
    {ini : Fin P.n → A.State} {g : Time} {y : Fin P.n} {k : Nat} {C : A.Blk}
    {s : Option (FG.Att P.n)}
    (hrun : Consensus.Goldilocks.Growing.LocalRun' proposer dg H sg tr ini)
    (hyz : y ∈ H (max (Healing.cutZ P g) (tr.time k)))
    (hq : (H (max (Healing.cutZ P g) (tr.time k)))ᶜ.ncard < P.fg.q)
    (hc : tr.CallAt y k (.fg (.attest C s)))
    (hh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state y k).fg.σ C.root).h) :
    ∃ a, Healing.Growing.IsReset tr H g a ∧ a ≤ tr.time k := by
  classical
  have hy := hrun.antitone (le_max_right _ _) hyz
  have hl := local_prefix hrun (hrun.time_nonneg k)
  have hst := Trace.upTo_state tr y (i := k) (fun q hq => hrun.time_mono hq.le)
  have hr := Node.fg_reachable_at' hl hy k
  rw [hst] at hr
  let hu := Store.finalitySpec_updateFinality' (P := P) (ACP := A.Payload)
  have he : ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).h =
      ((tr.state y k).fg.σ C.root).h := by
    rcases hC : (tr.state y k).fg.blocks C.root with _ | X
    · rw [Store.σ_of_blocks_none_with hu hr.reachableWith hC]
      exact congrArg FG.ChainState.h (Store.σ_genesis_with hu hr.reachableWith)
    · have hXr := Store.blocks_root_with hu hr.reachableWith hC
      have hX : X ∈ (tr.state y k).fg.tree := by
        change (tr.state y k).fg.blocks X.root = some X
        rw [hXr]; exact hC
      obtain ⟨⟨E, _, hEr, _, hEh, _⟩, _⟩ :=
        Store.entry_state_of_source_with hu hr.reachableWith X hX
      rw [← hXr, ← hEr]
      exact hEh
  by_cases hprev : ∃ j < k, ∃ att, tr.SignAt y j att ∧
      Healing.Growing.HZ tr H g + 1 ≤ att.h
  · obtain ⟨j, hj, att, hs, hh⟩ := hprev
    have hjt := hrun.time_mono hj.le
    have hjz := max_le_max (le_refl (Healing.cutZ P g)) hjt
    have hqj : (H (max (Healing.cutZ P g) (tr.time j)))ᶜ.ncard < P.fg.q :=
      lt_of_le_of_lt (Set.ncard_le_ncard (Set.compl_subset_compl.mpr
        (hrun.antitone hjz)) (Set.toFinite _)) hq
    obtain ⟨a, ha, haj⟩ := reset_of_height_advance_at_from hrun hqj
      (hrun.antitone hjz hyz) hs hh
    exact ⟨a, ha, haj.trans hjt⟩
  have hlock : (tr.state y k).record.lock ((tr.state y k).fg.σ C.root).h = none := by
    by_contra hn
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hn
    obtain ⟨j, hj, att, hs, hfin⟩ := record_lock_origin hl hy _ r k (by rwa [hst])
    have hw := (sign_wellFormed hl hy hs).2
      (((tr.state y k).fg.σ C.root).h, r) (by simp [hfin])
    exact hprev ⟨j, hj, att, ((RunTrace.upTo_signAt tr).mp hs).2, by omega⟩
  have hsent : ∀ b ∈ (tr.state y k).record.sent,
      b.1 ≠ ((tr.state y k).fg.σ C.root).h := by
    intro b hb hbh
    obtain ⟨j, hj, att, hs, heq⟩ := sent_origin hl hy k (by rwa [hst])
    have hah : att.h = b.1 := congrArg Prod.fst heq
    exact hprev ⟨j, hj, att, ((RunTrace.upTo_signAt tr).mp hs).2, by omega⟩
  have hany (τ : Bool) : (tr.state y k).record.sent.any (fun b =>
      b.1 = ((tr.state y k).fg.σ C.root).h ∧ (!τ ∨ b.2.1 =
        ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th)) = false := by
    apply List.any_eq_false.2
    intro b hb
    simp [hsent b hb]
  cases s with
  | some att =>
    have hcl := hrun.cutLaw y k _ hc hy
    rw [Node.cutStep'_attest_some] at hcl
    apply reset_of_height_advance_at_from hrun hq hyz ⟨C, hc⟩
    rw [(Healing.Store.createAtt_eq hcl.1).1, he]
    exact hh
  | none =>
    have hcl := hrun.cutLaw y k _ hc hy
    rw [Node.cutStep'_attest_none] at hcl
    obtain ⟨hcl, _⟩ := hcl
    exfalso
    change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
      ((tr.state y k).fg.σ C.root).Th) = none at hcl
    have hτ : ∃ τ, (tr.state y k).record.heightPair ((tr.state y k).fg.σ C.root).h
        ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th =
        some (((tr.state y k).fg.σ C.root).h,
          ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th, τ) := by
      unfold FG.Record.heightPair
      simp only [hlock, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
      split_ifs <;> exact ⟨_, rfl⟩
    obtain ⟨τ, hτ⟩ := hτ
    unfold FG.Record.createAtt at hcl
    rw [he, hτ] at hcl
    dsimp only at hcl
    rw [hany τ] at hcl
    simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hcl

/-- A high report yields a reset within the trace-level vote-latency deadline. -/
theorem reset_of_high_report_within_from {P : Params} {A : NodeAC P}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H : Time → Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}
    {ini : Fin P.n → A.State} {g D : Time} {y : Fin P.n} {i : Nat} {R : A.Blk}
    (hrun : Consensus.Goldilocks.Growing.LocalRun' proposer dg H sg tr ini)
    (hlat : VoteLatencyAt tr H D)
    (hyz : y ∈ H (max (Healing.cutZ P g) (tr.time i + D)))
    (hq : (H (max (Healing.cutZ P g) (tr.time i + D)))ᶜ.ncard < P.fg.q)
    (hR : ReportAt tr y i R)
    (hh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h) :
    ∃ a, Healing.Growing.IsReset tr H g a ∧ a ≤ tr.time i + D := by
  obtain ⟨k, -, hk, C, s, hc, hCh, -, -⟩ :=
    hlat.attests y i R hR (hrun.antitone (le_max_right _ _) hyz)
  have hmono : max (Healing.cutZ P g) (tr.time k) ≤ max (Healing.cutZ P g) (tr.time i + D) :=
    max_le_max le_rfl hk
  have hqk : (H (max (Healing.cutZ P g) (tr.time k)))ᶜ.ncard < P.fg.q :=
    lt_of_le_of_lt (Set.ncard_le_ncard
      (Set.compl_subset_compl.2 fun x hx => hrun.antitone hmono hx) (Set.toFinite _)) hq
  obtain ⟨a, ha, hat⟩ :=
    reset_of_high_source_at_from hrun (hrun.antitone hmono hyz) hqk hc (hh.trans hCh)
  exact ⟨a, ha, hat.trans hk⟩

end Consensus.Goldilocks.Generic.Shadow

end
