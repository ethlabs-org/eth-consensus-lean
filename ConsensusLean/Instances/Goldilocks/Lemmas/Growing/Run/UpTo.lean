module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Trace.UpTo
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Premises
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Tree
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees

public section

/-! # Retention: the prefix of a growing-fault run is a static run

A validator honest at `d` was honest at every earlier time (`Growing.LocalRun.antitone`), so on
the prefix `tr.upTo d` (`Trace.upTo`: the cuts after `d` stutter, nobody is awake after `d`) the
validators of `H d` obey every law of a run with the constant honest set `H d`
(`Growing.GoldilocksRun.upTo`). The state of a node before a cut whose earlier cuts are all at
times `≤ d` is the same in the prefix (`Trace.upTo_state`); every call, event and wake of the
prefix is one of the run at a time `≤ d`. With `SyncOnAt.upTo` and `NoCollRun.upTo`, a static
statement whose conclusion is about nodes honest at `d`, read at cuts up to `d`, applies to a
growing-fault run unchanged.

The static sleepy and healthy premises are not retained: `SleepyRun (H d)` would charge every slot
point with the faults of `d` (the terminal budget), and `HealthyRun` is infinite. -/

namespace Consensus.Goldilocks

variable {P : Params}

namespace RunTrace

variable {A : NodeAC P} (tr : RunTrace A) {d : Time}

theorem upTo_isCall {y : Fin P.n} {i : Nat} :
    (tr.upTo d).IsCall y i ↔ tr.time i ≤ d ∧ tr.IsCall y i := by
  simp only [IsCall, Trace.upTo_callAt, exists_and_left]

theorem upTo_restartAt {y : Fin P.n} {k : Nat} :
    (tr.upTo d).RestartAt y k ↔ tr.time k ≤ d ∧ tr.RestartAt y k := by
  simp only [RestartAt, Trace.upTo_callAt]
  exact ⟨fun ⟨ℓ, ⟨h, hc⟩, hl⟩ => ⟨h, ℓ, hc, hl⟩, fun ⟨h, ℓ, hc, hl⟩ => ⟨ℓ, ⟨h, hc⟩, hl⟩⟩

theorem upTo_blockCallAt {y : Fin P.n} {k : Nat} {B : A.Blk} :
    (tr.upTo d).BlockCallAt y k B ↔ tr.time k ≤ d ∧ tr.BlockCallAt y k B := by
  simp only [BlockCallAt, Trace.upTo_callAt, exists_and_left]

theorem upTo_ownBlockAt {y : Fin P.n} {k : Nat} {B : A.Blk} :
    (tr.upTo d).OwnBlockAt y k B ↔ tr.time k ≤ d ∧ tr.OwnBlockAt y k B := by
  simp only [OwnBlockAt, upTo_blockCallAt, and_assoc]
  rfl

theorem upTo_signAt {y : Fin P.n} {k : Nat} {a : FG.Att P.n} :
    (tr.upTo d).SignAt y k a ↔ tr.time k ≤ d ∧ tr.SignAt y k a := by
  simp only [SignAt, Trace.upTo_callAt, exists_and_left]

theorem upTo_attCallAt {y : Fin P.n} {k : Nat} {a : FG.Att P.n} :
    (tr.upTo d).AttCallAt y k a ↔ tr.time k ≤ d ∧ tr.AttCallAt y k a := by
  simp only [AttCallAt, Trace.upTo_callAt]

theorem upTo_acceptAt {y : Fin P.n} {k : Nat} {B : A.Blk} :
    (tr.upTo d).AcceptAt y k B ↔ tr.time k ≤ d ∧ tr.AcceptAt y k B := by
  simp only [AcceptAt, Trace.upTo_callAt]

theorem upTo_emitAt {y : Fin P.n} {k : Nat} {m : A.Msg} :
    (tr.upTo d).EmitAt y k m ↔ tr.time k ≤ d ∧ tr.EmitAt y k m := by
  simp only [EmitAt, Trace.upTo_callAt]
  exact ⟨fun ⟨ℓ, ⟨h, hc⟩, he⟩ => ⟨h, ℓ, hc, he⟩, fun ⟨h, ℓ, hc, he⟩ => ⟨ℓ, ⟨h, hc⟩, he⟩⟩

theorem upTo_msgCallAt {y : Fin P.n} {k : Nat} {m : A.Msg} :
    (tr.upTo d).MsgCallAt y k m ↔ tr.time k ≤ d ∧ tr.MsgCallAt y k m := by
  simp only [MsgCallAt, Trace.upTo_callAt]
  exact ⟨fun ⟨ℓ, ⟨h, hc⟩, he⟩ => ⟨h, ℓ, hc, he⟩, fun ⟨h, ℓ, hc, he⟩ => ⟨ℓ, ⟨h, hc⟩, he⟩⟩

theorem upTo_processMsgAt {y : Fin P.n} {k : Nat} {m : A.Msg} :
    (tr.upTo d).ProcessMsgAt y k m ↔ tr.time k ≤ d ∧ tr.ProcessMsgAt y k m := by
  simp only [ProcessMsgAt, upTo_msgCallAt, upTo_emitAt, ← and_or_left]

theorem upTo_processAttAt {y : Fin P.n} {k : Nat} {a : FG.Att P.n} :
    (tr.upTo d).ProcessAttAt y k a ↔ tr.time k ≤ d ∧ tr.ProcessAttAt y k a := by
  simp only [ProcessAttAt, upTo_attCallAt, upTo_acceptAt]
  constructor
  · rintro (⟨h, hc⟩ | ⟨B, ⟨h, hc⟩, ha⟩)
    exacts [⟨h, Or.inl hc⟩, ⟨h, Or.inr ⟨B, hc, ha⟩⟩]
  · rintro ⟨h, hc | ⟨B, hc, ha⟩⟩
    exacts [Or.inl ⟨h, hc⟩, Or.inr ⟨B, ⟨h, hc⟩, ha⟩]

variable {tr}

/-- In a run whose cuts are in time order, the state before a cut at a time `≤ d` is the run's. -/
theorem upTo_state_of_le (hmono : Monotone tr.time) {y : Fin P.n} {i : Nat}
    (hi : tr.time i ≤ d) : (tr.upTo d).state y i = tr.state y i :=
  Trace.upTo_state tr y fun _ hk => (hmono hk.le).trans hi

theorem upTo_sendOrAdmitAt (hmono : Monotone tr.time) {x : Fin P.n} {i : Nat} {m : A.Msg} :
    (tr.upTo d).SendOrAdmitAt x i m ↔ tr.time i ≤ d ∧ tr.SendOrAdmitAt x i m := by
  simp only [SendOrAdmitAt, Trace.upTo_callAt]
  constructor
  · rintro ⟨ℓ, ⟨h, hc⟩, hm⟩
    rw [upTo_state_of_le hmono h] at hm
    exact ⟨h, ℓ, hc, hm⟩
  · rintro ⟨h, ℓ, hc, hm⟩
    rw [← upTo_state_of_le hmono h] at hm
    exact ⟨ℓ, ⟨h, hc⟩, hm⟩

theorem upTo_sendOrAdmitAttAt (hmono : Monotone tr.time) {x : Fin P.n} {i : Nat}
    {a : FG.Att P.n} :
    (tr.upTo d).SendOrAdmitAttAt x i a ↔ tr.time i ≤ d ∧ tr.SendOrAdmitAttAt x i a := by
  simp only [SendOrAdmitAttAt, upTo_signAt, Trace.upTo_callAt]
  constructor
  · rintro (⟨h, hs⟩ | ⟨ℓ, ⟨h, hc⟩, hn⟩)
    · exact ⟨h, Or.inl hs⟩
    · rw [upTo_state_of_le hmono h] at hn
      exact ⟨h, Or.inr ⟨ℓ, hc, hn⟩⟩
  · rintro ⟨h, hs | ⟨ℓ, hc, hn⟩⟩
    · exact Or.inl ⟨h, hs⟩
    · rw [← upTo_state_of_le hmono h] at hn
      exact Or.inr ⟨ℓ, ⟨h, hc⟩, hn⟩

/-- The latest wake before a cut at a time `≤ d` is the run's. -/
theorem upTo_lastWake (hmono : Monotone tr.time) (y : Fin P.n) :
    ∀ {k : Nat}, tr.time k ≤ d → (tr.upTo d).lastWake y k = tr.lastWake y k
  | 0, h => by
    unfold lastWake
    by_cases hr : tr.RestartAt y 0
    · have hr' : (tr.upTo d).RestartAt y 0 := (upTo_restartAt tr).mpr ⟨h, hr⟩
      simp only [hr, hr', ite_true]
      rfl
    · have hr' : ¬ (tr.upTo d).RestartAt y 0 := fun h' => hr ((upTo_restartAt tr).mp h').2
      simp only [hr, hr', ite_false]
  | k + 1, h => by
    have ih := upTo_lastWake hmono y (k := k) ((hmono (Nat.le_succ k)).trans h)
    unfold lastWake
    by_cases hr : tr.RestartAt y (k + 1)
    · have hr' : (tr.upTo d).RestartAt y (k + 1) := (upTo_restartAt tr).mpr ⟨h, hr⟩
      simp only [hr, hr', ite_true]
      rfl
    · have hr' : ¬ (tr.upTo d).RestartAt y (k + 1) := fun h' => hr ((upTo_restartAt tr).mp h').2
      simp only [hr, hr', ite_false]
      exact ih

theorem upTo_deadline (hmono : Monotone tr.time) {y : Fin P.n} {k : Nat} (h : tr.time k ≤ d)
    (τ Δ' : Time) : (tr.upTo d).deadline y k τ Δ' = tr.deadline y k τ Δ' := by
  simp only [deadline, upTo_lastWake hmono y h]

/-- A group of the prefix is a group of the run at a time `≤ d`, and conversely. -/
theorem upTo_groupAt (hmono : Monotone tr.time) {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {y : Fin P.n} {j : Nat} {t : Time}
    {e : Node.Event A} :
    (tr.upTo d).GroupAt proposer dg y j t e ↔ t ≤ d ∧ tr.GroupAt proposer dg y j t e := by
  constructor
  · rintro ⟨hne, hcuts, hev⟩
    have h0 := hcuts 0 (List.length_pos_of_ne_nil hne)
    have ht : tr.time j = t := h0.2.1
    have hl : (tr.upTo d).label j ≠ none := by
      change (tr.upTo d).label (j + 0) ≠ none
      rw [h0.2.2.2.2]
      exact Option.some_ne_none _
    have hjd : tr.time j ≤ d := by
      by_contra hc
      exact hl (by simp [RunTrace.upTo, Trace.upTo_label, hc])
    have hs := upTo_state_of_le (y := y) hmono hjd
    rw [hs] at hne hcuts hev
    refine ⟨ht ▸ hjd, hne, fun k hk => ?_, hev⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hcuts k hk
    have hkd : tr.time (j + k) ≤ d := by
      rw [show tr.time (j + k) = t from h2, ← ht]
      exact hjd
    exact ⟨h1, h2, h3, h4, by simpa [RunTrace.upTo, Trace.upTo_label, hkd] using h5⟩
  · rintro ⟨htd, hne, hcuts, hev⟩
    have h0 := hcuts 0 (List.length_pos_of_ne_nil hne)
    have ht : tr.time j = t := h0.2.1
    have hs := upTo_state_of_le (y := y) hmono (d := d) (ht ▸ htd)
    refine ⟨?_, fun k hk => ?_, ?_⟩
    · rw [hs]; exact hne
    · rw [hs] at hk
      obtain ⟨h1, h2, h3, h4, h5⟩ := hcuts k hk
      have hkd : tr.time (j + k) ≤ d := by
        rw [show tr.time (j + k) = t from h2]
        exact htd
      refine ⟨h1, h2, h3, h4, ?_⟩
      simp only [RunTrace.upTo, Trace.upTo_label, hkd, ite_true]
      rw [h5]
      simp [hs]
    · rw [hs]; exact hev

theorem upTo_inGroup (hmono : Monotone tr.time) {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {y : Fin P.n} {j i : Nat} {t : Time}
    {e : Node.Event A} (htd : t ≤ d) (h : tr.InGroup proposer dg y j i t e) :
    (tr.upTo d).InGroup proposer dg y j i t e := by
  obtain ⟨hg, hji, hlt⟩ := h
  have hne := hg.1
  have ht : tr.time j = t := (hg.2.1 0 (List.length_pos_of_ne_nil hne)).2.1
  refine ⟨(upTo_groupAt hmono).mpr ⟨htd, hg⟩, hji, ?_⟩
  rwa [upTo_state_of_le hmono (ht ▸ htd)]

theorem upTo_tickAt (hmono : Monotone tr.time) {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {y : Fin P.n} {j : Nat} {t : Time} :
    (tr.upTo d).TickAt proposer dg y j t ↔ t ≤ d ∧ tr.TickAt proposer dg y j t := by
  simp only [TickAt, upTo_groupAt hmono, exists_and_left]

theorem upTo_inHorizon {t : Time} (htd : t ≤ d) (h : tr.InHorizon t) :
    (tr.upTo d).InHorizon t := by
  obtain ⟨i, _, hi⟩ := h
  exact ⟨i, Or.inr ⟨d, rfl, htd⟩, hi⟩

/-- The AC projection of the prefix is the prefix of the AC projection. -/
theorem upTo_projAC : (tr.upTo d).projAC = tr.projAC.upTo d := by
  simp only [projAC, RunTrace.upTo, Trace.upTo]
  congr 1
  funext i
  by_cases h : tr.time i ≤ d <;> simp [h]

/-- The FG projection of the prefix is the prefix of the FG projection. -/
theorem upTo_projFG : (tr.upTo d).projFG = tr.projFG.upTo d := by
  simp only [projFG, RunTrace.upTo, Trace.upTo]
  congr 1
  funext i
  by_cases h : tr.time i ≤ d <;> simp [h]

theorem upTo_occurs {B : A.Blk} (h : (tr.upTo d).Occurs B) : tr.Occurs B := by
  obtain ⟨y, k, hk⟩ := h
  exact ⟨y, k, ((upTo_blockCallAt tr).mp hk).2⟩

/-- The blocks that the prefix's nodes honest at `d` hold are held while honest in the run. -/
theorem honestBlocks_upTo_subset (hmono : Monotone tr.time) {H : Time → Set (Fin P.n)}
    (hd : 0 ≤ d) : (tr.upTo d).HonestBlocks (H d) ⊆ tr.HonestBlocksAt H := by
  rintro B ⟨y, hy, i, hB⟩
  obtain ⟨i₀, -, hb, hs⟩ := Trace.upTo_state_exists tr hmono y i
  exact ⟨y, i₀, d, hd, hb, hy, hs ▸ hB⟩

/-- **Retention of `Sync`.** On the prefix through `d ≥ 0`, `SyncOnAt` gives `SyncOn` for the
validators honest at `d`. -/
theorem SyncOnAt.upTo (hmono : Monotone tr.time) {H : Time → Set (Fin P.n)} (hanti : Antitone H)
    {ΔF : Time} {W Wr : Time → Prop} {eff : Time → Time} (h : tr.SyncOnAt H ΔF W Wr eff)
    (hd0 : 0 ≤ d) : (tr.upTo d).SyncOn (H d) ΔF W Wr eff := by
  have anti : ∀ {t}, t ≤ d → H d ⊆ H t := fun ht => hanti ht
  refine ⟨h.deltaF, h.delta_le, fun x hx i m hs hw y hy j hc hd => ?_,
    fun x hx i B hs hw y hy j hc hd => ?_, fun x hx i B hs hw y hy j hc hd hanc => ?_,
    fun x hx i a hs hw y hy j hc hd => ?_⟩
  · obtain ⟨hid, hs⟩ := (upTo_sendOrAdmitAt hmono).mp hs
    obtain ⟨hjd, hc⟩ := (upTo_isCall _).mp hc
    rw [upTo_deadline hmono hjd] at hd
    obtain ⟨k, hkj, hk0, hk, hkd⟩ := h.message x i m (anti hid hx) hs hw y j (anti hjd hy) hc hd
    have hkd' : tr.time k ≤ d := (hmono hkj).trans hjd
    exact ⟨k, hkj, hk0, (upTo_processMsgAt _).mpr ⟨hkd', hk⟩, by rwa [upTo_deadline hmono hkd']⟩
  · have hid : tr.time i ≤ d := by
      rcases hs with hs | hs
      exacts [((upTo_acceptAt _).mp hs).1, ((upTo_ownBlockAt _).mp hs).1]
    have hs' : tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B := by
      rcases hs with hs | hs
      exacts [Or.inl ((upTo_acceptAt _).mp hs).2, Or.inr ((upTo_ownBlockAt _).mp hs).2]
    obtain ⟨hjd, hc⟩ := (upTo_isCall _).mp hc
    rw [upTo_deadline hmono hjd] at hd
    obtain ⟨k, hkj, hk0, hk, hkd⟩ := h.block x i B (anti hid hx) hs' hw y j (anti hjd hy) hc hd
    have hkd' : tr.time k ≤ d := (hmono hkj).trans hjd
    exact ⟨k, hkj, hk0, (upTo_blockCallAt _).mpr ⟨hkd', hk⟩, by rwa [upTo_deadline hmono hkd']⟩
  · obtain ⟨hid, hs⟩ := (upTo_acceptAt _).mp hs
    obtain ⟨hjd, hc⟩ := (upTo_isCall _).mp hc
    rw [upTo_deadline hmono hjd] at hd
    rw [upTo_state_of_le hmono hjd] at hanc
    obtain ⟨k, hkj, hk, hkd⟩ := h.relay x i B (anti hid hx) hs hw y j (anti hjd hy) hc hd
      (Anc.mono (honestBlocks_upTo_subset hmono hd0) hanc)
    have hkd' : tr.time k ≤ d := (hmono hkj).trans hjd
    exact ⟨k, hkj, (upTo_acceptAt _).mpr ⟨hkd', hk⟩, by rwa [upTo_deadline hmono hkd']⟩
  · obtain ⟨hid, hs⟩ := (upTo_sendOrAdmitAttAt hmono).mp hs
    obtain ⟨hjd, hc⟩ := (upTo_isCall _).mp hc
    rw [upTo_deadline hmono hjd] at hd
    obtain ⟨k, hkj, hk, hkd⟩ := h.attestation x i a (anti hid hx) hs hw y j (anti hjd hy) hc hd
    have hkd' : tr.time k ≤ d := (hmono hkj).trans hjd
    exact ⟨k, hkj, (upTo_processAttAt _).mpr ⟨hkd', hk⟩, by rwa [upTo_deadline hmono hkd']⟩

end RunTrace

/-- **Retention of `NoColl`.** The blocks occurring in the prefix occur in the run. -/
theorem Compose.NoCollRun.upTo {A : NodeAC P} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {tr : RunTrace A} (h : Compose.NoCollRun dg tr) (d : Time) :
    Compose.NoCollRun dg (tr.upTo d) :=
  Compose.NoCollOn.mono h (Set.insert_subset_insert fun _ hB => RunTrace.upTo_occurs hB)

namespace Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro}

/-- **Retention.** The prefix through `d` of a run under growing faults is a static run for the
validators honest at `d` (`0 ≤ d`: they were honest at the start), from the same starts. -/
theorem GoldilocksRun.upTo {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (h : Growing.GoldilocksRun proposer dg H tr ini) {d : Time} (hd : 0 ≤ d) :
    Consensus.Goldilocks.GoldilocksRun proposer dg (H d) (tr.upTo d) ini := by
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
      msg_unforgeable := fun y hy i m hc hs => ?_
      stock := h.stock
      vstart := h.vstart
      genesis_root_ok := h.genesis_root_ok
      carried_vote_unforgeable := fun y hy i B hB v hv hvH => ?_ }
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
  · obtain ⟨hid, hB⟩ := (RunTrace.upTo_blockCallAt _).mp hB
    obtain ⟨j, hji, hj⟩ := h.carried_vote_unforgeable y i B (anti hid hy) hB v hv (anti hid hvH)
    exact ⟨j, hji, (RunTrace.upTo_emitAt _).mpr ⟨(hm hji.le).trans hid, hj⟩⟩

/-- A node honest at the time of a cut was honest at every earlier cut. -/
theorem GoldilocksRun.honest_of_event (h : Growing.GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    {i : Nat} {c : Cut (goldilocksNode sp ro)} (_hc : tr.CallAt y i c) (hy : y ∈ H (tr.time i)) :
    ∀ k ≤ i, y ∈ H (tr.time k) :=
  fun _ hk => h.antitone (h.time_mono hk) hy

end Growing

end Consensus.Goldilocks

end
