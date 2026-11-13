module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.VoteForwardRelease
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core

public section

/-! # First release of vote-forward envelopes under growing faults

Pool retention is local to a sender honest at the source cut. Earlier exact envelopes have
the same timestamp; no restart can intervene between their sending events at that time.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

private theorem time_before_event_end (hv : rho.ExecutionValid) {b : Nat}
    {ev : Model.Event V (Model.protoOf (compiled (goldilocksWith S)) E).Object}
    (he : rho.events[b]? = some ev) {k : Nat} (hk : k < cutMap S rho hn (b + 1)) :
    (simTrace S rho hn).time k ≤ ev.time := by
  have hlen : k < (allCuts S rho hn).length := by
    rw [length_allCuts]
    exact hk.trans_le (cutMap_mono S rho hn (List.getElem?_eq_some_iff.mp he).1)
  have hl : (simTrace S rho hn).label k ≠ none := by
    rw [simTrace_label, List.getElem?_eq_getElem hlen]; simp
  obtain ⟨r, a, e, -, ha, hlo, -, -, -, ht, -⟩ := simTrace_cut S rho hn hl
  have hab : a ≤ b := by
    by_contra h
    have := cutMap_mono S rho hn (show b + 1 ≤ a by omega)
    omega
  rw [ht]
  rcases hab.lt_or_eq with hab | rfl
  · rcases keyLe_of_lt S rho hv ha he hab with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  · cases Option.some.inj (ha.symm.trans he)
    exact le_rfl

private theorem pool_mono_same_time_at (hv : rho.ExecutionValid)
    [Fact (S.vote.participationKind = none)] -- TEMP(C2)
    {y : Fin (Fintype.card V)} {a b : Nat} {t : Time}
    (hy : y ∈ honestKeysAt S rho t) (ha : rho.SendsAt (rho.key y) a t)
    (hb : rho.SendsAt (rho.key y) b t) {k l : Nat}
    (hak : cutMap S rho hn a ≤ k) (hkl : k ≤ l)
    (hlb : l ≤ cutMap S rho hn (b + 1)) (σ : Nat) :
    ((simTrace S rho hn).state y k).ac.pool σ ⊆
      ((simTrace S rho hn).state y l).ac.pool σ := by
  have hr := simTraceAt_goldilocksRun S rho hn hv
  have ht0 : 0 ≤ t := by
    rcases hb with h | ⟨o, h⟩ <;> exact (hv.in_horizon _ (List.mem_of_getElem? h)).1
  have hbound : ∀ q < cutMap S rho hn (b + 1), (simTrace S rho hn).time q ≤ t := by
    intro q hq
    rcases hb with h | ⟨o, h⟩ <;> exact time_before_event_end S rho hn hv h hq
  have hpref := hr.upTo ht0
  rw [simTraceAt_eq] at hpref
  have hnr : ∀ i, a ≤ i → i < b + 1 → ∀ u,
      rho.events[i]? ≠ some (.restart (rho.key y) u) := by
    intro i hai hib u he
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hib) with hib | rfl
    · exact noRestart_between_same_time_sends S rho hv ha hb hai hib _ u he
    · rcases hb with hb | ⟨o, hb⟩ <;> rw [he] at hb <;> cases hb
  have hm := Compose.pool_mono hpref hy hkl (fun q hkq hql hrestart =>
    simTrace_noRestart_between S rho hn hnr (hak.trans hkq) (hql.trans_le hlb)
      ((RunTrace.upTo_restartAt _).mp hrestart).2) σ
  have hsk := Trace.upTo_state (simTrace S rho hn) y (i := k)
    (fun q hq => hbound q (hq.trans_le (hkl.trans hlb)))
  have hsl := Trace.upTo_state (simTrace S rho hn) y (i := l)
    (fun q hq => hbound q (hq.trans_le hlb))
  simpa only [Compose.projAC_state hpref.toLocalRun hy, hsk, hsl] using hm

private theorem sending_event_insertion_at (hv : rho.ExecutionValid)
    [Fact (S.vote.participationKind = none)] -- TEMP(C2)
    {y : Fin (Fintype.card V)} {i k : Nat} {t : Time} {m : SA.Vote (Fintype.card V)}
    (hy : y ∈ honestKeysAt S rho t) (hs : rho.SendsAt (rho.key y) i t)
    (hlo : cutMap S rho hn i ≤ k) (hhi : k < cutMap S rho hn (i + 1))
    (hc : (simTrace S rho hn).IsCall y k)
    (hold : m ∉ ((simTrace S rho hn).state y k).ac.pool m.slot)
    (hnew : m ∈ ((simTrace S rho hn).post k).ac.pool m.slot) :
    m ∉ (stateAt S rho hn (rho.key y) i).node.ac.pool m.slot ∧
      m ∈ (stateAt S rho hn (rho.key y) (i + 1)).node.ac.pool m.slot := by
  have hi : i < rho.events.length := by
    rcases hs with h | ⟨o, h⟩ <;> exact (List.getElem?_eq_some_iff.mp h).1
  have hstate (j : Nat) (hj : j ≤ rho.events.length) :
      (stateAt S rho hn (rho.key y) j).node =
        (simTrace S rho hn).state y (cutMap S rho hn j) := by
    simpa only [simTraceAt_eq, Model.Run.ownKey, Equiv.symm_apply_apply] using
      simTraceAt_state_all S rho hn hv (rho.key y) j hj
  constructor
  · rw [hstate i hi.le]
    intro hm
    exact hold (pool_mono_same_time_at S rho hn hv hy hs hs le_rfl hlo hhi.le _ hm)
  · rw [hstate (i + 1) (by omega)]
    apply pool_mono_same_time_at S rho hn hv hy hs hs
      (hlo.trans (Nat.le_succ k)) (by omega) le_rfl m.slot
    obtain ⟨c, hc⟩ := hc
    rwa [(simTrace S rho hn).state_succ_of_call hc]

private theorem admission_forward_first_at (hv : rho.ExecutionValid)
    [Fact (S.vote.participationKind = none)] -- TEMP(C2)
    {y : Fin (Fintype.card V)} {i k : Nat} {t : Time} {m : SA.Vote (Fintype.card V)}
    (hy : y ∈ honestKeysAt S rho t) (hs : rho.SendsAt (rho.key y) i t)
    (hlo : cutMap S rho hn i ≤ k) (hhi : k < cutMap S rho hn (i + 1))
    (hf : m ∉ ((simTrace S rho hn).state y k).ac.pool m.slot) :
    ∀ j < i, Model.Obj.mk (.signed y .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∉ rho.releasesAt j := by
  intro j hji hj
  obtain ⟨u, hsend⟩ := voteForward_release_sender S rho hj
  have hkey : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply y
  have ht : t = u := released_voteForward_stamp S rho hn hv hsend m
    (by simpa only [hkey] using hj)
  subst u
  have hm := released_voteForward_pool S rho hn hv hsend m (by simpa only [hkey] using hj)
  have hjlen : j + 1 ≤ rho.events.length := by
    rcases hsend with he | ⟨o, he⟩ <;> exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp he).1
  have hstate := simTraceAt_state_all S rho hn hv (rho.key y) (j + 1) hjlen
  rw [simTraceAt_eq, hkey] at hstate
  rw [hstate] at hm
  exact hf (pool_mono_same_time_at S rho hn hv hy hsend hs
    (cutMap_mono S rho hn (Nat.le_succ j))
    ((cutMap_mono S rho hn (Nat.succ_le_of_lt hji)).trans hlo) hhi.le m.slot hm)

/-- The canonical growing trace forwards each emitted or freshly admitted vote at its
source event, and that exact timestamped envelope has no earlier release. -/
theorem simTraceAt_vote_forwarded (hv : rho.ExecutionValid)
    [Fact (S.vote.participationKind = none)] : -- TEMP(C2)
    ∀ y k (m : SA.Vote (Fintype.card V)),
    y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time k) →
    ((simTraceAt S rho hn).EmitAt y k m ∨
      ((((simTraceAt S rho hn).MsgCallAt y k m ∨ ∃ ℓ B,
        (simTraceAt S rho hn).CallAt y k (.ac ℓ) ∧ ℓ.call = .block B ∧ m ∈ SA.blockVotes B)) ∧
        m ∉ ((simTraceAt S rho hn).state y k).ac.pool m.slot ∧
        m ∈ ((simTraceAt S rho hn).post k).ac.pool m.slot)) →
    let envelope : (Model.protoOf (compiled (goldilocksWith S)) E).Object :=
      .mk (.signed y .poll) (.data (.voteForward ((simTraceAt S rho hn).time k) (encodeVote m)))
        [voteObj m]
    ∃ i, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      rho.SendsAt (rho.key y) i ((simTraceAt S rho hn).time k) ∧ envelope ∈ rho.releasesAt i ∧
      ∀ j < i, envelope ∉ rho.releasesAt j := by
  rw [simTraceAt_eq]
  intro y k m hy hsource
  dsimp only
  have hr := simTraceAt_goldilocksRun S rho hn hv
  rw [simTraceAt_eq] at hr
  have hpref := hr.upTo (hr.time_nonneg k)
  have hstate : ((simTrace S rho hn).upTo ((simTrace S rho hn).time k)).state y k =
      (simTrace S rho hn).state y k :=
    Trace.upTo_state _ y fun q hq => hr.time_mono hq.le
  have hpost : ((simTrace S rho hn).upTo ((simTrace S rho hn).time k)).post k =
      (simTrace S rho hn).post k := rfl
  have hemit (hem : (simTrace S rho hn).EmitAt y k m) :
      ((simTrace S rho hn).upTo ((simTrace S rho hn).time k)).EmitAt y k m :=
    (RunTrace.upTo_emitAt _).mpr ⟨le_rfl, hem⟩
  have hevent : ∃ i, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      rho.SendsAt (rho.key y) i ((simTrace S rho hn).time k) := by
    rcases hsource with hem | ⟨hc, -, -⟩
    · obtain ⟨ℓ, hc, e, he, -⟩ := hemit hem
      have hstep := (hpref.cutLaw y hy k _ hc).2.1
      have hnr : ℓ.call ≠ .restart := by
        intro h
        rw [h] at hstep
        have hn := restart_emits_nil (S.ro _) y
          (((simTrace S rho hn).upTo ((simTrace S rho hn).time k)).state y k).ac ℓ.frame
          ((simTrace S rho hn).time k) (hr.time_nonneg k)
        have hnil : ℓ.emits = [] := (congrArg Prod.snd hstep).symm.trans hn
        simp only [hnil, List.not_mem_nil] at he
      exact simTrace_call_sending_event S rho hn ((Trace.upTo_callAt _).mp hc).2 hnr
    · rcases hc with ⟨ℓ, hc, hm⟩ | ⟨ℓ, B, hc, hb, -⟩
      · exact simTrace_call_sending_event S rho hn hc (by rw [hm]; simp)
      · exact simTrace_call_sending_event S rho hn hc (by rw [hb]; simp)
  obtain ⟨i, hlo, hhi, hs⟩ := hevent
  have hfresh : m ∉ ((simTrace S rho hn).state y k).ac.pool m.slot := by
    rcases hsource with hem | ⟨-, hf, -⟩
    · have hem' := hemit hem
      obtain ⟨ℓ, hc, e, he, hev⟩ := hem'
      have hΦ : FrameOK ℓ.frame := (hpref.cutLaw y hy k _ hc).1 ▸
        (Store.frame_realization _ _ _ _ (Compose.fg_reachable hpref.toLocalRun hy k)).1
      have hsign := SA.step_emission_signer y
        (((simTrace S rho hn).upTo ((simTrace S rho hn).time k)).state y k).ac
        ℓ.frame _ ℓ.call hΦ (hr.time_nonneg k)
        (e := e) (by
          have hstep := (hpref.cutLaw y hy k _ hc).2.1
          change _ = (_, ℓ.emits) at hstep
          exact (congrArg Prod.snd hstep).symm ▸ he)
      have hm : m.val = y := hev ▸ hsign
      have hf := Compose.emitted_slot_not_pooled hpref (simIni_pool S rho hn) hy hy le_rfl
        (hemit hem) hm rfl m.slot
      simpa only [Compose.projAC_state hpref.toLocalRun hy, hstate] using hf
    · exact hf
  have hcall : (simTrace S rho hn).IsCall y k := by
    rcases hsource with ⟨ℓ, hc, -⟩ | ⟨hc, -⟩
    · exact ⟨_, hc⟩
    · rcases hc with ⟨ℓ, hc, -⟩ | ⟨ℓ, B, hc, -⟩ <;> exact ⟨_, hc⟩
  have hnew : m ∈ ((simTrace S rho hn).post k).ac.pool m.slot := by
    rcases hsource with hem | ⟨-, -, hnew⟩
    · simpa only [hpost] using
        Compose.emitted_vote_mem_post hpref (simIni_pool S rho hn) hy (hemit hem)
    · exact hnew
  obtain ⟨hold, hnew⟩ := sending_event_insertion_at S rho hn hv hy hs hlo hhi hcall hfresh hnew
  refine ⟨i, hlo, hhi, hs, ?_, admission_forward_first_at S rho hn hv hy hs hlo hhi hfresh⟩
  rcases hs with he | ⟨o, he⟩
  · have h := tick_pool_insertion_released_at S rho hn hv he m hold hnew
    rw [ownKey_key] at h
    exact h
  · have h := delivery_pool_insertion_released_at S rho hn hv he m hold hnew
    rw [ownKey_key] at h
    exact h

end Consensus.Goldilocks.Simulation
