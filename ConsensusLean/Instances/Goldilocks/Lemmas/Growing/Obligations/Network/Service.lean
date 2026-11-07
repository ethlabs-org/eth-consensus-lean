module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Source
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Lift
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Forwarding
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NonfinalSuppliers
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Network transport under growing faults: finite service before an outage

The finite (`SyncUntil`) service of the canonical growing trace, with senders honest at their send
and recipients honest at their reading call:

* `publication_held_before_deadline_at`: an actual publication is held strictly before a
  qualifying node deadline;
* `held_forward_accepted_before_at`: holdings of a forwarding wrapper that is its signer's release
  give an acceptance before the observation deadline;
* `publication_acceptedBy_syncUntil_at`, `acceptance_relay_syncUntil_at`: acceptance relay;
* `vote_message_service_other_at`: another recipient processes a first-release vote envelope;
* `Simulation.sleepyServiceBefore_of_syncUntil_at`: the finite Sleepy service from raw synchrony
  through its deadline bound. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Shape Blocks

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)

/-- An actual publication by an origin honest at its event is held strictly before a qualifying
node deadline of a recipient honest at its call. -/
theorem publication_held_before_deadline_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {b : Time} (hbh : b ≤ rho.horizon) (hnet : rho.log.SyncUntil rho.point b)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r)
    (hx : rho.key r.origin ∉ rho.faultyAt ((publisherExecution S rho).eventTime r.event))
    (hrow : ¬ rho.log.fgAtt r.object)
    {y : Fin (Fintype.card V)} {j : Nat}
    (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time j))
    (hj : (simTraceAt S rho hn).IsCall y j) {τ : Time} (hτ : 0 ≤ τ)
    (ht : (publisherExecution S rho).eventTime r.event = τ)
    (hb : (simTraceAt S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ ≤ b)
    (hd : (simTraceAt S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ ≤
      (simTraceAt S rho hn).time j) :
    ∃ d, rho.log.Held rho.point (rho.key y) r.object d ∧
      d < (simTraceAt S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ := by
  obtain ⟨a, ha, heq, hw⟩ := deadline_awake_interval_at S rho hn hv hy hj hτ
  rw [heq] at hb hd ⊢
  have hslack : a + E.ΔAC - 1 < a + (S.params (Model.pubOf E) hn).Δ := by
    change a + E.ΔAC - 1 < a + E.ΔAC
    exact sub_one_lt _
  have hbj : a + E.ΔAC - 1 ≤ (simTraceAt S rho hn).time j := hslack.le.trans hd
  have hbh' : a + E.ΔAC - 1 ≤ rho.horizon := (hslack.le.trans hb).trans hbh
  obtain ⟨hheld, _⟩ := publication_held_syncUntil_at S rho hn hnet r hr hx hrow
    (not_faulty_of_mem_honestKeysAt S rho hy hbj hbh')
    (ht ▸ ha) hb hbh' (fun u hau hud => hw u hau (hud.trans hbj))
  exact ⟨a + E.ΔAC - 1, hheld, hslack⟩

/-- Network holdings of a forwarding wrapper that is its signer's actual release, with the signer
honest at the release, yield an acceptance before the observation deadline, at a reading cut `j`
of a recipient honest at a time `t₀` that bounds every cut before `j`. -/
theorem held_forward_accepted_before_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {y x : Fin (Fintype.card V)} {j : Nat} {t₀ : Time}
    (hj₀ : ∀ k < j, (simTraceAt S rho hn).time k ≤ t₀) (hy : rho.key y ∉ rho.faultyAt t₀)
    {o : Wire (Fintype.card V)} {t d D : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hx : rho.key x ∉ rho.faultyAt t) (hrel : rho.releases (rho.key x) o t)
    (hheld : rho.log.Held rho.point (rho.key y) o d)
    (hdecode : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B))
    (hd : d < D) (hj : D ≤ (simTraceAt S rho hn).time j)
    (hF : Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho))
      ((simTraceAt S rho hn).state y j).fg.F B) :
    ∃ k ≤ j, (simTraceAt S rho hn).AcceptAt y k B ∧ (simTraceAt S rho hn).time k < D := by
  obtain ⟨u, hud, hsource, _⟩ := hheld
  have huD : u < D := hud.trans_lt hd
  have event_before {i : Nat} {ev : Model.Event V (Wire (Fintype.card V))}
      (he : rho.events[i]? = some ev) (hu : ev.time = u) : cutMap S rho hn (i + 1) ≤ j := by
    rw [simTraceAt_eq] at hj
    by_contra h
    have hj' : j < cutMap S rho hn (i + 1) := by omega
    have hlen : j < (allCuts S rho hn).length := by
      rw [length_allCuts]
      exact hj'.trans_le (cutMap_mono S rho hn (List.getElem?_eq_some_iff.mp he).1)
    have hl : (simTrace S rho hn).label j ≠ none := by
      rw [simTrace_label, List.getElem?_eq_getElem hlen]
      simp
    obtain ⟨_, q, e, _, hq, hstart, _, _, _, htime, _⟩ := simTrace_cut S rho hn hl
    have hqi : q ≤ i := by
      by_contra hq'
      have := cutMap_mono S rho hn (show i + 1 ≤ q by omega)
      omega
    have hle : e.time ≤ ev.time := by
      rcases hqi.lt_or_eq with hlt | rfl
      · rcases keyLe_of_lt S rho hv hq he hlt with h | ⟨h, _⟩
        · exact h.le
        · exact h.le
      · rw [he] at hq
        cases hq
        rfl
    rw [hu, ← htime] at hle
    exact absurd (hle.trans_lt huD) (not_lt.mpr hj)
  have hkey : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply _
  rcases hsource with hs | hr
  · obtain ⟨i, hi, ho⟩ := hs
    have hxy := released_forward_signer S rho hn hi ho hdecode
    rw [hxy] at hdecode
    have hstamp : t = u := released_forward_stamp S rho hn hv hi ho hdecode
    have hacc : ∃ k < cutMap S rho hn (i + 1),
        (simTrace S rho hn).AcceptAt (rho.ownKey (rho.key y)) k B ∧
        (simTrace S rho hn).time k = t := by
      rcases hi with he | ⟨receipt, he⟩
      · exact tick_released_forward_acceptance S rho hn hv he ho hdecode
      · exact delivery_released_forward_acceptance S rho hn hv he ho hdecode
    obtain ⟨k, hk, ha, ht⟩ := hacc
    have hcut : cutMap S rho hn (i + 1) ≤ j := by
      rcases hi with he | ⟨receipt, he⟩ <;> exact event_before he rfl
    rw [simTraceAt_eq]
    exact ⟨k, (hk.trans_le hcut).le, hkey ▸ ha, ht ▸ hstamp ▸ huD⟩
  · obtain ⟨i, hi⟩ := hr
    obtain ⟨k, hk, ha, _, ht⟩ := received_forward_accepted_before_of_released_at S rho hn hv hnc
      hi hj₀ hy (.refl o) hx hrel hdecode (event_before hi rfl)
      (by simpa only [hkey] using hF) huD
    exact ⟨k, (hk.trans_le (event_before hi rfl)).le, hkey ▸ ha, ht⟩

/-- Acceptance service is measured at the processing cut, even when later restarts enlarge the
observation deadline. The origin is honest at its publication, the recipient at its call. -/
theorem publication_acceptedBy_syncUntil_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {b : Time} (hbh : b ≤ rho.horizon) (hnet : rho.log.SyncUntil rho.point b)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r)
    {τ : Time} (hτ : 0 ≤ τ) (ht : (publisherExecution S rho).eventTime r.event = τ)
    (hx : rho.key r.origin ∉ rho.faultyAt τ)
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hdecode : decodeForward (S.params (Model.pubOf E) hn)
      (Model.digests rho.hash r.object) r.object = some (r.origin, τ, p, B))
    {y : Fin (Fintype.card V)} {j : Nat}
    (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time j))
    (hj : (simTraceAt S rho hn).IsCall y j)
    (hb : (simTraceAt S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ ≤ b)
    (hd : (simTraceAt S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ ≤
      (simTraceAt S rho hn).time j)
    (hF : Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho))
      ((simTraceAt S rho hn).state y j).fg.F B) :
    (simTraceAt S rho hn).BlockAcceptedBy y j τ B := by
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  have hrel : rho.releases (rho.key r.origin) r.object τ :=
    ht ▸ ⟨r.event, (publisherExecution S rho).actual_event r hr,
      (publisherExecution S rho).actual_release r hr⟩
  induction j using Nat.strong_induction_on with
  | h j ih =>
    obtain ⟨d, hheld, hlt⟩ := publication_held_before_deadline_at S rho hn hv hbh hnet
      r hr (ht ▸ hx) (not_isFGAtt_of_decodeForward hdecode) hy hj hτ ht hb hd
    obtain ⟨k, hkj, hacc, htime⟩ := held_forward_accepted_before_at S rho hn hv hnc
      (fun k hk => hrun.time_mono hk.le)
      (not_faulty_of_mem_honestKeysAt S rho hy le_rfl (isCall_time_le_horizon S rho hn hv hj))
      hx hrel hheld hdecode hlt hd hF
    by_cases hk : (simTraceAt S rho hn).time k <
        (simTraceAt S rho hn).deadline y k τ (S.params (Model.pubOf E) hn).Δ
    · exact ⟨k, hkj, hacc, hk⟩
    · have hkj' : k < j := lt_of_le_of_ne hkj (by
        intro heq
        subst k
        exact hk htime)
      have hmono := deadline_mono_cut_at S rho hn hv y τ (S.params (Model.pubOf E) hn).Δ hkj
      obtain ⟨l, hl, ha, ht'⟩ := ih k hkj' (hrun.antitone (hrun.time_mono hkj) hy) ⟨_, hacc⟩
        (hmono.trans hb) (le_of_not_gt hk)
        ((run_F_mono_at hrun hy hkj).trans hF)
      exact ⟨l, hl.trans hkj, ha, ht'⟩

/-- The finite acceptance-relay field: an acceptance by a node honest at its cut is relayed to
every recipient honest at its call, inside the blocks held while honest. -/
theorem acceptance_relay_syncUntil_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {b : Time} (hbh : b ≤ rho.horizon) (hnet : rho.log.SyncUntil rho.point b)
    {x : Fin (Fintype.card V)} {i : Nat}
    (hx : x ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i))
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hi : (simTraceAt S rho hn).AcceptAt x i B) (ht : 0 ≤ (simTraceAt S rho hn).time i)
    {y : Fin (Fintype.card V)} {j : Nat}
    (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time j))
    (hj : (simTraceAt S rho hn).IsCall y j)
    (hb : (simTraceAt S rho hn).deadline y j ((simTraceAt S rho hn).time i)
      (S.params (Model.pubOf E) hn).Δ ≤ b)
    (hd : (simTraceAt S rho hn).deadline y j ((simTraceAt S rho hn).time i)
      (S.params (Model.pubOf E) hn).Δ ≤ (simTraceAt S rho hn).time j)
    (hF : Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho))
      ((simTraceAt S rho hn).state y j).fg.F B) :
    (simTraceAt S rho hn).BlockAcceptedBy y j ((simTraceAt S rho hn).time i) B := by
  obtain ⟨r, p, hr, horg, _, _, htime, _, hdecode⟩ :=
    (forwardAtAcceptanceAt_iff S rho hn _ _ _).mp
      (forwardAtAcceptance_at S rho hn hv) x i B hx hi
  have hih : (simTraceAt S rho hn).time i ≤ rho.horizon :=
    isCall_time_le_horizon S rho hn hv ⟨_, hi⟩
  apply publication_acceptedBy_syncUntil_at S rho hn hv hnc hbh hnet r hr ht htime
    (horg ▸ not_faulty_of_mem_honestKeysAt S rho hx le_rfl hih) (p := p)
    (by simpa only [horg] using hdecode) hy hj hb hd hF

/-- A different recipient honest at its call processes a first-release vote envelope of a sender
honest at its release before its processing-cut deadline. -/
theorem vote_message_service_other_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {b : Time} (hbh : b ≤ rho.horizon) (hnet : rho.log.SyncUntil rho.point b)
    {source : Nat} {x y : Fin (Fintype.card V)} {τ : Time} {m : SA.Vote (Fintype.card V)}
    (hx : rho.key x ∉ rho.faultyAt τ) (hne : y ≠ x)
    (hτ : 0 ≤ τ) (hs : rho.SendsAt (rho.key x) source τ)
    (hrel : Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m] ∈
      rho.releasesAt source)
    (hfirst : ∀ i < source,
      Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m] ∉
        rho.releasesAt i)
    {j : Nat} (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time j))
    (hj : (simTraceAt S rho hn).IsCall y j)
    (hb : (simTraceAt S rho hn).projAC.deadline y j τ ≤ b)
    (hd : (simTraceAt S rho hn).projAC.deadline y j τ ≤ (simTraceAt S rho hn).time j) :
    ∃ k ≤ j, τ ≤ (simTraceAt S rho hn).time k ∧
      (simTraceAt S rho hn).projAC.ProcessAt y k m ∧
      (simTraceAt S rho hn).time k < (simTraceAt S rho hn).projAC.deadline y k τ := by
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  induction j using Nat.strong_induction_on with
  | h j ih =>
    obtain ⟨a, ha, heq, hw⟩ := deadline_awake_interval_at S rho hn hv hy hj hτ
    have heq' : (simTraceAt S rho hn).projAC.deadline y j τ =
        a + (S.params (Model.pubOf E) hn).Δ := by
      rw [Compose.projAC_deadline]
      exact heq
    have hslack : a + E.ΔAC - 1 < a + (S.params (Model.pubOf E) hn).Δ := by
      change a + E.ΔAC - 1 < a + E.ΔAC
      linarith
    have hbound : a + E.ΔAC - 1 ≤ b := hslack.le.trans (heq' ▸ hb)
    have hbj : a + E.ΔAC - 1 ≤ (simTraceAt S rho hn).time j := hslack.le.trans (heq' ▸ hd)
    have hheld := hnet.msgs (rho.key x) _ τ ⟨source, hs, hrel⟩ hx
      (by simp [log_fgAtt_iff, isFGAtt, IsAttObj]) (rho.key y)
      a ha hbound (hbound.trans hbh)
      (not_faulty_of_mem_honestKeysAt S rho hy hbj (hbound.trans hbh))
      (fun u hau hud => hw u hau (hud.trans hbj))
    rcases held_voteForward_source_or_process_at S rho hn hv hx hs hfirst hheld with
      h | ⟨k, hp, hlo, hhi⟩
    · exact False.elim (hne h)
    have htime : (simTraceAt S rho hn).time k < (simTraceAt S rho hn).projAC.deadline y j τ := by
      rw [heq']
      exact hhi.trans_lt hslack
    have hkj : k < j := by
      by_contra h
      have := hrun.time_mono (Nat.le_of_not_gt h)
      linarith
    by_cases hk : (simTraceAt S rho hn).time k < (simTraceAt S rho hn).projAC.deadline y k τ
    · exact ⟨k, hkj.le, hlo, hp, hk⟩
    · have hm : (simTraceAt S rho hn).projAC.deadline y k τ ≤
          (simTraceAt S rho hn).projAC.deadline y j τ := by
        rw [Compose.projAC_deadline, Compose.projAC_deadline]
        exact deadline_mono_cut_at S rho hn hv y τ (S.params (Model.pubOf E) hn).Δ hkj.le
      obtain ⟨l, hl, hlo', hp', hlt⟩ := ih k hkj (hrun.antitone (hrun.time_mono hkj.le) hy)
        ⟨_, Compose.projAC_callAt.mp hp.choose_spec.1⟩ (hm.trans hb) (le_of_not_gt hk)
      exact ⟨l, hl.trans hkj.le, hlo', hp', hlt⟩

end Consensus.Goldilocks.Obligations.Growing

namespace Consensus.Goldilocks.Simulation
open AsChainShape Obligations.Growing
open Shape Blocks
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **The finite sleepy service under growing faults** from raw synchrony through its deadline
bound `b ≤ horizon`: senders honest at their sends, recipients honest at their reading calls
(the growing-fault `sleepyServiceBefore_of_syncUntil`). Self-service uses fresh processing at the
source time. -/
theorem sleepyServiceBefore_of_syncUntil_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {b : Time} (hbh : b ≤ rho.horizon) (hnet : rho.log.SyncUntil rho.point b) :
    Compose.Growing.SleepyServiceBefore (simTraceAt S rho hn) (honestKeysAt S rho)
      (S.params (pubOf E) hn).Δ b := by
  have hr := simTraceAt_goldilocksRun S rho hn hv
  have hsim := simTraceAt_simulates S rho hn hv
  apply sleepyServiceBefore_of_message_relay_at hr
  · intro x i m hx hsrc h0 y j ℓ hy hj hb hd
    rw [SA.messageServedBefore_iff]
    apply Or.inl
    have hsource : (simTraceAt S rho hn).SendOrAdmitAt x i m := by
      obtain ⟨l, hl, hm⟩ := hsrc
      refine ⟨l, Compose.projAC_callAt.mp hl, ?_⟩
      rw [projAC_state_at hr hx] at hm
      exact hm
    by_cases hxy : y = x
    · subst y
      obtain ⟨k, hp, ht⟩ := sendOrAdmit_process_same_time_at S rho hn hv hx hsource
      have hlt : ∀ q, (simTraceAt S rho hn).time i <
          (simTraceAt S rho hn).projAC.deadline x q ((simTraceAt S rho hn).time i) := by
        intro q
        unfold ACTrace.deadline
        cases (simTraceAt S rho hn).projAC.lastWake x q with
        | bot => exact lt_add_of_pos_right _ (S.params (Model.pubOf E) hn).toParams.hΔ
        | coe w =>
          exact lt_of_le_of_lt (le_max_left _ _)
            (lt_add_of_pos_right _ (S.params (Model.pubOf E) hn).toParams.hΔ)
      refine ⟨k, ?_, ht.ge, hp, ?_⟩
      · by_contra h
        have hm := hr.time_mono (Nat.le_of_lt (Nat.lt_of_not_ge h))
        have := hlt j
        linarith
      · change (simTraceAt S rho hn).time k < _
        rw [ht]
        exact hlt k
    · obtain ⟨r, -, -, hs, hrel, hf⟩ := hsim.vote_forwarded x i m hx
        (sendOrAdmit_forward_source_at hr hx hsrc)
      have hih : (simTraceAt S rho hn).time i ≤ rho.horizon :=
        isCall_time_le_horizon S rho hn hv ⟨_, hsource.choose_spec.1⟩
      exact vote_message_service_other_at S rho hn hv hbh hnet
        (not_faulty_of_mem_honestKeysAt S rho hx le_rfl hih) hxy h0 hs hrel hf hy
        ⟨_, Compose.projAC_callAt.mp hj⟩ hb hd
  · intro x i B hx hi h0 y j hy hj hb hd hF
    exact acceptance_relay_syncUntil_at S rho hn hv hnc hbh hnet hx hi h0 hy hj hb hd hF

end Consensus.Goldilocks.Simulation

end
