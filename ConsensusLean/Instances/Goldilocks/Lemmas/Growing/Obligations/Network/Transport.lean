module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Interface
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ForwardingInvariant
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationProvenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Simulates
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Attestations
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Forward.Receipt
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Forward.Accepted
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Forward.Tick
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Forward.AtAcceptance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.DeadlineWake
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OwnReleaseProcessing
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Network transport under growing faults: holdings, deadlines and attestation service

The engine-to-node network transport of `Obligations/NetworkTransport` on the canonical growing
trace `simTraceAt`, with honesty read at the time each law reads it:

* a sender is honest at its send (the L0 network laws read `HonestAt v t` at the send time `t`);
* a recipient honest at its reading call is honest at every earlier time of its delivery interval
  (compromise only grows), which is where the L0 laws read it (`HonestAt w (dl a)`);
* node-local run facts at a cut are the static ones on the prefix through that cut's time.

Contents: `deadline_awake_interval_at`, `deadline_mono_cut_at`, `publication_held_psync_at`,
`publication_held_syncUntil_at`, `signed_att_wellFormed_at`, `released_att_processAt_at`,
`held_att_processed_before_at`, the attestation service contract `PSyncFGAttTransportAt` with its
monotone lift, and its base supplier `signed_row_service_psync_at`. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Shape Blocks

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  (S : BoundSetup) (rho : Model.Run (compiled (goldilocksWith S)) E)

omit [DecidableEq V] in
/-- A key honest at `t` is the key of an engine node uncompromised at every in-horizon `a ≤ t`. -/
theorem not_faulty_of_mem_honestKeysAt {y : Fin (Fintype.card V)} {t a : Time}
    (hy : y ∈ honestKeysAt S rho t) (hat : a ≤ t) (hah : a ≤ rho.horizon) :
    rho.key y ∉ rho.faultyAt a := by
  rw [mem_honestKeysAt_iff] at hy
  exact fun h => hy (rho.faultyAt_mono (le_min hat hah) h)

omit [DecidableEq V] in
/-- An engine node uncompromised at `t` has its key honest at `t`. -/
theorem mem_honestKeysAt_of_not_faulty {y : Fin (Fintype.card V)} {t : Time}
    (hy : rho.key y ∉ rho.faultyAt t) : y ∈ honestKeysAt S rho t := by
  rw [mem_honestKeysAt_iff]
  exact fun h => hy (rho.faultyAt_mono (min_le_left _ _) h)

/-- A recipient is awake from its effective send/wake start through its call. The recipient is
honest at the call. -/
theorem deadline_awake_interval_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} {j : Nat}
    (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time j))
    (hj : (simTraceAt S rho hn).IsCall y j) {τ : Time} (hτ : 0 ≤ τ) :
    ∃ a, τ ≤ a ∧
      (simTraceAt S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ =
        a + (S.params (Model.pubOf E) hn).Δ ∧
      rho.point.AwakeOnClosed (rho.key y) a ((simTraceAt S rho hn).time j) := by
  have hr := simTraceAt_goldilocksRun S rho hn hv
  obtain ⟨a, hτa, heq, hw⟩ := (simTraceAt S rho hn).deadline_awake_of_call hr.time_mono hj
    (hr.awake_of_call y j hy hj) (fun u => hr.restart_at_wake y u _ hy)
    (fun k hk hkj => hr.sleep_of_restart y k (hr.antitone hkj hy) hk) hτ _
  refine ⟨a, hτa, heq, fun u hau huj => ?_⟩
  have h := (simTraceAt_awake_iff S rho hn y u).mp (hw u hau huj)
  rw [awakeAt_iff] at h
  exact h.1

/-- Later observation cuts can only increase a recipient's deadline. -/
theorem deadline_mono_cut_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (y : Fin (Fintype.card V)) (τ Δ : Time) :
    Monotone (fun j => (simTraceAt S rho hn).deadline y j τ Δ) :=
  (simTraceAt S rho hn).deadline_mono_cut_of_time_mono
    (simTraceAt_goldilocksRun S rho hn hv).time_mono y τ Δ

/-- Partial synchrony services an actual publication by an origin honest at its event strictly
before the protocol endpoint, at a recipient honest at the holding time. -/
theorem publication_held_psync_at (hn : 1 ≤ Fintype.card V) {g : Time}
    (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (goldilocksWith S)) E))
    (hr : (publisherExecution S rho).actual r)
    (hx : rho.key r.origin ∉ rho.faultyAt ((publisherExecution S rho).eventTime r.event))
    (hrow : ¬ rho.log.fgAtt r.object)
    {y : V} {a : Time} (hy : y ∉ rho.faultyAt (max a g + E.ΔAC - 1))
    (ha : (publisherExecution S rho).eventTime r.event ≤ a)
    (hh : max a g + E.ΔAC - 1 ≤ rho.horizon)
    (hawake : rho.point.AwakeOnClosed y a (max a g + E.ΔAC - 1)) :
    rho.log.Held rho.point y r.object (max a g + E.ΔAC - 1) ∧
      max a g + E.ΔAC - 1 < max a g + (S.params (Model.pubOf E) hn).Δ := by
  constructor
  · exact hnet.msgs _ _ _
      ⟨r.event, (publisherExecution S rho).actual_event r hr,
        (publisherExecution S rho).actual_release r hr⟩
      hx hrow y a ha hh hh hy hawake
  · change max a g + E.ΔAC - 1 < max a g + E.ΔAC
    exact sub_one_lt _

/-- Before an outage, only qualifying recipient deadlines receive service. The origin is honest
at its event, the recipient at the holding time. -/
theorem publication_held_syncUntil_at (hn : 1 ≤ Fintype.card V) {b : Time}
    (hnet : rho.log.SyncUntil rho.point b)
    (r : Publication (Model.protoOf (compiled (goldilocksWith S)) E))
    (hr : (publisherExecution S rho).actual r)
    (hx : rho.key r.origin ∉ rho.faultyAt ((publisherExecution S rho).eventTime r.event))
    (hrow : ¬ rho.log.fgAtt r.object)
    {y : V} {a : Time} (hy : y ∉ rho.faultyAt (a + E.ΔAC - 1))
    (ha : (publisherExecution S rho).eventTime r.event ≤ a)
    (hb : a + (S.params (Model.pubOf E) hn).Δ ≤ b)
    (hh : a + E.ΔAC - 1 ≤ rho.horizon)
    (hawake : rho.point.AwakeOnClosed y a (a + E.ΔAC - 1)) :
    rho.log.Held rho.point y r.object (a + E.ΔAC - 1) ∧ a + E.ΔAC - 1 < b := by
  have hlt : a + E.ΔAC - 1 < b := by
    change a + E.ΔAC ≤ b at hb
    exact (sub_one_lt _).trans_le hb
  exact ⟨hnet.msgs _ _ _
    ⟨r.event, (publisherExecution S rho).actual_event r hr,
      (publisherExecution S rho).actual_release r hr⟩
    hx hrow y a ha hlt.le hh hy hawake, hlt⟩

/-- A signing cut of the trace is at or before the engine horizon. -/
theorem signAt_time_le_horizon (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} {i : Nat} {a : FG.Att (Fintype.card V)}
    (hs : (simTraceAt S rho hn).SignAt y i a) :
    (simTraceAt S rho hn).time i ≤ rho.horizon := by
  obtain ⟨C, hc⟩ := hs
  rw [simTraceAt_eq] at hc ⊢
  exact simTrace_labelled_time_le S rho hn hv (by rw [hc.2]; simp)

/-- A call cut of the trace is at or before the engine horizon. -/
theorem isCall_time_le_horizon (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} {j : Nat} (hj : (simTraceAt S rho hn).IsCall y j) :
    (simTraceAt S rho hn).time j ≤ rho.horizon := by
  obtain ⟨c, hc⟩ := hj
  rw [simTraceAt_eq] at hc ⊢
  exact simTrace_labelled_time_le S rho hn hv (by rw [hc.2]; simp)

/-- Signatures of a node honest at the signing cut are well-formed attestations. -/
theorem signed_att_wellFormed_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} {i : Nat}
    (hy : y ∈ honestKeysAt ⟨S, stock⟩ rho ((simTraceAt ⟨S, stock⟩ rho hn).time i))
    {a : FG.Att (Fintype.card V)} (hs : (simTraceAt ⟨S, stock⟩ rho hn).SignAt y i a) :
    a.WellFormed := by
  obtain ⟨C, hc⟩ := hs
  have hrun := simTraceAt_goldilocksRun ⟨S, stock⟩ rho hn hv
  have hsign := (hrun.cutLaw y i _ hc hy).1
  have hst := Trace.upTo_state (simTraceAt ⟨S, stock⟩ rho hn) y
      (d := (simTraceAt ⟨S, stock⟩ rho hn).time i)
    (i := i) fun k hk => hrun.time_mono hk.le
  have hr := Compose.fg_reachable (hrun.upTo (hrun.time_nonneg i)).toLocalRun hy i
  rw [hst] at hr
  obtain ⟨h1, h2, h3⟩ := Store.entry_input hr
    (((simTraceAt ⟨S, stock⟩ rho hn).state y i).fg.σ C.root).Th
  exact Compose.createAtt_wellFormed h1 h2 h3 hsign

/-- An actual canonical attestation release includes own processing in that tick. No honesty
premise: an engine event's node is honest at the event. -/
theorem released_att_processAt_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) {v : V}
    {a : FG.Att (Fintype.card V)} {t : Time} (hs : rho.releases v (attObj a) t) :
    ∃ k, (simTraceAt S rho hn).ProcessAttAt (rho.ownKey v) k a ∧
      (simTraceAt S rho hn).time k = t := by
  rw [simTraceAt_eq]
  obtain ⟨i, he, ho⟩ := hs
  rcases he with he | ⟨o, he⟩
  · obtain ⟨hp, C, hc⟩ := att_released_inv_at S rho hn hv he ho
    exact tick_attest_processAt S rho hn he hp hc
  · exact (deliver_not_att S rho hn hv he a ho).elim

/-- Holdings suffice for processing before an observation deadline, even for an old receipt. No
honesty premise: the processing is the holder's own release or its receipt. -/
theorem held_att_processed_before_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)}
    {a : FG.Att (Fintype.card V)} (hwf : a.WellFormed) {j : Nat} {d D : Time}
    (hh : rho.log.Held rho.point (rho.key y) (attObj a) d)
    (hd : d < D) (hj : D ≤ (simTraceAt ⟨S, stock⟩ rho hn).time j) :
    ∃ k ≤ j, (simTraceAt ⟨S, stock⟩ rho hn).ProcessAttAt y k a ∧ (simTraceAt ⟨S, stock⟩ rho hn).time
        k < D := by
  obtain ⟨u, hud, hs, _⟩ := hh
  have huD := hud.trans_lt hd
  have hp : ∃ k, (simTraceAt ⟨S, stock⟩ rho hn).ProcessAttAt (rho.ownKey (rho.key y)) k a ∧
      (simTraceAt ⟨S, stock⟩ rho hn).time k = u := by
    rcases hs with hs | ⟨i, hi⟩
    · exact released_att_processAt_at ⟨S, stock⟩ rho hn hv hs
    · obtain ⟨k, _, hk, ht⟩ := received_att_processAt S rho hn hi hwf (.refl _)
      rw [simTraceAt_eq ⟨S, stock⟩ rho hn]
      exact ⟨k, hk, ht⟩
  obtain ⟨k, hk, ht⟩ := hp
  have hlt : (simTraceAt ⟨S, stock⟩ rho hn).time k < D := ht ▸ huD
  refine ⟨k, ?_, ?_, hlt⟩
  · by_contra h
    exact (not_lt_of_ge (hj.trans
      ((simTraceAt_goldilocksRun ⟨S, stock⟩ rho hn hv).time_mono (by omega)))) hlt
  · have he : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply y
    exact he ▸ hk

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) (ΔF : Time)

/-- Signed FG attestations of a node honest at the signing cut are processed before the
attestation deadline at FG delay `Δ_F` at recipient calls within the engine horizon, by every
recipient honest at its call. An earlier processing of the identical attestation is sufficient. -/
def PSyncFGAttTransportAt : Prop :=
  ∀ g, rho.log.PSync rho.point g →
    ∀ x i a, x ∈ H (tr.time i) → tr.SignAt x i a →
      ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.time j ≤ rho.horizon →
        tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
        ∃ k ≤ j, tr.ProcessAttAt y k a ∧
          tr.time k < tr.deadline y k (max (tr.time i) g) ΔF

/-- The signed-attestation service contract, without exposing its definition to consumers. -/
theorem psyncFGAttTransportAt_iff : PSyncFGAttTransportAt S rho tr H ΔF ↔
    ∀ g, rho.log.PSync rho.point g →
      ∀ x i a, x ∈ H (tr.time i) → tr.SignAt x i a →
        ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.time j ≤ rho.horizon →
          tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
          ∃ k ≤ j, tr.ProcessAttAt y k a ∧
            tr.time k < tr.deadline y k (max (tr.time i) g) ΔF := by
  rfl

variable {S rho tr H} in
/-- **The monotone lift of attestation service**: service at `Δ₁` is service at every
`Δ₂ ≥ Δ₁`. -/
theorem PSyncFGAttTransportAt.mono {Δ₁ Δ₂ : Time} (h : PSyncFGAttTransportAt S rho tr H Δ₁)
    (h12 : Δ₁ ≤ Δ₂) : PSyncFGAttTransportAt S rho tr H Δ₂ := by
  intro g hnet x i a hx hs y j hy hj hb hd
  obtain ⟨k, hkj, hp, ht⟩ := h g hnet x i a hx hs y j hy hj hb
    ((tr.deadline_mono_delta y j _ h12).trans hd)
  exact ⟨k, hkj, hp, ht.trans_le (tr.deadline_mono_delta y k _ h12)⟩

/-- **The base attestation supplier, at the FG delay**, under growing faults: partial synchrony
of the engine log serves the signed attestations of a node honest at its signing cut, at the
protocol FG delay `Δ_F,p = protoFGDelay (pubOf E)`, at every recipient call within the horizon by
a recipient honest at the call. -/
theorem signed_row_service_psync_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) :
    PSyncFGAttTransportAt ⟨S, stock⟩ rho (simTraceAt ⟨S, stock⟩ rho hn)
        (honestKeysAt ⟨S, stock⟩ rho)
      (protoFGDelay (Model.pubOf E)) := by
  intro g hnet x i a hx hsign y j hy hj hb hd
  have hsim := simTraceAt_simulates ⟨S, stock⟩ rho hn hv
  have run := simTraceAt_goldilocksRun ⟨S, stock⟩ rho hn hv
  have hwf := signed_att_wellFormed_at S rho hn hv hx hsign
  have hrel := hsim.att_released x i a hx hsign
  have hτ := run.time_nonneg i
  have hih := signAt_time_le_horizon ⟨S, stock⟩ rho hn hv hsign
  have hrowa : rho.log.fgAtt (attObj a) := (log_fgAtt_iff ⟨S, stock⟩ rho _).mpr (isFGAtt_attObj a)
  induction j using Nat.strong_induction_on with
  | h j ih =>
    obtain ⟨w, hw, heq₀, haw⟩ := deadline_awake_interval_at ⟨S, stock⟩ rho hn hv hy hj
      (hτ.trans (le_max_left _ g))
    have heq : (simTraceAt ⟨S, stock⟩ rho hn).deadline y j
        (max ((simTraceAt ⟨S, stock⟩ rho hn).time i) g)
        (protoFGDelay (Model.pubOf E)) = w + protoFGDelay (Model.pubOf E) := by
      unfold RunTrace.deadline at heq₀ ⊢
      linarith only [heq₀]
    have hgw : max w g = w := max_eq_left ((le_max_right _ g).trans hw)
    have slack : w + E.ΔFG - 1 < w + protoFGDelay (Model.pubOf E) := by
      rw [protoFGDelay_eq]
      exact sub_one_lt _
    have hbound : w + E.ΔFG - 1 ≤ (simTraceAt ⟨S, stock⟩ rho hn).time j :=
      slack.le.trans (heq ▸ hd)
    have held := hnet.fgAtts (rho.key x)
      (attObj a) _ ((releasedFrom_iff ⟨S, stock⟩ rho _ _ _).mp hrel)
      (not_faulty_of_mem_honestKeysAt ⟨S, stock⟩ rho hx le_rfl hih)
      hrowa (rho.key y) w
      ((le_max_left _ g).trans hw) (by rw [hgw]; exact hbound.trans hb)
      (by rw [hgw]; exact hbound.trans hb)
      (by rw [hgw]; exact not_faulty_of_mem_honestKeysAt ⟨S, stock⟩ rho hy hbound (hbound.trans hb))
      (by rw [hgw]; exact fun t hwt htd => haw t hwt (htd.trans hbound))
    rw [hgw] at held
    obtain ⟨k, hkj, hp, ht⟩ := held_att_processed_before_at S rho hn hv hwf held
      (heq ▸ slack) hd
    by_cases hk : (simTraceAt ⟨S, stock⟩ rho hn).time k <
        (simTraceAt ⟨S, stock⟩ rho hn).deadline y k (max ((simTraceAt ⟨S, stock⟩ rho hn).time i) g)
          (protoFGDelay (Model.pubOf E))
    · exact ⟨k, hkj, hp, hk⟩
    · have hkj' : k < j := lt_of_le_of_ne hkj (by intro he; subst k; exact hk ht)
      have hc : (simTraceAt ⟨S, stock⟩ rho hn).IsCall y k := by
        rcases hp with hp | ⟨B, hp, _⟩
        · exact ⟨_, hp⟩
        · exact ⟨_, hp⟩
      obtain ⟨l, hl, hp', ht'⟩ := ih k hkj' (run.antitone (run.time_mono hkj) hy) hc
        ((run.time_mono hkj).trans hb) (le_of_not_gt hk)
      exact ⟨l, hl.trans hkj, hp', ht'⟩

end Consensus.Goldilocks.Obligations.Growing

end
