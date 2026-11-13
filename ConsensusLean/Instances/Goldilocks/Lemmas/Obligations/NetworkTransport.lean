module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Forwarding
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationQueue
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationProvenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ForwardingDecode
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.SentForward
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.DeadlineWake
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OwnProposalPool
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OwnReleaseProcessing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
public import ConsensusLean.Lemmas.Model.SysLog
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Open network transport suppliers

These are goals for the concrete publisher/simulation adapter, not extra premises of
`MeetsObligations`.
The trace parameters remain independent here. `Setup.params` gives protocol delay Δp = Δe: the
engine holds an object strictly before `a + Δe` (by `a + Δe − 1`), which is the node's strict
deadline `a + Δp`. FG attestation service has its own delay `Δ_F` (`PSyncFGAttTransport`): the
engine serves standalone attestations (`isFGAtt`) strictly before its FG delay `ΔF` (the `fgAtts`
clause of `PSync`), and `signed_row_service_psync` serves them at the protocol FG delay
`Δ_F,p = protoFGDelay (pubOf E) = ΔF`.
Every other object (blocks, votes, forwarding and vote-forwarding wrappers) is served strictly
before the bound `Δ`; no statement here claims a block before `ΔF`.
All three suppliers include message, block, acceptance-relay and attestation service. Receipt
alone proves none of the acceptance-relay fields. The finite `ResetService` assembly below
uses the concrete message, block, relay and signed-attestation services; full GST remains separate.
-/

namespace Consensus.Goldilocks.RunTrace

variable {P : Params} {A : NodeAC P} (tr : RunTrace A)

/-- The delivery deadline is monotone in its delivery parameter. -/
theorem deadline_mono_delta (y : Fin P.n) (k : Nat) (τ : Time) {Δ₁ Δ₂ : Time}
    (h : Δ₁ ≤ Δ₂) : tr.deadline y k τ Δ₁ ≤ tr.deadline y k τ Δ₂ := by
  unfold deadline
  exact add_le_add le_rfl h

end Consensus.Goldilocks.RunTrace

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Shape Blocks

/-- The protocol FG delay of the public parameters: `ΔF_p = ΔFG`, the engine FG delay, as the
protocol delay `Δ_p = ΔAC` (`Setup.params`): L0 delivers strictly before the bound
(`CommLog.PSync`), which is the node's deadline `[τ, max(τ, w) + Δ_F)`. -/
def protoFGDelay (pub : Model.Public) : Time := pub.ΔFG

theorem protoFGDelay_eq (pub : Model.Public) : protoFGDelay pub = pub.ΔFG := by rfl

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
  {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (ΔF : Time)

/-- OPEN supplier: PSync supplies GST at the node level. Paper route: actual same-time
publication gives network service by max(send, GST, latest wake)+Δe; authenticated provenance
gives the lower bound, recursive processing gives a call, and the engine's strict deadline gives
the node's strict endpoint.
Acceptance relay additionally requires the parent-first induction, NoColl and chain-state
agreement. Vote admissions need their own source/time provenance; attestations have no lower
bound (`AttDeliveredBy`), so they need none. The adapter
must identify H, node keys, flattened cuts, horizon and awake intervals with the engine run.
It assumes `Δ ≤ Δ_F` (`SyncOn.delta_le`): an attestation admitted from a block leaves in the
block's relay wrapper, which the network serves within `Δ`, not `Δ_F`. -/
def PSyncTransport : Prop :=
  sp.Δ ≤ ΔF → ∀ g, rho.log.PSync rho.point g → tr.GSTRun H ΔF g

/-- OPEN supplier: SyncUntil supplies only recipient-deadline-cut SyncBefore, not SyncRun
with a send-time cutoff. Paper route: a node deadline ≤ b puts its engine service endpoint
strictly below b. Wakes are included in that deadline. All four service fields need
the same publication/processing joins as PSyncTransport. No post-outage service is inferred.
It assumes `Δ ≤ Δ_F` as `PSyncTransport` does, also for the cutoff `deadline … Δ_F ≤ b`. -/
def SyncUntilTransport : Prop :=
  sp.Δ ≤ ΔF → ∀ b, rho.log.SyncUntil rho.point b → tr.SyncBefore H ΔF b

/-- OPEN supplier: global synchrony gives SyncRun on nonnegative send windows. In particular
this does not derive a send-window SyncRun from SyncUntil: a late wake can put its deadline
after the latter's cutoff. The concrete adapter must discharge the same four service leaves. -/
def SyncRunTransport : Prop :=
  sp.Δ ≤ ΔF → rho.log.PSync rho.point 0 → ∀ a b, 0 ≤ a → tr.SyncRun H ΔF a b

/-- Signed FG attestations are processed before the attestation deadline at FG delay `Δ_F` (its own
bound, not the block/message bound `Δ`) at recipient calls within the engine horizon. An earlier
processing of the identical attestation is sufficient; no processing after the source signing is
required. This services an existing signed attestation and does not produce one. It has the shape of
the trusted `AttDeliveredBy`, restricted to signings. -/
def PSyncFGAttTransport : Prop :=
  ∀ g, rho.log.PSync rho.point g →
    ∀ x ∈ H, ∀ i a, tr.SignAt x i a →
      ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.time j ≤ rho.horizon →
        tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
        ∃ k ≤ j, tr.ProcessAttAt y k a ∧
          tr.time k < tr.deadline y k (max (tr.time i) g) ΔF

/-- The signed-attestation service contract, without exposing its definition to consumers. -/
theorem psyncFGAttTransport_iff : PSyncFGAttTransport S rho tr H ΔF ↔
    ∀ g, rho.log.PSync rho.point g →
      ∀ x ∈ H, ∀ i a, tr.SignAt x i a →
        ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.time j ≤ rho.horizon →
          tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
          ∃ k ≤ j, tr.ProcessAttAt y k a ∧
            tr.time k < tr.deadline y k (max (tr.time i) g) ΔF := by
  rfl

/-- **The monotone lift of attestation service**: attestation service at `Δ₁` is attestation service
at every `Δ₂ ≥ Δ₁`, since the attestation deadline is monotone in the delay. It is the only use of
an order between attestation delays here; a consumer lifts the base attestation service at `Δ_F,p`
only to a larger `Δ_F` (`hsSharedUpTo_of_healthy`). -/
theorem PSyncFGAttTransport.mono {Δ₁ Δ₂ : Time} (h : PSyncFGAttTransport S rho tr H Δ₁)
    (h12 : Δ₁ ≤ Δ₂) : PSyncFGAttTransport S rho tr H Δ₂ := by
  intro g hnet x hx i a hs y hy j hj hb hd
  obtain ⟨k, hkj, hp, ht⟩ := h g hnet x hx i a hs y hy j hj hb
    ((tr.deadline_mono_delta y j _ h12).trans hd)
  exact ⟨k, hkj, hp, ht.trans_le (tr.deadline_mono_delta y k _ h12)⟩

/-- The engine log's message class is the Goldilocks attestation class (`isFGAtt`). -/
theorem log_fgAtt_iff {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
    (rho : Model.Run (compiled (goldilocksWith S)) E) (o : Wire (Fintype.card V) S.vote) :
    rho.log.fgAtt o ↔ isFGAtt o := Iff.rfl

/-- A standalone attestation is an attestation. -/
theorem isFGAtt_attObj {binding : VoteBinding} {n : Nat} (a : FG.Att n) :
    isFGAtt (attObj (binding := binding) a) := by
  simp [isFGAtt, IsAttObj, attObj]

/-- A forwarding wrapper is not an attestation. -/
theorem not_isFGAtt_forwardObj {binding : VoteBinding} {sp : SA.SAParams} (origin : Fin sp.n)
    (t : Time) (parent : Option (Wire sp.n binding)) (B : Blk sp) :
    ¬ isFGAtt (forwardObj sp origin t parent B) := by
  simp [forwardObj, isFGAtt, IsAttObj]

/-- An object that decodes as a forwarding wrapper is not an attestation. -/
theorem not_isFGAtt_of_decodeForward {binding : VoteBinding} {sp : SA.SAParams}
    {hs : List (Header Info × Nat)} {o : Wire sp.n binding}
    {q : Fin sp.n × Time × Option (Wire sp.n binding) × Blk sp}
    (h : decodeForward sp hs o = some q) : ¬ isFGAtt o := by
  obtain ⟨origin, t, parent, B⟩ := q
  rw [forwardObj_of_decodeForward hs o origin t parent B h]
  exact not_isFGAtt_forwardObj origin t parent B

/-- Partial synchrony services an actual successful publication strictly before the
protocol endpoint. The start may be a later wake; its entire engine delivery interval
must be awake and inside the horizon. This proves holdings, not a node call or attestation
production. -/
theorem publication_held_psync (hn : 1 ≤ Fintype.card V) (hconst : rho.point.ConstantFaults)
    {g : Time}
    (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r) (hx : rho.key r.origin ∉ rho.faultyAt 0)
    (hrow : ¬ rho.log.fgAtt r.object)
    {y : V} (hy : y ∉ rho.faultyAt 0) {a : Time}
    (ha : (publisherExecution S rho).eventTime r.event ≤ a)
    (hh : max a g + E.ΔAC - 1 ≤ rho.horizon)
    (hawake : rho.point.AwakeOnClosed y a (max a g + E.ΔAC - 1)) :
    rho.log.Held rho.point y r.object (max a g + E.ΔAC - 1) ∧
      max a g + E.ΔAC - 1 < max a g + (S.params (Model.pubOf E) hn).Δ := by
  constructor
  · exact hnet.msgs _ _ _
      ⟨r.event, (publisherExecution S rho).actual_event r hr,
        (publisherExecution S rho).actual_release r hr⟩
      ((rho.point.honestAt_iff_zero hconst _ _).mpr hx) hrow y a ha hh hh
      ((rho.point.honestAt_iff_zero hconst _ _).mpr hy) hawake
  · change max a g + E.ΔAC - 1 < max a g + E.ΔAC
    exact sub_one_lt _

/-- Before an outage, only qualifying recipient deadlines receive service. The protocol
deadline may equal the cutoff: the engine endpoint is still strictly below it. -/
theorem publication_held_syncUntil (hn : 1 ≤ Fintype.card V) (hconst : rho.point.ConstantFaults)
    {b : Time}
    (hnet : rho.log.SyncUntil rho.point b)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r) (hx : rho.key r.origin ∉ rho.faultyAt 0)
    (hrow : ¬ rho.log.fgAtt r.object)
    {y : V} (hy : y ∉ rho.faultyAt 0) {a : Time}
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
    ((rho.point.honestAt_iff_zero hconst _ _).mpr hx) hrow y a ha hlt.le hh
    ((rho.point.honestAt_iff_zero hconst _ _).mpr hy) hawake, hlt⟩

/-- A recipient is awake from its effective send/wake start through its call.
This supplies the closed interval required by engine delivery, not merely wakefulness
at the observation cut. -/
theorem deadline_awake_interval (hn : 1 ≤ Fintype.card V) (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {j : Nat}
    (hj : (simTrace S rho hn).IsCall y j) {τ : Time} (hτ : 0 ≤ τ) :
    ∃ a, τ ≤ a ∧
      (simTrace S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ =
        a + (S.params (Model.pubOf E) hn).Δ ∧
      rho.point.AwakeOnClosed (rho.key y) a ((simTrace S rho hn).time j) := by
  have hr := simTrace_goldilocksRun S rho hn hconst hv
  obtain ⟨a, hτa, heq, hw⟩ := (simTrace S rho hn).deadline_awake_of_call hr.time_mono hj
    (hr.awake_of_call y hy j hj) (fun u => hr.restart_at_wake y hy u _)
    (fun k hk _ => hr.sleep_of_restart y hy k hk) hτ _
  exact ⟨a, hτa, heq, fun u hau huj => (simTrace_awake_of S rho hn hv y hy u (hw u hau huj)).1⟩

/-- Later observation cuts can only increase a recipient's deadline. -/
theorem deadline_mono_cut (hn : 1 ≤ Fintype.card V) (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid)
    (y : Fin (Fintype.card V)) (τ Δ : Time) :
    Monotone (fun j => (simTrace S rho hn).deadline y j τ Δ) :=
  (simTrace S rho hn).deadline_mono_cut_of_time_mono
    (simTrace_goldilocksRun S rho hn hconst hv).time_mono y τ Δ

/-- A real honest publication is held strictly before a qualifying node deadline.
The wake interval and horizon obligations follow from the recipient call and cutoff. -/
theorem publication_held_before_deadline (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {b : Time} (hbh : b ≤ rho.horizon)
    (hnet : rho.log.SyncUntil rho.point b)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r) (hx : rho.key r.origin ∉ rho.faultyAt 0)
    (hrow : ¬ rho.log.fgAtt r.object)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {j : Nat}
    (hj : (simTrace S rho hn).IsCall y j) {τ : Time} (hτ : 0 ≤ τ)
    (ht : (publisherExecution S rho).eventTime r.event = τ)
    (hb : (simTrace S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ ≤ b)
    (hd : (simTrace S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ ≤
      (simTrace S rho hn).time j) :
    ∃ d, rho.log.Held rho.point (rho.key y) r.object d ∧
      d < (simTrace S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ := by
  obtain ⟨a, ha, heq, hw⟩ := deadline_awake_interval S rho hn hconst hv hy hj hτ
  rw [heq] at hb hd ⊢
  have hslack : a + E.ΔAC - 1 < a + (S.params (Model.pubOf E) hn).Δ := by
    change a + E.ΔAC - 1 < a + E.ΔAC
    exact sub_one_lt _
  obtain ⟨hheld, _⟩ := publication_held_syncUntil S rho hn hconst hnet r hr hx hrow
    ((mem_honestKeys_iff S rho y).mp hy)
    (ht ▸ ha) hb ((hslack.le.trans hb).trans hbh)
    (fun u hau hud => hw u hau (hud.trans (hslack.le.trans hd)))
  exact ⟨a + E.ΔAC - 1, hheld, hslack⟩

/-- Network holdings of an authenticated forwarding envelope yield an acceptance
before the observation deadline. The sent case uses actual local acceptance, while
the received case uses recursive forwarding acceptance above the reader's `F`. -/
theorem held_forward_accepted_before (hn : 1 ≤ Fintype.card V) (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {y x : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) (hx : x ∈ honestKeys S rho)
    {j : Nat} {o : Wire (Fintype.card V)} {t d D : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hheld : rho.log.Held rho.point (rho.key y) o d)
    (hdecode : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B))
    (hd : d < D) (hj : D ≤ (simTrace S rho hn).time j)
    (hF : Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho))
      ((simTrace S rho hn).state y j).fg.F B) :
    ∃ k ≤ j, (simTrace S rho hn).AcceptAt y k B ∧ (simTrace S rho hn).time k < D := by
  have hrun := simTrace_goldilocksRun S rho hn hconst hv
  obtain ⟨u, hud, hsource, _⟩ := hheld
  have huD : u < D := hud.trans_lt hd
  have event_before {i : Nat} {ev : Model.Event V (Wire (Fintype.card V))}
      (he : rho.events[i]? = some ev) (hu : ev.time = u) : cutMap S rho hn (i + 1) ≤ j :=
    cutMap_succ_le_of_time_lt S rho hn hv he (hu.trans_lt (huD.trans_le hj))
  have hkey : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply _
  rcases hsource with hs | hr
  · obtain ⟨i, hi, ho⟩ := hs
    obtain ⟨hstamp, k, hk, ha, ht⟩ := sent_forward_accepted S rho hn hv hi ho hdecode
    have hcut : cutMap S rho hn (i + 1) ≤ j := by
      rcases hi with he | ⟨receipt, he⟩ <;> exact event_before he rfl
    exact ⟨k, (hk.trans_le hcut).le, ha, ht ▸ hstamp ▸ huD⟩
  · obtain ⟨i, hi⟩ := hr
    obtain ⟨k, hk, ha, _, ht⟩ := received_forward_accepted_before S rho hn hconst hv hrun hnc
      hi ((mem_honestKeys_iff S rho y).mp hy) (.refl o)
      ((mem_honestKeys_iff S rho x).mp hx) hdecode (event_before hi rfl)
      (by simpa only [hkey] using hF) huD
    exact ⟨k, (hk.trans_le (event_before hi rfl)).le, hkey ▸ ha, ht⟩

/-- Acceptance service is measured at the processing cut, even when later restarts
enlarge the observation deadline. Descent on cuts removes that apparent slack. -/
theorem publication_acceptedBy_syncUntil (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {b : Time} (hbh : b ≤ rho.horizon) (hnet : rho.log.SyncUntil rho.point b)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r) (hx : rho.key r.origin ∉ rho.faultyAt 0)
    {τ : Time} (hτ : 0 ≤ τ) (ht : (publisherExecution S rho).eventTime r.event = τ)
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hdecode : decodeForward (S.params (Model.pubOf E) hn)
      (Model.digests rho.hash r.object) r.object = some (r.origin, τ, p, B))
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {j : Nat}
    (hj : (simTrace S rho hn).IsCall y j)
    (hb : (simTrace S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ ≤ b)
    (hd : (simTrace S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ ≤
      (simTrace S rho hn).time j)
    (hF : Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho))
      ((simTrace S rho hn).state y j).fg.F B) :
    (simTrace S rho hn).BlockAcceptedBy y j τ B := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    obtain ⟨d, hheld, hlt⟩ := publication_held_before_deadline S rho hn hconst hv hbh hnet
      r hr hx (not_isFGAtt_of_decodeForward hdecode) hy hj hτ ht hb hd
    obtain ⟨k, hkj, hacc, htime⟩ := held_forward_accepted_before S rho hn hconst hv hnc
      hy ((mem_honestKeys_iff S rho r.origin).mpr hx) hheld hdecode hlt hd hF
    by_cases hk : (simTrace S rho hn).time k <
        (simTrace S rho hn).deadline y k τ (S.params (Model.pubOf E) hn).Δ
    · exact ⟨k, hkj, hacc, hk⟩
    · have hkj' : k < j := lt_of_le_of_ne hkj (by
        intro heq
        subst k
        exact hk htime)
      have hmono := deadline_mono_cut S rho hn hconst hv y τ (S.params (Model.pubOf E) hn).Δ hkj
      obtain ⟨l, hl, ha, ht'⟩ := ih k hkj' ⟨_, hacc⟩ (hmono.trans hb)
        (le_of_not_gt hk)
        ((Healing.run_F_mono
          (simTrace_goldilocksRun S rho hn hconst hv).toLocalRun hy hkj).trans hF)
      exact ⟨l, hl.trans hkj, ha, ht'⟩

/-- The finite acceptance-relay field. Valid executions supply same-event forwarding
and exact decoding; callers supply only network service and collision freedom. -/
theorem acceptance_relay_syncUntil (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {b : Time} (hbh : b ≤ rho.horizon) (hnet : rho.log.SyncUntil rho.point b)
    {x : Fin (Fintype.card V)} (hx : x ∈ honestKeys S rho) {i : Nat}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hi : (simTrace S rho hn).AcceptAt x i B) (ht : 0 ≤ (simTrace S rho hn).time i)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {j : Nat}
    (hj : (simTrace S rho hn).IsCall y j)
    (hb : (simTrace S rho hn).deadline y j ((simTrace S rho hn).time i)
      (S.params (Model.pubOf E) hn).Δ ≤ b)
    (hd : (simTrace S rho hn).deadline y j ((simTrace S rho hn).time i)
      (S.params (Model.pubOf E) hn).Δ ≤ (simTrace S rho hn).time j)
    (hF : Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho))
      ((simTrace S rho hn).state y j).fg.F B) :
    (simTrace S rho hn).BlockAcceptedBy y j ((simTrace S rho hn).time i) B := by
  obtain ⟨r, p, hr, horg, _, _, htime, _, hdecode⟩ :=
    (forwardAtAcceptance_iff S rho hn _ _ _).mp
      (forwardAtAcceptance S rho hn hconst hv) x hx i B hi
  apply publication_acceptedBy_syncUntil S rho hn hconst hv hnc hbh hnet r hr
    (horg ▸ (mem_honestKeys_iff S rho x).mp hx) ht htime (p := p)
    (by simpa only [horg] using hdecode) hy hj hb hd hF

/-- After GST, an actual publication is held before every qualifying finite deadline.
The recipient may wake after the publication; the call supplies its awake interval. -/
theorem publication_held_before_deadline_psync (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {g : Time} (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r) (hx : rho.key r.origin ∉ rho.faultyAt 0)
    (hrow : ¬ rho.log.fgAtt r.object)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {j : Nat}
    (hj : (simTrace S rho hn).IsCall y j) {τ : Time} (hτ : 0 ≤ τ) (hg : g ≤ τ)
    (ht : (publisherExecution S rho).eventTime r.event = τ)
    (hb : (simTrace S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ ≤ rho.horizon)
    (hd : (simTrace S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ ≤
      (simTrace S rho hn).time j) :
    ∃ d, rho.log.Held rho.point (rho.key y) r.object d ∧
      d < (simTrace S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ := by
  obtain ⟨a, ha, heq, hw⟩ := deadline_awake_interval S rho hn hconst hv hy hj hτ
  rw [heq] at hb hd ⊢
  have hga : max a g = a := max_eq_left (hg.trans ha)
  have hslack : a + E.ΔAC - 1 < a + (S.params (Model.pubOf E) hn).Δ := by
    change a + E.ΔAC - 1 < a + E.ΔAC
    exact sub_one_lt _
  have hheld := (publication_held_psync S rho hn hconst hnet r hr hx hrow
    ((mem_honestKeys_iff S rho y).mp hy) (ht ▸ ha)
    (by rw [hga]; exact hslack.le.trans hb)
    (by rw [hga]; exact fun u hau hud => hw u hau (hud.trans (hslack.le.trans hd)))).1
  rw [hga] at hheld
  exact ⟨a + E.ΔAC - 1, hheld, hslack⟩

/-- Post-GST acceptance service through a finite recipient deadline. Earlier acceptance
cuts inherit the horizon bound, so descent does not assume infinite execution service. -/
theorem publication_acceptedBy_psync (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {g : Time} (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r) (hx : rho.key r.origin ∉ rho.faultyAt 0)
    {τ : Time} (hτ : 0 ≤ τ) (hg : g ≤ τ)
    (ht : (publisherExecution S rho).eventTime r.event = τ)
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hdecode : decodeForward (S.params (Model.pubOf E) hn)
      (Model.digests rho.hash r.object) r.object = some (r.origin, τ, p, B))
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {j : Nat}
    (hj : (simTrace S rho hn).IsCall y j)
    (hb : (simTrace S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ ≤ rho.horizon)
    (hd : (simTrace S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ ≤
      (simTrace S rho hn).time j)
    (hF : Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho))
      ((simTrace S rho hn).state y j).fg.F B) :
    (simTrace S rho hn).BlockAcceptedBy y j τ B := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    obtain ⟨d, hheld, hlt⟩ := publication_held_before_deadline_psync S rho hn hconst hv hnet
      r hr hx (not_isFGAtt_of_decodeForward hdecode) hy hj hτ hg ht hb hd
    obtain ⟨k, hkj, hacc, htime⟩ := held_forward_accepted_before S rho hn hconst hv hnc
      hy ((mem_honestKeys_iff S rho r.origin).mpr hx) hheld hdecode hlt hd hF
    by_cases hk : (simTrace S rho hn).time k <
        (simTrace S rho hn).deadline y k τ (S.params (Model.pubOf E) hn).Δ
    · exact ⟨k, hkj, hacc, hk⟩
    · have hkj' : k < j := lt_of_le_of_ne hkj (by
        intro heq
        subst k
        exact hk htime)
      have hmono := deadline_mono_cut S rho hn hconst hv y τ (S.params (Model.pubOf E) hn).Δ hkj
      obtain ⟨l, hl, ha, ht'⟩ := ih k hkj' ⟨_, hacc⟩ (hmono.trans hb)
        (le_of_not_gt hk)
        ((Healing.run_F_mono
          (simTrace_goldilocksRun S rho hn hconst hv).toLocalRun hy hkj).trans hF)
      exact ⟨l, hl.trans hkj, ha, ht'⟩

/-- The bounded GST acceptance-relay field, with all forwarding obligations discharged.
A recipient call bounded by the horizon supplies the required deadline bound. -/
theorem acceptance_relay_psync (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {g : Time} (hnet : rho.log.PSync rho.point g)
    {x : Fin (Fintype.card V)} (hx : x ∈ honestKeys S rho) {i : Nat}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hi : (simTrace S rho hn).AcceptAt x i B) (ht : 0 ≤ (simTrace S rho hn).time i)
    (hg : g ≤ (simTrace S rho hn).time i)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {j : Nat}
    (hj : (simTrace S rho hn).IsCall y j)
    (hb : (simTrace S rho hn).time j ≤ rho.horizon)
    (hd : (simTrace S rho hn).deadline y j ((simTrace S rho hn).time i)
      (S.params (Model.pubOf E) hn).Δ ≤ (simTrace S rho hn).time j)
    (hF : Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho))
      ((simTrace S rho hn).state y j).fg.F B) :
    (simTrace S rho hn).BlockAcceptedBy y j ((simTrace S rho hn).time i) B := by
  obtain ⟨r, p, hr, horg, _, _, htime, _, hdecode⟩ :=
    (forwardAtAcceptance_iff S rho hn _ _ _).mp
      (forwardAtAcceptance S rho hn hconst hv) x hx i B hi
  exact publication_acceptedBy_psync S rho hn hconst hv hnc hnet r hr
    (horg ▸ (mem_honestKeys_iff S rho x).mp hx)
    ht hg htime (p := p) (by simpa only [horg] using hdecode) hy hj (hd.trans hb) hd hF

/-- Old honest acceptances catch up before the first two-delay snapshot after GST.
The snapshot itself supplies the finite service horizon; no infinite health is assumed. -/
theorem catchRun_of_psync (hn : 1 ≤ Fintype.card V) (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {g : Time} (hnet : rho.log.PSync rho.point g)
    (hawake : ∀ v, v ∉ rho.faultyAt 0 →
      rho.point.AwakeOnClosed v (max g 0) rho.horizon) :
    Healing.CatchRun (simTrace S rho hn) (honestKeys S rho) g
      (2 * (S.params (Model.pubOf E) hn).Δ) := by
  intro x hx i B hi hbefore y hy j hfirst hF
  have hstart := hfirst.1
  change max g 0 + 2 * E.ΔAC ≤ (simTrace S rho hn).time j at hstart
  have hbound : (simTrace S rho hn).time j ≤ rho.horizon + 1 := by
    cases hj : (allCuts S rho hn)[j]? with
    | none => rw [(simTrace_of_getElem?_none S rho hn hj).2]
    | some r =>
      have hl : (simTrace S rho hn).label j ≠ none := by rw [simTrace_label, hj]; simp
      have hh := simTrace_labelled_time_le S rho hn hv hl
      linarith only [hh]
  have hservice : max g 0 + E.ΔAC - 1 ≤ rho.horizon := by
    linarith only [E.ΔAC_pos, hstart, hbound]
  obtain ⟨r, p, hr, horg, _, _, htime, _, hdecode⟩ :=
    (forwardAtAcceptance_iff S rho hn _ _ _).mp
      (forwardAtAcceptance S rho hn hconst hv) x hx i B hi
  have hmax : max (max g 0) g = max g 0 := max_eq_left (le_max_left _ _)
  obtain ⟨hheld, hslack⟩ := publication_held_psync S rho hn hconst hnet r hr
    (horg ▸ (mem_honestKeys_iff S rho x).mp hx)
    (not_isFGAtt_of_decodeForward hdecode) ((mem_honestKeys_iff S rho y).mp hy)
    (a := max g 0) (by rw [htime]; exact hbefore.le)
    (by rw [hmax]; exact hservice)
    (by
      rw [hmax]
      exact fun u hlo hhi => hawake (rho.key y) ((mem_honestKeys_iff S rho y).mp hy)
        u hlo (hhi.trans hservice))
  rw [hmax] at hheld hslack
  have hdeadline : max g 0 + (S.params (Model.pubOf E) hn).Δ ≤
      (simTrace S rho hn).time j := by
    change max g 0 + E.ΔAC ≤ _
    linarith only [E.ΔAC_pos, hstart]
  obtain ⟨k, hkj, hk, hkt⟩ := held_forward_accepted_before S rho hn hconst hv hnc hy hx hheld
    hdecode hslack hdeadline hF
  refine ⟨k, lt_of_le_of_ne hkj ?_, hk⟩
  intro heq
  subst k
  exact (not_lt_of_ge hdeadline) hkt

/-- GST holdings for an arbitrary publication, including pre-GST sources. The effective
time controls the deadline while the publication retains its original source time. -/
theorem publication_held_before_gst_deadline (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {g : Time} (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r) (hx : rho.key r.origin ∉ rho.faultyAt 0)
    (hrow : ¬ rho.log.fgAtt r.object)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {j : Nat}
    (hj : (simTrace S rho hn).IsCall y j) {τ : Time} (hτ : 0 ≤ τ)
    (ht : (publisherExecution S rho).eventTime r.event = τ)
    (hb : (simTrace S rho hn).deadline y j (max τ g)
      (S.params (Model.pubOf E) hn).Δ ≤ rho.horizon)
    (hd : (simTrace S rho hn).deadline y j (max τ g)
      (S.params (Model.pubOf E) hn).Δ ≤ (simTrace S rho hn).time j) :
    ∃ d, rho.log.Held rho.point (rho.key y) r.object d ∧
      d < (simTrace S rho hn).deadline y j (max τ g) (S.params (Model.pubOf E) hn).Δ := by
  obtain ⟨a, ha, heq, hw⟩ := deadline_awake_interval S rho hn hconst hv hy hj
    (hτ.trans (le_max_left τ g))
  rw [heq] at hb hd ⊢
  have hga : max a g = a := max_eq_left ((le_max_right τ g).trans ha)
  have hslack : a + E.ΔAC - 1 < a + (S.params (Model.pubOf E) hn).Δ := by
    change a + E.ΔAC - 1 < a + E.ΔAC
    exact sub_one_lt _
  have hheld := (publication_held_psync S rho hn hconst hnet r hr hx hrow
    ((mem_honestKeys_iff S rho y).mp hy)
    (ht ▸ (le_max_left τ g).trans ha)
    (by rw [hga]; exact hslack.le.trans hb)
    (by rw [hga]; exact fun u hau hud => hw u hau (hud.trans (hslack.le.trans hd)))).1
  rw [hga] at hheld
  exact ⟨a + E.ΔAC - 1, hheld, hslack⟩

/-- Acceptance service for arbitrary publications, including pre-GST sources, uses
the effective max(source, GST) deadline at the acceptance cut. -/
theorem publication_acceptedBy_psync_any (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {g : Time} (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r) (hx : rho.key r.origin ∉ rho.faultyAt 0)
    {τ : Time} (hτ : 0 ≤ τ)
    (ht : (publisherExecution S rho).eventTime r.event = τ)
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hdecode : decodeForward (S.params (Model.pubOf E) hn)
      (Model.digests rho.hash r.object) r.object = some (r.origin, τ, p, B))
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {j : Nat}
    (hj : (simTrace S rho hn).IsCall y j)
    (hb : (simTrace S rho hn).deadline y j (max τ g) (S.params (Model.pubOf E) hn).Δ
      ≤ rho.horizon)
    (hd : (simTrace S rho hn).deadline y j (max τ g) (S.params (Model.pubOf E) hn).Δ
      ≤ (simTrace S rho hn).time j)
    (hF : Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho))
      ((simTrace S rho hn).state y j).fg.F B) :
    (simTrace S rho hn).BlockAcceptedBy y j (max τ g) B := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    obtain ⟨d, hheld, hlt⟩ := publication_held_before_gst_deadline S rho hn hconst hv hnet
      r hr hx (not_isFGAtt_of_decodeForward hdecode) hy hj hτ ht hb hd
    obtain ⟨k, hkj, hacc, htime⟩ := held_forward_accepted_before S rho hn hconst hv hnc
      hy ((mem_honestKeys_iff S rho r.origin).mpr hx) hheld hdecode hlt hd hF
    by_cases hk : (simTrace S rho hn).time k <
        (simTrace S rho hn).deadline y k (max τ g) (S.params (Model.pubOf E) hn).Δ
    · exact ⟨k, hkj, hacc, hk⟩
    · have hkj' : k < j := lt_of_le_of_ne hkj (by
        intro heq
        subst k
        exact hk htime)
      have hmono := deadline_mono_cut S rho hn hconst hv y (max τ g)
        (S.params (Model.pubOf E) hn).Δ hkj
      obtain ⟨l, hl, ha, ht'⟩ := ih k hkj' ⟨_, hacc⟩ (hmono.trans hb)
        (le_of_not_gt hk)
        ((Healing.run_F_mono
          (simTrace_goldilocksRun S rho hn hconst hv).toLocalRun hy hkj).trans hF)
      exact ⟨l, hl.trans hkj, ha, ht'⟩

/-- The acceptance-relay service for an arbitrary honest acceptance, including a pre-GST one.
The effective deadline base is max(acceptance time, GST); the receiver call is in the horizon. -/
theorem acceptance_relay_psync_any (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {g : Time} (hnet : rho.log.PSync rho.point g)
    {x : Fin (Fintype.card V)} (hx : x ∈ honestKeys S rho) {i : Nat}
    {B : Blk (S.params (Model.pubOf E) hn)} (hi : (simTrace S rho hn).AcceptAt x i B)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {j : Nat}
    (hj : (simTrace S rho hn).IsCall y j) (hb : (simTrace S rho hn).time j ≤ rho.horizon)
    (hd : (simTrace S rho hn).deadline y j (max ((simTrace S rho hn).time i) g)
      (S.params (Model.pubOf E) hn).Δ ≤ (simTrace S rho hn).time j)
    (hF : Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho))
      ((simTrace S rho hn).state y j).fg.F B) :
    (simTrace S rho hn).BlockAcceptedBy y j (max ((simTrace S rho hn).time i) g) B := by
  obtain ⟨r, p, hr, horg, _, _, htime, _, hdecode⟩ :=
    (forwardAtAcceptance_iff S rho hn _ _ _).mp
      (forwardAtAcceptance S rho hn hconst hv) x hx i B hi
  exact publication_acceptedBy_psync_any S rho hn hconst hv hnc hnet r hr
    (horg ▸ (mem_honestKeys_iff S rho x).mp hx)
    (simTrace_time_nonneg S rho hn hv i) htime (p := p) (by simpa only [horg] using hdecode)
    hy hj (hd.trans hb) hd hF

/-- Holdings of an honest decoded wrapper give a block call after its source stamp.
Local publication uses the actual acceptance; receipt uses recursive block processing. -/
theorem held_forward_blockCall_before (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {y x : Fin (Fintype.card V)} (hx : x ∈ honestKeys S rho)
    {j : Nat} {o : Wire (Fintype.card V)} {t d D : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hheld : rho.log.Held rho.point (rho.key y) o d)
    (hdecode : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B))
    (hd : d < D) (hj : D ≤ (simTrace S rho hn).time j) :
    ∃ k ≤ j, t ≤ (simTrace S rho hn).time k ∧
      (simTrace S rho hn).BlockCallAt y k B ∧ (simTrace S rho hn).time k < D := by
  obtain ⟨u, hud, hsource, _⟩ := hheld
  have huD : u < D := hud.trans_lt hd
  have hkey : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply _
  have before {k : Nat} (hk : (simTrace S rho hn).time k < D) : k ≤ j := by
    by_contra h
    have htime := simTrace_time_mono S rho hn hv (show j ≤ k by omega)
    exact (not_lt_of_ge (hj.trans htime)) hk
  rcases hsource with hs | hr
  · obtain ⟨i, hi, ho⟩ := hs
    obtain ⟨hstamp, k, -, ha, ht⟩ := sent_forward_accepted S rho hn hv hi ho hdecode
    have hk : (simTrace S rho hn).time k < D := ht ▸ hstamp ▸ huD
    exact ⟨k, before hk, ht.ge, ⟨true, ha⟩, hk⟩
  · obtain ⟨i, hi⟩ := hr
    have htu := received_forward_stamp_le S rho hn hconst hv hi (.refl o)
      ((mem_honestKeys_iff S rho x).mp hx) hdecode
    obtain ⟨k, _, hc, ht⟩ := received_forward_blockCall S rho hn hi (.refl o) hdecode htu
    have hk : (simTrace S rho hn).time k < D := ht ▸ huD
    exact ⟨k, before hk, ht ▸ htu, hkey ▸ hc, hk⟩

/-- A decoded publication receives block service at the processing cut's GST deadline,
including publications before GST. This does not require acceptance at the receiver. -/
theorem publication_blockDeliveredBy_psync (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {g : Time} (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r) (hx : rho.key r.origin ∉ rho.faultyAt 0)
    {τ : Time} (hτ : 0 ≤ τ) (ht : (publisherExecution S rho).eventTime r.event = τ)
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hdecode : decodeForward (S.params (Model.pubOf E) hn)
      (Model.digests rho.hash r.object) r.object = some (r.origin, τ, p, B))
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {j : Nat}
    (hj : (simTrace S rho hn).IsCall y j)
    (hb : (simTrace S rho hn).deadline y j (max τ g)
      (S.params (Model.pubOf E) hn).Δ ≤ rho.horizon)
    (hd : (simTrace S rho hn).deadline y j (max τ g)
      (S.params (Model.pubOf E) hn).Δ ≤ (simTrace S rho hn).time j) :
    (simTrace S rho hn).BlockDeliveredBy y j τ (max τ g) B := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    obtain ⟨d, hheld, hlt⟩ := publication_held_before_gst_deadline S rho hn hconst hv hnet
      r hr hx (not_isFGAtt_of_decodeForward hdecode) hy hj hτ ht hb hd
    obtain ⟨k, hkj, hlo, hcall, htime⟩ := held_forward_blockCall_before S rho hn hconst hv
      ((mem_honestKeys_iff S rho r.origin).mpr hx) hheld hdecode hlt hd
    by_cases hk : (simTrace S rho hn).time k <
        (simTrace S rho hn).deadline y k (max τ g) (S.params (Model.pubOf E) hn).Δ
    · exact ⟨k, hkj, hlo, hcall, hk⟩
    · have hkj' : k < j := lt_of_le_of_ne hkj (by
        intro heq
        subst k
        exact hk htime)
      have hmono := deadline_mono_cut S rho hn hconst hv y (max τ g)
        (S.params (Model.pubOf E) hn).Δ hkj
      obtain ⟨acc, hc⟩ := hcall
      obtain ⟨l, hl, hlo', hc', ht'⟩ := ih k hkj' ⟨_, hc⟩ (hmono.trans hb) (le_of_not_gt hk)
      exact ⟨l, hl.trans hkj, hlo', hc', ht'⟩

/-- An honest own-block call is an acceptance under collision freedom. -/
theorem ownBlockAt_accept (hn : 1 ≤ Fintype.card V) (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {i : Nat}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hown : (simTrace S rho hn).OwnBlockAt y i B) :
    (simTrace S rho hn).AcceptAt y i B := by
  obtain ⟨⟨acc, hc⟩, hpos⟩ := hown
  have run := simTrace_goldilocksRun S rho hn hconst hv
  rcases Compose.blockCall_cases run.toLocalRun hy hc with hg |
    ⟨j, x, rfl, hg, hp, d, p, hdp, hB, hacc, _, _, _⟩
  · exact False.elim (hpos (by
      simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1))
  · obtain ⟨cfg, hr, hst, hs⟩ := Compose.group_step run.toLocalRun hy hg
    have req := SA.interface_requirements (S.params (Model.pubOf E) hn)
      (List (FG.Att (Fintype.card V))) (S.ro _)
    have h := Compose.honest_block_accepted
      (A := goldilocksNode (S.params (Model.pubOf E) hn) (S.ro _))
      (runProposer S rho hn) (digestOf S rho) y
      ⟨req.1, req.2.1, req.2.2.1, req.2.2.2, SA.proposal_payload_valid _ _ _⟩
      run.genesis_root_ok cfg _ _ x hr hs hp d p (by rw [hst]; exact hdp)
    simp only [hst] at h
    have key : Compose.NoCollOn (digestOf S rho)
        (insert B ((simTrace S rho hn).state y j).fg.tree) →
        ∃ fg', ((simTrace S rho hn).state y j).fg.onBlock B = some fg' := by
      rw [hB]
      exact fun hnc => (h.2.2.2.2.2.2 hnc).2
    have hon := key (hnc.mono (Set.insert_subset_iff.2
      ⟨Or.inr ⟨y, j + 2, acc, hc⟩, Compose.tree_subset_run run.toLocalRun hy j⟩))
    have he := hacc.mpr hon
    subst acc
    exact hc

/-- Full finite GST block service for accepted and own blocks, retaining the original
source-time lower bound and the effective max(source,GST) processing deadline. -/
theorem block_service_psync (hn : 1 ≤ Fintype.card V) (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {g : Time} (hnet : rho.log.PSync rho.point g)
    {x : Fin (Fintype.card V)} (hx : x ∈ honestKeys S rho) {i : Nat}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hi : (simTrace S rho hn).AcceptAt x i B ∨ (simTrace S rho hn).OwnBlockAt x i B)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {j : Nat}
    (hj : (simTrace S rho hn).IsCall y j) (hb : (simTrace S rho hn).time j ≤ rho.horizon)
    (hd : (simTrace S rho hn).deadline y j (max ((simTrace S rho hn).time i) g)
      (S.params (Model.pubOf E) hn).Δ ≤ (simTrace S rho hn).time j) :
    (simTrace S rho hn).BlockDeliveredBy y j ((simTrace S rho hn).time i)
      (max ((simTrace S rho hn).time i) g) B := by
  have ha := hi.elim id (ownBlockAt_accept S rho hn hconst hv hnc hx)
  obtain ⟨r, p, hr, horg, _, _, htime, _, hdecode⟩ :=
    (forwardAtAcceptance_iff S rho hn _ _ _).mp
      (forwardAtAcceptance S rho hn hconst hv) x hx i B ha
  exact publication_blockDeliveredBy_psync S rho hn hconst hv hnet r hr
    (horg ▸ (mem_honestKeys_iff S rho x).mp hx)
    (simTrace_time_nonneg S rho hn hv i) htime (p := p)
    (by simpa only [horg] using hdecode) hy hj (hd.trans hb) hd

/-- Honest signatures produce well-formed attestations from reachable chain entry states. -/
theorem signed_att_wellFormed (hn : 1 ≤ Fintype.card V) (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {i : Nat}
    {a : FG.Att (Fintype.card V)} (hs : (simTrace S rho hn).SignAt y i a) :
    a.WellFormed := by
  obtain ⟨C, hc⟩ := hs
  have run := (simTrace_goldilocksRun S rho hn hconst hv).toLocalRun
  have hsign := (run.cutLaw y hy i _ hc).1
  have hr := Compose.fg_reachable run hy i
  obtain ⟨h1, h2, h3⟩ := Store.entry_input hr
    (((simTrace S rho hn).state y i).fg.σ C.root).Th
  exact Compose.createAtt_wellFormed h1 h2 h3 hsign

/-- Every well-formed attestation contained in an actual receipt gets a real processing
call at receipt time, including duplicate attestations already present in the pool. -/
theorem received_att_processAt (hn : 1 ≤ Fintype.card V)
    {i : Nat} {v : V} {receipt : Wire (Fintype.card V)} {t : Time}
    (he : rho.events[i]? = some (.deliver v receipt t)) {a : FG.Att (Fintype.card V)}
    (hwf : a.WellFormed) (hc : Model.Obj.Contains receipt (attObj a)) :
    ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).ProcessAttAt (rho.ownKey v) k a ∧
      (simTrace S rho hn).time k = t := by
  let proposer := runProposer S rho hn
  let dg := digestOf S rho
  let hs : List (Header Info × Nat) := Model.digests rho.hash receipt
  have find : ∀ (os : List (Wire (Fintype.card V)))
      (st : NodeState (goldilocksNode (S.params (Model.pubOf E) hn) (S.ro _))) (sub : Nat),
      attObj a ∈ os → ∃ r ∈ deliverRecs proposer dg hs (rho.ownKey v) t i os st sub,
        r.label = .fg (.attestation a) := by
    intro os
    induction os with
    | nil => intro st sub h; simp at h
    | cons o os ih =>
      intro st sub hm
      rcases List.mem_cons.mp hm with rfl | hm
      · rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _
          (canonEvent_attObj (sp := S.params (Model.pubOf E) hn) (ro := S.ro _) hs a hwf)]
        have hlen : 0 < (groupRecs proposer dg (rho.ownKey v) st t
            (Nat.pair i sub) (.attestation a)).length := by
          simp [length_groupRecs, Node.exec, Node.onAttestation]
        refine ⟨_, List.mem_append_left _ (List.getElem_mem hlen), ?_⟩
        rw [(getElem_groupRecs proposer dg (rho.ownKey v) st t
          (Nat.pair i sub) (.attestation a) 0 hlen).2.2.2.2]
        rfl
      · cases ho : canonEvent (S.params (Model.pubOf E) hn) (S.ro _) hs o with
        | none =>
          rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ ho]
          exact ih st (sub + 1) hm
        | some e =>
          rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ ho]
          obtain ⟨r, hr, hl⟩ := ih (Node.exec proposer dg (rho.ownKey v) st t e).1
            (sub + 1) hm
          exact ⟨r, List.mem_append_right _ hr, hl⟩
  have hmem : attObj a ∈ delivered (S.params (Model.pubOf E) hn) receipt := hc
  obtain ⟨r, hr, hl⟩ := find (delivered (S.params (Model.pubOf E) hn) receipt)
    (stateAt S rho hn v i).node 0 hmem
  obtain ⟨hn', ht, _⟩ := mem_deliverRecs (sp := S.params (Model.pubOf E) hn)
    (ro := S.ro _) proposer dg (rho.ownKey v) hs t i hr
  have hr' : r ∈ eventCuts S rho hn i := by
    rw [eventCuts_deliver S rho hn i v receipt t he]
    exact hr
  obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hr'
  have hk : (allCuts S rho hn)[cutMap S rho hn i + j]? = some r := by
    rw [allCuts_getElem?_add S rho hn i j (List.getElem?_eq_some_iff.mp he).1 hj,
      List.getElem?_eq_getElem hj, heq]
  refine ⟨cutMap S rho hn i + j, ?_, Or.inl ⟨?_, ?_⟩, ?_⟩
  · rw [cutMap_succ]; omega
  · simp only [simTrace_node, hk, Option.elim_some, hn']
  · simp only [simTrace_label, hk, Option.map_some, hl]
  · simp only [simTrace_time, hk, Option.elim_some, ht]

/-- An honest canonical attestation release includes own processing in that tick. -/
theorem released_att_processAt (hn : 1 ≤ Fintype.card V) (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid) {v : V} (hv' : v ∉ rho.faultyAt 0)
    {a : FG.Att (Fintype.card V)} {t : Time}
    (hs : rho.releases v (attObj a) t) :
    ∃ k, (simTrace S rho hn).ProcessAttAt (rho.ownKey v) k a ∧
      (simTrace S rho hn).time k = t := by
  obtain ⟨i, he, ho⟩ := hs
  rcases he with he | ⟨o, he⟩
  · obtain ⟨hp, C, hc⟩ := att_released_inv S rho hn hconst hv hv' he ho
    exact tick_attest_processAt S rho hn he hp hc
  · exact (deliver_not_att S rho hn hv he a ho).elim

/-- Holdings suffice for processing before an observation deadline, even for an old receipt. -/
theorem held_att_processed_before (hn : 1 ≤ Fintype.card V) (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho)
    {a : FG.Att (Fintype.card V)} (hwf : a.WellFormed) {j : Nat} {d D : Time}
    (hh : rho.log.Held rho.point (rho.key y) (attObj a) d)
    (hd : d < D) (hj : D ≤ (simTrace S rho hn).time j) :
    ∃ k ≤ j, (simTrace S rho hn).ProcessAttAt y k a ∧ (simTrace S rho hn).time k < D := by
  obtain ⟨u, hud, hs, _⟩ := hh
  have huD := hud.trans_lt hd
  have hp : ∃ k, (simTrace S rho hn).ProcessAttAt (rho.ownKey (rho.key y)) k a ∧
      (simTrace S rho hn).time k = u := by
    rcases hs with hs | ⟨i, hi⟩
    · exact released_att_processAt S rho hn hconst hv ((mem_honestKeys_iff S rho y).mp hy) hs
    · obtain ⟨k, _, hk, ht⟩ := received_att_processAt S rho hn hi hwf (.refl _)
      exact ⟨k, hk, ht⟩
  obtain ⟨k, hk, ht⟩ := hp
  have hlt : (simTrace S rho hn).time k < D := ht ▸ huD
  refine ⟨k, ?_, ?_, hlt⟩
  · by_contra h
    exact (not_lt_of_ge (hj.trans (simTrace_time_mono S rho hn hv (by omega)))) hlt
  · have he : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply y
    exact he ▸ hk

/-- **The base attestation supplier, at the FG delay.** Partial synchrony of the engine log serves
signed attestations (`fgAtts` clause, FG delay `ΔF`) at bounded recipient calls at the protocol FG
delay `Δ_F,p = protoFGDelay (pubOf E) = ΔF`: the engine holds an attestation by `w + ΔF − 1`,
strictly before the attestation deadline `w + Δ_F,p`. No order between `Δ` and `ΔF` is used: the
recipient's awake interval is the one of its call, and the attestation deadline is the call's
deadline at `Δ_F,p`. An identical earlier processing is enough, and descent supplies the processing
cut's own strict deadline. Every consumer takes attestation service at a parametric `Δ_F` as a
premise (`resetService_of_psync`, `hsSharedUpTo_of_rows`) or lifts this one where an upper envelope
of the FG delay is in scope (`PSyncFGAttTransport.mono`). -/
theorem signed_row_service_psync (hn : 1 ≤ Fintype.card V) (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid) :
    PSyncFGAttTransport S rho (simTrace S rho hn) (honestKeys S rho)
      (protoFGDelay (Model.pubOf E)) := by
  intro g hnet x hx i a hsign y hy j hj hb hd
  have run := simTrace_goldilocksRun S rho hn hconst hv
  have hwf := signed_att_wellFormed S rho hn hconst hv hx hsign
  have hrel := simTrace_att_released S rho hn hconst hv run x hx i a hsign
  have hτ := simTrace_time_nonneg S rho hn hv i
  have hrowa : rho.log.fgAtt (attObj a) := (log_fgAtt_iff S rho _).mpr (isFGAtt_attObj a)
  induction j using Nat.strong_induction_on with
  | h j ih =>
    obtain ⟨w, hw, heq₀, haw⟩ := deadline_awake_interval S rho hn hconst hv hy hj
      (hτ.trans (le_max_left _ g))
    have heq : (simTrace S rho hn).deadline y j (max ((simTrace S rho hn).time i) g)
        (protoFGDelay (Model.pubOf E)) = w + protoFGDelay (Model.pubOf E) := by
      unfold RunTrace.deadline at heq₀ ⊢
      linarith only [heq₀]
    have hgw : max w g = w := max_eq_left ((le_max_right _ g).trans hw)
    have slack : w + E.ΔFG - 1 < w + protoFGDelay (Model.pubOf E) := by
      change w + E.ΔFG - 1 < w + E.ΔFG
      exact sub_one_lt _
    have hbound : w + E.ΔFG - 1 ≤ (simTrace S rho hn).time j :=
      slack.le.trans (heq ▸ hd)
    have held := hnet.fgAtts (rho.key x)
      (attObj a) _ ((releasedFrom_iff S rho _ _ _).mp hrel)
      ((rho.point.honestAt_iff_zero hconst _ _).mpr ((mem_honestKeys_iff S rho x).mp hx))
      hrowa (rho.key y) w
      ((le_max_left _ g).trans hw) (by rw [hgw]; exact hbound.trans hb)
      (by rw [hgw]; exact hbound.trans hb)
      ((rho.point.honestAt_iff_zero hconst _ _).mpr ((mem_honestKeys_iff S rho y).mp hy))
      (by rw [hgw]; exact fun t hwt htd => haw t hwt (htd.trans hbound))
    rw [hgw] at held
    obtain ⟨k, hkj, hp, ht⟩ := held_att_processed_before S rho hn hconst hv hy hwf held
      (heq ▸ slack) hd
    by_cases hk : (simTrace S rho hn).time k <
        (simTrace S rho hn).deadline y k (max ((simTrace S rho hn).time i) g)
          (protoFGDelay (Model.pubOf E))
    · exact ⟨k, hkj, hp, hk⟩
    · have hkj' : k < j := lt_of_le_of_ne hkj (by intro he; subst k; exact hk ht)
      have hc : (simTrace S rho hn).IsCall y k := by
        rcases hp with hp | ⟨B, hp, _⟩
        · exact ⟨_, hp⟩
        · exact ⟨_, hp⟩
      obtain ⟨l, hl, hp', ht'⟩ := ih k hkj' hc
        ((simTrace_time_mono S rho hn hv hkj).trans hb) (le_of_not_gt hk)
      exact ⟨l, hl.trans hkj, hp', ht'⟩

/-- One protocol-delay publication tail supplies holdings strictly before a ready read. -/
theorem publication_held_ready_tail (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) {g : Time}
    (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r) (hx : rho.key r.origin ∉ rho.faultyAt 0)
    (hrow : ¬ rho.log.fgAtt r.object)
    {y : Fin (Fintype.card V)} {t c : Time}
    (hy : Regimes.ReadyAt (simTrace S rho hn) (honestKeys S rho) c y t)
    (ht : t ≤ rho.horizon)
    (hbudget : max (max ((publisherExecution S rho).eventTime r.event) g) 0 +
      (S.params (Model.pubOf E) hn).Δ ≤ t)
    (hc : (S.params (Model.pubOf E) hn).Δ ≤ c + 1) :
    ∃ d, rho.log.Held rho.point (rho.key y) r.object d ∧ d < t := by
  let a := max (max (max ((publisherExecution S rho).eventTime r.event) g) 0) (t - c - 1)
  have hga : max a g = a := max_eq_left (by dsimp [a, Time]; omega)
  have hlt : a + E.ΔAC - 1 < t := by
    change max (max ((publisherExecution S rho).eventTime r.event) g) 0 + E.ΔAC ≤ t
      at hbudget
    change E.ΔAC ≤ c + 1 at hc
    dsimp [a, Time] at *; omega
  have hw : rho.point.AwakeOnClosed (rho.key y) a (a + E.ΔAC - 1) := by
    intro u hau hud
    have h := hy.2 u (by dsimp [a, Time] at *; omega) (hud.trans hlt.le)
    exact ((awakeAt_iff S rho hn y u).mp ((simTrace_awake_iff S rho hn y u).mp h)).1
  have hh := (publication_held_psync S rho hn hconst hnet r hr hx hrow
    ((mem_honestKeys_iff S rho y).mp hy.1)
    (show (publisherExecution S rho).eventTime r.event ≤ a by dsimp [a, Time]; omega)
    (by rw [hga]; exact hlt.le.trans ht) (by rw [hga]; exact hw)).1
  rw [hga] at hh
  exact ⟨a + E.ΔAC - 1, hh, hlt⟩

/-- Votes in an actual own-proposal payload were already pooled before its AC block cut. -/
theorem own_proposal_payload_pooled (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {j : Nat} {t : Time} {x : Nat}
    (hg : (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho) y j t (.tick x))
    {d : DutyHead (Fintype.card V) (List (FG.Att (Fintype.card V)))
      (SA.Payload (Fintype.card V))} {p : SA.Payload (Fintype.card V)}
    (hd : (Node.acProposal
      (Node.tickStep (runProposer S rho hn) (digestOf S rho) y
        ((simTrace S rho hn).state y j) t x .acTick).1 t).2.2 = some (d, p))
    (hprop : ∃ ℓp, (simTrace S rho hn).CallAt y (j + 1) (.ac ℓp) ∧ ℓp.call = .proposal)
    (hfg : ∃ B, (simTrace S rho hn).CallAt y (j + 2) (.fg (.block B true)))
    {m : SA.Vote (Fintype.card V)} (hm : m ∈ p.1) :
    m ∈ ((simTrace S rho hn).state y (j + 3)).ac.pool m.slot :=
  Growing.own_proposal_payload_pooled_run (simTrace_goldilocksRun S rho hn hconst hv) hy hg hd
    hprop hfg hm

/-- A sending or freshly admitting source processes its vote at that same time.
Recursive delivery processing may occur later in the event, never at a later time. -/
theorem sendOrAdmit_process_same_time (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {i : Nat}
    {m : SA.Vote (Fintype.card V)} (hsource : (simTrace S rho hn).SendOrAdmitAt y i m) :
    ∃ k, (simTrace S rho hn).projAC.ProcessAt y k m ∧
      (simTrace S rho hn).time k = (simTrace S rho hn).time i := by
  have hr := simTrace_goldilocksRun S rho hn hconst hv
  have hproj : (simTrace S rho hn).projAC.SendOrAdmit y i m := by
    obtain ⟨ℓ, hc, hs⟩ := hsource
    refine ⟨ℓ, Compose.projAC_callAt.mpr hc, ?_⟩
    rw [Compose.projAC_state hr.toLocalRun hy]
    exact hs
  rcases Compose.sendOrAdmit_forward_source hr hy hproj with hem | ⟨hc, hf, _⟩
  · obtain ⟨ℓ, hc, he⟩ := hem
    exact ⟨i, ⟨ℓ, Compose.projAC_callAt.mpr hc, Or.inr he⟩, rfl⟩
  rcases hc with ⟨ℓ, hc, hm⟩ | ⟨ℓ, B, hc, hb, hm⟩
  · exact ⟨i, ⟨ℓ, Compose.projAC_callAt.mpr hc, Or.inl hm⟩, rfl⟩
  rcases acBlock_cut_cases S rho hn hc hb hm with h | ⟨n, v, t, he, hpublic, hkey, hlo, hhi, ht⟩
  · exact h
  have hvhon : v ∉ rho.faultyAt 0 := by
    have : rho.key y = v := by rw [← hkey]; exact rho.key.apply_symm_apply v
    exact this ▸ (mem_honestKeys_iff S rho y).mp hy
  obtain ⟨hengine, hlen⟩ := simTrace_tick_public_group S rho hn hconst hv v hvhon n t he hpublic
  rw [hkey] at hengine hlen
  exact (hf (acBlock_vote_pooled_in_tick hr hy hengine hlo (by omega) ht hc hb hm)).elim

/-- A first-release vote envelope reaches a different honest node under PSync.
The release time is the lower bound; GST changes only the service deadline. -/
theorem vote_message_service_psync_other (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {g : Time} (hnet : rho.log.PSync rho.point g)
    {source : Nat} {x y : Fin (Fintype.card V)} {τ : Time} {m : SA.Vote (Fintype.card V)}
    (hx : x ∈ honestKeys S rho) (hy : y ∈ honestKeys S rho) (hne : y ≠ x)
    (hτ : 0 ≤ τ) (hs : rho.SendsAt (rho.key x) source τ)
    (hrel : Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m] ∈
      rho.releasesAt source)
    (hfirst : ∀ i < source,
      Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m] ∉
        rho.releasesAt i)
    {j : Nat} (hj : (simTrace S rho hn).IsCall y j)
    (hb : (simTrace S rho hn).time j ≤ rho.horizon)
    (hd : (simTrace S rho hn).projAC.deadline y j (max τ g) ≤ (simTrace S rho hn).time j) :
    ∃ k ≤ j, τ ≤ (simTrace S rho hn).time k ∧
      (simTrace S rho hn).projAC.ProcessAt y k m ∧
      (simTrace S rho hn).time k < (simTrace S rho hn).projAC.deadline y k (max τ g) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    obtain ⟨a, ha, heq, hw⟩ := deadline_awake_interval S rho hn hconst hv hy hj
      (hτ.trans (le_max_left _ g))
    have heq' : (simTrace S rho hn).projAC.deadline y j (max τ g) =
        a + (S.params (Model.pubOf E) hn).Δ := by
      rw [Compose.projAC_deadline]
      exact heq
    have hslack : a + E.ΔAC - 1 < a + (S.params (Model.pubOf E) hn).Δ := by
      change a + E.ΔAC - 1 < a + E.ΔAC
      simp only [Time]; omega
    have hbound := hslack.le.trans (heq' ▸ hd)
    have hag : max a g = a := max_eq_left ((le_max_right _ _).trans ha)
    have hheld := hnet.msgs (rho.key x)
      _ τ ⟨source, hs, hrel⟩
      ((rho.point.honestAt_iff_zero hconst _ _).mpr ((mem_honestKeys_iff S rho x).mp hx))
      (by simp [log_fgAtt_iff, isFGAtt, IsAttObj]) (rho.key y)
      a ((le_max_left _ _).trans ha) (by rw [hag]; exact hbound.trans hb)
      (by rw [hag]; exact hbound.trans hb)
      ((rho.point.honestAt_iff_zero hconst _ _).mpr ((mem_honestKeys_iff S rho y).mp hy))
      (by rw [hag]; exact fun u hau hud => hw u hau (hud.trans hbound))
    rcases held_voteForward_source_or_process S rho hn hconst hv
      ((mem_honestKeys_iff S rho x).mp hx) hs hfirst hheld with
      h | ⟨k, hp, hlo, hhi⟩
    · exact False.elim (hne h)
    rw [hag] at hhi
    have htime : (simTrace S rho hn).time k < (simTrace S rho hn).projAC.deadline y j
        (max τ g) := by rw [heq']; exact hhi.trans_lt hslack
    have hkj : k < j := by
      by_contra h
      have := simTrace_time_mono S rho hn hv (Nat.le_of_not_gt h)
      linarith only [this, htime, hd]
    by_cases hk : (simTrace S rho hn).time k <
        (simTrace S rho hn).projAC.deadline y k (max τ g)
    · exact ⟨k, hkj.le, hlo, hp, hk⟩
    · obtain ⟨l, hl, hlo', hp', hlt⟩ := ih k hkj
        ⟨_, Compose.projAC_callAt.mp hp.choose_spec.1⟩
        ((simTrace_time_mono S rho hn hv hkj.le).trans hb) (le_of_not_gt hk)
      exact ⟨l, hl.trans hkj.le, hlo', hp', hlt⟩

/-- Honest SA sends and fresh admissions are processed within the PSync deadline.
The sender processes at the source time; other nodes use the first-release envelope. -/
theorem message_service_psync (hn : 1 ≤ Fintype.card V) (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid)
    {g : Time} (hnet : rho.log.PSync rho.point g)
    {x : Fin (Fintype.card V)} (hx : x ∈ honestKeys S rho) {i : Nat}
    {m : SA.Vote (Fintype.card V)} (hi : (simTrace S rho hn).SendOrAdmitAt x i m)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {j : Nat}
    (hj : (simTrace S rho hn).IsCall y j) (hb : (simTrace S rho hn).time j ≤ rho.horizon)
    (hd : (simTrace S rho hn).deadline y j (max ((simTrace S rho hn).time i) g)
      (S.params (Model.pubOf E) hn).Δ ≤ (simTrace S rho hn).time j) :
    (simTrace S rho hn).MsgDeliveredBy y j ((simTrace S rho hn).time i)
      (max ((simTrace S rho hn).time i) g) m := by
  have hr := simTrace_goldilocksRun S rho hn hconst hv
  by_cases heq : y = x
  · subst y
    obtain ⟨k, hp, ht⟩ := sendOrAdmit_process_same_time S rho hn hconst hv hx hi
    have hlt (l : Nat) : (simTrace S rho hn).time i <
        (simTrace S rho hn).deadline x l (max ((simTrace S rho hn).time i) g)
          (S.params (Model.pubOf E) hn).Δ := by
      unfold RunTrace.deadline
      change _ < Option.elim _ _ _ + E.ΔAC
      have := E.ΔAC_pos
      cases (simTrace S rho hn).lastWake x l with
      | bot => change _ < max _ g + E.ΔAC; simp only [Time] at *; omega
      | coe w => change _ < max (max _ g) w + E.ΔAC; simp only [Time] at *; omega
    refine ⟨k, ?_, ht.ge, ?_, ht ▸ hlt k⟩
    · by_contra h
      have := simTrace_time_mono S rho hn hv (Nat.le_of_not_ge h)
      have := hlt j
      linarith
    · obtain ⟨l, hc, hm⟩ := hp
      exact hm.elim (fun h => Or.inl ⟨l, Compose.projAC_callAt.mp hc, h⟩)
        (fun h => Or.inr ⟨l, Compose.projAC_callAt.mp hc, h⟩)
  · have hproj : (simTrace S rho hn).projAC.SendOrAdmit x i m := by
      obtain ⟨l, hc, hs⟩ := hi
      refine ⟨l, Compose.projAC_callAt.mpr hc, ?_⟩
      rw [Compose.projAC_state hr.toLocalRun hx]
      exact hs
    obtain ⟨source, _, _, hs, hrel, hfirst⟩ := simTrace_vote_forwarded S rho hn hconst hv x hx i m
      (Compose.sendOrAdmit_forward_source hr hx hproj)
    obtain ⟨k, hkj, hlo, hp, hlt⟩ := vote_message_service_psync_other S rho hn hconst hv hnet hx hy
      heq (simTrace_time_nonneg S rho hn hv i) hs hrel hfirst hj hb
      (by rw [Compose.projAC_deadline]; exact hd)
    refine ⟨k, hkj, hlo, ?_, ?_⟩
    · obtain ⟨l, hc, hm⟩ := hp
      exact hm.elim (fun h => Or.inl ⟨l, Compose.projAC_callAt.mp hc, h⟩)
        (fun h => Or.inr ⟨l, Compose.projAC_callAt.mp hc, h⟩)
    · rw [Compose.projAC_deadline] at hlt
      exact hlt

/-- The finite valid engine run supplies every reset-service field, with attestation service at a
parametric `Δ_F` as a premise (`hrow`). Actual receiver calls lie within the engine horizon,
including the unguarded AC fields; the message, block and relay fields are at `Δ`. The
positivity `hΔF : 0 < Δ_F` fills the field `ResetService.deltaF` (Healing/Retention/Defs); no
order between `Δ` and `Δ_F` is used. -/
theorem resetService_of_psync (hn : 1 ≤ Fintype.card V) (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {g ΔF : Time} (hnet : rho.log.PSync rho.point g)
    (hrow : PSyncFGAttTransport S rho (simTrace S rho hn) (honestKeys S rho) ΔF)
    (hΔF : 0 < ΔF) :
    Healing.ResetService (simTrace S rho hn) (honestKeys S rho) g ΔF rho.horizon := by
  have bound {y j} (hj : (simTrace S rho hn).IsCall y j) :
      (simTrace S rho hn).time j ≤ rho.horizon := by
    obtain ⟨l, _, hl⟩ := hj
    exact simTrace_labelled_time_le S rho hn hv (by rw [hl]; simp)
  refine ⟨hΔF, ?_, ?_, ?_, ?_⟩
  · intro x hx i m hi y hy j hj hd
    exact message_service_psync S rho hn hconst hv hnet hx hi hy hj (bound hj) hd
  · intro x hx i B hi y hy j hj hd
    exact block_service_psync S rho hn hconst hv hnc hnet hx hi hy hj (bound hj) hd
  · intro x hx i B hi hg y hy j hj hd hF
    rw [max_eq_left hg] at hd ⊢
    exact acceptance_relay_psync S rho hn hconst hv hnc hnet hx hi
      (simTrace_time_nonneg S rho hn hv i) hg hy hj (bound hj) hd hF
  · exact (psyncFGAttTransport_iff S rho _ _ _).mp hrow g hnet

end Consensus.Goldilocks.Obligations
