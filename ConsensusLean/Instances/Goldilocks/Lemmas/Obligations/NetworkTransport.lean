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
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Open network transport suppliers

These are goals for the concrete publisher/simulation adapter, not extra premises of
`MeetsObligations`.
The trace parameters remain independent here. `Setup.params` gives protocol delay Δp = Δe: the
engine holds an object strictly before `a + Δe` (by `a + Δe − 1`), which is the node's strict
deadline `a + Δp`. FG attestation service has its own delay `Δ_F`: the engine serves
standalone attestations (`isFGAtt`) strictly before its FG delay `ΔF` (the `fgAtts` clause of
`PSync`), at the protocol FG delay `Δ_F,p = protoFGDelay (pubOf E) = ΔF`.
Every other object (blocks, votes, forwarding and vote-forwarding wrappers) is served strictly
before the bound `Δ`; no statement here claims a block before `ΔF`.
All three suppliers include message, block, acceptance-relay and attestation service. Receipt
alone proves none of the acceptance-relay fields. The finite services up to a synchronous horizon
(`publication_held_syncUntil`, `acceptance_relay_syncUntil`) are proved here; full GST remains
separate.
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

/-- Before an outage, only qualifying recipient deadlines receive service. The protocol
deadline may equal the cutoff: the engine endpoint is still strictly below it. -/
theorem publication_held_syncUntil (hn : 1 ≤ Fintype.card V) (hconst : rho.point.ConstantFaults)
    {b : Time}
    (hnet : rho.log.SyncUntil rho.point b)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution ⟨S, stock⟩ rho).actual r) (hx : rho.key r.origin ∉ rho.faultyAt 0)
    (hrow : ¬ rho.log.fgAtt r.object)
    {y : V} (hy : y ∉ rho.faultyAt 0) {a : Time}
    (ha : (publisherExecution ⟨S, stock⟩ rho).eventTime r.event ≤ a)
    (hb : a + (S.params (Model.pubOf E) hn).Δ ≤ b)
    (hh : a + E.ΔAC - 1 ≤ rho.horizon)
    (hawake : rho.point.AwakeOnClosed y a (a + E.ΔAC - 1)) :
    rho.log.Held rho.point y r.object (a + E.ΔAC - 1) ∧ a + E.ΔAC - 1 < b := by
  have hlt : a + E.ΔAC - 1 < b := by
    change a + E.ΔAC ≤ b at hb
    exact (sub_one_lt _).trans_le hb
  exact ⟨hnet.msgs _ _ _
    ⟨r.event, (publisherExecution ⟨S, stock⟩ rho).actual_event r hr,
      (publisherExecution ⟨S, stock⟩ rho).actual_release r hr⟩
    ((rho.point.honestAt_iff_zero hconst _ _).mpr hx) hrow y a ha hlt.le hh
    ((rho.point.honestAt_iff_zero hconst _ _).mpr hy) hawake, hlt⟩

/-- A recipient is awake from its effective send/wake start through its call.
This supplies the closed interval required by engine delivery, not merely wakefulness
at the observation cut. -/
theorem deadline_awake_interval (hn : 1 ≤ Fintype.card V) (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys ⟨S, stock⟩ rho) {j : Nat}
    (hj : (simTrace ⟨S, stock⟩ rho hn).IsCall y j) {τ : Time} (hτ : 0 ≤ τ) :
    ∃ a, τ ≤ a ∧
      (simTrace ⟨S, stock⟩ rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ =
        a + (S.params (Model.pubOf E) hn).Δ ∧
      rho.point.AwakeOnClosed (rho.key y) a ((simTrace ⟨S, stock⟩ rho hn).time j) := by
  have hr := simTrace_goldilocksRun S rho hn hconst hv
  obtain ⟨a, hτa, heq, hw⟩ := (simTrace ⟨S, stock⟩ rho hn).deadline_awake_of_call hr.time_mono hj
    (hr.awake_of_call y hy j hj) (fun u => hr.restart_at_wake y hy u _)
    (fun k hk _ => hr.sleep_of_restart y hy k hk) hτ _
  exact ⟨a, hτa, heq, fun u hau huj =>
      (simTrace_awake_of ⟨S, stock⟩ rho hn hv y hy u (hw u hau huj)).1⟩

/-- Later observation cuts can only increase a recipient's deadline. -/
theorem deadline_mono_cut (hn : 1 ≤ Fintype.card V) (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid)
    (y : Fin (Fintype.card V)) (τ Δ : Time) :
    Monotone (fun j => (simTrace ⟨S, stock⟩ rho hn).deadline y j τ Δ) :=
  (simTrace ⟨S, stock⟩ rho hn).deadline_mono_cut_of_time_mono
    (simTrace_goldilocksRun S rho hn hconst hv).time_mono y τ Δ

/-- A real honest publication is held strictly before a qualifying node deadline.
The wake interval and horizon obligations follow from the recipient call and cutoff. -/
theorem publication_held_before_deadline (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {b : Time} (hbh : b ≤ rho.horizon)
    (hnet : rho.log.SyncUntil rho.point b)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution ⟨S, stock⟩ rho).actual r) (hx : rho.key r.origin ∉ rho.faultyAt 0)
    (hrow : ¬ rho.log.fgAtt r.object)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys ⟨S, stock⟩ rho) {j : Nat}
    (hj : (simTrace ⟨S, stock⟩ rho hn).IsCall y j) {τ : Time} (hτ : 0 ≤ τ)
    (ht : (publisherExecution ⟨S, stock⟩ rho).eventTime r.event = τ)
    (hb : (simTrace ⟨S, stock⟩ rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ ≤ b)
    (hd : (simTrace ⟨S, stock⟩ rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ ≤
      (simTrace ⟨S, stock⟩ rho hn).time j) :
    ∃ d, rho.log.Held rho.point (rho.key y) r.object d ∧
      d < (simTrace ⟨S, stock⟩ rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ := by
  obtain ⟨a, ha, heq, hw⟩ := deadline_awake_interval S rho hn hconst hv hy hj hτ
  rw [heq] at hb hd ⊢
  have hslack : a + E.ΔAC - 1 < a + (S.params (Model.pubOf E) hn).Δ := by
    change a + E.ΔAC - 1 < a + E.ΔAC
    exact sub_one_lt _
  obtain ⟨hheld, _⟩ := publication_held_syncUntil S rho hn hconst hnet r hr hx hrow
    ((mem_honestKeys_iff ⟨S, stock⟩ rho y).mp hy)
    (ht ▸ ha) hb ((hslack.le.trans hb).trans hbh)
    (fun u hau hud => hw u hau (hud.trans (hslack.le.trans hd)))
  exact ⟨a + E.ΔAC - 1, hheld, hslack⟩

/-- Network holdings of an authenticated forwarding envelope yield an acceptance
before the observation deadline. The sent case uses actual local acceptance, while
the received case uses recursive forwarding acceptance above the reader's `F`. -/
theorem held_forward_accepted_before (hn : 1 ≤ Fintype.card V) (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf ⟨S, stock⟩ rho) (simTrace ⟨S, stock⟩ rho hn))
    {y x : Fin (Fintype.card V)} (hy : y ∈ honestKeys ⟨S, stock⟩ rho)
        (hx : x ∈ honestKeys ⟨S, stock⟩ rho)
    {j : Nat} {o : Wire (Fintype.card V)} {t d D : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hheld : rho.log.Held rho.point (rho.key y) o d)
    (hdecode : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B))
    (hd : d < D) (hj : D ≤ (simTrace ⟨S, stock⟩ rho hn).time j)
    (hF : Anc ((simTrace ⟨S, stock⟩ rho hn).HonestBlocks (honestKeys ⟨S, stock⟩ rho))
      ((simTrace ⟨S, stock⟩ rho hn).state y j).fg.F B) :
    ∃ k ≤ j, (simTrace ⟨S, stock⟩ rho hn).AcceptAt y k B ∧ (simTrace ⟨S, stock⟩ rho hn).time k <
        D := by
  have hrun := simTrace_goldilocksRun S rho hn hconst hv
  obtain ⟨u, hud, hsource, _⟩ := hheld
  have huD : u < D := hud.trans_lt hd
  have event_before {i : Nat} {ev : Model.Event V (Wire (Fintype.card V))}
      (he : rho.events[i]? = some ev) (hu : ev.time = u) : cutMap ⟨S, stock⟩ rho hn (i + 1) ≤ j :=
    cutMap_succ_le_of_time_lt ⟨S, stock⟩ rho hn hv he (hu.trans_lt (huD.trans_le hj))
  have hkey : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply _
  rcases hsource with hs | hr
  · obtain ⟨i, hi, ho⟩ := hs
    obtain ⟨hstamp, k, hk, ha, ht⟩ := sent_forward_accepted ⟨S, stock⟩ rho hn hv hi ho hdecode
    have hcut : cutMap ⟨S, stock⟩ rho hn (i + 1) ≤ j := by
      rcases hi with he | ⟨receipt, he⟩ <;> exact event_before he rfl
    exact ⟨k, (hk.trans_le hcut).le, ha, ht ▸ hstamp ▸ huD⟩
  · obtain ⟨i, hi⟩ := hr
    obtain ⟨k, hk, ha, _, ht⟩ := received_forward_accepted_before ⟨S, stock⟩ rho hn hconst hv
        hrun hnc
      hi ((mem_honestKeys_iff ⟨S, stock⟩ rho y).mp hy) (.refl o)
      ((mem_honestKeys_iff ⟨S, stock⟩ rho x).mp hx) hdecode (event_before hi rfl)
      (by erw [hkey]; exact hF) huD
    exact ⟨k, (hk.trans_le (event_before hi rfl)).le, hkey ▸ ha, ht⟩

/-- Acceptance service is measured at the processing cut, even when later restarts
enlarge the observation deadline. Descent on cuts removes that apparent slack. -/
theorem publication_acceptedBy_syncUntil (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf ⟨S, stock⟩ rho) (simTrace ⟨S, stock⟩ rho hn))
    {b : Time} (hbh : b ≤ rho.horizon) (hnet : rho.log.SyncUntil rho.point b)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution ⟨S, stock⟩ rho).actual r) (hx : rho.key r.origin ∉ rho.faultyAt 0)
    {τ : Time} (hτ : 0 ≤ τ) (ht : (publisherExecution ⟨S, stock⟩ rho).eventTime r.event = τ)
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hdecode : decodeForward (S.params (Model.pubOf E) hn)
      (Model.digests rho.hash r.object) r.object = some (r.origin, τ, p, B))
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys ⟨S, stock⟩ rho) {j : Nat}
    (hj : (simTrace ⟨S, stock⟩ rho hn).IsCall y j)
    (hb : (simTrace ⟨S, stock⟩ rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ ≤ b)
    (hd : (simTrace ⟨S, stock⟩ rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ ≤
      (simTrace ⟨S, stock⟩ rho hn).time j)
    (hF : Anc ((simTrace ⟨S, stock⟩ rho hn).HonestBlocks (honestKeys ⟨S, stock⟩ rho))
      ((simTrace ⟨S, stock⟩ rho hn).state y j).fg.F B) :
    (simTrace ⟨S, stock⟩ rho hn).BlockAcceptedBy y j τ B := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    obtain ⟨d, hheld, hlt⟩ := publication_held_before_deadline S rho hn hconst hv hbh hnet
      r hr hx (not_isFGAtt_of_decodeForward hdecode) hy hj hτ ht hb hd
    obtain ⟨k, hkj, hacc, htime⟩ := held_forward_accepted_before S rho hn hconst hv hnc
      hy ((mem_honestKeys_iff ⟨S, stock⟩ rho r.origin).mpr hx) hheld hdecode hlt hd hF
    by_cases hk : (simTrace ⟨S, stock⟩ rho hn).time k <
        (simTrace ⟨S, stock⟩ rho hn).deadline y k τ (S.params (Model.pubOf E) hn).Δ
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
    (hnc : Compose.NoCollRun (digestOf ⟨S, stock⟩ rho) (simTrace ⟨S, stock⟩ rho hn))
    {b : Time} (hbh : b ≤ rho.horizon) (hnet : rho.log.SyncUntil rho.point b)
    {x : Fin (Fintype.card V)} (hx : x ∈ honestKeys ⟨S, stock⟩ rho) {i : Nat}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hi : (simTrace ⟨S, stock⟩ rho hn).AcceptAt x i B)
        (ht : 0 ≤ (simTrace ⟨S, stock⟩ rho hn).time i)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys ⟨S, stock⟩ rho) {j : Nat}
    (hj : (simTrace ⟨S, stock⟩ rho hn).IsCall y j)
    (hb : (simTrace ⟨S, stock⟩ rho hn).deadline y j ((simTrace ⟨S, stock⟩ rho hn).time i)
      (S.params (Model.pubOf E) hn).Δ ≤ b)
    (hd : (simTrace ⟨S, stock⟩ rho hn).deadline y j ((simTrace ⟨S, stock⟩ rho hn).time i)
      (S.params (Model.pubOf E) hn).Δ ≤ (simTrace ⟨S, stock⟩ rho hn).time j)
    (hF : Anc ((simTrace ⟨S, stock⟩ rho hn).HonestBlocks (honestKeys ⟨S, stock⟩ rho))
      ((simTrace ⟨S, stock⟩ rho hn).state y j).fg.F B) :
    (simTrace ⟨S, stock⟩ rho hn).BlockAcceptedBy y j ((simTrace ⟨S, stock⟩ rho hn).time i) B := by
  obtain ⟨r, p, hr, horg, _, _, htime, _, hdecode⟩ :=
    (forwardAtAcceptance_iff ⟨S, stock⟩ rho hn _ _ _).mp
      (forwardAtAcceptance S rho hn hconst hv) x hx i B hi
  apply publication_acceptedBy_syncUntil S rho hn hconst hv hnc hbh hnet r hr
    (horg ▸ (mem_honestKeys_iff ⟨S, stock⟩ rho x).mp hx) ht htime (p := p)
    (by rw [horg]; exact hdecode) hy hj hb hd hF

/-- Every well-formed attestation contained in an actual receipt gets a real processing
call at receipt time, including duplicate attestations already present in the pool. -/
theorem received_att_processAt (hn : 1 ≤ Fintype.card V)
    {i : Nat} {v : V} {receipt : Wire (Fintype.card V)} {t : Time}
    (he : rho.events[i]? = some (.deliver v receipt t)) {a : FG.Att (Fintype.card V)}
    (hwf : a.WellFormed) (hc : Model.Obj.Contains receipt (attObj a)) :
    ∃ k < cutMap ⟨S, stock⟩ rho hn (i + 1),
      (simTrace ⟨S, stock⟩ rho hn).ProcessAttAt (rho.ownKey v) k a ∧
      (simTrace ⟨S, stock⟩ rho hn).time k = t := by
  let proposer := runProposer ⟨S, stock⟩ rho hn
  let dg := digestOf ⟨S, stock⟩ rho
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
    (stateAt ⟨S, stock⟩ rho hn v i).node 0 hmem
  obtain ⟨hn', ht, _⟩ := mem_deliverRecs (sp := S.params (Model.pubOf E) hn)
    (ro := S.ro _) proposer dg (rho.ownKey v) hs t i hr
  have hr' : r ∈ eventCuts ⟨S, stock⟩ rho hn i := by
    rw [eventCuts_deliver ⟨S, stock⟩ rho hn i v receipt t he]
    exact hr
  obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hr'
  have hk : (allCuts ⟨S, stock⟩ rho hn)[cutMap ⟨S, stock⟩ rho hn i + j]? = some r := by
    rw [allCuts_getElem?_add ⟨S, stock⟩ rho hn i j (List.getElem?_eq_some_iff.mp he).1 hj,
      List.getElem?_eq_getElem hj, heq]
  refine ⟨cutMap ⟨S, stock⟩ rho hn i + j, ?_, Or.inl ⟨?_, ?_⟩, ?_⟩
  · rw [cutMap_succ ⟨S, stock⟩ rho hn]; omega
  · simp only [simTrace_node ⟨S, stock⟩ rho hn, hk, Option.elim_some, hn']
  · simp only [simTrace_label ⟨S, stock⟩ rho hn, hk, Option.map_some, hl]
  · simp only [simTrace_time ⟨S, stock⟩ rho hn, hk, Option.elim_some, ht]

/-- Votes in an actual own-proposal payload were already pooled before its AC block cut. -/
theorem own_proposal_payload_pooled (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys ⟨S, stock⟩ rho) {j : Nat} {t : Time} {x : Nat}
    (hg : (simTrace ⟨S, stock⟩ rho hn).GroupAt (runProposer ⟨S, stock⟩ rho hn)
        (digestOf ⟨S, stock⟩ rho) y j t (.tick x))
    {d : DutyHead (Fintype.card V) (List (FG.Att (Fintype.card V)))
      (SA.Payload (Fintype.card V))} {p : SA.Payload (Fintype.card V)}
    (hd : (Node.acProposal
      (Node.tickStep (runProposer ⟨S, stock⟩ rho hn) (digestOf ⟨S, stock⟩ rho) y
        ((simTrace ⟨S, stock⟩ rho hn).state y j) t x .acTick).1 t).2.2 = some (d, p))
    (hprop : ∃ ℓp, (simTrace ⟨S, stock⟩ rho hn).CallAt y (j + 1) (.ac ℓp) ∧ ℓp.call = .proposal)
    (hfg : ∃ B, (simTrace ⟨S, stock⟩ rho hn).CallAt y (j + 2) (.fg (.block B true)))
    {m : SA.Vote (Fintype.card V)} (hm : m ∈ p.1) :
    m ∈ ((simTrace ⟨S, stock⟩ rho hn).state y (j + 3)).ac.pool m.slot :=
  Growing.own_proposal_payload_pooled_run (simTrace_goldilocksRun S rho hn hconst hv) hy hg hd
    hprop hfg hm

/-- A sending or freshly admitting source processes its vote at that same time.
Recursive delivery processing may occur later in the event, never at a later time. -/
theorem sendOrAdmit_process_same_time (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys ⟨S, stock⟩ rho) {i : Nat}
    {m : SA.Vote (Fintype.card V)} (hsource : (simTrace ⟨S, stock⟩ rho hn).SendOrAdmitAt y i m) :
    ∃ k, (simTrace ⟨S, stock⟩ rho hn).projAC.ProcessAt y k m ∧
      (simTrace ⟨S, stock⟩ rho hn).time k = (simTrace ⟨S, stock⟩ rho hn).time i := by
  have hr := simTrace_goldilocksRun S rho hn hconst hv
  have hproj : (simTrace ⟨S, stock⟩ rho hn).projAC.SendOrAdmit y i m := by
    obtain ⟨ℓ, hc, hs⟩ := hsource
    refine ⟨ℓ, Compose.projAC_callAt.mpr hc, ?_⟩
    rw [Compose.projAC_state hr.toLocalRun hy]
    exact hs
  rcases Compose.sendOrAdmit_forward_source hr hy hproj with hem | ⟨hc, hf, _⟩
  · obtain ⟨ℓ, hc, he⟩ := hem
    exact ⟨i, ⟨ℓ, Compose.projAC_callAt.mpr hc, Or.inr he⟩, rfl⟩
  rcases hc with ⟨ℓ, hc, hm⟩ | ⟨ℓ, B, hc, hb, hm⟩
  · exact ⟨i, ⟨ℓ, Compose.projAC_callAt.mpr hc, Or.inl hm⟩, rfl⟩
  rcases acBlock_cut_cases ⟨S, stock⟩ rho hn hc hb hm with h |
      ⟨n, v, t, he, hpublic, hkey, hlo, hhi, ht⟩
  · exact h
  have hvhon : v ∉ rho.faultyAt 0 := by
    have : rho.key y = v := by rw [← hkey]; exact rho.key.apply_symm_apply v
    exact this ▸ (mem_honestKeys_iff ⟨S, stock⟩ rho y).mp hy
  obtain ⟨hengine, hlen⟩ := simTrace_tick_public_group ⟨S, stock⟩ rho hn hconst hv v hvhon n t he
      hpublic
  rw [hkey] at hengine hlen
  exact (hf (acBlock_vote_pooled_in_tick hr hy hengine hlo (by omega) ht hc hb hm)).elim

end Consensus.Goldilocks.Obligations
