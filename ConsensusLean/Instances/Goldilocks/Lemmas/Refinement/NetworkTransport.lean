module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Forwarding
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.PublicationProvenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ForwardingDecode
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Run

public section

/-! # Open network transport suppliers

These are goals for the concrete publisher/simulation adapter, not extra premises of Accepted.
The trace parameters remain independent here. `Setup.params` now gives protocol delay
Δp = Δe + 1; this endpoint slack does not instantiate any supplier below. For FG row service,
ΔF := sp.Δ is the protocol bound, not the engine delay.
All three suppliers include message, block, acceptance-relay and attestation service. Receipt
alone proves none of the acceptance-relay fields. No supplier is claimed implemented here.
-/

namespace Consensus.Goldilocks.Refinement

open Shape Blocks

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  (S : Setup) (rho : Model.Run (compiled (family S)) E)
  {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (ΔF : Time)

/-- OPEN supplier: PSync supplies GST at the node level. Paper route: actual same-time
publication gives network service by max(send, GST, latest wake)+Δe; authenticated provenance
gives the lower bound, recursive processing gives a call, and +1 gives the strict endpoint.
Acceptance relay additionally requires the parent-first induction, NoColl and chain-state
agreement. Vote/attestation admissions need their own source/time provenance. The adapter
must identify H, node keys, flattened cuts, horizon and awake intervals with the engine run. -/
def PSyncTransport : Prop :=
  ∀ g, rho.log.PSync rho.point g → tr.GSTRun H ΔF g

/-- OPEN supplier: SyncUntil supplies only recipient-deadline-cut SyncBefore, not SyncRun
with a send-time cutoff. Paper route: a node deadline ≤ b puts its engine service endpoint
strictly below b under +1. Wakes are included in that deadline. All four service fields need
the same publication/processing joins as PSyncTransport. No post-outage service is inferred. -/
def SyncUntilTransport : Prop :=
  ∀ b, rho.log.SyncUntil rho.point b → tr.SyncBefore H ΔF b

/-- OPEN supplier: global synchrony gives SyncRun on nonnegative send windows. In particular
this does not derive a send-window SyncRun from SyncUntil: a late wake can put its deadline
after the latter's cutoff. The concrete adapter must discharge the same four service leaves. -/
def SyncRunTransport : Prop :=
  rho.log.PSync rho.point 0 → ∀ a b, 0 ≤ a → tr.SyncRun H ΔF a b

/-- OPEN concrete supplier: actual signed/admitted FG rows receive the protocol delay,
not an independent setup coefficient. This services an existing attestation; it never
produces a row. Source emission/admission must supply an actual released canonical object;
engine service supplies holdings by Δe, provenance and recursive processing supply the call
after its source time, and the installed Δp = Δe + 1 gives the strict endpoint. The adapter
must still identify keys, cuts, awake intervals and horizon. This is not an extra Healthy
premise; source availability and usable-row obligations remain separate. -/
def PSyncFGRowTransport : Prop :=
  ∀ g, rho.log.PSync rho.point g →
    ∀ x ∈ H, ∀ i a, tr.SendOrAdmitAttAt x i a →
      ∀ y ∈ H, ∀ j, tr.IsCall y j →
        tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
        tr.AttDeliveredBy y j (tr.time i) (max (tr.time i) g) sp.Δ a

/-- Pure endpoint arithmetic, independent of the unimplemented adapter. Service at the engine
endpoint is strictly before the protocol endpoint, including equality at the engine bound.
This buys no forwarding delay and is paid once, not once per ancestor. -/
theorem delivery_endpoint_slack (base received Δe Δp : Time)
    (hdelay : Δp = Δe + 1) (hreceived : received ≤ base + Δe) :
    received < base + Δp := by
  simp only [Time] at *
  omega

/-- A qualifying protocol deadline places the engine endpoint strictly before the outage
cutoff. The cutoff itself is allowed for the protocol deadline. -/
theorem delivery_endpoint_before_cutoff (base cutoff Δe Δp : Time)
    (hdelay : Δp = Δe + 1) (hcut : base + Δp ≤ cutoff) :
    base + Δe < cutoff := by
  simp only [Time] at *
  omega

/-- Partial synchrony services an actual successful publication strictly before the
protocol endpoint. The start may be a later wake; its entire engine delivery interval
must be awake and inside the horizon. This proves holdings, not a node call or row production. -/
theorem publication_held_psync (hn : 1 ≤ Fintype.card V) {g : Time}
    (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (family S)) E))
    (hr : (publisherExecution S rho).actual r) (hx : rho.key r.origin ∈ rho.honest)
    {y : V} (hy : y ∈ rho.honest) {a : Time}
    (ha : (publisherExecution S rho).eventTime r.event ≤ a)
    (hh : max a g + E.Δ ≤ rho.horizon)
    (hawake : rho.point.AwakeOnClosed y a (max a g + E.Δ)) :
    rho.log.Held rho.point y r.object (max a g + E.Δ) ∧
      max a g + E.Δ < max a g + (S.params (Model.pubOf E) hn).Δ := by
  constructor
  · exact hnet.msgs _ hx _ _
      ⟨r.event, (publisherExecution S rho).actual_event r hr,
        (publisherExecution S rho).actual_release r hr⟩ y hy a ha hh hh hawake
  · change max a g + E.Δ < max a g + (E.Δ + 1)
    linarith

/-- Before an outage, only qualifying recipient deadlines receive service. The protocol
deadline may equal the cutoff: the engine endpoint is still strictly below it. -/
theorem publication_held_syncUntil (hn : 1 ≤ Fintype.card V) {b : Time}
    (hnet : rho.log.SyncUntil rho.point b)
    (r : Publication (Model.protoOf (compiled (family S)) E))
    (hr : (publisherExecution S rho).actual r) (hx : rho.key r.origin ∈ rho.honest)
    {y : V} (hy : y ∈ rho.honest) {a : Time}
    (ha : (publisherExecution S rho).eventTime r.event ≤ a)
    (hb : a + (S.params (Model.pubOf E) hn).Δ ≤ b)
    (hh : a + E.Δ ≤ rho.horizon)
    (hawake : rho.point.AwakeOnClosed y a (a + E.Δ)) :
    rho.log.Held rho.point y r.object (a + E.Δ) ∧ a + E.Δ < b := by
  have hlt : a + E.Δ < b := by
    change a + (E.Δ + 1) ≤ b at hb
    linarith
  exact ⟨hnet.msgs _ hx _ _
    ⟨r.event, (publisherExecution S rho).actual_event r hr,
      (publisherExecution S rho).actual_release r hr⟩ y hy a ha hlt.le hh hawake, hlt⟩

/-- Delivery of an honest publication yields a real block call at receipt time, no earlier
than its source event. A bounded receipt therefore gives a strictly protocol-bounded call.
This includes refused calls; it does not establish acceptance or supply network delivery. -/
theorem publication_received_blockCall (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid)
    (r : Publication (Model.protoOf (compiled (family S)) E))
    (hr : (publisherExecution S rho).actual r) (hx : rho.key r.origin ∈ rho.honest)
    {i : Nat} {v : V} {receipt : Wire (Fintype.card V)} {t u base : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    (hc : Model.Obj.Contains receipt r.object)
    (hd : decodeForward (S.params (Model.pubOf E) hn)
      (Model.digests rho.hash r.object) r.object = some (r.origin, t, p, B))
    (hu : u ≤ base + E.Δ) :
    ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).BlockCallAt (rho.ownKey v) k B ∧
      (simTrace S rho hn).time k = u ∧
      (publisherExecution S rho).eventTime r.event ≤ (simTrace S rho hn).time k ∧
      (simTrace S rho hn).time k < base + (S.params (Model.pubOf E) hn).Δ := by
  have htu := received_forward_stamp_le S rho hn hv he hc hx hd
  obtain ⟨k, hk, hcall, htime⟩ := received_forward_blockCall S rho hn he hc hd htu
  refine ⟨k, hk, hcall, htime, ?_, ?_⟩
  · rw [htime, ← publication_forward_stamp S rho hn hv r hr hd]
    exact htu
  · rw [htime]
    exact delivery_endpoint_slack base u E.Δ (S.params (Model.pubOf E) hn).Δ rfl hu

/-- A recipient is awake from its effective send/wake start through its call.
This supplies the closed interval required by engine delivery, not merely wakefulness
at the observation cut. -/
theorem deadline_awake_interval (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {j : Nat}
    (hj : (simTrace S rho hn).IsCall y j) {τ : Time} (hτ : 0 ≤ τ) :
    ∃ a, τ ≤ a ∧
      (simTrace S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ =
        a + (S.params (Model.pubOf E) hn).Δ ∧
      rho.point.AwakeOnClosed (rho.key y) a ((simTrace S rho hn).time j) := by
  let tr := simTrace S rho hn
  have hr := simTrace_goldilocksRun S rho hn hv
  let a := Option.elim (tr.lastWake y j) τ (fun w => max τ w)
  have hτa : τ ≤ a := by
    dsimp [a]
    cases tr.lastWake y j with
    | bot => exact le_rfl
    | coe w => exact le_max_left _ _
  have hrestart : ∀ k ≤ j, tr.RestartAt y k → tr.time k ≤ a := by
    have hmax : ∀ c, ∀ k ≤ c, tr.RestartAt y k →
        (tr.time k : WithBot Time) ≤ tr.lastWake y c := by
      intro c
      induction c with
      | zero =>
        intro k hk hk'
        obtain rfl : k = 0 := by omega
        simp [RunTrace.lastWake, hk']
      | succ c ih =>
        intro k hk hk'
        by_cases hc : tr.RestartAt y (c + 1)
        · simp only [RunTrace.lastWake, hc, ite_true]
          exact WithBot.coe_le_coe.mpr (hr.time_mono hk)
        · have hk0 : k ≤ c := by
            by_contra h
            obtain rfl : k = c + 1 := by omega
            exact hc hk'
          simpa only [RunTrace.lastWake, hc, ite_false] using ih k hk0 hk'
    intro k hk hk'
    have hm := hmax j k hk hk'
    dsimp [a]
    cases hw : tr.lastWake y j with
    | bot => rw [hw] at hm; exact (WithBot.not_coe_le_bot _ hm).elim
    | coe w =>
      rw [hw] at hm
      exact (WithBot.coe_le_coe.mp hm).trans (le_max_right _ _)
  refine ⟨a, hτa, rfl, ?_⟩
  intro u hau huj
  have hu0 : 0 ≤ u := hτ.trans (hτa.trans hau)
  have hwu : tr.awake y u := by
    by_contra hsleep
    have hwj := hr.awake_of_call y hy j hj
    have huj' : u < tr.time j := lt_of_le_of_ne huj (by
      intro heq
      exact hsleep (heq ▸ hwj))
    obtain ⟨k, hk, huk, hkj⟩ := hr.restart_at_wake y hy u (tr.time j) hu0 huj' hsleep hwj
    have hkidx : k ≤ j := by
      by_contra h
      obtain ⟨v, _, hvk, _, hvprev⟩ := hr.sleep_of_restart y hy k hk
      have := hvprev j (by omega) hj
      linarith
    have := hrestart k hkidx hk
    linarith
  exact (simTrace_awake_of S rho hn hv y hy u hwu).1

/-- Later observation cuts can only increase a recipient's deadline. -/
theorem deadline_mono_cut (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (y : Fin (Fintype.card V)) (τ Δ : Time) :
    Monotone (fun j => (simTrace S rho hn).deadline y j τ Δ) := by
  let tr := simTrace S rho hn
  have hr := simTrace_goldilocksRun S rho hn hv
  have hw : ∀ c (w : Time), tr.lastWake y c = (w : WithBot Time) → w ≤ tr.time c := by
    intro c
    induction c with
    | zero =>
      intro w h
      unfold RunTrace.lastWake at h
      split at h
      · exact (WithBot.coe_injective h).ge
      · cases h
    | succ c ih =>
      intro w h
      unfold RunTrace.lastWake at h
      split at h
      · exact (WithBot.coe_injective h).ge
      · exact (ih w h).trans (hr.time_mono (Nat.le_succ c))
  apply monotone_nat_of_le_succ
  intro c
  change tr.deadline y c τ Δ ≤ tr.deadline y (c + 1) τ Δ
  unfold RunTrace.deadline
  rw [RunTrace.lastWake]
  split
  · cases heq : tr.lastWake y c with
    | bot =>
      change τ + Δ ≤ max τ (tr.time (c + 1)) + Δ
      have := le_max_left τ (tr.time (c + 1))
      dsimp [Time] at *
      omega
    | coe w =>
      change max τ w + Δ ≤ max τ (tr.time (c + 1)) + Δ
      have hle : w ≤ tr.time (c + 1) :=
        (hw c w heq).trans (hr.time_mono (Nat.le_succ c))
      simp only [Time] at hle ⊢
      omega
  · exact le_rfl

/-- A real honest publication is held strictly before a qualifying node deadline.
The wake interval and horizon obligations follow from the recipient call and cutoff. -/
theorem publication_held_before_deadline (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) {b : Time} (hbh : b ≤ rho.horizon)
    (hnet : rho.log.SyncUntil rho.point b)
    (r : Publication (Model.protoOf (compiled (family S)) E))
    (hr : (publisherExecution S rho).actual r) (hx : rho.key r.origin ∈ rho.honest)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {j : Nat}
    (hj : (simTrace S rho hn).IsCall y j) {τ : Time} (hτ : 0 ≤ τ)
    (ht : (publisherExecution S rho).eventTime r.event = τ)
    (hb : (simTrace S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ ≤ b)
    (hd : (simTrace S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ ≤
      (simTrace S rho hn).time j) :
    ∃ d, rho.log.Held rho.point (rho.key y) r.object d ∧
      d < (simTrace S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ := by
  obtain ⟨a, ha, heq, hw⟩ := deadline_awake_interval S rho hn hv hy hj hτ
  rw [heq] at hb hd ⊢
  have hslack : a + E.Δ < a + (S.params (Model.pubOf E) hn).Δ := by
    change a + E.Δ < a + (E.Δ + 1)
    linarith
  obtain ⟨hheld, _⟩ := publication_held_syncUntil S rho hn hnet r hr hx hy
    (ht ▸ ha) hb ((hslack.le.trans hb).trans hbh)
    (fun u hau hud => hw u hau (hud.trans (hslack.le.trans hd)))
  exact ⟨a + E.Δ, hheld, hslack⟩

/-- Network holdings of an authenticated forwarding envelope yield an acceptance
before the observation deadline. The sent case uses actual local acceptance, while
the received case uses recursive forwarding acceptance above the reader's `F`. -/
theorem held_forward_accepted_before (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
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
  have hrun := simTrace_goldilocksRun S rho hn hv
  obtain ⟨u, hud, hsource, _⟩ := hheld
  have huD : u < D := hud.trans_lt hd
  have event_before {i : Nat} {ev : Model.Event V (Wire (Fintype.card V))}
      (he : rho.events[i]? = some ev) (hu : ev.time = u) : cutMap S rho hn (i + 1) ≤ j := by
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
    linarith
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
    exact ⟨k, (hk.trans_le hcut).le, hkey ▸ ha, ht ▸ hstamp ▸ huD⟩
  · obtain ⟨i, hi⟩ := hr
    obtain ⟨k, hk, ha, _, ht⟩ := received_forward_accepted_before S rho hn hv hrun hnc
      hi hy (.refl o) hx hdecode (event_before hi rfl) (by simpa only [hkey] using hF) huD
    exact ⟨k, (hk.trans_le (event_before hi rfl)).le, hkey ▸ ha, ht⟩

/-- Acceptance service is measured at the processing cut, even when later restarts
enlarge the observation deadline. Descent on cuts removes that apparent slack. -/
theorem publication_acceptedBy_syncUntil (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {b : Time} (hbh : b ≤ rho.horizon) (hnet : rho.log.SyncUntil rho.point b)
    (r : Publication (Model.protoOf (compiled (family S)) E))
    (hr : (publisherExecution S rho).actual r) (hx : rho.key r.origin ∈ rho.honest)
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
    obtain ⟨d, hheld, hlt⟩ := publication_held_before_deadline S rho hn hv hbh hnet
      r hr hx hy hj hτ ht hb hd
    obtain ⟨k, hkj, hacc, htime⟩ := held_forward_accepted_before S rho hn hv hnc
      hy hx hheld hdecode hlt hd hF
    by_cases hk : (simTrace S rho hn).time k <
        (simTrace S rho hn).deadline y k τ (S.params (Model.pubOf E) hn).Δ
    · exact ⟨k, hkj, hacc, hk⟩
    · have hkj' : k < j := lt_of_le_of_ne hkj (by
        intro heq
        subst k
        exact hk htime)
      have hmono := deadline_mono_cut S rho hn hv y τ (S.params (Model.pubOf E) hn).Δ hkj
      obtain ⟨l, hl, ha, ht'⟩ := ih k hkj' ⟨_, hacc⟩ (hmono.trans hb)
        (le_of_not_gt hk)
        ((Healing.run_F_mono (simTrace_goldilocksRun S rho hn hv).toLocalRun hy hkj).trans hF)
      exact ⟨l, hl.trans hkj, ha, ht'⟩

/-- The finite acceptance-relay field. Valid executions supply same-event forwarding
and exact decoding; callers supply only network service and collision freedom. -/
theorem acceptance_relay_syncUntil (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid)
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
    (forwardAtAcceptance_iff S rho hn _ _ _).mp (forwardAtAcceptance S rho hn hv) x hx i B hi
  apply publication_acceptedBy_syncUntil S rho hn hv hnc hbh hnet r hr
    (horg ▸ hx) ht htime (p := p) (by simpa only [horg] using hdecode) hy hj hb hd hF

/-- After GST, an actual publication is held before every qualifying finite deadline.
The recipient may wake after the publication; the call supplies its awake interval. -/
theorem publication_held_before_deadline_psync (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) {g : Time} (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (family S)) E))
    (hr : (publisherExecution S rho).actual r) (hx : rho.key r.origin ∈ rho.honest)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {j : Nat}
    (hj : (simTrace S rho hn).IsCall y j) {τ : Time} (hτ : 0 ≤ τ) (hg : g ≤ τ)
    (ht : (publisherExecution S rho).eventTime r.event = τ)
    (hb : (simTrace S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ ≤ rho.horizon)
    (hd : (simTrace S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ ≤
      (simTrace S rho hn).time j) :
    ∃ d, rho.log.Held rho.point (rho.key y) r.object d ∧
      d < (simTrace S rho hn).deadline y j τ (S.params (Model.pubOf E) hn).Δ := by
  obtain ⟨a, ha, heq, hw⟩ := deadline_awake_interval S rho hn hv hy hj hτ
  rw [heq] at hb hd ⊢
  have hga : max a g = a := max_eq_left (hg.trans ha)
  have hslack : a + E.Δ < a + (S.params (Model.pubOf E) hn).Δ := by
    change a + E.Δ < a + (E.Δ + 1)
    linarith
  have hheld := (publication_held_psync S rho hn hnet r hr hx hy (ht ▸ ha)
    (by rw [hga]; exact hslack.le.trans hb)
    (by rw [hga]; exact fun u hau hud => hw u hau (hud.trans (hslack.le.trans hd)))).1
  rw [hga] at hheld
  exact ⟨a + E.Δ, hheld, hslack⟩

/-- Post-GST acceptance service through a finite recipient deadline. Earlier acceptance
cuts inherit the horizon bound, so descent does not assume infinite execution service. -/
theorem publication_acceptedBy_psync (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {g : Time} (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (family S)) E))
    (hr : (publisherExecution S rho).actual r) (hx : rho.key r.origin ∈ rho.honest)
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
    obtain ⟨d, hheld, hlt⟩ := publication_held_before_deadline_psync S rho hn hv hnet
      r hr hx hy hj hτ hg ht hb hd
    obtain ⟨k, hkj, hacc, htime⟩ := held_forward_accepted_before S rho hn hv hnc
      hy hx hheld hdecode hlt hd hF
    by_cases hk : (simTrace S rho hn).time k <
        (simTrace S rho hn).deadline y k τ (S.params (Model.pubOf E) hn).Δ
    · exact ⟨k, hkj, hacc, hk⟩
    · have hkj' : k < j := lt_of_le_of_ne hkj (by
        intro heq
        subst k
        exact hk htime)
      have hmono := deadline_mono_cut S rho hn hv y τ (S.params (Model.pubOf E) hn).Δ hkj
      obtain ⟨l, hl, ha, ht'⟩ := ih k hkj' ⟨_, hacc⟩ (hmono.trans hb)
        (le_of_not_gt hk)
        ((Healing.run_F_mono (simTrace_goldilocksRun S rho hn hv).toLocalRun hy hkj).trans hF)
      exact ⟨l, hl.trans hkj, ha, ht'⟩

/-- The bounded GST acceptance-relay field, with all forwarding obligations discharged.
A recipient call bounded by the horizon supplies the required deadline bound. -/
theorem acceptance_relay_psync (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid)
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
    (forwardAtAcceptance_iff S rho hn _ _ _).mp (forwardAtAcceptance S rho hn hv) x hx i B hi
  exact publication_acceptedBy_psync S rho hn hv hnc hnet r hr (horg ▸ hx)
    ht hg htime (p := p) (by simpa only [horg] using hdecode) hy hj (hd.trans hb) hd hF

/-- Old honest acceptances catch up before the first two-delay snapshot after GST.
The snapshot itself supplies the finite service horizon; no infinite health is assumed. -/
theorem catchRun_of_psync (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {g : Time} (hnet : rho.log.PSync rho.point g)
    (hawake : ∀ v ∈ rho.honest, rho.point.AwakeOnClosed v (max g 0) rho.horizon) :
    Healing.CatchRun (simTrace S rho hn) (honestKeys S rho) g
      (2 * (S.params (Model.pubOf E) hn).Δ) := by
  intro x hx i B hi hbefore y hy j hfirst hF
  have hstart := hfirst.1
  change max g 0 + 2 * (E.Δ + 1) ≤ (simTrace S rho hn).time j at hstart
  have hbound : (simTrace S rho hn).time j ≤ rho.horizon + 1 := by
    cases hj : (allCuts S rho hn)[j]? with
    | none => rw [(simTrace_of_getElem?_none S rho hn hj).2]
    | some r =>
      have hl : (simTrace S rho hn).label j ≠ none := by rw [simTrace_label, hj]; simp
      have hh := simTrace_labelled_time_le S rho hn hv hl
      linarith
  have hservice : max g 0 + E.Δ ≤ rho.horizon := by linarith [E.Δ_pos]
  obtain ⟨r, p, hr, horg, _, _, htime, _, hdecode⟩ :=
    (forwardAtAcceptance_iff S rho hn _ _ _).mp (forwardAtAcceptance S rho hn hv) x hx i B hi
  have hmax : max (max g 0) g = max g 0 := max_eq_left (le_max_left _ _)
  obtain ⟨hheld, hslack⟩ := publication_held_psync S rho hn hnet r hr (horg ▸ hx) hy
    (a := max g 0) (by rw [htime]; exact hbefore.le)
    (by rw [hmax]; exact hservice)
    (by
      rw [hmax]
      exact fun u hlo hhi => hawake (rho.key y) hy u hlo (hhi.trans hservice))
  rw [hmax] at hheld hslack
  have hdeadline : max g 0 + (S.params (Model.pubOf E) hn).Δ ≤
      (simTrace S rho hn).time j := by
    change max g 0 + (E.Δ + 1) ≤ _
    linarith [E.Δ_pos]
  obtain ⟨k, hkj, hk, hkt⟩ := held_forward_accepted_before S rho hn hv hnc hy hx hheld
    hdecode hslack hdeadline hF
  refine ⟨k, lt_of_le_of_ne hkj ?_, hk⟩
  intro heq
  subst k
  exact (not_lt_of_ge hdeadline) hkt

/-- GST holdings for an arbitrary publication, including pre-GST sources. The effective
time controls the deadline while the publication retains its original source time. -/
theorem publication_held_before_gst_deadline (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) {g : Time} (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (family S)) E))
    (hr : (publisherExecution S rho).actual r) (hx : rho.key r.origin ∈ rho.honest)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {j : Nat}
    (hj : (simTrace S rho hn).IsCall y j) {τ : Time} (hτ : 0 ≤ τ)
    (ht : (publisherExecution S rho).eventTime r.event = τ)
    (hb : (simTrace S rho hn).deadline y j (max τ g)
      (S.params (Model.pubOf E) hn).Δ ≤ rho.horizon)
    (hd : (simTrace S rho hn).deadline y j (max τ g)
      (S.params (Model.pubOf E) hn).Δ ≤ (simTrace S rho hn).time j) :
    ∃ d, rho.log.Held rho.point (rho.key y) r.object d ∧
      d < (simTrace S rho hn).deadline y j (max τ g) (S.params (Model.pubOf E) hn).Δ := by
  obtain ⟨a, ha, heq, hw⟩ := deadline_awake_interval S rho hn hv hy hj
    (hτ.trans (le_max_left τ g))
  rw [heq] at hb hd ⊢
  have hga : max a g = a := max_eq_left ((le_max_right τ g).trans ha)
  have hslack : a + E.Δ < a + (S.params (Model.pubOf E) hn).Δ := by
    change a + E.Δ < a + (E.Δ + 1)
    linarith
  have hheld := (publication_held_psync S rho hn hnet r hr hx hy
    (ht ▸ (le_max_left τ g).trans ha)
    (by rw [hga]; exact hslack.le.trans hb)
    (by rw [hga]; exact fun u hau hud => hw u hau (hud.trans (hslack.le.trans hd)))).1
  rw [hga] at hheld
  exact ⟨a + E.Δ, hheld, hslack⟩

/-- Holdings of an honest decoded wrapper give a block call after its source stamp.
Local publication uses the actual acceptance; receipt uses recursive block processing. -/
theorem held_forward_blockCall_before (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
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
    have hxy := released_forward_signer S rho hn hi ho hdecode
    rw [hxy] at hdecode
    have hstamp : t = u := released_forward_stamp S rho hn hv hi ho hdecode
    have hacc : ∃ k < cutMap S rho hn (i + 1),
        (simTrace S rho hn).AcceptAt (rho.ownKey (rho.key y)) k B ∧
        (simTrace S rho hn).time k = t := by
      rcases hi with he | ⟨receipt, he⟩
      · exact tick_released_forward_acceptance S rho hn hv he ho hdecode
      · exact delivery_released_forward_acceptance S rho hn hv he ho hdecode
    obtain ⟨k, _, ha, ht⟩ := hacc
    have hk : (simTrace S rho hn).time k < D := ht ▸ hstamp ▸ huD
    exact ⟨k, before hk, ht.ge, ⟨true, hkey ▸ ha⟩, hk⟩
  · obtain ⟨i, hi⟩ := hr
    have htu := received_forward_stamp_le S rho hn hv hi (.refl o) hx hdecode
    obtain ⟨k, _, hc, ht⟩ := received_forward_blockCall S rho hn hi (.refl o) hdecode htu
    have hk : (simTrace S rho hn).time k < D := ht ▸ huD
    exact ⟨k, before hk, ht ▸ htu, hkey ▸ hc, hk⟩

/-- A decoded publication receives block service at the processing cut's GST deadline,
including publications before GST. This does not require acceptance at the receiver. -/
theorem publication_blockDeliveredBy_psync (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) {g : Time} (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (family S)) E))
    (hr : (publisherExecution S rho).actual r) (hx : rho.key r.origin ∈ rho.honest)
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
    obtain ⟨d, hheld, hlt⟩ := publication_held_before_gst_deadline S rho hn hv hnet
      r hr hx hy hj hτ ht hb hd
    obtain ⟨k, hkj, hlo, hcall, htime⟩ := held_forward_blockCall_before S rho hn hv
      hx hheld hdecode hlt hd
    by_cases hk : (simTrace S rho hn).time k <
        (simTrace S rho hn).deadline y k (max τ g) (S.params (Model.pubOf E) hn).Δ
    · exact ⟨k, hkj, hlo, hcall, hk⟩
    · have hkj' : k < j := lt_of_le_of_ne hkj (by
        intro heq
        subst k
        exact hk htime)
      have hmono := deadline_mono_cut S rho hn hv y (max τ g)
        (S.params (Model.pubOf E) hn).Δ hkj
      obtain ⟨acc, hc⟩ := hcall
      obtain ⟨l, hl, hlo', hc', ht'⟩ := ih k hkj' ⟨_, hc⟩ (hmono.trans hb) (le_of_not_gt hk)
      exact ⟨l, hl.trans hkj, hlo', hc', ht'⟩

/-- An honest own-block call is an acceptance under collision freedom. -/
theorem ownBlockAt_accept (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {i : Nat}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hown : (simTrace S rho hn).OwnBlockAt y i B) :
    (simTrace S rho hn).AcceptAt y i B := by
  obtain ⟨⟨acc, hc⟩, hpos⟩ := hown
  have run := simTrace_goldilocksRun S rho hn hv
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
theorem block_service_psync (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
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
  have ha := hi.elim id (ownBlockAt_accept S rho hn hv hnc hx)
  obtain ⟨r, p, hr, horg, _, _, htime, _, hdecode⟩ :=
    (forwardAtAcceptance_iff S rho hn _ _ _).mp (forwardAtAcceptance S rho hn hv) x hx i B ha
  exact publication_blockDeliveredBy_psync S rho hn hv hnet r hr (horg ▸ hx)
    (simTrace_time_nonneg S rho hn hv i) htime (p := p)
    (by simpa only [horg] using hdecode) hy hj (hd.trans hb) hd

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

end Consensus.Goldilocks.Refinement
