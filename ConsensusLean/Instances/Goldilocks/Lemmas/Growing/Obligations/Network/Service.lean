module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Source
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Lift
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Forwarding
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NonfinalSuppliers
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.SentForward
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.DeadlineWake
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

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Shape Blocks

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
  {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
  {hn : 1 ≤ Fintype.card V} {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)}
  {e : Encoding F E p hN hn A} {rho : Model.Run (compiled F) E}
  {proposer : Nat → Fin (Fintype.card V)} {sg : A.Msg → Fin (Fintype.card V)}
  {ini : Fin (Fintype.card V) → A.State}

/-- Relay a decoded publication. The instance supplies the ancestry-dependent conversion
from a holding to an acceptance, for the original release, not the effective deadline time. -/
theorem publication_acceptedBy
    (hr : Growing.LocalRun proposer (digestOf e rho) (honestKeysAt rho) sg (simTrace e rho) ini)
    {x y : Fin (Fintype.card V)} {τ σ b : Time} {B : A.Blk}
    {o : (Model.protoOf (compiled F) E).Object}
    (hx : rho.key x ∉ rho.faultyAt τ) (hrel : rho.releases (rho.key x) o τ)
    (held : ∀ j, y ∈ honestKeysAt rho ((simTrace e rho).time j) → (simTrace e rho).IsCall y j →
      (simTrace e rho).deadline y j σ p.Δ ≤ b →
      (simTrace e rho).deadline y j σ p.Δ ≤ (simTrace e rho).time j →
      ∃ d, rho.log.Held rho.point (rho.key y) o d ∧ d < (simTrace e rho).deadline y j σ p.Δ)
    (accept : ∀ {j t₀ d D}, (∀ k < j, (simTrace e rho).time k ≤ t₀) →
      rho.key y ∉ rho.faultyAt t₀ → rho.key x ∉ rho.faultyAt τ →
      rho.releases (rho.key x) o τ → rho.log.Held rho.point (rho.key y) o d →
      d < D → D ≤ (simTrace e rho).time j →
      Anc ((simTrace e rho).HonestBlocksAt (honestKeysAt rho))
        ((simTrace e rho).state y j).fg.F B →
      ∃ k ≤ j, (simTrace e rho).AcceptAt y k B ∧ (simTrace e rho).time k < D)
    {j : Nat} (hy : y ∈ honestKeysAt rho ((simTrace e rho).time j))
    (hj : (simTrace e rho).IsCall y j) (hh : (simTrace e rho).time j ≤ rho.horizon)
    (hb : (simTrace e rho).deadline y j σ p.Δ ≤ b)
    (hd : (simTrace e rho).deadline y j σ p.Δ ≤ (simTrace e rho).time j)
    (hF : Anc ((simTrace e rho).HonestBlocksAt (honestKeysAt rho))
      ((simTrace e rho).state y j).fg.F B) : (simTrace e rho).BlockAcceptedBy y j σ B := by
  let tr := simTrace e rho
  apply RunTrace.service_at_processing_cut hr
    (inScope := fun k => tr.time k ≤ rho.horizon ∧ tr.deadline y k σ p.Δ ≤ b ∧
      Anc (tr.HonestBlocksAt (honestKeysAt rho)) (tr.state y k).fg.F B) _ _ hy hj ⟨hh, hb, hF⟩ hd
  · intro k j hkj hy hscope
    exact ⟨(hr.time_mono hkj).trans hscope.1,
      (RunTrace.deadline_mono_cut_of_time_mono tr hr.time_mono y σ p.Δ hkj).trans hscope.2.1,
      (hr.finalized_mono hy hkj).trans hscope.2.2⟩
  · intro j hy hj hscope hd
    obtain ⟨d, hh, hlt⟩ := held j hy hj hscope.2.1 hd
    obtain ⟨k, hkj, ha, ht⟩ := accept (fun i hi => hr.time_mono hi.le)
      (not_faulty_of_mem_honestKeysAt hy le_rfl hscope.1) hx hrel hh hlt hd hscope.2.2
    exact ⟨k, hkj, ⟨_, ha⟩, ha, ht⟩

/-- Relay an acceptance using an actual publication in its containing event and the
interpretation of its wrapper. -/
theorem acceptanceRelay
    (hr : Growing.LocalRun proposer (digestOf e rho) (honestKeysAt rho) sg (simTrace e rho) ini)
    {fwd : (Model.protoOf (compiled F) E).Object →
      Option (Fin (Fintype.card V) × Time × Option (Model.protoOf (compiled F) E).Object × A.Blk)}
    {x y : Fin (Fintype.card V)} {i j : Nat} {σ b : Time} {B : A.Blk}
    (hx : rho.key x ∉ rho.faultyAt ((simTrace e rho).time i))
    (pub : ∃ o parent ev, cutMap e rho ev ≤ i ∧ i < cutMap e rho (ev + 1) ∧
      rho.SendsAt (rho.key x) ev ((simTrace e rho).time i) ∧ o ∈ rho.releasesAt ev ∧
      fwd o = some (x, (simTrace e rho).time i, parent, B) ∧ ¬ rho.log.fgAtt o)
    (held : ∀ o, rho.releases (rho.key x) o ((simTrace e rho).time i) → ¬ rho.log.fgAtt o →
      ∀ k, y ∈ honestKeysAt rho ((simTrace e rho).time k) → (simTrace e rho).IsCall y k →
        (simTrace e rho).deadline y k σ p.Δ ≤ b →
        (simTrace e rho).deadline y k σ p.Δ ≤ (simTrace e rho).time k →
        ∃ d, rho.log.Held rho.point (rho.key y) o d ∧ d < (simTrace e rho).deadline y k σ p.Δ)
    (accept : ∀ {o parent k t₀ d D}, fwd o = some (x, (simTrace e rho).time i, parent, B) →
      (∀ l < k, (simTrace e rho).time l ≤ t₀) → rho.key y ∉ rho.faultyAt t₀ →
      rho.key x ∉ rho.faultyAt ((simTrace e rho).time i) →
      rho.releases (rho.key x) o ((simTrace e rho).time i) →
      rho.log.Held rho.point (rho.key y) o d →
      d < D → D ≤ (simTrace e rho).time k →
      Anc ((simTrace e rho).HonestBlocksAt (honestKeysAt rho)) ((simTrace e rho).state y k).fg.F B →
      ∃ l ≤ k, (simTrace e rho).AcceptAt y l B ∧ (simTrace e rho).time l < D)
    (hy : y ∈ honestKeysAt rho ((simTrace e rho).time j)) (hj : (simTrace e rho).IsCall y j)
    (hh : (simTrace e rho).time j ≤ rho.horizon) (hb : (simTrace e rho).deadline y j σ p.Δ ≤ b)
    (hd : (simTrace e rho).deadline y j σ p.Δ ≤ (simTrace e rho).time j)
    (hF : Anc ((simTrace e rho).HonestBlocksAt (honestKeysAt rho))
      ((simTrace e rho).state y j).fg.F B) : (simTrace e rho).BlockAcceptedBy y j σ B := by
  obtain ⟨o, parent, ev, _, _, hs, ho, hdec, hrow⟩ := pub
  have hrel : rho.releases (rho.key x) o ((simTrace e rho).time i) := ⟨ev, hs, ho⟩
  exact publication_acceptedBy hr hx hrel (held o hrel hrow) (accept hdec) hy hj hh hb hd hF

/-- A remote publication is processed with its original send-time lower bound. The same
`MsgPub` witness that accompanies the timely release is supplied to the processing law. -/
theorem publication_messageDeliveredBy
    (hr : Growing.LocalRun proposer (digestOf e rho) (honestKeysAt rho) sg (simTrace e rho) ini)
    {MsgPub : Fin (Fintype.card V) → Time → A.Msg → (Model.protoOf (compiled F) E).Object → Prop}
    {x y : Fin (Fintype.card V)} {τ σ b : Time} {m : A.Msg}
    {o : (Model.protoOf (compiled F) E).Object}
    (hx : rho.key x ∉ rho.faultyAt τ) (hne : y ≠ x) (hpub : MsgPub x τ m o)
    (held : ∀ j, y ∈ honestKeysAt rho ((simTrace e rho).time j) → (simTrace e rho).IsCall y j →
      (simTrace e rho).deadline y j σ p.Δ ≤ b →
      (simTrace e rho).deadline y j σ p.Δ ≤ (simTrace e rho).time j →
      ∃ d, rho.log.Held rho.point (rho.key y) o d ∧ d < (simTrace e rho).deadline y j σ p.Δ)
    (process : ∀ d, MsgPub x τ m o → rho.key x ∉ rho.faultyAt τ →
      rho.log.Held rho.point (rho.key y) o d → y = x ∨
      ∃ k, (simTrace e rho).ProcessMsgAt y k m ∧ τ ≤ (simTrace e rho).time k ∧
        (simTrace e rho).time k ≤ d)
    {j : Nat} (hy : y ∈ honestKeysAt rho ((simTrace e rho).time j))
    (hj : (simTrace e rho).IsCall y j) (hb : (simTrace e rho).deadline y j σ p.Δ ≤ b)
    (hd : (simTrace e rho).deadline y j σ p.Δ ≤ (simTrace e rho).time j) :
    (simTrace e rho).MsgDeliveredBy y j τ σ m := by
  let tr := simTrace e rho
  obtain ⟨k, hkj, ⟨hlo, hp⟩, ht⟩ := RunTrace.service_at_processing_cut hr
    (inScope := fun k => tr.deadline y k σ p.Δ ≤ b)
    (processed := fun k => τ ≤ tr.time k ∧ tr.ProcessMsgAt y k m)
    (fun hkj _ h => (RunTrace.deadline_mono_cut_of_time_mono tr hr.time_mono y σ p.Δ hkj).trans h)
    (by
      intro j hy hj hb hd
      obtain ⟨d, hh, hlt⟩ := held j hy hj hb hd
      obtain heq | ⟨k, hp, hlo, hhi⟩ := process d hpub hx hh
      · exact (hne heq).elim
      have ht := hhi.trans_lt hlt
      have hkj : k ≤ j := le_of_not_gt fun h => (not_lt_of_ge (hr.time_mono h.le)) (ht.trans_le hd)
      have hc : tr.IsCall y k := hp.elim (fun ⟨_, hc, _⟩ => ⟨_, hc⟩) (fun ⟨_, hc, _⟩ => ⟨_, hc⟩)
      exact ⟨k, hkj, hc, ⟨hlo, hp⟩, ht⟩) hy hj hb hd
  exact ⟨k, hkj, hlo, hp, ht⟩

/-- Same-time self processing or remote publication service, before the observation cutoff. -/
theorem messageDeliveredBy
    (hr : Growing.LocalRun proposer (digestOf e rho) (honestKeysAt rho) sg (simTrace e rho) ini)
    {MsgPub : Fin (Fintype.card V) → Time → A.Msg → (Model.protoOf (compiled F) E).Object → Prop}
    {x y : Fin (Fintype.card V)} {i j : Nat} {m : A.Msg} {σ b : Time}
    (hσ : (simTrace e rho).time i ≤ σ)
    (own : ∃ k, (simTrace e rho).ProcessMsgAt x k m ∧
      (simTrace e rho).time k = (simTrace e rho).time i)
    (pub : ∃ o, MsgPub x ((simTrace e rho).time i) m o ∧
      rho.releases (rho.key x) o ((simTrace e rho).time i) ∧ ¬ rho.log.fgAtt o)
    (hx : rho.key x ∉ rho.faultyAt ((simTrace e rho).time i))
    (held : ∀ o, rho.releases (rho.key x) o ((simTrace e rho).time i) → ¬ rho.log.fgAtt o →
      ∀ k, y ∈ honestKeysAt rho ((simTrace e rho).time k) → (simTrace e rho).IsCall y k →
        (simTrace e rho).deadline y k σ p.Δ ≤ b →
        (simTrace e rho).deadline y k σ p.Δ ≤ (simTrace e rho).time k →
        ∃ d, rho.log.Held rho.point (rho.key y) o d ∧ d < (simTrace e rho).deadline y k σ p.Δ)
    (process : ∀ o d, MsgPub x ((simTrace e rho).time i) m o →
      rho.key x ∉ rho.faultyAt ((simTrace e rho).time i) →
      rho.log.Held rho.point (rho.key y) o d → y = x ∨
        ∃ k, (simTrace e rho).ProcessMsgAt y k m ∧
          (simTrace e rho).time i ≤ (simTrace e rho).time k ∧ (simTrace e rho).time k ≤ d)
    (hy : y ∈ honestKeysAt rho ((simTrace e rho).time j)) (hj : (simTrace e rho).IsCall y j)
    (hb : (simTrace e rho).deadline y j σ p.Δ ≤ b)
    (hd : (simTrace e rho).deadline y j σ p.Δ ≤ (simTrace e rho).time j) :
    (simTrace e rho).MsgDeliveredBy y j ((simTrace e rho).time i) σ m := by
  let tr := simTrace e rho
  by_cases heq : y = x
  · subst y
    obtain ⟨k, hp, ht⟩ := own
    have hlt (l : Nat) : tr.time i < tr.deadline x l σ p.Δ := by
      unfold RunTrace.deadline
      cases tr.lastWake x l with
      | bot => exact hσ.trans_lt (lt_add_of_pos_right _ p.hΔ)
      | coe w => exact (hσ.trans (le_max_left _ _)).trans_lt (lt_add_of_pos_right _ p.hΔ)
    have htime : tr.time k < tr.time j := ht.trans_lt ((hlt j).trans_le hd)
    have hkj : k ≤ j := le_of_not_gt fun h => (not_lt_of_ge (hr.time_mono h.le)) htime
    exact ⟨k, hkj, ht.ge, hp, ht ▸ hlt k⟩
  · obtain ⟨o, hpub, hrel, hrow⟩ := pub
    exact publication_messageDeliveredBy hr hx heq hpub (held o hrel hrow) (process o) hy hj hb hd

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Shape Blocks

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)

/-- Goldilocks interprets message publication as its first release of the vote envelope. -/
def VotePublication (x : Fin (Fintype.card V)) (τ : Time) (m : AC.Vote (Fintype.card V))
    (o : Wire (Fintype.card V) S.vote) : Prop :=
  (∃ z, rho.verify (m.val, S.vote.voteRole m.slot, encodeVote m) z = true ∧
    o = .mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m z]) ∧
    ∃ i, rho.SendsAt (rho.key x) i τ ∧ o ∈ rho.releasesAt i ∧
      ∀ j < i, o ∉ rho.releasesAt j

/-- A held vote publication gives a processing cut, not an admission or store mutation. -/
theorem votePublication_process (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {x y : Fin (Fintype.card V)} {τ d : Time} {m : AC.Vote (Fintype.card V)}
    {o : Wire (Fintype.card V) S.vote} (hpub : VotePublication S rho x τ m o)
    (hx : rho.key x ∉ rho.faultyAt τ) (hh : rho.log.Held rho.point (rho.key y) o d) :
    y = x ∨ ∃ k, (simTraceAt S rho hn).ProcessMsgAt y k m ∧
      τ ≤ (simTraceAt S rho hn).time k ∧ (simTraceAt S rho hn).time k ≤ d := by
  obtain ⟨⟨z, hck, rfl⟩, i, hs, _, hf⟩ := hpub
  obtain h | ⟨k, ⟨ℓ, hc, hm⟩, hlo, hhi⟩ :=
    held_voteForward_source_or_process_at S rho hn hv hck hx hs hf hh
  · exact Or.inl h
  · exact Or.inr ⟨k, hm.elim (fun h => Or.inl ⟨ℓ, Compose.projAC_callAt.mp hc, h⟩)
      (fun h => Or.inr ⟨ℓ, Compose.projAC_callAt.mp hc, h⟩), hlo, hhi⟩

/-- Construct the instance's publication witness from the containing event's first release. -/
theorem votePublication_intro {source : Nat} {x : Fin (Fintype.card V)}
    {τ : Time} {m : AC.Vote (Fintype.card V)} {z : Nat}
    (hck : rho.verify (m.val, S.vote.voteRole m.slot, encodeVote m) z = true)
    (hs : rho.SendsAt (rho.key x) source τ)
    (hrel : Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m z] ∈
      rho.releasesAt source)
    (hfirst : ∀ i < source,
      Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m z] ∉
        rho.releasesAt i) :
    VotePublication S rho x τ m
      (.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m z]) :=
  ⟨⟨z, hck, rfl⟩, source, hs, hrel, hfirst⟩

/-- An actual publication by an origin honest at its event is held strictly before a qualifying
node deadline of a recipient honest at its call. -/
private theorem publication_held_before_deadline_at (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid)
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
  have hrel : rho.releases (rho.key r.origin) r.object τ :=
    ht ▸ ⟨r.event, (publisherExecution S rho).actual_event r hr,
      (publisherExecution S rho).actual_release r hr⟩
  have htr := network_trace_eq S rho hn
  rw [htr, network_honestKeysAt_eq] at hy
  rw [htr] at hj hb hd ⊢
  exact NodeAsChainShape.CanonicalTrace.publication_held_before_syncUntil
    (network_localRun S rho hn hv) le_rfl hbh hnet hrel (ht ▸ hx) hrow hy hj hτ hb hd

/-- Network holdings of a forwarding wrapper that is its signer's actual release, with the signer
honest at the release, yield an acceptance before the observation deadline, at a reading cut `j`
of a recipient honest at a time `t₀` that bounds every cut before `j`. -/
theorem held_forward_accepted_before_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {y x : Fin (Fintype.card V)} {j : Nat} {t₀ : Time}
    (hj₀ : ∀ k < j, (simTraceAt S rho hn).time k ≤ t₀) (hy : rho.key y ∉ rho.faultyAt t₀)
    {o : Wire (Fintype.card V) S.vote} {t d D : Time}
    {p : Option (Wire (Fintype.card V) S.vote)} {B : Blk (S.params (Model.pubOf E) hn)}
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
  have event_before {i : Nat} {ev : Model.Event V (Wire (Fintype.card V) S.vote)}
      (he : rho.events[i]? = some ev) (hu : ev.time = u) : cutMap S rho hn (i + 1) ≤ j :=
    cutMap_succ_le_of_time_lt S rho hn hv he
      (hu.trans_lt (huD.trans_le (by rwa [simTraceAt_eq] at hj)))
  have hkey : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply _
  rcases hsource with hs | hr
  · obtain ⟨i, hi, ho⟩ := hs
    obtain ⟨hstamp, k, hk, ha, ht⟩ := sent_forward_accepted S rho hn hv hi ho hdecode
    have hcut : cutMap S rho hn (i + 1) ≤ j := by
      rcases hi with he | ⟨receipt, he⟩ <;> exact event_before he rfl
    rw [simTraceAt_eq]
    exact ⟨k, (hk.trans_le hcut).le, ha, ht ▸ hstamp ▸ huD⟩
  · obtain ⟨i, hi⟩ := hr
    obtain ⟨k, hk, ha, _, ht⟩ := received_forward_accepted_before_of_released_at S rho hn hv hnc
      hi hj₀ hy rfl hx hrel hdecode (event_before hi rfl)
      (by simpa only [hkey] using hF) huD
    exact ⟨k, (hk.trans_le (event_before hi rfl)).le, hkey ▸ ha, ht⟩

/-- The Goldilocks acceptance publication, with its decoder closed over the run. -/
theorem acceptancePublication (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {x : Fin (Fintype.card V)} {i : Nat} {B : Blk (S.params (Model.pubOf E) hn)}
    (hx : x ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i))
    (hi : (simTraceAt S rho hn).AcceptAt x i B) :
    ∃ o parent ev, NodeAsChainShape.CanonicalTrace.cutMap (traceEncoding S hn) rho ev ≤ i ∧
      i < NodeAsChainShape.CanonicalTrace.cutMap (traceEncoding S hn) rho (ev + 1) ∧
      rho.SendsAt (rho.key x) ev ((simTraceAt S rho hn).time i) ∧ o ∈ rho.releasesAt ev ∧
      decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
        some (x, (simTraceAt S rho hn).time i, parent, B) ∧ ¬ rho.log.fgAtt o := by
  obtain ⟨r, parent, hr, horg, hlo, hhi, htime, _, hdecode⟩ :=
    (forwardAtAcceptanceAt_iff S rho hn _ _ _).mp (forwardAtAcceptance_at S rho hn hv) x i B hx hi
  rw [(simTrace_encoding S rho hn).2] at hlo hhi
  refine ⟨r.object, parent, r.event, hlo, hhi, ?_,
    (publisherExecution S rho).actual_release r hr, hdecode, not_isFGAtt_of_decodeForward hdecode⟩
  rw [← horg, ← htime]
  exact (publisherExecution S rho).actual_event r hr

/-- Acceptance service is measured at the processing cut, even when later restarts enlarge the
observation deadline. The origin is honest at its publication, the recipient at its call. -/
private theorem publication_acceptedBy_syncUntil_at (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {b : Time} (hbh : b ≤ rho.horizon) (hnet : rho.log.SyncUntil rho.point b)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r)
    {τ : Time} (hτ : 0 ≤ τ) (ht : (publisherExecution S rho).eventTime r.event = τ)
    (hx : rho.key r.origin ∉ rho.faultyAt τ)
    {p : Option (Wire (Fintype.card V) S.vote)} {B : Blk (S.params (Model.pubOf E) hn)}
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
  have hrel : rho.releases (rho.key r.origin) r.object τ :=
    ht ▸ ⟨r.event, (publisherExecution S rho).actual_event r hr,
      (publisherExecution S rho).actual_release r hr⟩
  have hh := isCall_time_le_horizon S rho hn hv hj
  have htr := network_trace_eq S rho hn
  have hH := network_honestKeysAt_eq S rho
  rw [htr, hH] at hy hF
  rw [htr] at hj hh hb hd ⊢
  have hrun := network_localRun S rho hn hv
  apply NodeAsChainShape.CanonicalTrace.publication_acceptedBy hrun hx hrel
    (fun _ hy hj => NodeAsChainShape.CanonicalTrace.publication_held_before_syncUntil
      hrun le_rfl hbh hnet hrel hx (not_isFGAtt_of_decodeForward hdecode) hy hj hτ)
    _ hy hj hh hb hd hF
  intro j t₀ d D hj₀ hy hx hrel hheld hlt hd hF
  rw [← htr] at hj₀ hd ⊢
  rw [← htr, ← hH] at hF
  exact held_forward_accepted_before_at S rho hn hv hnc hj₀ hy hx hrel hheld hdecode hlt hd hF

/-- The finite acceptance-relay field: an acceptance by a node honest at its cut is relayed to
every recipient honest at its call, inside the blocks held while honest. -/
private theorem acceptance_relay_syncUntil_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
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
  have hih : (simTraceAt S rho hn).time i ≤ rho.horizon :=
    isCall_time_le_horizon S rho hn hv ⟨_, hi⟩
  have hh := isCall_time_le_horizon S rho hn hv hj
  have hpub := acceptancePublication S rho hn hv hx hi
  have hxt := not_faulty_of_mem_honestKeysAt S rho hx le_rfl hih
  have htr := network_trace_eq S rho hn
  rw [htr, network_honestKeysAt_eq] at hy hF
  rw [htr] at ht hpub hxt hj hh hb hd ⊢
  have hrun := network_localRun S rho hn hv
  apply NodeAsChainShape.CanonicalTrace.acceptanceRelay hrun hxt hpub
    (fun _ hrel hrow _ hy hj => NodeAsChainShape.CanonicalTrace.publication_held_before_syncUntil
      hrun le_rfl hbh hnet hrel hxt hrow hy hj ht) _ hy hj hh hb hd hF
  intro o parent k t₀ d D hdecode hj₀ hy hx hrel held hlt hd hF
  rw [← htr] at hj₀ hd ⊢
  rw [← htr, ← network_honestKeysAt_eq S rho] at hF
  exact held_forward_accepted_before_at S rho hn hv hnc hj₀ hy hx hrel held hdecode hlt hd hF

/-- A different recipient honest at its call processes a first-release vote envelope of a sender
honest at its release before its processing-cut deadline. -/
private theorem vote_message_service_other_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {b : Time} (hbh : b ≤ rho.horizon) (hnet : rho.log.SyncUntil rho.point b)
    {source : Nat} {x y : Fin (Fintype.card V)} {τ : Time} {m : AC.Vote (Fintype.card V)}
    {z : Nat} (hck : rho.verify (m.val, S.vote.voteRole m.slot, encodeVote m) z = true)
    (hx : rho.key x ∉ rho.faultyAt τ) (hne : y ≠ x)
    (hτ : 0 ≤ τ) (hs : rho.SendsAt (rho.key x) source τ)
    (hrel : Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m z] ∈
      rho.releasesAt source)
    (hfirst : ∀ i < source,
      Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m z] ∉
        rho.releasesAt i)
    {j : Nat} (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time j))
    (hj : (simTraceAt S rho hn).IsCall y j)
    (hb : (simTraceAt S rho hn).projAC.deadline y j τ ≤ b)
    (hd : (simTraceAt S rho hn).projAC.deadline y j τ ≤ (simTraceAt S rho hn).time j) :
    ∃ k ≤ j, τ ≤ (simTraceAt S rho hn).time k ∧
      (simTraceAt S rho hn).projAC.ProcessAt y k m ∧
      (simTraceAt S rho hn).time k < (simTraceAt S rho hn).projAC.deadline y k τ := by
  have hrun := network_localRun S rho hn hv
  have htr := network_trace_eq S rho hn
  rw [Compose.projAC_deadline] at hb hd
  rw [htr, network_honestKeysAt_eq] at hy
  rw [htr] at hj hb hd
  have hp := NodeAsChainShape.CanonicalTrace.publication_messageDeliveredBy hrun hx hne
    (votePublication_intro S rho hck hs hrel hfirst)
    (fun _ hy hj => NodeAsChainShape.CanonicalTrace.publication_held_before_syncUntil
      hrun le_rfl hbh hnet ⟨source, hs, hrel⟩ hx
      (by simp [log_fgAtt_iff, isFGAtt, IsAttObj]) hy hj hτ)
    (fun _ hh hx hhld => htr ▸ votePublication_process S rho hn hv hh hx hhld) hy hj hb hd
  rw [← htr] at hp
  obtain ⟨k, hk, hlo, hm, ht⟩ := hp
  refine ⟨k, hk, hlo, ?_, by rwa [Compose.projAC_deadline]⟩
  exact hm.elim (fun ⟨ℓ, hc, h⟩ => ⟨ℓ, Compose.projAC_callAt.mpr hc, Or.inl h⟩)
    (fun ⟨ℓ, hc, h⟩ => ⟨ℓ, Compose.projAC_callAt.mpr hc, Or.inr h⟩)

end Consensus.Goldilocks.Obligations.Growing

namespace Consensus.Goldilocks.Simulation
open AsChainShape Obligations Obligations.Growing
open Shape Blocks
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **The finite sleepy service under growing faults** from raw synchrony through its deadline
bound `b ≤ horizon`: senders honest at their sends, recipients honest at their reading calls
(`Compose.Growing.SleepyServiceBefore`). Self-service uses fresh processing at the source time. -/
theorem sleepyServiceBefore_of_syncUntil_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {b : Time} (hbh : b ≤ rho.horizon) (hnet : rho.log.SyncUntil rho.point b) :
    Compose.Growing.SleepyServiceBefore (simTraceAt S rho hn) (honestKeysAt S rho)
      (S.params (pubOf E) hn).Δ b := by
  have hr := simTraceAt_goldilocksRun S rho hn hv
  have hsim := simTraceAt_simulates S rho hn hv
  apply sleepyServiceBefore_of_message_relay_at hr
  · intro x i m hx hsrc h0 y j ℓ hy hj hb hd
    rw [AC.messageServedBefore_iff]
    apply Or.inl
    have hsource : (simTraceAt S rho hn).SendOrAdmitAt x i m := by
      obtain ⟨l, hl, hm⟩ := hsrc
      refine ⟨l, Compose.projAC_callAt.mp hl, ?_⟩
      rw [projAC_state_at hr hx] at hm
      exact hm
    have htr := network_trace_eq S rho hn
    have hrun := network_localRun S rho hn hv
    have hih := isCall_time_le_horizon S rho hn hv ⟨_, hsource.choose_spec.1⟩
    have hh := not_faulty_of_mem_honestKeysAt S rho hx le_rfl hih
    have hc : (simTraceAt S rho hn).IsCall y j := ⟨_, Compose.projAC_callAt.mp hj⟩
    rw [Compose.projAC_deadline] at hb hd
    rw [htr, network_honestKeysAt_eq] at hy
    rw [htr] at h0 hh hc hb hd
    have hm := NodeAsChainShape.CanonicalTrace.messageDeliveredBy hrun
      (MsgPub := VotePublication S rho) (i := i) le_rfl
      (by
        rw [← htr]
        obtain ⟨k, ⟨l, hc, hm⟩, ht⟩ := sendOrAdmit_process_same_time_at S rho hn hv hx hsource
        exact ⟨k, hm.elim (fun h => Or.inl ⟨l, Compose.projAC_callAt.mp hc, h⟩)
          (fun h => Or.inr ⟨l, Compose.projAC_callAt.mp hc, h⟩), ht⟩)
      (by
        rw [← htr]
        obtain ⟨z, hck, r, -, -, hs, hrel, hf⟩ := hsim.vote_forwarded x i m hx
          (sendOrAdmit_forward_source_at hr hx hsrc)
        exact ⟨_, votePublication_intro S rho hck hs hrel hf, ⟨r, hs, hrel⟩,
          by simp [log_fgAtt_iff, isFGAtt, IsAttObj]⟩)
      hh (fun _ hrel hrow _ hy hj =>
        NodeAsChainShape.CanonicalTrace.publication_held_before_syncUntil
          hrun le_rfl hbh hnet hrel hh hrow hy hj h0)
      (fun _ _ hpub hx held => htr ▸ votePublication_process S rho hn hv hpub hx held) hy hc hb hd
    rw [← htr] at hm
    obtain ⟨k, hk, hlo, hp, ht⟩ := hm
    refine ⟨k, hk, hlo, ?_, by rwa [Compose.projAC_deadline]⟩
    exact hp.elim (fun ⟨l, hc, h⟩ => ⟨l, Compose.projAC_callAt.mpr hc, Or.inl h⟩)
      (fun ⟨l, hc, h⟩ => ⟨l, Compose.projAC_callAt.mpr hc, Or.inr h⟩)
  · intro x i B hx hi h0 y j hy hj hb hd hF
    exact acceptance_relay_syncUntil_at S rho hn hv hnc hbh hnet hx hi h0 hy hj hb hd hF

end Consensus.Goldilocks.Simulation

end
