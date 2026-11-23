module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Obligations
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Retention
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.DeadlineWake
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Network transport under growing faults: service after GST

The partial-synchrony (`PSync g`) service of the canonical growing trace, with senders honest at
their event and recipients honest at their call:

* `received_forward_stamp_le_of_stamp_at`: a received wrapper of a signer honest at its stamp is
  stamped no later than the receipt;
* `publication_held_before_gst_deadline_at`, `publication_acceptedBy_psync_any_at`,
  `acceptance_relay_psync_any_at`: acceptance relay at the effective `max(source, GST)` deadline;
* `held_forward_blockCall_before_at`, `publication_blockDeliveredBy_psync_at`,
  `ownBlockAt_accept_at`, `block_service_psync_at`: block service;
* `vote_message_service_psync_other_at`, `message_service_psync_at`: message service;
* `resetService_of_psync_at`: the reset service of a healthy run;
* `catchRun_of_psync_at`: old acceptances catch up by the first `2Δ` snapshot after GST. -/

namespace Consensus.Goldilocks.Growing.LocalRun

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- An honest node's own block call accepts, given the requirements at its actual start. -/
theorem ownBlockAt_accept (hrun : LocalRun proposer dg H sg tr ini)
    (hreq : ∀ y, ({ A with initial := ini y } : NodeAC P).Requirements)
    (hroot : (P.genesisBlock A.genesisPayload).RootOk dg)
    (hnc : Compose.NoCollRun dg tr) {y : Fin P.n} {i : Nat} {B : A.Blk}
    (hy : y ∈ H (tr.time i)) (hown : tr.OwnBlockAt y i B) : tr.AcceptAt y i B := by
  let d := tr.time i
  have run := hrun.upTo (hrun.time_nonneg i)
  have hnc' := Compose.NoCollRun.upTo hnc (d := d)
  obtain ⟨⟨acc, hc⟩, hpos⟩ := hown
  have hc' := (Trace.upTo_callAt_of_le _ le_rfl).mpr hc
  rcases Compose.blockCall_cases run hy hc' with hg |
    ⟨j, x, rfl, hg, hp, dd, pay, hdp, hB, hacc, _, _, _⟩
  · have h0 := (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1
    simp only [Nat.add_zero] at h0
    exact False.elim (hpos h0)
  · obtain ⟨cfg, hr, hst, hs⟩ := Compose.group_step run hy hg
    have h := Compose.honest_block_accepted_from proposer dg y (hreq y)
      hroot cfg _ _ x hr hs hp dd pay (by rw [hst]; exact hdp)
    simp only [hst] at h
    have key : Compose.NoCollOn dg (insert B ((tr.upTo d).state y j).fg.tree) →
        ∃ fg', ((tr.upTo d).state y j).fg.onBlock B = some fg' := by
      rw [hB]
      exact fun hnc => (h.2.2.2.2.2.2 hnc).2
    have hon := key (hnc'.mono (Set.insert_subset_iff.2
      ⟨Or.inr ⟨y, j + 2, acc, hc'⟩, Compose.tree_subset_run run hy j⟩))
    have he := hacc.mpr hon
    subst acc
    exact hc

end Consensus.Goldilocks.Growing.LocalRun

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Shape Blocks

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
  {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
  {hn : 1 ≤ Fintype.card V} {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)}
  {e : Encoding F E p hN hn A} {rho : Model.Run (compiled F) E}
  {proposer : Nat → Fin (Fintype.card V)} {sg : A.Msg → Fin (Fintype.card V)}
  {ini : Fin (Fintype.card V) → A.State}

/-- The held wrapper supplies a block call, not necessarily an acceptance. -/
theorem publication_blockDeliveredBy_psync
    (hr : Growing.LocalRun proposer (digestOf e rho) (honestKeysAt rho) sg (simTrace e rho) ini)
    (hΔ : E.ΔAC ≤ p.Δ) {g : Time} (hnet : rho.log.PSync rho.point g)
    {x y : Fin (Fintype.card V)} {τ : Time} {B : A.Blk}
    {o : (Model.protoOf (compiled F) E).Object}
    (hrel : rho.releases (rho.key x) o τ) (hx : rho.key x ∉ rho.faultyAt τ)
    (hrow : ¬ rho.log.fgAtt o) (hτ : 0 ≤ τ)
    (blockCall : ∀ {j d D}, rho.log.Held rho.point (rho.key y) o d → d < D →
      D ≤ (simTrace e rho).time j → ∃ k ≤ j, τ ≤ (simTrace e rho).time k ∧
        (simTrace e rho).BlockCallAt y k B ∧ (simTrace e rho).time k < D)
    {j : Nat} (hy : y ∈ honestKeysAt rho ((simTrace e rho).time j))
    (hj : (simTrace e rho).IsCall y j)
    (hb : (simTrace e rho).deadline y j (max τ g) p.Δ ≤ rho.horizon)
    (hd : (simTrace e rho).deadline y j (max τ g) p.Δ ≤ (simTrace e rho).time j) :
    (simTrace e rho).BlockDeliveredBy y j τ (max τ g) B := by
  let tr := simTrace e rho
  obtain ⟨k, hkj, ⟨hlo, hc⟩, ht⟩ := RunTrace.service_at_processing_cut hr
    (inScope := fun k => tr.deadline y k (max τ g) p.Δ ≤ rho.horizon)
    (processed := fun k => τ ≤ tr.time k ∧ tr.BlockCallAt y k B)
    (fun hkj _ h => (RunTrace.deadline_mono_cut_of_time_mono tr hr.time_mono y _ _ hkj).trans h)
    (by
      intro k hy hj hb hd
      obtain ⟨d, hh, hlt⟩ := publication_held_before_psync hr hΔ hnet hrel hx hrow hy hj hτ hb hd
      obtain ⟨l, hl, hlo, hc, ht⟩ := blockCall hh hlt hd
      obtain ⟨acc, hcall⟩ := hc
      exact ⟨l, hl, ⟨_, hcall⟩, ⟨hlo, acc, hcall⟩, ht⟩) hy hj hb hd
  exact ⟨k, hkj, hlo, hc, ht⟩

/-- Block service from an acceptance publication. An own block call first uses the
node's actual start requirements to obtain its acceptance. -/
theorem blockService_psync
    (hr : Growing.LocalRun proposer (digestOf e rho) (honestKeysAt rho) sg (simTrace e rho) ini)
    (hΔ : E.ΔAC ≤ p.Δ) {g : Time} (hnet : rho.log.PSync rho.point g)
    (hreq : ∀ x, ({ A with initial := ini x } : NodeAC _).Requirements)
    (hroot : ((paramsAtCount p (Fintype.card V) hN hn).genesisBlock A.genesisPayload).RootOk
      (digestOf e rho)) (hnc : Compose.NoCollRun (digestOf e rho) (simTrace e rho))
    {fwd : (Model.protoOf (compiled F) E).Object →
      Option (Fin (Fintype.card V) × Time × Option (Model.protoOf (compiled F) E).Object × A.Blk)}
    {x y : Fin (Fintype.card V)} {i j : Nat} {B : A.Blk}
    (hx : x ∈ honestKeysAt rho ((simTrace e rho).time i))
    (hi : (simTrace e rho).AcceptAt x i B ∨ (simTrace e rho).OwnBlockAt x i B)
    (hih : (simTrace e rho).time i ≤ rho.horizon)
    (pub : (simTrace e rho).AcceptAt x i B →
      ∃ o parent ev, cutMap e rho ev ≤ i ∧ i < cutMap e rho (ev + 1) ∧
        rho.SendsAt (rho.key x) ev ((simTrace e rho).time i) ∧ o ∈ rho.releasesAt ev ∧
        fwd o = some (x, (simTrace e rho).time i, parent, B) ∧ ¬ rho.log.fgAtt o)
    (blockCall : ∀ {o parent k d D}, fwd o = some (x, (simTrace e rho).time i, parent, B) →
      rho.releases (rho.key x) o ((simTrace e rho).time i) →
      rho.key x ∉ rho.faultyAt ((simTrace e rho).time i) →
      rho.log.Held rho.point (rho.key y) o d → d < D → D ≤ (simTrace e rho).time k →
      ∃ l ≤ k, (simTrace e rho).time i ≤ (simTrace e rho).time l ∧
        (simTrace e rho).BlockCallAt y l B ∧ (simTrace e rho).time l < D)
    (hy : y ∈ honestKeysAt rho ((simTrace e rho).time j)) (hj : (simTrace e rho).IsCall y j)
    (hb : (simTrace e rho).time j ≤ rho.horizon)
    (hd : (simTrace e rho).deadline y j (max ((simTrace e rho).time i) g) p.Δ ≤
      (simTrace e rho).time j) :
    (simTrace e rho).BlockDeliveredBy y j ((simTrace e rho).time i)
      (max ((simTrace e rho).time i) g) B := by
  obtain ⟨o, parent, ev, _, _, hs, ho, hdec, hrow⟩ :=
    pub (hi.elim id (hr.ownBlockAt_accept hreq hroot hnc hx))
  have hrel : rho.releases (rho.key x) o ((simTrace e rho).time i) := ⟨ev, hs, ho⟩
  have hxt := not_faulty_of_mem_honestKeysAt hx le_rfl hih
  exact publication_blockDeliveredBy_psync hr hΔ hnet hrel hxt hrow (hr.time_nonneg i)
    (blockCall hdec hrel hxt) hy hj (hd.trans hb) hd

/-- Assemble post-stop service from the two bounded readers. In particular the relay row
also covers acceptances before GST. -/
theorem postStopService_of_bounded {g : Time}
    (inHorizon : ∀ {y j}, (simTrace e rho).IsCall y j → (simTrace e rho).time j ≤ rho.horizon)
    (message : ∀ x i m, x ∈ honestKeysAt rho ((simTrace e rho).time i) →
      (simTrace e rho).SendOrAdmitAt x i m →
      ∀ y j, y ∈ honestKeysAt rho ((simTrace e rho).time j) → (simTrace e rho).IsCall y j →
        (simTrace e rho).time j ≤ rho.horizon →
        (simTrace e rho).deadline y j (max ((simTrace e rho).time i) g) p.Δ ≤
          (simTrace e rho).time j →
        (simTrace e rho).MsgDeliveredBy y j ((simTrace e rho).time i)
          (max ((simTrace e rho).time i) g) m)
    (relay : ∀ x i B, x ∈ honestKeysAt rho ((simTrace e rho).time i) →
      (simTrace e rho).AcceptAt x i B →
      ∀ y j, y ∈ honestKeysAt rho ((simTrace e rho).time j) → (simTrace e rho).IsCall y j →
        (simTrace e rho).time j ≤ rho.horizon →
        (simTrace e rho).deadline y j (max ((simTrace e rho).time i) g) p.Δ ≤
          (simTrace e rho).time j →
        Anc ((simTrace e rho).HonestBlocksAt (honestKeysAt rho))
          ((simTrace e rho).state y j).fg.F B →
        (simTrace e rho).BlockAcceptedBy y j (max ((simTrace e rho).time i) g) B) :
    Generic.PostStopService (simTrace e rho) (honestKeysAt rho) g where
  message x i m hx hi y j hy hj := message x i m hx hi y j hy hj (inHorizon hj)
  relay x i B hx hi y j hy hj := relay x i B hx hi y j hy hj (inHorizon hj)

/-- The healthy service uses the same message and relay rows as post-stop service. The
additional block-call and signed-row suppliers are consumed only in their own rows. -/
theorem service_of_postStop {g ΔF : Time}
    (hs : Generic.PostStopService (simTrace e rho) (honestKeysAt rho) g)
    (hΔF : 0 < ΔF)
    (block : ∀ x i B, x ∈ honestKeysAt rho ((simTrace e rho).time i) →
      (simTrace e rho).AcceptAt x i B ∨ (simTrace e rho).OwnBlockAt x i B →
      ∀ y j, y ∈ honestKeysAt rho ((simTrace e rho).time j) → (simTrace e rho).IsCall y j →
        (simTrace e rho).deadline y j (max ((simTrace e rho).time i) g) p.Δ ≤
          (simTrace e rho).time j →
        (simTrace e rho).BlockDeliveredBy y j ((simTrace e rho).time i)
          (max ((simTrace e rho).time i) g) B)
    (row : ∀ x i att, x ∈ honestKeysAt rho ((simTrace e rho).time i) →
      (simTrace e rho).SignAt x i att →
      ∀ y j, y ∈ honestKeysAt rho ((simTrace e rho).time j) → (simTrace e rho).IsCall y j →
        (simTrace e rho).time j ≤ rho.horizon →
        (simTrace e rho).deadline y j (max ((simTrace e rho).time i) g) ΔF ≤
          (simTrace e rho).time j →
        ∃ k ≤ j, (simTrace e rho).ProcessAttAt y k att ∧
          (simTrace e rho).time k <
            (simTrace e rho).deadline y k (max ((simTrace e rho).time i) g) ΔF) :
    Generic.Service (simTrace e rho) (honestKeysAt rho) g ΔF rho.horizon :=
  ⟨hΔF, hs.message, block, fun x i B hx hi _ => hs.relay x i B hx hi, row⟩

/-- Catch up at the first snapshot after the publication window, even if the snapshot is a
stutter beyond the horizon. The witness is an acceptance strictly before the snapshot cut. -/
theorem catchUp_at_snapshot (hΔ : E.ΔAC ≤ p.Δ) {g : Time}
    (hnet : rho.log.PSync rho.point g)
    (hawake : ∀ v u, max g 0 ≤ u → u ≤ rho.horizon → u ≤ max g 0 + E.ΔAC - 1 →
      v ∉ rho.faultyAt u → E.awake v u = true)
    {x y : Fin (Fintype.card V)} {i j : Nat} {B : A.Blk}
    {o : (Model.protoOf (compiled F) E).Object}
    (hx : rho.key x ∉ rho.faultyAt ((simTrace e rho).time i))
    (hrel : rho.releases (rho.key x) o ((simTrace e rho).time i)) (hrow : ¬ rho.log.fgAtt o)
    (hbefore : (simTrace e rho).time i < max g 0)
    (hy : y ∈ honestKeysAt rho (max g 0 + 2 * p.Δ))
    (hfirst : (simTrace e rho).FirstCutFrom j (max g 0 + 2 * p.Δ))
    (hbound : (simTrace e rho).time j ≤ rho.horizon + 1)
    (hF : Anc ((simTrace e rho).HonestBlocksAt (honestKeysAt rho))
      ((simTrace e rho).state y j).fg.F B)
    (accept : ∀ {t₀ d D}, (∀ k < j, (simTrace e rho).time k ≤ t₀) →
      rho.key y ∉ rho.faultyAt t₀ → rho.log.Held rho.point (rho.key y) o d →
      d < D → D ≤ (simTrace e rho).time j →
      Anc ((simTrace e rho).HonestBlocksAt (honestKeysAt rho))
        ((simTrace e rho).state y j).fg.F B →
      ∃ k ≤ j, (simTrace e rho).AcceptAt y k B ∧ (simTrace e rho).time k < D) :
    ∃ k < j, (simTrace e rho).AcceptAt y k B := by
  have hstart := hfirst.1
  have hpos := p.hΔ
  have hservice : max g 0 + E.ΔAC - 1 ≤ rho.horizon := by linarith
  have hdl : max g 0 + E.ΔAC - 1 < max g 0 + p.Δ := by linarith
  have hdeadline : max g 0 + p.Δ ≤ (simTrace e rho).time j := by linarith
  have hyT := (mem_honestKeysAt_iff _ _ _).mp hy
  have hdlT : max g 0 + E.ΔAC - 1 ≤ min (max g 0 + 2 * p.Δ) rho.horizon :=
    le_min (by linarith) hservice
  have hat : rho.key y ∉ rho.faultyAt (max g 0 + E.ΔAC - 1) :=
    fun h => hyT (rho.faultyAt_mono hdlT h)
  have haw : rho.point.AwakeOnClosed (rho.key y) (max g 0) (max g 0 + E.ΔAC - 1) :=
    fun u hlo hhi => hawake (rho.key y) u hlo (hhi.trans hservice) hhi
      (fun h => hyT (rho.faultyAt_mono (hhi.trans hdlT) h))
  have hg : max (max g 0) g = max g 0 := max_eq_left (le_max_left _ _)
  have hservice' : max (max g 0) g + E.ΔAC - 1 ≤ rho.horizon := hg.symm ▸ hservice
  have hat' : rho.key y ∉ rho.faultyAt (max (max g 0) g + E.ΔAC - 1) := hg.symm ▸ hat
  have haw' : rho.point.AwakeOnClosed (rho.key y) (max g 0)
      (max (max g 0) g + E.ΔAC - 1) := hg.symm ▸ haw
  have held := hnet.msgs _ _ _ hrel hx hrow (rho.key y) (max g 0) hbefore.le
    hservice' hservice' hat' haw'
  change rho.log.Held rho.point (rho.key y) o (max (max g 0) g + E.ΔAC - 1) at held
  rw [hg] at held
  have hj₀ : ∀ k < j, (simTrace e rho).time k ≤ min (max g 0 + 2 * p.Δ) rho.horizon := by
    intro k hk
    have hkT := hfirst.2 k hk
    exact le_min hkT.le (Int.lt_add_one_iff.mp (hkT.trans_le (hstart.trans hbound)))
  obtain ⟨k, hk, ha, ht⟩ := accept hj₀ hyT held hdl hdeadline hF
  exact ⟨k, lt_of_le_of_ne hk (by rintro rfl; exact (not_lt_of_ge hdeadline) ht), ha⟩

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Shape Blocks

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)

/-- A received forwarding wrapper of a signer honest at its stamp carries a stamp no later than
the receipt: were the receipt earlier, the signer would be honest at it. -/
theorem received_forward_stamp_le_of_stamp_at (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {receipt o : Wire (Fintype.card V) S.vote} {x : Fin (Fintype.card V)} {t u : Time}
    {p : Option (Wire (Fintype.card V) S.vote)} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    (hc : Model.Obj.Contains receipt o) (hx : rho.key x ∉ rho.faultyAt t)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) : t ≤ u := by
  by_contra h
  have hut : u ≤ t := (lt_of_not_ge h).le
  exact h (received_forward_stamp_le_at S rho hn hv he hc
    (fun hf => hx (rho.faultyAt_mono hut hf)) hd)

/-- GST holdings of an actual publication by an origin honest at its event, at a recipient
honest at its call, before the effective `max(source, GST)` deadline. -/
theorem publication_held_before_gst_deadline_at (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) {g : Time} (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r)
    (hx : rho.key r.origin ∉ rho.faultyAt ((publisherExecution S rho).eventTime r.event))
    (hrow : ¬ rho.log.fgAtt r.object)
    {y : Fin (Fintype.card V)} {j : Nat}
    (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time j))
    (hj : (simTraceAt S rho hn).IsCall y j) {τ : Time} (hτ : 0 ≤ τ)
    (ht : (publisherExecution S rho).eventTime r.event = τ)
    (hb : (simTraceAt S rho hn).deadline y j (max τ g)
      (S.params (Model.pubOf E) hn).Δ ≤ rho.horizon)
    (hd : (simTraceAt S rho hn).deadline y j (max τ g)
      (S.params (Model.pubOf E) hn).Δ ≤ (simTraceAt S rho hn).time j) :
    ∃ d, rho.log.Held rho.point (rho.key y) r.object d ∧
      d < (simTraceAt S rho hn).deadline y j (max τ g) (S.params (Model.pubOf E) hn).Δ := by
  have hrel : rho.releases (rho.key r.origin) r.object τ :=
    ht ▸ ⟨r.event, (publisherExecution S rho).actual_event r hr,
      (publisherExecution S rho).actual_release r hr⟩
  have htr := network_trace_eq S rho hn
  rw [htr, network_honestKeysAt_eq] at hy
  rw [htr] at hj hb hd ⊢
  exact NodeAsChainShape.CanonicalTrace.publication_held_before_psync (network_localRun S rho hn hv)
    le_rfl hnet hrel (ht ▸ hx) hrow hy hj hτ hb hd

/-- Acceptance service for an actual publication by an origin honest at its event, including a
pre-GST one, at the effective `max(source, GST)` deadline at the acceptance cut. -/
theorem publication_acceptedBy_psync_any_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {g : Time} (hnet : rho.log.PSync rho.point g)
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
    (hb : (simTraceAt S rho hn).deadline y j (max τ g) (S.params (Model.pubOf E) hn).Δ
      ≤ rho.horizon)
    (hd : (simTraceAt S rho hn).deadline y j (max τ g) (S.params (Model.pubOf E) hn).Δ
      ≤ (simTraceAt S rho hn).time j)
    (hF : Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho))
      ((simTraceAt S rho hn).state y j).fg.F B) :
    (simTraceAt S rho hn).BlockAcceptedBy y j (max τ g) B := by
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
    (fun _ hy hj => NodeAsChainShape.CanonicalTrace.publication_held_before_psync
      hrun le_rfl hnet hrel hx (not_isFGAtt_of_decodeForward hdecode) hy hj hτ) _ hy hj hh hb hd hF
  intro j t₀ d D hj₀ hy hx hrel hheld hlt hd hF
  rw [← htr] at hj₀ hd ⊢
  rw [← htr, ← hH] at hF
  exact held_forward_accepted_before_at S rho hn hv hnc hj₀ hy hx hrel hheld hdecode hlt hd hF

/-- The acceptance-relay service for an acceptance by a node honest at its cut, including a
pre-GST one, at a recipient honest at its call within the horizon. -/
theorem acceptance_relay_psync_any_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {g : Time} (hnet : rho.log.PSync rho.point g)
    {x : Fin (Fintype.card V)} {i : Nat}
    (hx : x ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i))
    {B : Blk (S.params (Model.pubOf E) hn)} (hi : (simTraceAt S rho hn).AcceptAt x i B)
    {y : Fin (Fintype.card V)} {j : Nat}
    (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time j))
    (hj : (simTraceAt S rho hn).IsCall y j) (hb : (simTraceAt S rho hn).time j ≤ rho.horizon)
    (hd : (simTraceAt S rho hn).deadline y j (max ((simTraceAt S rho hn).time i) g)
      (S.params (Model.pubOf E) hn).Δ ≤ (simTraceAt S rho hn).time j)
    (hF : Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho))
      ((simTraceAt S rho hn).state y j).fg.F B) :
    (simTraceAt S rho hn).BlockAcceptedBy y j (max ((simTraceAt S rho hn).time i) g) B := by
  have hih : (simTraceAt S rho hn).time i ≤ rho.horizon :=
    isCall_time_le_horizon S rho hn hv ⟨_, hi⟩
  have hpub := acceptancePublication S rho hn hv hx hi
  have hxt := not_faulty_of_mem_honestKeysAt S rho hx le_rfl hih
  have htr := network_trace_eq S rho hn
  rw [htr, network_honestKeysAt_eq] at hy hF
  rw [htr] at hpub hxt hj hb hd ⊢
  have hrun := network_localRun S rho hn hv
  apply NodeAsChainShape.CanonicalTrace.acceptanceRelay hrun hxt hpub
    (fun _ hrel hrow _ hy hj => NodeAsChainShape.CanonicalTrace.publication_held_before_psync
      hrun le_rfl hnet hrel hxt hrow hy hj (hrun.time_nonneg i)) _ hy hj hb (hd.trans hb) hd hF
  intro o parent k t₀ d D hdecode hj₀ hy hx hrel held hlt hd hF
  rw [← htr] at hj₀ hd ⊢
  rw [← htr, ← network_honestKeysAt_eq S rho] at hF
  exact held_forward_accepted_before_at S rho hn hv hnc hj₀ hy hx hrel held hdecode hlt hd hF

/-- Holdings of a decoded wrapper of a signer honest at its stamp give a block call after the
stamp. Local publication uses the actual acceptance; receipt uses recursive block processing. -/
theorem held_forward_blockCall_before_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {y x : Fin (Fintype.card V)} {j : Nat} {o : Wire (Fintype.card V) S.vote} {t d D : Time}
    {p : Option (Wire (Fintype.card V) S.vote)}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hx : rho.key x ∉ rho.faultyAt t)
    (hheld : rho.log.Held rho.point (rho.key y) o d)
    (hdecode : decodeForward (S.params
      (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B))
    (hd : d < D) (hj : D ≤ (simTraceAt S rho hn).time j) :
    ∃ k ≤ j, t ≤ (simTraceAt S rho hn).time k ∧
      (simTraceAt S rho hn).BlockCallAt y k B ∧
        (simTraceAt S rho hn).time k <
          D := by
  have hmono := (simTraceAt_goldilocksRun S rho hn hv).time_mono
  rw [simTraceAt_eq S rho hn] at hj hmono ⊢
  obtain ⟨u, hud, hsource, _⟩ := hheld
  have huD : u < D := hud.trans_lt hd
  have hkey : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply _
  have before {k : Nat} (hk : (simTrace S rho hn).time k < D) : k ≤ j := by
    by_contra h
    have htime := hmono (show j ≤ k by omega)
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
    have htu := received_forward_stamp_le_of_stamp_at
      S rho hn hv hi (.refl o) hx hdecode
    obtain ⟨k, _, hc, ht⟩ := received_forward_blockCall
      S rho hn hi rfl hdecode htu
    have hk : (simTrace S rho hn).time k < D := ht ▸ huD
    exact ⟨k, before hk, ht ▸ htu, hkey ▸ hc, hk⟩

/-- A decoded publication by an origin honest at its event receives block service at the
processing cut's GST deadline, including publications before GST. -/
theorem publication_blockDeliveredBy_psync_at {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) {g : Time} (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r)
    {τ : Time} (hτ : 0 ≤ τ)
    (ht : (publisherExecution S rho).eventTime r.event = τ)
    (hx : rho.key r.origin ∉ rho.faultyAt τ)
    {p : Option (Wire (Fintype.card V) S.vote)}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hdecode : decodeForward (S.params
      (Model.pubOf E) hn)
      (Model.digests rho.hash r.object) r.object = some (r.origin, τ, p, B))
    {y : Fin (Fintype.card V)} {j : Nat}
    (hy : y ∈ honestKeysAt S rho
      ((simTraceAt S rho hn).time j))
    (hj : (simTraceAt S rho hn).IsCall y j)
    (hb : (simTraceAt S rho hn).deadline y j (max τ g)
      (S.params (Model.pubOf E) hn).Δ ≤ rho.horizon)
    (hd : (simTraceAt S rho hn).deadline y j (max τ g)
      (S.params (Model.pubOf E) hn).Δ ≤
        (simTraceAt S rho hn).time j) :
    (simTraceAt S rho hn).BlockDeliveredBy y j τ (max τ g) B := by
  have hrel : rho.releases (rho.key r.origin) r.object τ :=
    ht ▸ ⟨r.event, (publisherExecution S rho).actual_event r hr,
      (publisherExecution S rho).actual_release r hr⟩
  have htr := network_trace_eq S rho hn
  rw [htr, network_honestKeysAt_eq] at hy
  rw [htr] at hj hb hd ⊢
  apply NodeAsChainShape.CanonicalTrace.publication_blockDeliveredBy_psync
    (network_localRun S rho hn hv) le_rfl hnet hrel hx (not_isFGAtt_of_decodeForward hdecode)
    hτ _ hy hj hb hd
  intro j d D hh hlt hd
  rw [← htr] at hd ⊢
  exact held_forward_blockCall_before_at S rho hn hv hx hh hdecode hlt hd

/-- An own-block call of a node honest at it is an acceptance under collision freedom. -/
theorem ownBlockAt_accept_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho)
      (simTraceAt S rho hn))
    {y : Fin (Fintype.card V)} {i : Nat}
    (hy : y ∈ honestKeysAt S rho
      ((simTraceAt S rho hn).time i))
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hown : (simTraceAt S rho hn).OwnBlockAt y i B) :
    (simTraceAt S rho hn).AcceptAt y i B := by
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  exact hrun.toLocalRun.ownBlockAt_accept (fun y => Compose.requirements_from _ _ (hrun.vstart y))
    hrun.genesis_root_ok hnc hy hown

/-- Finite GST block service for blocks accepted or proposed by a node honest at its cut, at a
recipient honest at its call within the horizon, with the source-time lower bound and the
effective `max(source, GST)` processing deadline. -/
theorem block_service_psync_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho)
      (simTraceAt S rho hn))
    {g : Time} (hnet : rho.log.PSync rho.point g)
    {x : Fin (Fintype.card V)} {i : Nat}
    (hx : x ∈ honestKeysAt S rho
      ((simTraceAt S rho hn).time i))
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hi : (simTraceAt S rho hn).AcceptAt x i B ∨
        (simTraceAt S rho hn).OwnBlockAt x i B)
    {y : Fin (Fintype.card V)} {j : Nat}
    (hy : y ∈ honestKeysAt S rho
      ((simTraceAt S rho hn).time j))
    (hj : (simTraceAt S rho hn).IsCall y j)
        (hb : (simTraceAt S rho hn).time j ≤ rho.horizon)
    (hd : (simTraceAt S rho hn).deadline y j
        (max ((simTraceAt S rho hn).time i) g)
      (S.params (Model.pubOf E) hn).Δ ≤
        (simTraceAt S rho hn).time j) :
    (simTraceAt S rho hn).BlockDeliveredBy y j
      ((simTraceAt S rho hn).time i)
      (max ((simTraceAt S rho hn).time i) g) B := by
  have hih : (simTraceAt S rho hn).time i ≤ rho.horizon :=
    isCall_time_le_horizon S rho hn hv
      (hi.elim (fun ha => ⟨_, ha⟩) (fun ⟨⟨_, hc⟩, _⟩ => ⟨_, hc⟩))
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  have htr := network_trace_eq S rho hn
  have hH := network_honestKeysAt_eq S rho
  have hpub := acceptancePublication S rho hn hv hx (i := i) (B := B)
  obtain ⟨_, hdg⟩ := runProposer_digestOf S rho hn
  have hroot := hrun.genesis_root_ok
  rw [hdg] at hroot
  rw [hdg, htr] at hnc
  rw [htr, hH] at hx hy
  rw [htr] at hi hih hpub hj hb hd ⊢
  apply NodeAsChainShape.CanonicalTrace.blockService_psync (network_localRun S rho hn hv)
    le_rfl hnet (fun x => Compose.requirements_from _ _ (hrun.vstart x))
    hroot hnc hx hi hih hpub _ hy hj hb hd
  intro o parent k d D hdecode _ hx held hd' hk
  rw [← htr] at hdecode hx hk ⊢
  exact held_forward_blockCall_before_at S rho hn hv hx held hdecode hd' hk

/-- A first-release vote envelope of a sender honest at its release reaches a different recipient
honest at its call under PSync. The release time is the lower bound; GST changes only the service
deadline. -/
theorem vote_message_service_psync_other_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {g : Time} (hnet : rho.log.PSync rho.point g)
    {source : Nat} {x y : Fin (Fintype.card V)} {τ : Time} {m : AC.Vote (Fintype.card V)}
    (hx : rho.key x ∉ rho.faultyAt τ) (hne : y ≠ x)
    (hτ : 0 ≤ τ) (hs : rho.SendsAt (rho.key x) source τ)
    (hrel : Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m] ∈
      rho.releasesAt source)
    (hfirst : ∀ i < source,
      Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m] ∉
        rho.releasesAt i)
    {j : Nat} (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time j))
    (hj : (simTraceAt S rho hn).IsCall y j)
    (hb : (simTraceAt S rho hn).time j ≤ rho.horizon)
    (hd : (simTraceAt S rho hn).projAC.deadline y j (max τ g) ≤ (simTraceAt S rho hn).time j) :
    ∃ k ≤ j, τ ≤ (simTraceAt S rho hn).time k ∧
      (simTraceAt S rho hn).projAC.ProcessAt y k m ∧
      (simTraceAt S rho hn).time k < (simTraceAt S rho hn).projAC.deadline y k (max τ g) := by
  have hrun := network_localRun S rho hn hv
  have htr := network_trace_eq S rho hn
  rw [Compose.projAC_deadline] at hd
  rw [htr, network_honestKeysAt_eq] at hy
  rw [htr] at hj hb hd
  have hp := NodeAsChainShape.CanonicalTrace.publication_messageDeliveredBy hrun hx hne
    (votePublication_intro S rho hs hrel hfirst)
    (fun _ hy hj hb hd => NodeAsChainShape.CanonicalTrace.publication_held_before_psync
      hrun le_rfl hnet ⟨source, hs, hrel⟩ hx
      (by simp [log_fgAtt_iff, isFGAtt, IsAttObj]) hy hj hτ hb hd)
    (fun _ hh hx hhld => htr ▸ votePublication_process S rho hn hv hh hx hhld)
    hy hj (hd.trans hb) hd
  rw [← htr] at hp
  obtain ⟨k, hk, hlo, hm, ht⟩ := hp
  refine ⟨k, hk, hlo, ?_, by rwa [Compose.projAC_deadline]⟩
  exact hm.elim (fun ⟨ℓ, hc, h⟩ => ⟨ℓ, Compose.projAC_callAt.mpr hc, Or.inl h⟩)
    (fun ⟨ℓ, hc, h⟩ => ⟨ℓ, Compose.projAC_callAt.mpr hc, Or.inr h⟩)

/-- AC sends and fresh admissions by a node honest at its cut are processed within the PSync
deadline by every recipient honest at its call within the horizon. The sender processes at the
source time; other nodes use the first-release envelope. -/
theorem message_service_psync_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {g : Time} (hnet : rho.log.PSync rho.point g)
    {x : Fin (Fintype.card V)} {i : Nat}
    (hx : x ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i))
    {m : AC.Vote (Fintype.card V)} (hi : (simTraceAt S rho hn).SendOrAdmitAt x i m)
    {y : Fin (Fintype.card V)} {j : Nat}
    (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time j))
    (hj : (simTraceAt S rho hn).IsCall y j) (hb : (simTraceAt S rho hn).time j ≤ rho.horizon)
    (hd : (simTraceAt S rho hn).deadline y j (max ((simTraceAt S rho hn).time i) g)
      (S.params (Model.pubOf E) hn).Δ ≤ (simTraceAt S rho hn).time j) :
    (simTraceAt S rho hn).MsgDeliveredBy y j ((simTraceAt S rho hn).time i)
      (max ((simTraceAt S rho hn).time i) g) m := by
  have hr := simTraceAt_goldilocksRun S rho hn hv
  have hsim := simTraceAt_simulates S rho hn hv
  have htr := network_trace_eq S rho hn
  have hrun := network_localRun S rho hn hv
  have hih := isCall_time_le_horizon S rho hn hv ⟨_, hi.choose_spec.1⟩
  have hhon := not_faulty_of_mem_honestKeysAt S rho hx le_rfl hih
  have h0 := hr.time_nonneg i
  rw [htr] at hhon h0 hb hj hd ⊢
  rw [htr, network_honestKeysAt_eq] at hy
  refine NodeAsChainShape.CanonicalTrace.messageDeliveredBy hrun (MsgPub := VotePublication S rho)
    (le_max_left _ _) ?_ ?_ hhon ?_ ?_ hy hj (hd.trans hb) hd
  · rw [← htr]
    obtain ⟨k, hp, ht⟩ := sendOrAdmit_process_same_time_at S rho hn hv hx hi
    obtain ⟨ℓ, hc, hm⟩ := hp
    exact ⟨k, hm.elim (fun h => Or.inl ⟨ℓ, Compose.projAC_callAt.mp hc, h⟩)
      (fun h => Or.inr ⟨ℓ, Compose.projAC_callAt.mp hc, h⟩), ht⟩
  · rw [← htr]
    have hproj : (simTraceAt S rho hn).projAC.SendOrAdmit x i m := by
      obtain ⟨l, hc, hs⟩ := hi
      refine ⟨l, Compose.projAC_callAt.mpr hc, ?_⟩
      rw [projAC_state_at hr hx]
      exact hs
    obtain ⟨source, _, _, hs, hrel, hfirst⟩ := hsim.vote_forwarded x i m hx
      (sendOrAdmit_forward_source_at hr hx hproj)
    exact ⟨_, votePublication_intro S rho hs hrel hfirst, ⟨source, hs, hrel⟩,
      by simp [log_fgAtt_iff, isFGAtt, IsAttObj]⟩
  · intro o hrel hrow k hy hj
    exact NodeAsChainShape.CanonicalTrace.publication_held_before_psync hrun
      le_rfl hnet hrel hhon hrow hy hj h0
  · intro o d
    rw [← htr]
    exact votePublication_process S rho hn hv

theorem postStopService_of_psync_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn)) {g : Time}
    (hnet : rho.log.PSync rho.point g) :
    Generic.PostStopService (simTraceAt S rho hn) (honestKeysAt S rho) g := by
  have htr := network_trace_eq S rho hn
  have hH := network_honestKeysAt_eq S rho
  rw [htr, hH]
  apply NodeAsChainShape.CanonicalTrace.postStopService_of_bounded
    (e := traceEncoding S hn) (rho := rho)
  · intro y j hj
    rw [← htr] at hj ⊢
    exact isCall_time_le_horizon S rho hn hv hj
  · rw [← htr, ← hH]
    exact fun _ _ _ hx hi _ _ hy hj => message_service_psync_at S rho hn hv hnet hx hi hy hj
  · rw [← htr, ← hH]
    exact fun _ _ _ hx hi _ _ hy hj =>
      acceptance_relay_psync_any_at S rho hn hv hnc hnet hx hi hy hj

/-- The finite valid engine run supplies every reset-service field under growing faults, with
attestation service at a parametric `Δ_F` as a premise (`hrow`). Senders are honest at their
event, recipients at their call; actual recipient calls lie within the engine horizon. -/
theorem resetService_of_psync_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho)
      (simTraceAt S rho hn))
    {g ΔF : Time} (hnet : rho.log.PSync rho.point g)
    (hrow : PSyncFGAttTransportAt S rho
      (simTraceAt S rho hn)
        (honestKeysAt S rho) ΔF)
    (hΔF : 0 < ΔF) :
    Healing.Growing.ResetService (simTraceAt S rho hn)
      (honestKeysAt S rho) g ΔF
      rho.horizon := by
  have htr := network_trace_eq S rho hn
  have hH := network_honestKeysAt_eq S rho
  have hs := postStopService_of_psync_at S rho hn hv hnc hnet
  rw [htr, hH] at hs
  have h := NodeAsChainShape.CanonicalTrace.service_of_postStop hs hΔF
    (by
      rw [← htr, ← hH]
      intro x i B hx hi y j hy hj hd
      exact block_service_psync_at S rho hn hv hnc hnet hx hi hy hj
        (isCall_time_le_horizon S rho hn hv hj) hd)
    (by
      rw [← htr, ← hH]
      exact (psyncFGAttTransportAt_iff S rho _ _ _).mp hrow g hnet)
  rw [← htr, ← hH] at h
  exact ⟨h.deltaF, h.message, h.block, h.relay, h.signedRow⟩

/-- Old acceptances by nodes honest at their cut catch up before the first `2Δ` snapshot after GST
at every node honest at that snapshot, when every node honest at a time of
`[max g 0, max g 0 + Δ − 1]` (within the horizon) is awake then: the snapshot node's publication
window. The snapshot supplies the finite service horizon. -/
theorem catchRun_of_psync_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho)
      (simTraceAt S rho hn))
    {g : Time} (hnet : rho.log.PSync rho.point g)
    (hawake : ∀ v u, max g 0 ≤ u → u ≤ rho.horizon → u ≤ max g 0 + E.ΔAC - 1 →
      v ∉ rho.faultyAt u → E.awake v u = true) :
    Healing.Growing.CatchRun (simTraceAt S rho hn)
      (honestKeysAt S rho) g
      (2 * (S.params (Model.pubOf E) hn).Δ) := by
  intro x i B hx hi hbefore y j hy hfirst hF
  have hbound : (simTraceAt S rho hn).time j ≤ rho.horizon + 1 := by
    rw [simTraceAt_eq S rho hn]
    cases hj : (allCuts S rho hn)[j]? with
    | none => rw [(simTrace_of_getElem?_none S rho hn hj).2]
    | some r =>
      have hl : (simTrace S rho hn).label j ≠ none := by
        rw [simTrace_label S rho hn, hj]; simp
      have hh := simTrace_labelled_time_le S rho hn hv hl
      linarith only [hh]
  have hih : (simTraceAt S rho hn).time i ≤ rho.horizon :=
    isCall_time_le_horizon S rho hn hv ⟨_, hi⟩
  obtain ⟨o, parent, ev, _, _, hs, ho, hdecode, hrow⟩ := acceptancePublication S rho hn hv hx hi
  have hrel : rho.releases (rho.key x) o ((simTraceAt S rho hn).time i) := ⟨ev, hs, ho⟩
  have hxt := not_faulty_of_mem_honestKeysAt S rho hx le_rfl hih
  have htr := network_trace_eq S rho hn
  have hH := network_honestKeysAt_eq S rho
  rw [hH] at hy hF
  rw [htr] at hF hrel hxt hbefore hfirst hbound ⊢
  apply NodeAsChainShape.CanonicalTrace.catchUp_at_snapshot le_rfl hnet hawake hxt hrel
    hrow hbefore hy hfirst hbound hF
  intro t₀ d D hj₀ hy hheld hlt hdeadline hF
  rw [← htr] at hj₀ hdeadline ⊢
  rw [← htr, ← hH] at hF
  rw [← htr] at hrel hxt
  exact held_forward_accepted_before_at S rho hn hv hnc hj₀ hy hxt hrel hheld
    hdecode hlt hdeadline hF

end Consensus.Goldilocks.Obligations.Growing

end
