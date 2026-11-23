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
public import ConsensusLean.Instances.Goldilocks.Results.Spec.NodeCanonicalTrace
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Retention
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeDeliveryOrigin
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

namespace Consensus.Goldilocks.RunTrace

variable {P : Params} {A : NodeAC P} {tr : RunTrace A}
  {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {H : Time → Set (Fin P.n)} {sg : A.Msg → Fin P.n} {ini : Fin P.n → A.State}

/-- Move the observation back to the processing cut if a restart enlarged its deadline.
`inScope` carries the prefix bound (or ancestry) needed by the particular reader. -/
theorem service_at_processing_cut (hr : Growing.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {τ Δ : Time} {inScope processed : Nat → Prop}
    (earlier : ∀ {k j}, k ≤ j → y ∈ H (tr.time j) → inScope j → inScope k)
    (step : ∀ j, y ∈ H (tr.time j) → tr.IsCall y j → inScope j →
      tr.deadline y j τ Δ ≤ tr.time j →
      ∃ k ≤ j, tr.IsCall y k ∧ processed k ∧ tr.time k < tr.deadline y j τ Δ)
    {j : Nat} (hy : y ∈ H (tr.time j)) (hj : tr.IsCall y j) (hs : inScope j)
    (hd : tr.deadline y j τ Δ ≤ tr.time j) :
    ∃ k ≤ j, processed k ∧ tr.time k < tr.deadline y k τ Δ := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    obtain ⟨k, hkj, hc, hp, ht⟩ := step j hy hj hs hd
    by_cases hk : tr.time k < tr.deadline y k τ Δ
    · exact ⟨k, hkj, hp, hk⟩
    · have hkj' : k < j := lt_of_le_of_ne hkj (by rintro rfl; exact hk ht)
      obtain ⟨l, hl, hl', hlt⟩ := ih k hkj' (hr.antitone (hr.time_mono hkj) hy) hc
        (earlier hkj hy hs) (le_of_not_gt hk)
      exact ⟨l, hl.trans hkj, hl', hlt⟩

end Consensus.Goldilocks.RunTrace

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Shape

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
  {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
  {hn : 1 ≤ Fintype.card V} {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)}
  {e : Encoding F E p hN hn A} {rho : Model.Run (compiled F) E}
  {proposer : Nat → Fin (Fintype.card V)} {sg : A.Msg → Fin (Fintype.card V)}
  {ini : Fin (Fintype.card V) → A.State}

omit [DecidableEq V] in
/-- Honesty at the observation implies engine honesty at earlier in-horizon times. -/
theorem not_faulty_of_mem_honestKeysAt {y : Fin (Fintype.card V)} {t a : Time}
    (hy : y ∈ honestKeysAt rho t) (hat : a ≤ t) (hah : a ≤ rho.horizon) :
    rho.key y ∉ rho.faultyAt a := by
  rw [mem_honestKeysAt_iff] at hy
  exact fun h => hy (rho.faultyAt_mono (le_min hat hah) h)

/-- The recipient is awake from its effective send/wake start through the reading call. -/
theorem deadline_awake_interval
    (hr : Growing.LocalRun proposer (digestOf e rho) (honestKeysAt rho) sg (simTrace e rho) ini)
    {y : Fin (Fintype.card V)} {j : Nat}
    (hy : y ∈ honestKeysAt rho ((simTrace e rho).time j)) (hj : (simTrace e rho).IsCall y j)
    {τ : Time} (hτ : 0 ≤ τ) (Δ : Time) :
    ∃ a, τ ≤ a ∧ (simTrace e rho).deadline y j τ Δ = a + Δ ∧
      rho.point.AwakeOnClosed (rho.key y) a ((simTrace e rho).time j) := by
  obtain ⟨a, hτa, heq, hw⟩ := (simTrace e rho).deadline_awake_of_call hr.time_mono hj
    (hr.awake_of_call y j hy hj) (fun u => hr.restart_at_wake y u _ hy)
    (fun k hk hkj => hr.sleep_of_restart y k (hr.antitone hkj hy) hk) hτ Δ
  exact ⟨a, hτa, heq, fun u hau huj => (simTrace_awake_iff e rho y u).mp (hw u hau huj) |>.1⟩

/-- A published non-FG object is held strictly before the reading cut's deadline.
The service function is supplied by `SyncUntil` or `PSync`; in the latter case the
effective send time is at least GST, so the start supplied to the log is also at least GST. -/
theorem publication_held_before_deadline
    (hr : Growing.LocalRun proposer (digestOf e rho) (honestKeysAt rho) sg (simTrace e rho) ini)
    (hΔ : E.ΔAC ≤ p.Δ) {b : Time} (hbh : b ≤ rho.horizon)
    {y : Fin (Fintype.card V)} {j : Nat} {σ : Time}
    {o : (Model.protoOf (compiled F) E).Object}
    (hnet : ∀ a, σ ≤ a → a + E.ΔAC - 1 ≤ b → a + E.ΔAC - 1 ≤ rho.horizon →
      rho.key y ∉ rho.faultyAt (a + E.ΔAC - 1) →
      rho.point.AwakeOnClosed (rho.key y) a (a + E.ΔAC - 1) →
      rho.log.Held rho.point (rho.key y) o (a + E.ΔAC - 1))
    (hy : y ∈ honestKeysAt rho ((simTrace e rho).time j)) (hj : (simTrace e rho).IsCall y j)
    (hσ : 0 ≤ σ) (hb : (simTrace e rho).deadline y j σ p.Δ ≤ b)
    (hd : (simTrace e rho).deadline y j σ p.Δ ≤ (simTrace e rho).time j) :
    ∃ d, rho.log.Held rho.point (rho.key y) o d ∧ d < (simTrace e rho).deadline y j σ p.Δ := by
  obtain ⟨a, ha, heq, hw⟩ := deadline_awake_interval hr hy hj hσ p.Δ
  rw [heq] at hb hd ⊢
  have hslack : a + E.ΔAC - 1 < a + p.Δ := by linarith
  have hdb := hslack.le.trans hb
  have hdh := hdb.trans hbh
  have hdj := hslack.le.trans hd
  exact ⟨_, hnet a ha hdb hdh (not_faulty_of_mem_honestKeysAt hy hdj hdh)
    (fun u hau hud => hw u hau (hud.trans hdj)), hslack⟩

/-- The holding step before the stop, keeping the original send time. -/
theorem publication_held_before_syncUntil
    (hr : Growing.LocalRun proposer (digestOf e rho) (honestKeysAt rho) sg (simTrace e rho) ini)
    (hΔ : E.ΔAC ≤ p.Δ) {b : Time} (hbh : b ≤ rho.horizon)
    (hnet : rho.log.SyncUntil rho.point b) {x y : Fin (Fintype.card V)} {j : Nat} {τ : Time}
    {o : (Model.protoOf (compiled F) E).Object}
    (hrel : rho.releases (rho.key x) o τ) (hx : rho.key x ∉ rho.faultyAt τ)
    (hrow : ¬ rho.log.fgAtt o)
    (hy : y ∈ honestKeysAt rho ((simTrace e rho).time j)) (hj : (simTrace e rho).IsCall y j)
    (hτ : 0 ≤ τ) (hb : (simTrace e rho).deadline y j τ p.Δ ≤ b)
    (hd : (simTrace e rho).deadline y j τ p.Δ ≤ (simTrace e rho).time j) :
    ∃ d, rho.log.Held rho.point (rho.key y) o d ∧ d < (simTrace e rho).deadline y j τ p.Δ :=
  publication_held_before_deadline hr hΔ hbh
    (fun a ha hb hh hy hw => hnet.msgs _ _ _ hrel hx hrow _ a ha hb hh hy hw) hy hj hτ hb hd

/-- The holding step after the stop, with the effective time `max τ g`. -/
theorem publication_held_before_psync
    (hr : Growing.LocalRun proposer (digestOf e rho) (honestKeysAt rho) sg (simTrace e rho) ini)
    (hΔ : E.ΔAC ≤ p.Δ) {g : Time} (hnet : rho.log.PSync rho.point g)
    {x y : Fin (Fintype.card V)} {j : Nat} {τ : Time}
    {o : (Model.protoOf (compiled F) E).Object}
    (hrel : rho.releases (rho.key x) o τ) (hx : rho.key x ∉ rho.faultyAt τ)
    (hrow : ¬ rho.log.fgAtt o)
    (hy : y ∈ honestKeysAt rho ((simTrace e rho).time j)) (hj : (simTrace e rho).IsCall y j)
    (hτ : 0 ≤ τ) (hb : (simTrace e rho).deadline y j (max τ g) p.Δ ≤ rho.horizon)
    (hd : (simTrace e rho).deadline y j (max τ g) p.Δ ≤ (simTrace e rho).time j) :
    ∃ d, rho.log.Held rho.point (rho.key y) o d ∧
      d < (simTrace e rho).deadline y j (max τ g) p.Δ := by
  apply publication_held_before_deadline hr hΔ le_rfl _ hy hj (hτ.trans (le_max_left _ _)) hb hd
  intro a ha hb hh hy hw
  have hga : max a g = a := max_eq_left ((le_max_right τ g).trans ha)
  have hh' : max a g + E.ΔAC - 1 ≤ rho.horizon := hga.symm ▸ hh
  have hy' : rho.key y ∉ rho.faultyAt (max a g + E.ΔAC - 1) := hga.symm ▸ hy
  have hw' : rho.point.AwakeOnClosed (rho.key y) a (max a g + E.ΔAC - 1) := hga.symm ▸ hw
  have h := hnet.msgs _ _ _ hrel hx hrow (rho.key y) a ((le_max_left τ g).trans ha) hh' hh' hy' hw'
  change rho.log.Held rho.point (rho.key y) o (max a g + E.ΔAC - 1) at h
  rwa [hga] at h

/-- Signatures of a node honest at the signing cut are well-formed attestations. -/
theorem signed_att_wellFormed
    (hr : Growing.LocalRun proposer (digestOf e rho) (honestKeysAt rho) sg (simTrace e rho) ini)
    {y : Fin (Fintype.card V)} {i : Nat} {a : FG.Att (Fintype.card V)}
    (hy : y ∈ honestKeysAt rho ((simTrace e rho).time i))
    (hs : (simTrace e rho).SignAt y i a) : a.WellFormed := by
  obtain ⟨C, hc⟩ := hs
  have hsign := (hr.cutLaw y i _ hc hy).1
  have hst := Trace.upTo_state (simTrace e rho) y (d := (simTrace e rho).time i)
    (i := i) fun k hk => hr.time_mono hk.le
  have hreach := Compose.fg_reachable (hr.upTo (hr.time_nonneg i)) hy i
  rw [hst] at hreach
  obtain ⟨h1, h2, h3⟩ := Store.entry_input hreach (((simTrace e rho).state y i).fg.σ C.root).Th
  exact Compose.createAtt_wellFormed h1 h2 h3 hsign

/-- A holding is backed by own processing no later than release, or by processing at receipt. -/
theorem held_att_processed_before
    (hr : Growing.LocalRun proposer (digestOf e rho) (honestKeysAt rho) sg (simTrace e rho) ini)
    {y : Fin (Fintype.card V)} {a : FG.Att (Fintype.card V)}
    {o : (Model.protoOf (compiled F) E).Object}
    (hdecode : canonEvent (receiverCodec e rho (rho.key y)) (Model.digests rho.hash o)
      (wireOf e o) = some (.attestation a))
    (hown : ∀ u, rho.releases (rho.key y) o u →
      ∃ k, (simTrace e rho).ProcessAttAt y k a ∧ (simTrace e rho).time k ≤ u)
    {j : Nat} {d D : Time} (hh : rho.log.Held rho.point (rho.key y) o d)
    (hd : d < D) (hj : D ≤ (simTrace e rho).time j) :
    ∃ k ≤ j, (simTrace e rho).ProcessAttAt y k a ∧ (simTrace e rho).time k < D := by
  obtain ⟨u, hud, hs, _⟩ := hh
  have hp : ∃ k, (simTrace e rho).ProcessAttAt y k a ∧ (simTrace e rho).time k ≤ u := by
    rcases hs with hs | ⟨i, hi⟩
    · exact hown u hs
    · obtain ⟨k, _, _, hk, ht⟩ := received_att_processAt e rho hi
        ⟨wireOf e o, mem_delivered_self _ e.adapter _ _ _, hdecode⟩
      rw [Model.Run.ownKey, Equiv.symm_apply_apply] at hk
      exact ⟨k, hk, ht.le⟩
  obtain ⟨k, hk, ht⟩ := hp
  have hlt := (ht.trans hud).trans_lt hd
  exact ⟨k, le_of_not_gt fun h => (not_lt_of_ge (hj.trans (hr.time_mono h.le))) hlt, hk, hlt⟩

/-- Supply the `Generic.Service.signedRow` law from FG partial synchrony. -/
theorem signed_row_service_psync
    (hr : Growing.LocalRun proposer (digestOf e rho) (honestKeysAt rho) sg (simTrace e rho) ini)
    {g ΔF : Time} (hnet : rho.log.PSync rho.point g)
    (attObj : FG.Att (Fintype.card V) → (Model.protoOf (compiled F) E).Object)
    (hdecode : ∀ a, a.WellFormed → ∀ v,
      canonEvent (receiverCodec e rho v) (Model.digests rho.hash (attObj a)) (wireOf e (attObj a)) =
        some (.attestation a))
    (hrow : ∀ a, rho.log.fgAtt (attObj a))
    (hrel : ∀ x i a, x ∈ honestKeysAt rho ((simTrace e rho).time i) →
      (simTrace e rho).SignAt x i a →
      rho.releases (rho.key x) (attObj a) ((simTrace e rho).time i))
    (hhorizon : ∀ x i a, (simTrace e rho).SignAt x i a → (simTrace e rho).time i ≤ rho.horizon)
    (hown : ∀ y a u, rho.releases (rho.key y) (attObj a) u →
      ∃ k, (simTrace e rho).ProcessAttAt y k a ∧ (simTrace e rho).time k ≤ u)
    (hslack : ∀ w : Time, w + E.ΔFG - 1 < w + ΔF) :
    ∀ x i a, x ∈ honestKeysAt rho ((simTrace e rho).time i) → (simTrace e rho).SignAt x i a →
      ∀ y j, y ∈ honestKeysAt rho ((simTrace e rho).time j) → (simTrace e rho).IsCall y j →
        (simTrace e rho).time j ≤ rho.horizon →
        (simTrace e rho).deadline y j (max ((simTrace e rho).time i) g) ΔF ≤
          (simTrace e rho).time j →
        ∃ k ≤ j, (simTrace e rho).ProcessAttAt y k a ∧
          (simTrace e rho).time k <
            (simTrace e rho).deadline y k (max ((simTrace e rho).time i) g) ΔF := by
  intro x i a hx hs y j hy hj hb hd
  let tr := simTrace e rho
  have hwf := signed_att_wellFormed hr hx hs
  apply RunTrace.service_at_processing_cut hr (inScope := fun k => tr.time k ≤ rho.horizon)
    (processed := fun k => tr.ProcessAttAt y k a) _ _ hy hj hb hd
  · exact fun hkj _ hb => (hr.time_mono hkj).trans hb
  · intro j hy hj hb hd
    obtain ⟨w, hw, heq, haw⟩ := deadline_awake_interval hr hy hj
      ((hr.time_nonneg i).trans (le_max_left _ g)) ΔF
    have hgw : max w g = w := max_eq_left ((le_max_right _ g).trans hw)
    have hbound : w + E.ΔFG - 1 ≤ tr.time j := (hslack w).le.trans (heq ▸ hd)
    have hh := hbound.trans hb
    have held := hnet.fgAtts (rho.key x) (attObj a) _ (hrel x i a hx hs)
      (not_faulty_of_mem_honestKeysAt hx le_rfl (hhorizon x i a hs)) (hrow a)
      (rho.key y) w ((le_max_left _ g).trans hw) (by rwa [hgw]) (by rwa [hgw])
      (by rw [hgw]; exact not_faulty_of_mem_honestKeysAt hy hbound hh)
      (by rw [hgw]; exact fun t hwt htd => haw t hwt (htd.trans hbound))
    rw [hgw] at held
    obtain ⟨k, hkj, hp, ht⟩ := held_att_processed_before hr (hdecode a hwf _) (hown y a) held
      (heq ▸ hslack w) hd
    refine ⟨k, hkj, ?_, hp, ht⟩
    rcases hp with hp | ⟨B, hp, _⟩ <;> exact ⟨_, hp⟩

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Shape Blocks

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)

omit [DecidableEq V] in
/-- The Goldilocks network instance reads the canonical honest-key set. -/
theorem network_honestKeysAt_eq :
    honestKeysAt S rho = NodeAsChainShape.CanonicalTrace.honestKeysAt rho := by
  funext t; ext y
  rw [mem_honestKeysAt_iff, NodeAsChainShape.CanonicalTrace.mem_honestKeysAt_iff]

/-- The Goldilocks network instance uses the encoded replay. -/
theorem network_trace_eq (hn : 1 ≤ Fintype.card V) :
    simTraceAt S rho hn = NodeAsChainShape.CanonicalTrace.simTrace (traceEncoding S hn) rho :=
  (simTraceAt_eq S rho hn).trans (simTrace_encoding S rho hn).1

/-- The structural laws specialized to the network instance's canonical replay. -/
theorem network_localRun (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) :
    Growing.LocalRun (runProposer S rho hn)
      (NodeAsChainShape.CanonicalTrace.digestOf (traceEncoding S hn) rho)
      (NodeAsChainShape.CanonicalTrace.honestKeysAt rho) AC.Vote.val
      (NodeAsChainShape.CanonicalTrace.simTrace (traceEncoding S hn) rho) (simIni S rho hn) := by
  obtain ⟨_, hdg⟩ := runProposer_digestOf S rho hn
  rw [← hdg, ← network_trace_eq, ← network_honestKeysAt_eq]
  exact (simTraceAt_goldilocksRun S rho hn hv).toLocalRun

omit [DecidableEq V] in
/-- A key honest at `t` is the key of an engine node uncompromised at every in-horizon `a ≤ t`. -/
theorem not_faulty_of_mem_honestKeysAt {y : Fin (Fintype.card V)} {t a : Time}
    (hy : y ∈ honestKeysAt S rho t) (hat : a ≤ t) (hah : a ≤ rho.horizon) :
    rho.key y ∉ rho.faultyAt a := by
  rw [mem_honestKeysAt_iff] at hy
  rw [← NodeAsChainShape.CanonicalTrace.mem_honestKeysAt_iff] at hy
  exact NodeAsChainShape.CanonicalTrace.not_faulty_of_mem_honestKeysAt hy hat hah

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
  have htr := network_trace_eq S rho hn
  rw [htr, network_honestKeysAt_eq] at hy
  rw [htr] at hj ⊢
  exact NodeAsChainShape.CanonicalTrace.deadline_awake_interval
    (network_localRun S rho hn hv) hy hj hτ _

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
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
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
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
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
    (hy : y ∈ honestKeysAt S rho
      ((simTraceAt S rho hn).time i))
    {a : FG.Att (Fintype.card V)} (hs : (simTraceAt S rho hn).SignAt y i a) :
    a.WellFormed := by
  rw [network_trace_eq S rho hn, network_honestKeysAt_eq S rho] at hy
  rw [network_trace_eq S rho hn] at hs
  exact NodeAsChainShape.CanonicalTrace.signed_att_wellFormed (network_localRun S rho hn hv) hy hs

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

omit [DecidableEq V] in
/-- The concrete codec reads the canonical attestation object of a well-formed attestation. -/
private theorem decode_attObj (hn : 1 ≤ Fintype.card V) (a : FG.Att (Fintype.card V))
    (hwf : a.WellFormed) (v : V) :
    NodeAsChainShape.canonEvent
      (NodeAsChainShape.CanonicalTrace.receiverCodec (traceEncoding (E := E) S hn) rho v)
      (Model.digests rho.hash (attObj a))
      (NodeAsChainShape.CanonicalTrace.wireOf (traceEncoding S hn) (attObj a)) =
        some (.attestation a) := by
  apply traceEncoding_induction S hn (fun e _ => NodeAsChainShape.canonEvent
    (NodeAsChainShape.CanonicalTrace.receiverCodec e rho v)
    (Model.digests rho.hash (attObj a)) (NodeAsChainShape.CanonicalTrace.wireOf e (attObj a)) =
      some (.attestation a))
  intro _ _
  rw (config := { transparency := .default }) [NodeAsChainShape.CanonicalTrace.wireOf_eq]
  rw [NodeAsChainShape.CanonicalTrace.receiverCodec_eq, NodeAsChainShape.CanonicalTrace.voteIOAt_eq]
  exact canonEvent_attObj (sp := S.params (Model.pubOf E) hn) (ro := S.ro _) _ _ a hwf

private theorem own_att_process_by (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} {a : FG.Att (Fintype.card V)} {u : Time}
    (hs : rho.releases (rho.key y) (attObj a) u) :
    ∃ k, (NodeAsChainShape.CanonicalTrace.simTrace (traceEncoding S hn) rho).ProcessAttAt y k a ∧
      (NodeAsChainShape.CanonicalTrace.simTrace (traceEncoding S hn) rho).time k ≤ u := by
  obtain ⟨k, hk, ht⟩ := released_att_processAt_at S rho hn hv hs
  rw [network_trace_eq S rho hn, Model.Run.ownKey, Equiv.symm_apply_apply] at hk
  rw [network_trace_eq S rho hn] at ht
  exact ⟨k, hk, ht.le⟩

/-- Holdings suffice for processing before an observation deadline, even for an old receipt. No
honesty premise: the processing is the holder's own release or its receipt. -/
theorem held_att_processed_before_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)}
    {a : FG.Att (Fintype.card V)} (hwf : a.WellFormed) {j : Nat} {d D : Time}
    (hh : rho.log.Held rho.point (rho.key y) (attObj a) d)
    (hd : d < D) (hj : D ≤ (simTraceAt S rho hn).time j) :
    ∃ k ≤ j, (simTraceAt S rho hn).ProcessAttAt y k a ∧
      (simTraceAt S rho hn).time
        k < D := by
  rw [network_trace_eq S rho hn] at hj ⊢
  apply NodeAsChainShape.CanonicalTrace.held_att_processed_before (network_localRun S rho hn hv)
    (decode_attObj S rho hn a hwf _) (fun _ => own_att_process_by S rho hn hv) hh hd hj

variable {sp : AC.ACParams} {ro : AC.ReplayOrder sp (List (FG.Att sp.n))}
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
    PSyncFGAttTransportAt S rho (simTraceAt S rho hn)
        (honestKeysAt S rho)
      (protoFGDelay (Model.pubOf E)) := by
  rw [psyncFGAttTransportAt_iff, network_trace_eq S rho hn, network_honestKeysAt_eq S rho]
  intro g hnet
  have hsim := simTraceAt_simulates S rho hn hv
  apply NodeAsChainShape.CanonicalTrace.signed_row_service_psync (network_localRun S rho hn hv)
    hnet (attObj (binding := S.vote)) (decode_attObj S rho hn)
    (fun a => (log_fgAtt_iff S rho _).mpr (isFGAtt_attObj a))
  · intro x i a hx hs
    rw [← network_trace_eq S rho hn, ← network_honestKeysAt_eq S rho] at hx
    rw [← network_trace_eq S rho hn] at hs ⊢
    exact (releasedFrom_iff S rho _ _ _).mp (hsim.att_released x i a hx hs)
  · intro x i a hs
    rw [← network_trace_eq S rho hn] at hs ⊢
    exact signAt_time_le_horizon S rho hn hv hs
  · exact fun _ _ _ => own_att_process_by S rho hn hv
  · intro w
    rw [protoFGDelay_eq]
    exact sub_one_lt _

end Consensus.Goldilocks.Obligations.Growing

end
