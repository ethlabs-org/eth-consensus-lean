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
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.HeldRefusal
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.HeldFlush
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.HeldSign
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.HeldRelease
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Release
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.PublishedAttestations
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.ReleasedPool

public section

/-! # Network transport under growing faults: holdings, deadlines and attestation service

The engine-to-node network transport of `Obligations/NetworkTransport` on the canonical growing
trace `simTraceAt`, with honesty read at the time each law reads it:

* a sender is honest at its send (the L0 network laws read `HonestAt v t` at the send time `t`);
* a recipient honest at its reading call is honest at every earlier time of its delivery interval
  (compromise only grows), which is where the L0 laws read it (`HonestAt w (dl a)`);
* node-local run facts at a cut are the static ones on the prefix through that cut's time.

Contents: network holdings (`publication_held_psync_at`), releases by a deadline
(`signed_released_by_at`), the attestation service contract
`PSyncFGAttTransportAt` with its monotone lift, and its base supplier `signed_row_service_psync_at`
at the release hold `R·Δ_AC` of a release schedule of gap `R`. -/

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
private theorem deadline_awake_interval
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
private theorem signed_att_wellFormed
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
private theorem held_att_processed_before
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

/-- Supply the `Generic.Service.signedRow` law from FG partial synchrony, at release hold `hold`:
a signing at `i` by `x` is released (`hrel`) at a time in `[time i, max (time i) g + hold]` by
`x` honest then, when `x` is honest at the release bound or `hold = 0` and the bound is within
the horizon, and the FG delay `ΔF`
pays the engine's FG delay after that bound. The own signing premise is the one of
`SyncOnAt.attestation`. -/
theorem signed_row_service_psync
    (hr : Growing.LocalRun proposer (digestOf e rho) (honestKeysAt rho) sg (simTrace e rho) ini)
    {g ΔF hold : Time} (hnet : rho.log.PSync rho.point g)
    (attObj : FG.Att (Fintype.card V) → (Model.protoOf (compiled F) E).Object)
    (hdecode : ∀ a, a.WellFormed → ∀ v,
      canonEvent (receiverCodec e rho v) (Model.digests rho.hash (attObj a)) (wireOf e (attObj a)) =
        some (.attestation a))
    (hrow : ∀ a, rho.log.fgAtt (attObj a))
    (hrel : ∀ x i a, x ∈ honestKeysAt rho ((simTrace e rho).time i) →
      (simTrace e rho).SignAt x i a →
      (hold ≠ 0 → x ∈ honestKeysAt rho (max ((simTrace e rho).time i) g + hold)) →
      ∀ c, max ((simTrace e rho).time i) g + hold ≤ c → c ≤ rho.horizon →
      (hold ≠ 0 → ∀ v t, max g 0 ≤ t → t ≤ c → rho.point.HonestAt v t →
        rho.point.env.awake v t = true) →
      ∃ u, (simTrace e rho).time i ≤ u ∧ u ≤ max ((simTrace e rho).time i) g + hold ∧
        rho.releases (rho.key x) (attObj a) u ∧ rho.key x ∉ rho.faultyAt u)
    (hown : ∀ y a u, rho.releases (rho.key y) (attObj a) u →
      ∃ k, (simTrace e rho).ProcessAttAt y k a ∧ (simTrace e rho).time k ≤ u)
    (hhold : 0 ≤ hold) (hslack : ∀ w : Time, w + hold + E.ΔFG - 1 < w + ΔF) :
    ∀ x i a, x ∈ honestKeysAt rho ((simTrace e rho).time i) → (simTrace e rho).SignAt x i a →
      (∀ k ≤ i, (simTrace e rho).SignAt x k a →
        (simTrace e rho).time k = (simTrace e rho).time i → hold ≠ 0 →
        x ∈ honestKeysAt rho (max ((simTrace e rho).time i) g + hold)) →
      ∀ y j, y ∈ honestKeysAt rho ((simTrace e rho).time j) → (simTrace e rho).IsCall y j →
        (simTrace e rho).time j ≤ rho.horizon →
        (hold ≠ 0 → ∀ v t, max g 0 ≤ t → t ≤ (simTrace e rho).time j →
          rho.point.HonestAt v t → rho.point.env.awake v t = true) →
        (simTrace e rho).deadline y j (max ((simTrace e rho).time i) g) ΔF ≤
          (simTrace e rho).time j →
        ∃ k ≤ j, (simTrace e rho).ProcessAttAt y k a ∧
          (simTrace e rho).time k <
            (simTrace e rho).deadline y k (max ((simTrace e rho).time i) g) ΔF := by
  intro x i a hx hs hxh y j₀ hy hj hb haw₀ hd
  let tr := simTrace e rho
  have hwf := signed_att_wellFormed hr hx hs
  apply RunTrace.service_at_processing_cut hr
    (inScope := fun k => tr.time k ≤ rho.horizon ∧ tr.time k ≤ tr.time j₀)
    (processed := fun k => tr.ProcessAttAt y k a) _ _ hy hj ⟨hb, le_rfl⟩ hd
  · exact fun hkj _ hb => ⟨(hr.time_mono hkj).trans hb.1, (hr.time_mono hkj).trans hb.2⟩
  · intro j hy hj hbj hd
    have hb := hbj.1
    obtain ⟨w, hw, heq, haw⟩ := deadline_awake_interval hr hy hj
      ((hr.time_nonneg i).trans (le_max_left _ g)) ΔF
    have hFG : 0 + 1 ≤ E.ΔFG := Int.add_one_le_of_lt E.ΔFG_pos
    obtain ⟨u, hsu, hub, hrel', hxu⟩ := hrel x i a hx hs (hxh i le_rfl hs rfl) (tr.time j)
      (by rw [heq] at hd; linarith [hslack w]) hb
      fun h0 v t hgt htj => haw₀ h0 v t hgt (htj.trans hbj.2)
    obtain ⟨c, hc⟩ : ∃ c, c = max u w := ⟨_, rfl⟩
    have hwc : w ≤ c := hc ▸ le_max_right _ _
    have huc : u ≤ c := hc ▸ le_max_left _ _
    have hcw : c ≤ w + hold := hc ▸ max_le (hub.trans (by linarith)) (by linarith)
    have hgc : max c g = c := max_eq_left ((le_max_right _ g).trans (hw.trans hwc))
    have hlt : c + E.ΔFG - 1 < tr.deadline y j (max (tr.time i) g) ΔF := by
      rw [heq]; linarith [hslack w]
    have hbound : c + E.ΔFG - 1 ≤ tr.time j := hlt.le.trans hd
    have hh := hbound.trans hb
    have held := hnet.fgAtts (rho.key x) (attObj a) u hrel' hxu (hrow a)
      (rho.key y) c huc (by rwa [hgc]) (by rwa [hgc])
      (by rw [hgc]; exact not_faulty_of_mem_honestKeysAt hy hbound hh)
      (by rw [hgc]; exact fun t hct htd => haw t (hwc.trans hct) (htd.trans hbound))
    rw [hgc] at held
    obtain ⟨k, hkj, hp, ht⟩ := held_att_processed_before hr (hdecode a hwf _) (hown y a) held
      hlt hd
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

/-- A signing cut of the trace is at or before the engine horizon. -/
private theorem signAt_time_le_horizon (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
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

/-- An actual canonical attestation release is backed by own processing no later than the release
(`released_att_processAt`): at the releasing tick for an own admission, or earlier for an
attestation already in the releaser's pool. No honesty premise: an engine event's node is honest
at the event. -/
private theorem released_att_processAt_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {v : V}
    {a : FG.Att (Fintype.card V)} {t : Time} (hs : rho.releases v (attObj a) t) :
    ∃ k, (simTraceAt S rho hn).ProcessAttAt (rho.ownKey v) k a ∧
      (simTraceAt S rho hn).time k ≤ t := by
  rw [simTraceAt_eq]
  exact released_att_processAt S rho hn hv hs

omit [DecidableEq V] in
/-- The concrete codec reads the canonical attestation object of a well-formed attestation. -/
private theorem decode_attObj (hn : 1 ≤ Fintype.card V) (a : FG.Att (Fintype.card V))
    (hwf : a.WellFormed) (v : V) :
    NodeAsChainShape.canonEvent
      (NodeAsChainShape.CanonicalTrace.receiverCodec (traceEncoding (E := E) S hn) rho v)
      (Model.digests rho.hash (attObj a))
      (NodeAsChainShape.CanonicalTrace.wireOf (traceEncoding S hn) (attObj a)) =
        some (.attestation a) := by
  apply traceEncoding_induction S hn (fun e _ _ => NodeAsChainShape.canonEvent
    (NodeAsChainShape.CanonicalTrace.receiverCodec e rho v)
    (Model.digests rho.hash (attObj a)) (NodeAsChainShape.CanonicalTrace.wireOf e (attObj a)) =
      some (.attestation a))
  intro _ _
  rw (config := { transparency := .default }) [NodeAsChainShape.CanonicalTrace.wireOf_eq]
  rw [NodeAsChainShape.CanonicalTrace.receiverCodec_eq, NodeAsChainShape.CanonicalTrace.voteIOAt_eq]
  exact canonEvent_attObj (sp := S.params (Model.pubOf E) hn) _ _ a hwf

private theorem own_att_process_by (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} {a : FG.Att (Fintype.card V)} {u : Time}
    (hs : rho.releases (rho.key y) (attObj a) u) :
    ∃ k, (NodeAsChainShape.CanonicalTrace.simTrace (traceEncoding S hn) rho).ProcessAttAt y k a ∧
      (NodeAsChainShape.CanonicalTrace.simTrace (traceEncoding S hn) rho).time k ≤ u := by
  obtain ⟨k, hk, ht⟩ := released_att_processAt_at S rho hn hv hs
  rw [network_trace_eq S rho hn, Model.Run.ownKey, Equiv.symm_apply_apply] at hk
  rw [network_trace_eq S rho hn] at ht
  exact ⟨k, hk, ht⟩

/-- **A signing is released by its release-gap bound.** For a release schedule of gap `R`
(`ReleaseGapAt`), a signing at `i` by `x` honest then is released at some `u` with
`time i ≤ u ≤ max (time i) g + R·Δ_AC`, by `x` uncompromised at `u`: at the signing tick when the
schedule allows release then, and otherwise from the held queue by the first awake tick allowing
release (`released_by_of_release_liveness` with `held_flush`). In that case `R ≠ 0`, and the
premises are those of `PSyncFGAttTransportAt` at hold `R·Δ_AC`: `x` honest at the bound, the
bound `c` within the horizon and participation from `max g 0` through `c`. -/
private theorem signed_released_by_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) {R : ℕ}
    (hgap : ReleaseGapAt (S.params (Model.pubOf E) hn).toParams (S.release (Model.pubOf E)) R 0)
    {g : Time} {x : Fin (Fintype.card V)} {i : Nat} {a : FG.Att (Fintype.card V)}
    (hx : x ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i))
    (hs : (simTraceAt S rho hn).SignAt x i a)
    (hxR : (R : Time) * E.ΔAC ≠ 0 →
      x ∈ honestKeysAt S rho (max ((simTraceAt S rho hn).time i) g + (R : Time) * E.ΔAC))
    {c : Time} (hc : max ((simTraceAt S rho hn).time i) g + (R : Time) * E.ΔAC ≤ c)
    (hch : c ≤ rho.horizon)
    (haw : (R : Time) * E.ΔAC ≠ 0 → ∀ v t, max g 0 ≤ t → t ≤ c → rho.point.HonestAt v t →
      rho.point.env.awake v t = true) :
    ∃ u, (simTraceAt S rho hn).time i ≤ u ∧
      u ≤ max ((simTraceAt S rho hn).time i) g + (R : Time) * E.ΔAC ∧
      rho.releases (rho.key x) (attObj a) u ∧ rho.key x ∉ rho.faultyAt u := by
  obtain ⟨v, rfl⟩ : ∃ v, rho.ownKey v = x := ⟨_, ownKey_key S rho x⟩
  have hh := signAt_time_le_horizon S rho hn hv hs
  have hrel := simTraceAt_att_released S rho hn hv _ i a hx hs
  obtain ⟨j, s, he, hp, hts, C, hcut⟩ := signAt_tick_cut_at S rho hn hs
  rw [ownKey_key'] at he hcut ⊢
  rw [hts] at hx hxR hc hh hrel ⊢
  have hs0 : 0 ≤ s := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  have hxs : (R : Time) * E.ΔAC ≠ 0 → ∀ u, u ≤ max s g + (R : Time) * E.ΔAC →
      v ∉ rho.faultyAt u := fun hR u hu => by
    have := not_faulty_of_mem_honestKeysAt S rho (hxR hR) hu (hu.trans (hc.trans hch))
    rwa [ownKey_key'] at this
  cases hR : S.release (Model.pubOf E) (rho.ownKey v) s
  · have hR0 : (R : Time) * E.ΔAC ≠ 0 := by
      intro h0
      obtain ⟨t', h1, h2, h3⟩ := hgap (rho.ownKey v) s hs0
      have h2' : t' ≤ s + (R : Time) * E.ΔAC := h2
      rw [le_antisymm (by linarith) h1, hR] at h3
      exact Bool.false_ne_true h3
    have ha := tick_sign_held S rho hn hv he hp (preNode_releasable_at S rho hn hv he) hcut hR
    have hobj := heldObj_eq_attObj S rho (attest_val_of_mem_exec _ _ _ _ _ _ hcut)
    obtain ⟨r, hsr, hre, hr⟩ := released_by_of_release_liveness (Δ := E.ΔAC) (e := max s g)
      (release := S.release (Model.pubOf E) (rho.ownKey v))
      (awake := fun t => E.awake v t = true ∧ v ∉ rho.faultyAt t ∧ t ≤ rho.horizon)
      (released := fun t => rho.releases v (attObj a) t) (hgap (rho.ownKey v))
      (le_max_of_le_left hs0) (le_max_left _ _)
      (fun t h1 h2 => ⟨haw hR0 v t (max_le ((le_max_right _ _).trans h1)
          (hs0.trans ((le_max_left _ _).trans h1))) (h2.trans hc) (hxs hR0 t h2),
        hxs hR0 t h2, h2.trans (hc.trans hch)⟩)
      (fun t hst _ ⟨hw, hf, hth⟩ hrt hnot => by
        have := held_flush S rho hn hv he ha hst hth hf hw hrt (by rwa [hobj])
        rwa [hobj] at this)
    exact ⟨r, hsr, hre, hr, hxs hR0 r hre⟩
  · have hu := not_faulty_of_mem_honestKeysAt S rho hx le_rfl hh
    rw [ownKey_key'] at hu hrel
    exact ⟨s, le_rfl, (le_max_left _ _).trans (le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg _) E.ΔAC_pos.le)),
      (releasedFrom_iff S rho _ _ _).mp (hrel hR), hu⟩

variable {sp : AC.ACParams}
  (tr : GoldilocksTrace sp) (H : Time → Set (Fin sp.n)) (ΔF : Time)

/-- Signed FG attestations of a node honest at the signing cut are processed before the
attestation deadline at FG delay `Δ_F` at recipient calls within the engine horizon, by every
recipient honest at its call. An earlier processing of the identical attestation is sufficient.
With a release hold `hold ≠ 0` (own attestations published up to `hold` after the effective
signing time), the signer must also be honest at `max (time i) g + hold`, in the form of
`SyncOnAt.attestation`, and every node honest at a time from `max g 0` up to the reading call is
awake then (the participation of `HealthyOn`). At `hold = 0` both premises are vacuous. -/
def PSyncFGAttTransportAt (hold : Time := 0) : Prop :=
  ∀ g, rho.log.PSync rho.point g →
    ∀ x i a, x ∈ H (tr.time i) → tr.SignAt x i a →
      (∀ k ≤ i, tr.SignAt x k a → tr.time k = tr.time i → hold ≠ 0 →
        x ∈ H (max (tr.time i) g + hold)) →
      ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.time j ≤ rho.horizon →
        (hold ≠ 0 → ∀ v t, max g 0 ≤ t → t ≤ tr.time j → rho.point.HonestAt v t →
          rho.point.env.awake v t = true) →
        tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
        ∃ k ≤ j, tr.ProcessAttAt y k a ∧
          tr.time k < tr.deadline y k (max (tr.time i) g) ΔF

/-- The signed-attestation service contract, without exposing its definition to consumers. -/
theorem psyncFGAttTransportAt_iff (hold : Time := 0) :
    PSyncFGAttTransportAt S rho tr H ΔF hold ↔
    ∀ g, rho.log.PSync rho.point g →
      ∀ x i a, x ∈ H (tr.time i) → tr.SignAt x i a →
        (∀ k ≤ i, tr.SignAt x k a → tr.time k = tr.time i → hold ≠ 0 →
          x ∈ H (max (tr.time i) g + hold)) →
        ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.time j ≤ rho.horizon →
          (hold ≠ 0 → ∀ v t, max g 0 ≤ t → t ≤ tr.time j → rho.point.HonestAt v t →
            rho.point.env.awake v t = true) →
          tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
          ∃ k ≤ j, tr.ProcessAttAt y k a ∧
            tr.time k < tr.deadline y k (max (tr.time i) g) ΔF := by
  rfl

variable {S rho tr H} in
/-- **The monotone lift of attestation service**: service at `Δ₁` is service at every
`Δ₂ ≥ Δ₁`, at the same hold. -/
theorem PSyncFGAttTransportAt.mono {Δ₁ Δ₂ hold : Time}
    (h : PSyncFGAttTransportAt S rho tr H Δ₁ hold) (h12 : Δ₁ ≤ Δ₂) :
    PSyncFGAttTransportAt S rho tr H Δ₂ hold := by
  intro g hnet x i a hx hs hxh y j hy hj hb haw hd
  obtain ⟨k, hkj, hp, ht⟩ := h g hnet x i a hx hs hxh y j hy hj hb haw
    ((tr.deadline_mono_delta y j _ h12).trans hd)
  exact ⟨k, hkj, hp, ht.trans_le (tr.deadline_mono_delta y k _ h12)⟩

/-- **The base attestation supplier, at the FG delay and release hold**, under growing faults:
for a release schedule of gap `R`, partial synchrony of the engine log serves the signed
attestations of a node honest at its signing cut at the release hold `R·Δ_AC` and the FG delay
`protoFGDelay (pubOf E) + R·Δ_AC`, at every recipient call within the horizon by a recipient honest
at the call. Held attestations are released within the hold through `held_flush`. -/
theorem signed_row_service_psync_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) {R : ℕ}
    (hgap : ReleaseGapAt (S.params (Model.pubOf E) hn).toParams (S.release (Model.pubOf E)) R 0) :
    PSyncFGAttTransportAt S rho (simTraceAt S rho hn) (honestKeysAt S rho)
      (protoFGDelay (Model.pubOf E) + (R : Time) * E.ΔAC) ((R : Time) * E.ΔAC) := by
  rw [psyncFGAttTransportAt_iff (hold := (R : Time) * E.ΔAC),
    network_trace_eq S rho hn, network_honestKeysAt_eq S rho]
  intro g hnet
  apply NodeAsChainShape.CanonicalTrace.signed_row_service_psync (network_localRun S rho hn hv)
    hnet (attObj (binding := S.vote)) (decode_attObj S rho hn)
    (fun a => (log_fgAtt_iff S rho _).mpr (isFGAtt_attObj a)) (hold := (R : Time) * E.ΔAC)
  · intro x i a hx hs hxR c hc hch haw
    rw [← network_trace_eq S rho hn, ← network_honestKeysAt_eq S rho] at hx hxR
    rw [← network_trace_eq S rho hn] at hs hc ⊢
    exact signed_released_by_at S rho hn hv hgap hx hs hxR hc hch haw
  · exact fun _ _ _ => own_att_process_by S rho hn hv
  · exact mul_nonneg (Nat.cast_nonneg _) E.ΔAC_pos.le
  · intro w
    have hFG : (Model.pubOf E).ΔFG = E.ΔFG := rfl
    rw [protoFGDelay_eq, hFG]
    linarith

end Consensus.Goldilocks.Obligations.Growing

end
