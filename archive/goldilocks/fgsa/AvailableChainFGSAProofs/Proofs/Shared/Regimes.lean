module
public import AvailableChainFGSAProofs.Proofs.Shared.ExactHead
public import AvailableChainFGSAProofs.Proofs.Shared.Recurrence
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedEndpoint
public import AvailableChainFGSAProofs.Proofs.Shared.ExactService
public import AvailableChainFGSAProofs.Proofs.Shared.SelfDelivery

/-! F-23 exception (L47): each theorem here takes at most one regime record, Set or Contract
premise and concludes a field-level fact or another regime record. -/

public section

namespace AvailableChain.FGSA.Run

variable {ΔF : Time}

open Gen.Pure
open Gen.V2.Duty (faulty faulty_def awakeHonest awakeHonest_def SeedAt SeedAt_def)
variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
variable {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. The old prefix fields imply the per-object regime at ΔF = Δ.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem HealthyPrefix₂.of_legacy {b₀ : Time} (base : Base₂ p c E rho)
    (cut : 0 ≤ b₀ ∧ b₀ ≤ rho.horizon)
    (healthy : V2.D.HealthyPrefixDelivery E rho b₀)
    (partBefore : ∀ t : Time, 0 ≤ t → t < b₀ →
      (faulty rho).card < (awakeHonest E rho t).card) :
    HealthyPrefix₂ p c E rho b₀ E.Δ := by
  refine ⟨base, cut, ?_, le_rfl, partBefore⟩
  rw [fgsaDelay_self]
  exact (Gen.V2.Duty.healthyPrefix_iff_by_const E rho b₀).1 healthy

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Recover the old prefix delivery law at ΔF = Δ.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem HealthyPrefix₂.legacy_delivery {b₀ : Time} (h : HealthyPrefix₂ p c E rho b₀ E.Δ) :
    V2.D.HealthyPrefixDelivery E rho b₀ := by
  apply (Gen.V2.Duty.healthyPrefix_iff_by_const E rho b₀).2
  have hh := h.healthy
  rw [fgsaDelay_self] at hh
  exact hh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. The old recovery fields imply the per-object regime at ΔF = Δ.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem Recovery₂.of_legacy {G : Time}
    (core : Gen.V2.Duty.RecoveryCore (fgsa p c) (fgsaInterface p c) E rho G)
    (base : Base₂ p c E rho) (fault : (faulty rho).card ≤ (p.n - 1) / 3)
    (awake : ∀ v ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon → E.awake v t = true)
    (gapPos : 4 * p.Δ ≤ G) :
    Recovery₂ p c E rho G E.Δ := by
  refine ⟨?_, le_rfl, core.gap, base, fault, awake, gapPos⟩
  rw [fgsaDelay_self]
  exact (Gen.V2.Duty.partialSynchrony_iff_by_const E rho).1 core.sync

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. GUP r2: alignment is internal proof data, not a recovery premise. -/
structure Recovery₂Aligned (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (G : Time) (ΔF : Time := E.Δ)
    : Prop extends Recovery₂ p c E rho G ΔF where
  gapAligned : 4 * p.Δ ∣ G

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
GUP r2: the internal aligned regime keeps the original gap value. -/
theorem Recovery₂Aligned.gamma_eq {G ΔF : Time}
    (h : Recovery₂Aligned p c E rho G ΔF) : Γ p G = G :=
  fgsa_gamma_eq_of_dvd p h.gapAligned

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
GUP r2: a longer recurrence window preserves each original witness. -/
theorem recovery₂_roundUp {G ΔF : Time} (h : Recovery₂ p c E rho G ΔF) :
    Recovery₂Aligned p c E rho (Γ p G) ΔF := by
  have hle := (fgsa_gamma_bounds p G).1
  refine ⟨⟨h.sync, h.deltaF, ?_, h.base, h.fault, h.awake,
    h.gapPos.trans hle⟩, fgsa_gamma_aligned p G⟩
  intro t hgst hhor
  obtain ⟨s, hlo, hhi, hs⟩ := h.gap t hgst (by linarith)
  exact ⟨s, hlo, by linarith, hs⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Recover the old recovery core at ΔF = Δ.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem Recovery₂.toRecoveryCore {G : Time} (h : Recovery₂ p c E rho G E.Δ) :
    Gen.V2.Duty.RecoveryCore (fgsa p c) (fgsaInterface p c) E rho G := by
  refine ⟨?_, h.gap⟩
  apply (Gen.V2.Duty.partialSynchrony_iff_by_const E rho).2
  have hh := h.sync
  rw [fgsaDelay_self] at hh
  exact hh

omit [DecidableEq V] in
theorem card_eq_n_of_linked (hL : V2.D.Linked (fgsaFamilies p c).linked rho) :
    Fintype.card V = p.n :=
  (V2.D.CStar.seats_eq (ℓ := .base .fg) hL.toCStar trivial).symm

private theorem fgsa_honest_card (hL : V2.D.Linked (fgsaFamilies p c).linked rho) :
    rho.honest.card = p.n - (faulty rho).card := by
  rw [faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, card_eq_n_of_linked hL]
  have hc := Finset.card_le_univ rho.honest
  rw [card_eq_n_of_linked hL] at hc
  omega

private theorem fgsa_awake_card_le (hL : V2.D.Linked (fgsaFamilies p c).linked rho) (t : Time) :
    (awakeHonest E rho t).card ≤ p.n - (faulty rho).card := by
  rw [awakeHonest_def, ← fgsa_honest_card hL]
  exact Finset.card_filter_le _ _

theorem CleanPrefix₂.toCleanCut {b₀ : Time} (h : CleanPrefix₂ p c E rho b₀ ΔF) :
    CleanCut₂ p c E rho b₀ ΔF := h.toHealthyPrefix₂

theorem HealthyPrefix₂.faultQ_of_pos {b₀ : Time} (h : HealthyPrefix₂ p c E rho b₀ ΔF)
    (hb : 0 < b₀) : FaultQ p.n (faulty rho).card :=
  count_clean (h.partBefore 0 le_rfl hb) (fgsa_awake_card_le h.base.linked 0)

theorem CleanPrefix₂.faultQ {b₀ : Time} (h : CleanPrefix₂ p c E rho b₀ ΔF) :
    FaultQ p.n (faulty rho).card :=
  count_clean h.partAt (fgsa_awake_card_le h.base.linked b₀)

theorem HealthyPrefix₂.batch {b₀ t : Time} (h : HealthyPrefix₂ p c E rho b₀ ΔF)
    (ht : 0 ≤ t) (hb : t < b₀) : Batch (awakeHonest E rho t).card (faulty rho).card :=
  ⟨h.partBefore t ht hb⟩

theorem CleanPrefix₂.batchAt {b₀ : Time} (h : CleanPrefix₂ p c E rho b₀ ΔF) :
    Batch (awakeHonest E rho b₀).card (faulty rho).card := ⟨h.partAt⟩

-- P3 §4.4 places regime producers here; F1.9 supplies these two bridges.
theorem Recovery₂.faultX_count_rec {G : Time} (h : Recovery₂ p c E rho G ΔF) :
    FaultX p.n (faulty rho).card := count_rec p.nPos h.fault

theorem Recovery₂.faultQ {G : Time} (h : Recovery₂ p c E rho G ΔF) :
    FaultQ p.n (faulty rho).card := by
  have hx := h.faultX_count_rec.lt
  constructor
  rw [qF_def] at hx ⊢
  omega

theorem Recovery₂.batch {G t : Time} (h : Recovery₂ p c E rho G ΔF)
    (ht : E.t_GST ≤ t) (hh : t ≤ rho.horizon) :
    Batch (awakeHonest E rho t).card (faulty rho).card := by
  have he : awakeHonest E rho t = rho.honest := by
    rw [awakeHonest_def]
    exact Finset.filter_eq_self.mpr (fun v hv => h.awake v hv t ht hh)
  rw [he, fgsa_honest_card h.base.linked]
  have hn := p.nPos
  have hf := h.fault
  exact ⟨by omega⟩

-- LabelSync and LabelFacts producers live in Gen.V2.Duty. Use them with the
-- default vote/gate times and the Batch producers above; do not copy them.
-- DeliveryWithin producers are Gen.V2.Duty.deliveryWithin_of_partialSynchrony
-- and Gen.V2.Duty.deliveryWithin_of_healthyPrefix, with no Base premise.

/- With the schedule already in Base, the two horizon delivery conditions agree. -/
omit [Fintype V] in
theorem fgsa_clean_delivery_iff (_hS : V2.D.ScheduleWellFormed E rho) (hG : E.t_GST = 0) :
    V2.D.HealthyPrefixDelivery E rho rho.horizon ↔ V2.D.PartialSynchrony E rho := by
  constructor
  · intro h
    constructor
    · intro v hv o t he w hw a hta ha
      simpa only [hG, max_eq_left ha] using h.broadcast_emitted v hv o t he w hw a hta ha
    · intro v hv i o t he w hw a hta ha
      simpa only [hG, max_eq_left ha] using h.relay_accepted v hv i o t he w hw a hta ha
  · intro h
    constructor
    · intro v hv o t he w hw a hta ha
      simpa only [hG, max_eq_left ha] using h.broadcast_emitted v hv o t he w hw a hta ha
    · intro v hv i o t he w hw a hta ha
      simpa only [hG, max_eq_left ha] using h.relay_accepted v hv i o t he w hw a hta ha

/- T7.5 supplies the fixed reachable-state predicate at any explicit event cut. -/
omit [Fintype V] in
theorem fgsa_seed_reachable (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (start : Nat) :
    SeedAt E rho start (fun _ nd => Reachable p nd.st) := by
  rw [SeedAt_def]
  exact reachable_stateBefore E rho start

/- T7.7/T7.8 supplies the fixed processed predicate after acceptance.
The predicate selects one receiver; the cut is after its accepting event. -/
omit [Fintype V] in
theorem fgsa_seed_accepted (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (w : V) (o : Obj p) (i start : Nat) (t : Time)
    (ha : V2.D.Run.acceptsAt E rho i w o t) (his : i + 1 ≤ start)
    (hrf : V2.D.restartFree rho w (i + 1) start) :
    SeedAt E rho start (fun v nd => v = w → (fgsa p c).processed nd o = true) := by
  rw [SeedAt_def]
  intro v hv
  subst v
  exact processed_stable E rho hS w o (i + 1) start his hrf ha.2.2

theorem Outage₂.pos {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : Outage₂ p c fast E rho T b₀ b₁ ΔF) : 0 < b₀ := by
  have hT := h.order.1
  have hlag := h.lag
  have hd := p.deltaPos
  have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
  cases fast with
  | false =>
    change T + ((4 * (p.k : Time) - 1) * p.Δ - 3 * p.Δ) ≤ b₀ at hlag
    nlinarith
  | true =>
    change T + 4 * p.Δ ≤ b₀ at hlag
    linarith

theorem Outage₂.toCleanCut {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : Outage₂ p c fast E rho T b₀ b₁ ΔF) : CleanCut₂ p c E rho b₀ ΔF := h.pre

theorem Outage₂.faultQ {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : Outage₂ p c fast E rho T b₀ b₁ ΔF) : FaultQ p.n (faulty rho).card :=
  h.pre.faultQ_of_pos h.pos

open AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 02:537–539; P3 erratum 13, Clean wrapper.
DC: Generic/Conditions.lean:134–156 and Goldfish/Confirmation.lean:434–441.
INTENTIONAL: healthy-prefix delivery supplies the vote-to-gate LabelSync;
geometry stays an explicit consumer obligation.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_gateReceipt_clean
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (s : Slot) (hcut : SA.gateTime p.toParams s ≤ b₀)
    {i : Nat} {x : V} (ht : IsGateTick p c rho i x s) (B : Block)
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B)
    (hScope : GateReceiptScope E rho i x s) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head s)) q ∈ rho.honest →
      joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s) →
      ∃ K t,
        rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
          (ofHead p ⟨.seat (.head s) q, K.root⟩) t ∧
        baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n) ∈
          (storeAt p c E rho i x).base.votes ∧
        K ∈ (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))).blocks ∧
        K.slot ≤ s ∧
        GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)))
          (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) <
            GridCO.earlyTime p.toParams.engine s ∧
        GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))) K < GridCO.earlyTime p.toParams.engine s ∧
        Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)).fg.F) K ∧ Block.Preceq B K := by
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [h.base.delta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hsync := Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _) hvd hcut h.cut.2
  exact (fgsa_gateReceipt_on (hroots := h.base.receiptIdealization)
    E rho h.base.valid h.base.delta h.base.cstar s hsync ht B hgeom hScope).2.2

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.22:3100–3120; P3 erratum 13, Recovery wrapper.
DC: Generic/Conditions.lean:110–132 and Goldfish/Confirmation.lean:434–441.
INTENTIONAL: post-GST delivery supplies the vote-to-gate LabelSync.
GST ≤ voteTime s suffices; no earlier synchrony pair is used.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_gateReceipt_recovery
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (s : Slot) (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    {i : Nat} {x : V} (ht : IsGateTick p c rho i x s) (B : Block)
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B)
    (hScope : GateReceiptScope E rho i x s) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head s)) q ∈ rho.honest →
      joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s) →
      ∃ K t,
        rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
          (ofHead p ⟨.seat (.head s) q, K.root⟩) t ∧
        baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n) ∈
          (storeAt p c E rho i x).base.votes ∧
        K ∈ (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))).blocks ∧
        K.slot ≤ s ∧
        GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)))
          (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) <
            GridCO.earlyTime p.toParams.engine s ∧
        GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))) K < GridCO.earlyTime p.toParams.engine s ∧
        Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)).fg.F) K ∧ Block.Preceq B K := by
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [h.base.delta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hhorizon : SA.gateTime p.toParams s ≤ rho.horizon :=
    (h.base.valid.in_horizon _ (List.mem_of_getElem? ht)).2
  have hsync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST hvd hhorizon
  exact (fgsa_gateReceipt_on (hroots := h.base.receiptIdealization)
    E rho h.base.valid h.base.delta h.base.cstar s hsync ht B hgeom hScope).2.2

/-- Explicit legacy regime adapter; receiver service follows from NoRestart. -/
theorem fgsa_gateReceipt_clean_legacy
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (hN : V2.D.NoRestart rho)
    (s : Slot) (hcut : SA.gateTime p.toParams s ≤ b₀)
    {i : Nat} {x : V} (ht : IsGateTick p c rho i x s) (B : Block)
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head s)) q ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s) = true →
      ∃ K t,
        rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
          (ofHead p ⟨.seat (.head s) q, K.root⟩) t ∧
        baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n) ∈
          (storeAt p c E rho i x).base.votes ∧
        K ∈ (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))).blocks ∧
        K.slot ≤ s ∧
        GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)))
          (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) <
            GridCO.earlyTime p.toParams.engine s ∧
        GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))) K < GridCO.earlyTime p.toParams.engine s ∧
        Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)).fg.F) K ∧ Block.Preceq B K := by
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [h.base.delta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hsync := Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _) hvd hcut h.cut.2
  exact fgsa_gateReceipt (hroots := h.base.receiptIdealization)
    E rho h.base.valid hN h.base.delta h.base.cstar
    s hsync ht B hgeom

/-- Explicit legacy regime adapter; receiver service follows from NoRestart. -/
theorem fgsa_gateReceipt_recovery_legacy
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (hN : V2.D.NoRestart rho)
    (s : Slot) (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    {i : Nat} {x : V} (ht : IsGateTick p c rho i x s) (B : Block)
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head s)) q ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s) = true →
      ∃ K t,
        rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
          (ofHead p ⟨.seat (.head s) q, K.root⟩) t ∧
        baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n) ∈
          (storeAt p c E rho i x).base.votes ∧
        K ∈ (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))).blocks ∧
        K.slot ≤ s ∧
        GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)))
          (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) <
            GridCO.earlyTime p.toParams.engine s ∧
        GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))) K < GridCO.earlyTime p.toParams.engine s ∧
        Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)).fg.F) K ∧ Block.Preceq B K := by
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [h.base.delta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hhorizon : SA.gateTime p.toParams s ≤ rho.horizon :=
    (h.base.valid.in_horizon _ (List.mem_of_getElem? ht)).2
  have hsync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST hvd hhorizon
  exact fgsa_gateReceipt (hroots := h.base.receiptIdealization)
    E rho h.base.valid hN h.base.delta h.base.cstar
    s hsync ht B hgeom

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 N1:2518–2525; blueprint 03:256–317.
DC: Goldfish/ProposalSnapshotBridge.lean:210,225; Conditions.lean:134.
INTENTIONAL: the Clean wrapper uses the healthy prefix through v_s and
Gen LabelSync at (t_s - Δ, v_s); geometry remains a separate consumer input.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ.
legacy: sleep consumers use the _on form in RegimesService -/
theorem fgsa_score_eq_on_clean_of_retained_proposal
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hNR : V2.D.NoRestart rho)
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (s : Slot) (hcut : SA.voteTime p.toParams s ≤ b₀)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : N.erase ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (hFN : Block.Preceq (eraseFG (clock p (V2.D.Run.stateBefore E rho ih y).st
      (SA.voteTime p.toParams s)).fg.F) N.erase)
    (D : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) D) :
    let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s)
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    let U := proposerVotes src s
    let U' := headVotes p dst s
    (GridCO.seats p.n U).toFinset = (GridCO.seats p.n U').toFinset ∧
    (∀ i, GridCO.equivocates U i = GridCO.equivocates U' i) ∧
    GridCO.voterCount U = GridCO.voterCount U' ∧
    (∀ X, Block.Preceq D X →
      GridCO.goldfishScore src.base.blocks U (proposerSupport src s) X =
        GridCO.goldfishScore dst.base.blocks U' (headSupport p dst s) X) := by
  have hvd : SA.proposalTime p.toParams s - p.Δ + E.Δ ≤ SA.voteTime p.toParams s := by
    rw [h.base.delta]
    change 4 * p.Δ * (s : Int) - p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hsync := Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _) hvd hcut h.cut.2
  exact fgsa_score_eq_on_run (hroots := h.base.receiptIdealization)
    E rho h.base.valid hNR h.base.delta s hsync
    hx hy hip hih hseat N hem hadm hFN D hgeom

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 N1:2518–2525 and O25 §7; blueprint 03:256–317.
DC: Goldfish/ProposalSnapshotBridge.lean:210,225; Conditions.lean:110.
INTENTIONAL: Recovery requires GST ≤ t_s - Δ, not merely GST ≤ v_s.
The actual HEAD tick supplies the horizon bound for Gen LabelSync.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ.
legacy: sleep consumers use the _on form in RegimesService -/
theorem fgsa_score_eq_on_recovery_of_retained_proposal
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hNR : V2.D.NoRestart rho)
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (s : Slot) (hGST : E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : N.erase ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (hFN : Block.Preceq (eraseFG (clock p (V2.D.Run.stateBefore E rho ih y).st
      (SA.voteTime p.toParams s)).fg.F) N.erase)
    (D : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) D) :
    let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s)
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    let U := proposerVotes src s
    let U' := headVotes p dst s
    (GridCO.seats p.n U).toFinset = (GridCO.seats p.n U').toFinset ∧
    (∀ i, GridCO.equivocates U i = GridCO.equivocates U' i) ∧
    GridCO.voterCount U = GridCO.voterCount U' ∧
    (∀ X, Block.Preceq D X →
      GridCO.goldfishScore src.base.blocks U (proposerSupport src s) X =
        GridCO.goldfishScore dst.base.blocks U' (headSupport p dst s) X) := by
  have hvd : SA.proposalTime p.toParams s - p.Δ + E.Δ ≤ SA.voteTime p.toParams s := by
    rw [h.base.delta]
    change 4 * p.Δ * (s : Int) - p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hhorizon : SA.voteTime p.toParams s ≤ rho.horizon :=
    (h.base.valid.in_horizon _ (List.mem_of_getElem? hih)).2
  have hsync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST hvd hhorizon
  exact fgsa_score_eq_on_run (hroots := h.base.receiptIdealization)
    E rho h.base.valid hNR h.base.delta s hsync
    hx hy hip hih hseat N hem hadm hFN D hgeom

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 F1b.4b N1 C14 and C9/C11–C13/C19; blueprint 03:350–379.
DC: Goldfish/ProposalWalkTransportCore.lean:162–191; Conditions.lean:134.
INTENTIONAL: the Clean healthy prefix ends no earlier than v_s. Both N1
LabelSync records come from the same healthy prefix.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ.
legacy: sleep consumers use the _on form in RegimesService -/
theorem fgsa_ghost_transfer_sfx_on_clean
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hNR : V2.D.NoRestart rho)
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (s : Slot) (hcut : SA.voteTime p.toParams s ≤ b₀)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : N.erase ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (D : FGBlock (Fin p.n))
    (hgeom : WalkRunGeometry p
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) s D) :
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    Block.Preceq N.erase.parent (headVote p dst s) := by
  have hpt : SA.proposalTime p.toParams s - p.Δ + E.Δ ≤ SA.proposalTime p.toParams s := by
    rw [h.base.delta]
    exact le_of_eq (sub_add_cancel _ _)
  have htv : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hscore := Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _)
    (hpt.trans htv) hcut h.cut.2
  have hwalk := Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _)
    hpt (htv.trans hcut) h.cut.2
  exact fgsa_ghost_transfer_sfx_on_run (hroots := h.base.receiptIdealization)
    E rho h.base.valid hNR h.base.delta s
    hscore hwalk hx hy hip hih hseat N hem hadm D hgeom

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 F1b.4b N1 C14 and C9/C11–C13/C19; blueprint 03:350–379.
DC: Goldfish/ProposalWalkTransportCore.lean:162–191; Conditions.lean:110.
INTENTIONAL: Recovery requires GST ≤ t_s - Δ. The actual proposal and
HEAD ticks supply the horizons for the two N1 LabelSync records.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ.
legacy: sleep consumers use the _on form in RegimesService -/
theorem fgsa_ghost_transfer_sfx_on_recovery
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hNR : V2.D.NoRestart rho)
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (s : Slot) (hGST : E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : N.erase ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (D : FGBlock (Fin p.n))
    (hgeom : WalkRunGeometry p
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) s D) :
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    Block.Preceq N.erase.parent (headVote p dst s) := by
  have hpt : SA.proposalTime p.toParams s - p.Δ + E.Δ ≤ SA.proposalTime p.toParams s := by
    rw [h.base.delta]
    exact le_of_eq (sub_add_cancel _ _)
  have htv : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hvh : SA.voteTime p.toParams s ≤ rho.horizon :=
    (h.base.valid.in_horizon _ (List.mem_of_getElem? hih)).2
  have hscore := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST (hpt.trans htv) hvh
  have hwalk := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST hpt (htv.trans hvh)
  exact fgsa_ghost_transfer_sfx_on_run (hroots := h.base.receiptIdealization)
    E rho h.base.valid hNR h.base.delta s
    hscore hwalk hx hy hip hih hseat N hem hadm D hgeom

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. J2 HEAD clause on a Clean prefix; 21 H.22:3100–3120, S1b E1–E6.
DC: Goldfish/PreparedV4CanonicalProposalDuty.lean:867–887; Conditions.lean:134.
INTENTIONAL: the Clean record supplies both G25/G11 synchronization intervals.
The consumer supplies the same per-reader geometry as the Shared producer.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ.
legacy: sleep consumers use the _on form in RegimesService -/
theorem exactService_head_of_proposal_clean
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hNR : V2.D.NoRestart rho)
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (s : Slot) (hcut : SA.voteTime p.toParams s ≤ b₀)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : FGBlock (Fin p.n)) (hgeom : ExactHeadRunGeometry E rho ip x s D N.erase) :
    SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
        headAtLabel p c E rho y s = some N.erase := by
  have hpt : SA.proposalTime p.toParams s - p.Δ + E.Δ ≤ SA.proposalTime p.toParams s := by
    rw [h.base.delta]
    exact le_of_eq (sub_add_cancel _ _)
  have htv : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hscore := Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _)
    (hpt.trans htv) hcut h.cut.2
  have hwalk := Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _)
    hpt (htv.trans hcut) h.cut.2
  exact exactService_head_of_proposal (hroots := h.base.receiptIdealization)
    E rho h.base.valid hNR h.base.delta s
    hscore hwalk hx hip hseat N hem D hgeom

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. J2 HEAD clause in Recovery; 21 H.22:3100–3120, S1b E1–E6.
DC: Goldfish/PreparedV4CanonicalProposalDuty.lean:867–887; Conditions.lean:110.
INTENTIONAL: GST precedes t_s - Δ, and the HEAD horizon supplies both
G25/G11 synchronization intervals. Geometry remains a consumer obligation.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ.
legacy: sleep consumers use the _on form in RegimesService -/
theorem exactService_head_of_proposal_recovery
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hNR : V2.D.NoRestart rho)
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (s : Slot) (hGST : E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : FGBlock (Fin p.n)) (hgeom : ExactHeadRunGeometry E rho ip x s D N.erase) :
    SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
        headAtLabel p c E rho y s = some N.erase := by
  intro hhorizon
  have hpt : SA.proposalTime p.toParams s - p.Δ + E.Δ ≤ SA.proposalTime p.toParams s := by
    rw [h.base.delta]
    exact le_of_eq (sub_add_cancel _ _)
  have htv : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hscore := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST (hpt.trans htv) hhorizon
  have hwalk := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST hpt (htv.trans hhorizon)
  exact exactService_head_of_proposal (hroots := h.base.receiptIdealization)
    E rho h.base.valid hNR h.base.delta s
    hscore hwalk hx hip hseat N hem D hgeom hhorizon

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. J2 HEAD clause on a Clean prefix; 21 H.22:3100–3120, S1b E1–E6.
DC: Goldfish/PreparedV4CanonicalProposalDuty.lean:867–887; Conditions.lean:134.
INTENTIONAL: the Clean record supplies both G25/G11 synchronization intervals.
Class (iii). The Shared supplier constructs walk and endpoint geometry
from the same per-reader elementary premises. Gate service stays separate.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ.
legacy: sleep consumers use the _on form in RegimesService -/
theorem exactService_head_of_retained_proposal_clean
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hNR : V2.D.NoRestart rho)
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (s : Slot) (hcut : SA.voteTime p.toParams s ≤ b₀)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : FGBlock (Fin p.n))
    (hreads : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D N.erase Kc) :
    SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
        headAtLabel p c E rho y s = some N.erase := by
  have hpt : SA.proposalTime p.toParams s - p.Δ + E.Δ ≤ SA.proposalTime p.toParams s := by
    rw [h.base.delta]
    exact le_of_eq (sub_add_cancel _ _)
  have htv : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hscore := Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _)
    (hpt.trans htv) hcut h.cut.2
  have hwalk := Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _)
    hpt (htv.trans hcut) h.cut.2
  have hgeom := fgsa_retainedExactHead_geometry_on_run (hroots := h.base.receiptIdealization)
    E rho h.base.valid hNR
    h.base.delta s hwalk hscore hx hip hseat N hem D hreads
  exact exactService_head_of_retained_proposal E rho h.base.valid h.base.delta s
    hip N hem D hgeom

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. J2 HEAD clause in Recovery; 21 H.22:3100–3120, S1b E1–E6.
DC: Goldfish/PreparedV4CanonicalProposalDuty.lean:867–887; Conditions.lean:110.
INTENTIONAL: GST precedes t_s - Δ, and the HEAD horizon supplies both
G25/G11 synchronization intervals. Class (iii). The Shared supplier
constructs geometry from per-reader premises. Gate service stays separate.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ.
legacy: sleep consumers use the _on form in RegimesService -/
theorem exactService_head_of_retained_proposal_recovery
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hNR : V2.D.NoRestart rho)
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (s : Slot) (hGST : E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : FGBlock (Fin p.n))
    (hreads : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D N.erase Kc) :
    SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
        headAtLabel p c E rho y s = some N.erase := by
  intro hhorizon
  have hpt : SA.proposalTime p.toParams s - p.Δ + E.Δ ≤ SA.proposalTime p.toParams s := by
    rw [h.base.delta]
    exact le_of_eq (sub_add_cancel _ _)
  have htv : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hscore := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST (hpt.trans htv) hhorizon
  have hwalk := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST hpt (htv.trans hhorizon)
  have hgeom := fgsa_retainedExactHead_geometry_on_run (hroots := h.base.receiptIdealization)
    E rho h.base.valid hNR
    h.base.delta s hwalk hscore hx hip hseat N hem D hreads
  exact exactService_head_of_retained_proposal E rho h.base.valid h.base.delta s
    hip N hem D hgeom hhorizon

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 A.9 and blueprint 21 H.22 H3, conditional Clean exact service.
DC: Generic/Conditions.lean:134–156; UserConfirmationRecovery.lean:235.
INTENTIONAL: healthy-prefix delivery supplies LabelSync. Clean participation
alone need not reach the fast threshold, so that count stays explicit.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ.
legacy: sleep consumers use the _on form in RegimesService -/
theorem exactService_of_head_clean
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hNR : V2.D.NoRestart rho)
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (v : Slot) (Q : Block) (hne : Q ≠ .genesis)
    (hcut : SA.gateTime p.toParams v ≤ b₀)
    (hhead : SA.voteTime p.toParams v ≤ rho.horizon →
      ∀ x ∈ rho.honest, headAtLabel p c E rho x v = some Q)
    (hfast : SA.releaseThreshold p.toParams ≤ (awakeHonest E rho (SA.voteTime p.toParams v)).card)
    (hgeometry : ∀ i x, x ∈ rho.honest → IsGateTick p c rho i x v →
      ExactServiceGateGeometry E rho i x v Q) : ExactService p c E rho v Q := by
  have hvd : SA.voteTime p.toParams v + E.Δ ≤ SA.gateTime p.toParams v := by
    rw [h.base.delta]
    change 4 * p.Δ * (v : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (v : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hvpos : 0 ≤ SA.voteTime p.toParams v := by
    change 0 ≤ 4 * p.Δ * (v : Int) + p.Δ
    have hd := p.deltaPos
    positivity
  have hvcut : SA.voteTime p.toParams v < b₀ := by
    have hd : 0 < E.Δ := h.base.delta.symm ▸ p.deltaPos
    linarith
  apply exactService_of_head_and_gate (hroots := h.base.receiptIdealization)
    E rho h.base.valid hNR h.base.delta
    h.base.cstar v Q hne hhead
    (fun _ => Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _) hvd hcut h.cut.2)
    _ hgeometry
  intro _
  exact exactService_participation_of_card E rho h.base.cstar v
    ⟨h.partBefore _ hvpos hvcut⟩ hfast

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 A.9 and blueprint 21 H.22 H3, conditional Recovery exact service.
DC: Generic/Conditions.lean:110–132; UserConfirmationRecovery.lean:235.
INTENTIONAL: post-GST waking and the one-third fault bound supply the SA
fast count. Cardinality uses only the fresh HEAD-seat bijection.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ.
legacy: sleep consumers use the _on form in RegimesService -/
theorem exactService_of_head_recovery
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hNR : V2.D.NoRestart rho)
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (v : Slot) (Q : Block) (hne : Q ≠ .genesis)
    (hGST : E.t_GST ≤ SA.voteTime p.toParams v)
    (hhead : SA.voteTime p.toParams v ≤ rho.horizon →
      ∀ x ∈ rho.honest, headAtLabel p c E rho x v = some Q)
    (hgeometry : ∀ i x, x ∈ rho.honest → IsGateTick p c rho i x v →
      ExactServiceGateGeometry E rho i x v Q) : ExactService p c E rho v Q := by
  have hvd : SA.voteTime p.toParams v + E.Δ ≤ SA.gateTime p.toParams v := by
    rw [h.base.delta]
    change 4 * p.Δ * (v : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (v : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  apply exactService_of_head_and_gate (hroots := h.base.receiptIdealization)
    E rho h.base.valid hNR h.base.delta
    h.base.cstar v Q hne hhead
    (fun hh => Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST hvd hh) _ hgeometry
  intro hh
  have hvhor : SA.voteTime p.toParams v ≤ rho.horizon := by
    have hd : 0 < E.Δ := h.base.delta.symm ▸ p.deltaPos
    linarith
  have hawake : awakeHonest E rho (SA.voteTime p.toParams v) = rho.honest := by
    rw [awakeHonest_def]
    exact Finset.filter_eq_self.mpr (fun x hx => h.awake x hx _ hGST hvhor)
  have hn : Fintype.card V = p.n :=
    (V2.D.CStar.seats_eq (ℓ := .base (.head v)) h.base.cstar trivial).symm
  have hcard : (faulty rho).card + rho.honest.card = p.n := by
    rw [faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hn]
    have hc := Finset.card_le_univ rho.honest
    rw [hn] at hc
    omega
  have hf := h.fault
  have hp := p.nPos
  apply exactService_participation_of_card E rho h.base.cstar v
  · rw [hawake]
    exact ⟨by omega⟩
  · rw [hawake]
    change (p.n + 1) / 2 ≤ rho.honest.card
    omega

/-- [own-row Option 1; DC N3] `HealthyPrefix₂` survives the same-time self-delivery of a
released FG row: the base through `Base₂.snoc_ownRow`, the delivery premise through
`healthyPrefixDeliveryBy_snoc_selfDelivery`; the cut and participation fields read no event.
Scope: `hkey` restricts the run to events at or before `(t, 2)`, so the run ends at the
action time `t`; `HealthyPrefix₂.ownRow_run` removes the restriction through the cut. -/
theorem HealthyPrefix₂.snoc_ownRow {b₀ : Time} (h : HealthyPrefix₂ p c E rho b₀ ΔF)
    {i : Nat} {v : V} {t : Time} (hkey : ∀ e ∈ rho.events, e.key ≤ toLex (t, 2))
    (hi : rho.events[i]? = some (.tick v t))
    (hlast : ∀ k e, i < k → rho.events[k]? = some e → e.node ≠ v)
    {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    HealthyPrefix₂ p c E
      ({ rho with events := rho.events ++ [.deliver v (ofRow p ⟨.seat .fg j, body⟩) t] })
      b₀ ΔF where
  base := h.base.snoc_ownRow hkey hi hlast ho
  cut := h.cut
  healthy := healthyPrefixDeliveryBy_snoc_selfDelivery h.healthy hi ho (fgsa_row_noCarried _)
  deltaF := h.deltaF
  partBefore := h.partBefore

/-- [own-row Option 1; DC N3] `Recovery₂` survives the same-time self-delivery of a released
FG row: the delivery premise through `partialSynchronyBy_snoc_selfDelivery`, the base through
`Base₂.snoc_ownRow`; the recurrence, fault, awake and gap fields read no event. Scope: as for
`HealthyPrefix₂.snoc_ownRow`; `Recovery₂.ownRow_run` removes the restriction. -/
theorem Recovery₂.snoc_ownRow {G : Time} (h : Recovery₂ p c E rho G ΔF)
    {i : Nat} {v : V} {t : Time} (hkey : ∀ e ∈ rho.events, e.key ≤ toLex (t, 2))
    (hi : rho.events[i]? = some (.tick v t))
    (hlast : ∀ k e, i < k → rho.events[k]? = some e → e.node ≠ v)
    {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    Recovery₂ p c E
      ({ rho with events := rho.events ++ [.deliver v (ofRow p ⟨.seat .fg j, body⟩) t] })
      G ΔF where
  sync := partialSynchronyBy_snoc_selfDelivery h.sync hi ho (fgsa_row_noCarried _)
  deltaF := h.deltaF
  gap := h.gap
  base := h.base.snoc_ownRow hkey hi hlast ho
  fault := h.fault
  awake := h.awake
  gapPos := h.gapPos

/-- [own-row Option 1; DC N3] `HealthyPrefix₂` survives the cut after the ticks at `t` when
the prefix cut `b₀` is at most `t`: `Base₂.cut` and `healthyPrefixDeliveryBy_cut`. -/
theorem HealthyPrefix₂.cutAt {b₀ : Time} (h : HealthyPrefix₂ p c E rho b₀ ΔF)
    {n i : Nat} {v : V} {t : Time}
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    (hi : rho.events[i]? = some (.tick v t)) (hb : b₀ ≤ t) :
    HealthyPrefix₂ p c E ({ rho with events := rho.events.take n, horizon := t }) b₀ ΔF where
  base := h.base.cutAt hcut hi
  cut := ⟨h.cut.1, hb⟩
  healthy := healthyPrefixDeliveryBy_cut hcut hb
    (h.base.valid.in_horizon _ (List.mem_of_getElem? hi)).2 h.healthy
  deltaF := h.deltaF
  partBefore := h.partBefore

/-- [own-row Option 1; DC N3] The spec-like run of an arbitrary `HealthyPrefix₂` run, for an
action time at or after the prefix cut. -/
theorem HealthyPrefix₂.ownRow_run {b₀ : Time} (h : HealthyPrefix₂ p c E rho b₀ ΔF)
    {n i : Nat} {v : V} {t : Time}
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    (hi : rho.events[i]? = some (.tick v t)) (hb : b₀ ≤ t) {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    HealthyPrefix₂ p c E
      ({ rho with events := rho.events.take n ++ [.deliver v (ofRow p ⟨.seat .fg j, body⟩) t],
                  horizon := t }) b₀ ΔF := by
  have hin : i < n := (hcut i _ hi).mpr (tick_key_le.mpr le_rfl)
  exact (h.cutAt hcut hi hb).snoc_ownRow (cut_key_le hcut) (getElem?_cut_iff.mpr ⟨hin, hi⟩)
    (cut_lastEvent h.base.valid.toScheduleWellFormed hcut hi)
    (by rw [emitsAt_cut_of_lt hin]; exact ho)

/-- [own-row Option 1; DC N3] `Recovery₂` survives the cut after the ticks at `t`:
`partialSynchronyBy_cut` and `Base₂.cut`; the recurrence and awake fields on the shorter
horizon follow from the old ones. -/
theorem Recovery₂.cutAt {G : Time} (h : Recovery₂ p c E rho G ΔF) {n i : Nat} {v : V}
    {t : Time}
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    (hi : rho.events[i]? = some (.tick v t)) :
    Recovery₂ p c E ({ rho with events := rho.events.take n, horizon := t }) G ΔF := by
  obtain ⟨-, hth⟩ := h.base.valid.in_horizon _ (List.mem_of_getElem? hi)
  exact
    { sync := partialSynchronyBy_cut hcut hth h.sync
      deltaF := h.deltaF
      gap := fun t' hG hle => h.gap t' hG (le_trans hle hth)
      base := h.base.cutAt hcut hi
      fault := h.fault
      awake := fun u hu t' hG hle => h.awake u hu t' hG (le_trans hle hth)
      gapPos := h.gapPos }

/-- [own-row Option 1; DC N3] The spec-like run of an arbitrary `Recovery₂` run. -/
theorem Recovery₂.ownRow_run {G : Time} (h : Recovery₂ p c E rho G ΔF) {n i : Nat} {v : V}
    {t : Time} (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    (hi : rho.events[i]? = some (.tick v t)) {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    Recovery₂ p c E
      ({ rho with events := rho.events.take n ++ [.deliver v (ofRow p ⟨.seat .fg j, body⟩) t],
                  horizon := t }) G ΔF := by
  have hin : i < n := (hcut i _ hi).mpr (tick_key_le.mpr le_rfl)
  exact (h.cutAt hcut hi).snoc_ownRow (cut_key_le hcut) (getElem?_cut_iff.mpr ⟨hin, hi⟩)
    (cut_lastEvent h.base.valid.toScheduleWellFormed hcut hi)
    (by rw [emitsAt_cut_of_lt hin]; exact ho)

/-- [own-row Option 1; DC N3] `HealthyPrefix₂` survives the cut after the ticks at `t` with the
prefix cut lowered to `t`, for an action time at most the prefix cut: the old delivery
obligations have deadlines at most `t` (`healthyPrefixDeliveryBy_of_le`), and participation
before `t` is participation before `b₀`. -/
theorem HealthyPrefix₂.cutAt_le {b₀ : Time} (h : HealthyPrefix₂ p c E rho b₀ ΔF)
    {n i : Nat} {v : V} {t : Time}
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    (hi : rho.events[i]? = some (.tick v t)) (hb : t ≤ b₀) :
    HealthyPrefix₂ p c E ({ rho with events := rho.events.take n, horizon := t }) t ΔF where
  base := h.base.cutAt hcut hi
  cut := ⟨(h.base.valid.in_horizon _ (List.mem_of_getElem? hi)).1, le_rfl⟩
  healthy := healthyPrefixDeliveryBy_cut hcut le_rfl
    (h.base.valid.in_horizon _ (List.mem_of_getElem? hi)).2
    (healthyPrefixDeliveryBy_of_le hb h.healthy)
  deltaF := h.deltaF
  partBefore := fun t' h0 hlt => h.partBefore t' h0 (lt_of_lt_of_le hlt hb)

/-- [own-row Option 1; DC N3] The spec-like run of an arbitrary `HealthyPrefix₂` run, for an
action time at most the prefix cut; the prefix cut is lowered to `t`. -/
theorem HealthyPrefix₂.ownRow_run_le {b₀ : Time} (h : HealthyPrefix₂ p c E rho b₀ ΔF)
    {n i : Nat} {v : V} {t : Time}
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    (hi : rho.events[i]? = some (.tick v t)) (hb : t ≤ b₀) {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    HealthyPrefix₂ p c E
      ({ rho with events := rho.events.take n ++ [.deliver v (ofRow p ⟨.seat .fg j, body⟩) t],
                  horizon := t }) t ΔF := by
  have hin : i < n := (hcut i _ hi).mpr (tick_key_le.mpr le_rfl)
  exact (h.cutAt_le hcut hi hb).snoc_ownRow (cut_key_le hcut) (getElem?_cut_iff.mpr ⟨hin, hi⟩)
    (cut_lastEvent h.base.valid.toScheduleWellFormed hcut hi)
    (by rw [emitsAt_cut_of_lt hin]; exact ho)

/-- [own-row Option 1; DC N3] The spec-like run of an arbitrary `CleanPrefix₂` run, for an
action time at or after the prefix cut. -/
theorem CleanPrefix₂.ownRow_run {b₀ : Time} (h : CleanPrefix₂ p c E rho b₀ ΔF)
    {n i : Nat} {v : V} {t : Time}
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    (hi : rho.events[i]? = some (.tick v t)) (hb : b₀ ≤ t) {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    CleanPrefix₂ p c E
      ({ rho with events := rho.events.take n ++ [.deliver v (ofRow p ⟨.seat .fg j, body⟩) t],
                  horizon := t }) b₀ ΔF where
  toHealthyPrefix₂ := h.toHealthyPrefix₂.ownRow_run hcut hi hb ho
  partAt := h.partAt

/-- [own-row Option 1; DC N3] The spec-like run of an arbitrary `CleanPrefix₂` run, for an
action time at most the prefix cut; the prefix cut is lowered to `t`. Participation at `t`
is participation before `b₀` when `t < b₀`, and the old participation at the cut when
`t = b₀`. -/
theorem CleanPrefix₂.ownRow_run_le {b₀ : Time} (h : CleanPrefix₂ p c E rho b₀ ΔF)
    {n i : Nat} {v : V} {t : Time}
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    (hi : rho.events[i]? = some (.tick v t)) (hb : t ≤ b₀) {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    CleanPrefix₂ p c E
      ({ rho with events := rho.events.take n ++ [.deliver v (ofRow p ⟨.seat .fg j, body⟩) t],
                  horizon := t }) t ΔF where
  toHealthyPrefix₂ := h.toHealthyPrefix₂.ownRow_run_le hcut hi hb ho
  partAt := by
    rcases lt_or_eq_of_le hb with hlt | heq
    · exact h.partBefore t (h.base.valid.in_horizon _ (List.mem_of_getElem? hi)).1 hlt
    · obtain rfl := heq
      exact h.partAt

/-- [own-row Option 1; DC N3] The spec-like run of an arbitrary `Clean₂` run: the clean prefix
runs to the horizon, so every action time is at most the prefix cut. -/
theorem Clean₂.ownRow_run (h : Clean₂ p c E rho ΔF) {n i : Nat} {v : V} {t : Time}
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    (hi : rho.events[i]? = some (.tick v t)) {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    Clean₂ p c E
      ({ rho with events := rho.events.take n ++ [.deliver v (ofRow p ⟨.seat .fg j, body⟩) t],
                  horizon := t }) ΔF where
  pre := h.pre.ownRow_run_le hcut hi
    (h.pre.base.valid.in_horizon _ (List.mem_of_getElem? hi)).2 ho
  gst := h.gst

/-- [own-row Option 1; DC N3] The spec-like run of an arbitrary `Outage₂` run, for an action
time at or after the end of the outage window: the prefix through `HealthyPrefix₂.ownRow_run`,
the window fields read no event, and the horizon `t` is at or after `b₁`. -/
theorem Outage₂.ownRow_run {fast : Bool} {T b₀ b₁ : Time}
    (h : Outage₂ p c fast E rho T b₀ b₁ ΔF) {n i : Nat} {v : V} {t : Time}
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    (hi : rho.events[i]? = some (.tick v t)) (hb : b₁ ≤ t) {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    Outage₂ p c fast E
      ({ rho with events := rho.events.take n ++ [.deliver v (ofRow p ⟨.seat .fg j, body⟩) t],
                  horizon := t }) T b₀ b₁ ΔF where
  pre := h.pre.ownRow_run hcut hi (le_trans h.order.2.2.1 hb) ho
  sleepy := h.sleepy
  order := ⟨h.order.1, h.order.2.1, h.order.2.2.1, hb⟩
  lag := h.lag
  budget := h.budget
  fastPart := h.fastPart

/-- [own-row Option 1; DC N3] The spec-like run of an arbitrary `Outage₂` run, for an action
time in the outage window; the window end is lowered to `t`. -/
theorem Outage₂.ownRow_run_mid {fast : Bool} {T b₀ b₁ : Time}
    (h : Outage₂ p c fast E rho T b₀ b₁ ΔF) {n i : Nat} {v : V} {t : Time}
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    (hi : rho.events[i]? = some (.tick v t)) (hb0 : b₀ ≤ t) (hb1 : t ≤ b₁)
    {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    Outage₂ p c fast E
      ({ rho with events := rho.events.take n ++ [.deliver v (ofRow p ⟨.seat .fg j, body⟩) t],
                  horizon := t }) T b₀ t ΔF where
  pre := h.pre.ownRow_run hcut hi hb0 ho
  sleepy := h.sleepy
  order := ⟨h.order.1, h.order.2.1, hb0, le_rfl⟩
  lag := h.lag
  budget := le_trans (by linarith) h.budget
  fastPart := h.fastPart

end AvailableChain.FGSA.Run

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.V2.Duty (faulty)
variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
variable {ΔF : Time}

/-- Continuous Recovery awake time supplies join after the previous slot start.
The vote-time GST bound alone does not supply this join window. -/
theorem Recovery₂.joinedAt_of_slotStart_le
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G : Time} (h : Recovery₂ p c E rho G ΔF) (s : Slot)
    (hGST : E.t_GST ≤ slotStartZ p ((s : Int) - 1))
    (hhor : SA.voteTime p.toParams s ≤ rho.horizon) :
    ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) := by
  have hb : slotStartZ p ((s : Int) - 1) ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * ((s : Int) - 1) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  intro y hy
  have hw : ∀ u, 0 < u → u ≤ SA.voteTime p.toParams s →
      V2.D.Wakes E y u → u ≤ slotStartZ p ((s : Int) - 1) := by
    intro u hu hut hW
    by_contra hn
    have ha := h.awake y hy (u - 1)
      (by dsimp [Time] at *; omega) (by dsimp [Time] at *; omega)
    have hFalse := hW.2
    rw [ha] at hFalse
    exact Bool.noConfusion hFalse
  refine ⟨h.awake y hy _ (hGST.trans hb) hhor, hw, ?_⟩
  intro u hu hut hr
  have hW := h.base.restartsAtWakes y u hr
  exact hw u hW.1 hut hW.2

/-- Exact service on a Clean prefix uses joined participation and local gate receipts.
The joined releaseThreshold count hfast is a separate input. -/
theorem exactService_of_head_clean_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (v : Slot) (Q : Block) (hne : Q ≠ .genesis)
    (hcut : SA.gateTime p.toParams v ≤ b₀)
    (hhead : SA.voteTime p.toParams v ≤ rho.horizon →
      ∀ x ∈ rho.honest, joinedAt p E rho x v (SA.voteTime p.toParams v) →
        headAtLabel p c E rho x v = some Q)
    (hfast : SA.releaseThreshold p.toParams ≤
      (joinedHonest p E rho (SA.voteTime p.toParams v)).card)
    (hbatch : Gen.Pure.Batch (joinedHonest p E rho (SA.voteTime p.toParams v)).card
      (faulty rho).card)
    (hgeometry : ∀ i x, x ∈ rho.honest → IsGateTick p c rho i x v →
      ExactServiceGateGeometry E rho i x v Q)
    (hScopes : ∀ i x,
      confirmedReaderAtIdx p c E rho x (afterTicksIdx rho (SA.gateTime p.toParams v))
        (SA.gateTime p.toParams v) → IsGateTick p c rho i x v →
      GateReceiptScope E rho i x v) : ExactService p c E rho v Q := by
  have hvd : SA.voteTime p.toParams v + E.Δ ≤ SA.gateTime p.toParams v := by
    rw [h.base.delta]
    change 4 * p.Δ * (v : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (v : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  apply exactService_of_head_and_gate_on (hroots := h.base.receiptIdealization)
    E rho h.base.valid h.base.delta
    h.base.cstar v Q hne hhead
    (fun _ => Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _) hvd hcut h.cut.2)
    (fun _ => exactService_participation_of_card_joined E rho h.base.cstar v
      hbatch hfast) hgeometry hScopes

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 A.9 and blueprint 21 H.22 H3, conditional Recovery exact service.
DC: Generic/Conditions.lean:110–132; UserConfirmationRecovery.lean:235.
INTENTIONAL: hfast supplies the releaseThreshold bound on joined honest voters.
Recovery awake time supplies join only after the previous slot start passes GST.
Cardinality uses only the fresh HEAD-seat bijection.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem exactService_of_head_recovery_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (v : Slot) (Q : Block) (hne : Q ≠ .genesis)
    (hGST : E.t_GST ≤ SA.voteTime p.toParams v)
    (hhead : SA.voteTime p.toParams v ≤ rho.horizon →
      ∀ x ∈ rho.honest, joinedAt p E rho x v (SA.voteTime p.toParams v) →
        headAtLabel p c E rho x v = some Q)
    (hfast : SA.releaseThreshold p.toParams ≤
      (joinedHonest p E rho (SA.voteTime p.toParams v)).card)
    (hbatch : Gen.Pure.Batch (joinedHonest p E rho (SA.voteTime p.toParams v)).card
      (faulty rho).card)
    (hgeometry : ∀ i x, x ∈ rho.honest → IsGateTick p c rho i x v →
      ExactServiceGateGeometry E rho i x v Q)
    (hScopes : ∀ i x,
      confirmedReaderAtIdx p c E rho x (afterTicksIdx rho (SA.gateTime p.toParams v))
        (SA.gateTime p.toParams v) → IsGateTick p c rho i x v →
      GateReceiptScope E rho i x v) : ExactService p c E rho v Q := by
  have hvd : SA.voteTime p.toParams v + E.Δ ≤ SA.gateTime p.toParams v := by
    rw [h.base.delta]
    change 4 * p.Δ * (v : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (v : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  apply exactService_of_head_and_gate_on (hroots := h.base.receiptIdealization)
    E rho h.base.valid h.base.delta
    h.base.cstar v Q hne hhead
    (fun hh => Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST hvd hh)
    (fun _ => exactService_participation_of_card_joined E rho h.base.cstar v
      hbatch hfast) hgeometry hScopes

/-- Local receiver services compose with the regime's base at the actual reads. -/
theorem exactService_head_of_proposal_clean_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (s : Slot) (_hcut : SA.voteTime p.toParams s ≤ b₀)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : FGBlock (Fin p.n)) (hgeom : ExactHeadRunGeometry E rho ip x s D N.erase)
    (hScopes : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      ScoreServiceScope E rho ip ih x y s (eraseFG D)) :
    SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
        headAtLabel p c E rho y s = some N.erase := by
  exact exactService_head_of_proposal_on (hroots := h.base.receiptIdealization)
    E rho h.base.valid h.base.delta s hx hip hseat N hem D hgeom hScopes

/-- Local receiver services compose with the regime's base at the actual reads. -/
theorem exactService_head_of_proposal_recovery_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (s : Slot) (_hGST : E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : FGBlock (Fin p.n)) (hgeom : ExactHeadRunGeometry E rho ip x s D N.erase)
    (hScopes : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      ScoreServiceScope E rho ip ih x y s (eraseFG D)) :
    SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
        headAtLabel p c E rho y s = some N.erase := by
  exact exactService_head_of_proposal_on (hroots := h.base.receiptIdealization)
    E rho h.base.valid h.base.delta s hx hip hseat N hem D hgeom hScopes

/-- Local receiver services compose with the regime's base at the actual reads. -/
theorem fgsa_score_eq_on_clean_of_retained_proposal_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (s : Slot) (_hcut : SA.voteTime p.toParams s ≤ b₀)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : N.erase ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (hFN : Block.Preceq (eraseFG (clock p (V2.D.Run.stateBefore E rho ih y).st
      (SA.voteTime p.toParams s)).fg.F) N.erase)
    (D : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) D)
    (hScope : ScoreServiceScope E rho ip ih x y s D) :
    let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s)
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    let U := proposerVotes src s
    let U' := headVotes p dst s
    (GridCO.seats p.n U).toFinset = (GridCO.seats p.n U').toFinset ∧
    (∀ i, GridCO.equivocates U i = GridCO.equivocates U' i) ∧
    GridCO.voterCount U = GridCO.voterCount U' ∧
    (∀ X, Block.Preceq D X →
      GridCO.goldfishScore src.base.blocks U (proposerSupport src s) X =
        GridCO.goldfishScore dst.base.blocks U' (headSupport p dst s) X) := by
  exact fgsa_score_eq_on_run_on (hroots := h.base.receiptIdealization)
    E rho h.base.valid s hx hy hip hih hseat N hem hadm hFN D hgeom hScope

/-- Local receiver services compose with the regime's base at the actual reads. -/
theorem fgsa_score_eq_on_recovery_of_retained_proposal_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (s : Slot) (_hGST : E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : N.erase ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (hFN : Block.Preceq (eraseFG (clock p (V2.D.Run.stateBefore E rho ih y).st
      (SA.voteTime p.toParams s)).fg.F) N.erase)
    (D : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) D)
    (hScope : ScoreServiceScope E rho ip ih x y s D) :
    let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s)
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    let U := proposerVotes src s
    let U' := headVotes p dst s
    (GridCO.seats p.n U).toFinset = (GridCO.seats p.n U').toFinset ∧
    (∀ i, GridCO.equivocates U i = GridCO.equivocates U' i) ∧
    GridCO.voterCount U = GridCO.voterCount U' ∧
    (∀ X, Block.Preceq D X →
      GridCO.goldfishScore src.base.blocks U (proposerSupport src s) X =
        GridCO.goldfishScore dst.base.blocks U' (headSupport p dst s) X) := by
  exact fgsa_score_eq_on_run_on (hroots := h.base.receiptIdealization)
    E rho h.base.valid s hx hy hip hih hseat N hem hadm hFN D hgeom hScope

/-- Local receiver services compose with the regime's base at the actual reads. -/
theorem fgsa_ghost_transfer_sfx_on_clean_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (s : Slot) (_hcut : SA.voteTime p.toParams s ≤ b₀)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : N.erase ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (D : FGBlock (Fin p.n))
    (hgeom : WalkRunGeometry p
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) s D)
    (hScope : ScoreServiceScope E rho ip ih x y s (eraseFG D)) :
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    Block.Preceq N.erase.parent (headVote p dst s) := by
  exact fgsa_ghost_transfer_sfx_on_run_on (hroots := h.base.receiptIdealization)
    E rho h.base.valid s hx hy hip hih hseat N hem hadm D hgeom hScope

/-- Local receiver services compose with the regime's base at the actual reads. -/
theorem fgsa_ghost_transfer_sfx_on_recovery_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (s : Slot) (_hGST : E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : N.erase ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (D : FGBlock (Fin p.n))
    (hgeom : WalkRunGeometry p
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) s D)
    (hScope : ScoreServiceScope E rho ip ih x y s (eraseFG D)) :
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    Block.Preceq N.erase.parent (headVote p dst s) := by
  exact fgsa_ghost_transfer_sfx_on_run_on (hroots := h.base.receiptIdealization)
    E rho h.base.valid s hx hy hip hih hseat N hem hadm D hgeom hScope

/-- Retained HEAD service uses joined reads and per-object replay history. -/
theorem exactService_head_of_retained_proposal_clean_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (s : Slot) (_hcut : SA.voteTime p.toParams s ≤ b₀)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : FGBlock (Fin p.n))
    (hreads : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D N.erase Kc)
    (hScopes : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      RetainedServiceScope E rho ip ih x y s N) :
    SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
        headAtLabel p c E rho y s = some N.erase := by
  have hgeom := fgsa_retainedExactHead_geometry_on_run_on
    (hroots := h.base.receiptIdealization)
    E rho h.base.valid s hx hip hseat N hem D hreads hScopes
  exact exactService_head_of_retained_proposal_on E rho h.base.valid h.base.delta s
    hip N hem D hgeom

/-- Retained HEAD service uses joined reads and per-object replay history. -/
theorem exactService_head_of_retained_proposal_recovery_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (s : Slot) (_hGST : E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : FGBlock (Fin p.n))
    (hreads : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D N.erase Kc)
    (hScopes : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      RetainedServiceScope E rho ip ih x y s N) :
    SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
        headAtLabel p c E rho y s = some N.erase := by
  have hgeom := fgsa_retainedExactHead_geometry_on_run_on
    (hroots := h.base.receiptIdealization)
    E rho h.base.valid s hx hip hseat N hem D hreads hScopes
  exact exactService_head_of_retained_proposal_on E rho h.base.valid h.base.delta s
    hip N hem D hgeom

end AvailableChain.FGSA.Run
end
