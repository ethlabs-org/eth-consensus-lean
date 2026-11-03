module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthySuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Outputs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyRecordGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyResetEnvelope
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyRecordWriters
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Simulation
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LocksWF
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.CoefficientAdapters
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Regimes.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Accountable
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor

public section

/-! # Conditional read safety and the healthy repair schedule -/

namespace Consensus.Goldilocks.Refinement
open Blocks Shape

/-- A completed result is strictly older than the current latest view, including
the equality boundary at its update time. -/
theorem result_label_lt_latest_of_time
    {sp : SA.SAParams} {FGP : Type} {A : SA.SAState sp.n} {Φ : SA.Frm sp.n FGP}
    {s : Nat} {t : Time} (ht0 : 0 ≤ t) (ht : sp.ts s + 6 * sp.Δ ≤ t) :
    (s : Int) < (SA.latestView sp A Φ t).2 := by
  have hnext : sp.ts (s + 1 : Nat) + 2 * sp.Δ ≤ t := by
    simp only [SA.SAParams.ts] at ht ⊢
    push_cast
    linarith
  have hd := sp.toParams.hΔ
  simp only [SA.latestView]
  split_ifs with hphase
  · have hh := (SA.ts_le_iff_le_slot sp ht0 (s + 1 : Nat)).mp
      (show sp.ts (s + 1 : Nat) ≤ t by linarith)
    push_cast at hh
    omega
  · have hh := (SA.ts_lt_iff sp).mp
      (show sp.ts (s + 1 : Nat) < sp.ts (sp.slot t) by linarith)
    push_cast at hh
    omega

/-- An actual stored time-live lock gives the anchor arm only when its normalized
block still covers the record and the current live blocks form a chain. -/
theorem record_below_anchor_of_stored_live_lock
    {sp : SA.SAParams} {FGP : Type} {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ)
    {A : SA.SAState sp.n} {t : Time} {R B : SA.Blk sp.n FGP} {l : SA.Lock}
    (hl : l ∈ A.locks) (hB : B ∈ Φ.tree) (hroot : B.root = l.block)
    (ht : l.LiveAt sp t) (hcover : Φ.Anc R (Φ.viableAncestor B))
    (hchain : ∀ X ∈ SA.liveLockBlocks sp A.locks Φ t,
      ∀ Y ∈ SA.liveLockBlocks sp A.locks Φ t, Goldilocks.Compatible Φ.tree X Y) :
    Φ.Anc R (SA.getAnchor sp A Φ t) := by
  have hmem : Φ.viableAncestor B ∈ SA.liveLockBlocks sp A.locks Φ t :=
    ⟨(SA.viableAncestor_anc hΦ hB).1,
      ⟨⟨(Φ.viableAncestor B).root, l.slot, l.fast, l.expiry⟩, ⟨l, hl, B, hB, hroot, ht, rfl⟩,
        rfl⟩⟩
  exact hcover.trans ((SA.anc_getAnchor hΦ hchain).2 _ (Or.inl hmem))

/-- Whole-record equality at the actual clock. Current source classification, viability
and live-candidate compatibility remain explicit, with no pre-repair invariant. -/
theorem read_eq_record_of_current_votes
    {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {a : Time}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time} (ht0 : 0 ≤ t)
    (hrp : Regimes.ReadPoint tr i t) (hw : tr.awake y t) (hj : tr.JoinedAt y t)
    (hsync : SyncACWindowBefore H (tr.HonestBlocks H) a t tr.projAC)
    (hcatch : CatchACWindowBefore tr.projAC H (tr.HonestBlocks H) a (2 * sp.Δ) t)
    {L : Nat} (hL : (L : Int) =
      (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    (ha : a ≤ sp.ts L)
    (hrecord : ∀ R, SA.lookup (Node.frame (tr.state y i))
        (tr.state y i).ac.latestConfirmed = some R →
      (∀ X ∈ SA.liveLockBlocks sp (tr.state y i).ac.locks (Node.frame (tr.state y i)) t ∪
          {(Node.frame (tr.state y i)).fcRoot},
        Goldilocks.Compatible (Node.frame (tr.state y i)).tree X R) ∧
      ((Node.frame (tr.state y i)).Anc R
          (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
        (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
          ∀ z ∈ H, ∀ q, tr.time q ≤ t → ∀ e, SA.VoteAt tr.projAC z q e →
            e.msg.slot = L → SA.VoteExtends (tr.HonestBlocks H) e.msg R)))
    (hfault : Hᶜ.ncard <
      {x | x ∈ H ∧ tr.awake x (sp.ts L + sp.Δ) ∧ tr.JoinedAt x (sp.ts L + sp.Δ)}.ncard) :
    Regimes.readAfter tr y i t =
      (SA.lookup (Node.frame (tr.state y i))
        (tr.state y i).ac.latestConfirmed).getD (tr.state y i).fg.F := by
  have hΦ := Compose.frameOK_state hrun.toLocalRun hy i
  cases hl : SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed with
  | none => exact SA.acConfirmed_eq_F hΦ (SA.lookup_eq_none hl)
  | some R =>
    obtain ⟨hR, hRr⟩ := SA.lookup_eq_some hl
    obtain ⟨hcomp, hsource⟩ := hrecord R hl
    have hanchor := Compose.anchor_compatible_of_live_candidates hΦ hcomp
    obtain ⟨hc, hs⟩ := Compose.read_head_support_of_target_votes hrun hnc hy ht0
      hrp.1 hrp.2 hw hj hsync hcatch hL ha hR hanchor hsource hfault
    exact SA.acConfirmed_eq hΦ hR hRr (SA.anc_acHead hΦ hR hc hs)

/-- The source arm consumed by `read_eq_record_of_current_votes`: either actual anchor
coverage, or an actual recent raw witness covering the whole record. Its finite transfer
uses explicit current-domain and stored-lock comparisons, not last-setter recency. -/
theorem read_source_of_recent_result
    {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a b t : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {y : Fin sp.n} {i L : Nat}
    {R : SA.Blk sp.n (List (FG.Att sp.n))} (htb : t ≤ b)
    (hsource : (Node.frame (tr.state y i)).Anc R
        (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
      (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
        ∃ x ∈ H, ∃ r s C CV, SA.ResultAt tr.projAC x r s C CV ∧
          Anc (tr.HonestBlocks H) R C ∧ tr.time r ≤ b ∧
          Healing.cutZ sp.toParams g ≤ sp.ts s ∧ s < L ∧
          (∀ z ∈ H, ∀ q ell e, SA.CastAt tr.projAC z q ell e →
            tr.time q ≤ b → s < e.msg.slot →
            (∀ w ∈ H, ∀ p < q, ∀ e', SA.VoteAt tr.projAC w p e' →
              s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e'.msg R) →
            Anc (tr.HonestBlocks H) R ell.frame.fcRoot ∨
              R ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot)) ∧
          (∀ z ∈ H, ∀ q ell e, SA.CastAt tr.projAC z q ell e →
            tr.time q ≤ b → e.msg.slot = s + 1 → ∀ l ∈ (tr.projAC.state z q).locks,
              sp.slot (tr.time q) ≤ l.slot + sp.k → l.slot ≤ s →
              ∀ Y ∈ tr.HonestBlocks H, Y.root = l.block →
                Goldilocks.Compatible (tr.HonestBlocks H) Y R))) :
    (Node.frame (tr.state y i)).Anc R
        (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
      (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
        ∀ z ∈ H, ∀ q, tr.time q ≤ t → ∀ e, SA.VoteAt tr.projAC z q e →
          e.msg.slot = L → SA.VoteExtends (tr.HonestBlocks H) e.msg R) := by
  rcases hsource with h | ⟨hv, x, hx, r, s, C, CV, hres, hRC, hrb, hts, hsL, hd, hl⟩
  · exact Or.inl h
  · exact Or.inr ⟨hv, hp.latest_votes_of_recent_result hc hx hres hRC hrb hts hd hl htb hsL⟩

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- Actual tips below compatible origin witnesses are comparable. The read
producer must supply these witnesses at the actual stored-clock cuts, including
cuts preceding endCut heal; post-base preservation alone cannot do so. -/
theorem tips_comparable_of_origin_witnesses (Q : HealthyPreparationQuery S A V)
    {R R' C C' : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hR : Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R C)
    (hR' : Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R' C')
    (hCC : Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2)) C C') :
    Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R R' := by
  have hU := Compose.honest_blocks_coherent
    (simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid).toLocalRun
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)
  rcases hCC with h | h
  · exact Anc.total hU (hR.trans h) hR'
  · exact Anc.total hU hR (hR'.trans h)

section ConditionalSafety
variable (Q : HealthyPreparationQuery S A V) {c t₀ ΔF a : Time}
  (hsync : Healing.ResetService Q.trace (honestKeys S Q.run.2)
    Q.gst ΔF Q.run.2.horizon)
  (hreset : Healing.IsReset Q.trace (honestKeys S Q.run.2) Q.gst a)
  (ha : a ≤ Q.run.2.horizon)
  (hsnapshot : ∃ k, Healing.FirstCutAfter Q.trace k
    (Healing.cutZ Q.params.toParams Q.gst) ∧ Q.trace.time k ≤ Q.run.2.horizon)
  (hc : 0 ≤ c)
  (hread : ∀ y k t, (∃ q ≤ Q.run.2.events.length, k = cutMap S Q.run.2 Q.hn q) →
    Regimes.ReadPoint Q.trace k t →
    Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) c y t → t₀ ≤ t → t ≤ Q.run.2.horizon →
    Regimes.readAfter Q.trace y k t =
      (SA.lookup (Node.frame (Q.trace.state y k))
        (Q.trace.state y k).ac.latestConfirmed).getD (Q.trace.state y k).fg.F)

include hsync hreset ha hsnapshot hc hread

end ConditionalSafety

/-- Finite schedule to be synthesized from the original healthy progress interval.
The window pays for the opening and its update, with strict pre-read reserve. -/
structure HealthyRepairSchedule (Q : HealthyPreparationQuery S A V) where
  resetTime : Time
  deltaF : Time
  reset : Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
    (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst deltaF resetTime Q.run.2.horizon
  cleanLabel : Nat
  cleanLabel_eq : cleanLabel = Healing.cleanLabel Q.params resetTime
  duration_bound : 18 * Q.params.Δ ≤ (Sys (family S) V).cDur (K S A) Q.run
  oldLabel : Nat
  old_bound : cleanLabel + 2 * Q.params.k + 1 ≤ oldLabel
  query : Time
  lower : max Q.ready (max (Healing.drainTime Q.params resetTime)
    (max (Q.params.ts oldLabel) (max (SA.gbar Q.gst + 4 * Q.params.Δ) 0))) ≤ query
  reserve : query + (4 * (Q.index : Time) + 6) * Q.params.Δ < Q.heal - 1

/-- A supplied finite reset and its strict joint reserve suffice for the canonical
repair schedule. Neither the reset nor the reserve is produced here. -/
theorem healthy_repair_schedule_of_reset
    (Q : HealthyPreparationQuery S A V) {ΔF a : Time}
    (hreset : Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
      (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2)
      Q.gst ΔF a Q.run.2.horizon)
    (hreserve : max Q.ready (Healing.drainTime Q.params a) +
      (4 * (Q.index : Time) + 6) * Q.params.Δ < Q.heal - 1) :
    ∃ D : HealthyRepairSchedule S A V Q,
      D.resetTime = a ∧ D.deltaF = ΔF ∧
      D.query = max Q.ready (Healing.drainTime Q.params a) ∧
      D.oldLabel = Q.params.slot a + 2 * Q.params.k + 4 := by
  have hc : (19 : Time) ≤ (accepted_catchUp S A : Nat) := by
    exact_mod_cast accepted_catchUp_ge_sleepy S A
  have hd : (1 : Time) ≤ Q.run.1.Δ := Q.run.1.Δ_pos
  have hduration : 18 * Q.params.Δ + 1 ≤ (Sys (family S) V).cDur (K S A) Q.run := by
    simp only [System.cDur, Params.standard, accepted_coefficients_catchUp]
    change 18 * Q.run.1.Δ + 1 ≤ (accepted_catchUp S A : Nat) * Q.run.1.Δ
    nlinarith
  have hΔ := Q.params.toParams.hΔ
  have hready : SA.gbar Q.gst + 4 * Q.params.Δ ≤ Q.ready := by
    change max Q.gst 0 + 4 * Q.params.Δ ≤
      max Q.gst 0 + (Sys (family S) V).cDur (K S A) Q.run + 1
    linarith
  have hzero : 0 ≤ Q.ready := by
    change 0 ≤ max Q.gst 0 + (Sys (family S) V).cDur (K S A) Q.run + 1
    linarith [le_max_right Q.gst 0]
  have hold : Q.params.ts (Q.params.slot a + 2 * Q.params.k + 4 : Nat) ≤
      Healing.drainTime Q.params a := by
    rw [Healing.drainTime_eq]
    exact (SA.ts_le_iff Q.params).mpr (by omega)
  refine ⟨{
    resetTime := a
    deltaF := ΔF
    reset := hreset
    cleanLabel := Healing.cleanLabel Q.params a
    cleanLabel_eq := rfl
    duration_bound := by linarith
    oldLabel := Q.params.slot a + 2 * Q.params.k + 4
    old_bound := by rw [Healing.cleanLabel_eq]; omega
    query := max Q.ready (Healing.drainTime Q.params a)
    lower := ?_
    reserve := hreserve }, rfl, rfl, rfl, rfl⟩
  exact max_le (le_max_left _ _) (max_le (le_max_right _ _)
    (max_le (hold.trans (le_max_right _ _))
      (max_le (hready.trans (le_max_left _ _)) (hzero.trans (le_max_left _ _)))))

/-- A preparation schedule for the same query supplies a repair schedule with
the very same reset time, service delay and query, without a base-slot comparison. -/
theorem healthy_repair_schedule_of_preparation
    (Q : HealthyPreparationQuery S A V)
    (W : HealthyBaseTiming S A V Q)
    (Dprep : HealthyPreparationSchedule S A V Q W) :
    ∃ D : HealthyRepairSchedule S A V Q,
      D.resetTime = Dprep.resetTime ∧ D.deltaF = Dprep.deltaF ∧ D.query = Dprep.query := by
  have hlower : max Q.ready (Healing.drainTime Q.params Dprep.resetTime) ≤ Dprep.query :=
    max_le ((le_max_left _ _).trans Dprep.lower)
      ((le_max_left _ _).trans ((le_max_right _ _).trans Dprep.lower))
  obtain ⟨D, hreset, hdelta, hquery, _⟩ := healthy_repair_schedule_of_reset S A V Q
    Dprep.reset (by linarith [Dprep.reserve])
  refine ⟨{ D with query := Dprep.query, lower := ?_, reserve := Dprep.reserve },
    hreset, hdelta, rfl⟩
  exact D.lower.trans (hquery ▸ hlower)

/-- An operational opening; no unguarded support-head premise is included. -/
structure HealthyRepairOpening (Q : HealthyPreparationQuery S A V)
    (D : HealthyRepairSchedule S A V Q) where
  slot : Nat
  cut : Nat
  block : SA.Blk Q.params.n (List (FG.Att Q.params.n))
  fresh : D.query < Q.params.ts slot
  bounded : Q.params.ts slot ≤ D.query + 4 * (Q.index : Time) * Q.params.Δ
  old_lt : D.oldLabel < slot
  label : block.slot = slot
  proposes : Q.trace.ProposesAt (runProposer S Q.run.2 Q.hn slot) cut block
  accepts : Q.trace.AcceptAt (runProposer S Q.run.2 Q.hn slot) cut block
  time : Q.trace.time cut = Q.params.ts slot
  ready : Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
    ((Sys (family S) V).cDur (K S A) Q.run)
    (runProposer S Q.run.2 Q.hn slot) (Q.params.ts slot)

/-- Immediate receiver repair at its actual update. This says nothing about later
canonical reads. A retained optimistic source may have label u+1 and is not mature
at this update; no latest-view inequality follows. A missing lookup needs no cover. -/
def HealthyReceiverRepair (Q : HealthyPreparationQuery S A V)
    (D : HealthyRepairSchedule S A V Q) (O : HealthyRepairOpening S A V Q D) : Prop :=
  ∀ y ∈ honestKeys S Q.run.2,
    Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
      ((Sys (family S) V).cDur (K S A) Q.run) y
      (Q.params.ts O.slot + 6 * Q.params.Δ) → ∃ j ell,
    SA.UpdateAt Q.trace.projAC y j O.slot ell ∧
    Q.trace.time j = Q.params.ts O.slot + 6 * Q.params.Δ ∧
    Q.trace.time j ≤ Q.run.2.horizon ∧
    ∀ R, SA.lookup (Node.frame (Q.trace.state y (j + 1)))
      (Q.trace.state y (j + 1)).ac.latestConfirmed = some R →
      ∃ x ∈ honestKeys S Q.run.2, ∃ q s C CV,
        q ≤ j ∧ Q.trace.time q ≤ Q.trace.time j ∧ D.oldLabel ≤ s ∧
        (SA.ResultAt Q.trace.projAC x q s C CV ∨
          SA.OptimisticLockAt Q.trace.projAC x q s C CV) ∧
        Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R C

/-- The last local representative and finite service at the actual stored clock.
No record geometry is part of this context. -/
structure HealthyReadContext (Q : HealthyPreparationQuery S A V)
    (D : HealthyRepairSchedule S A V Q) (v : V) (i : Nat) where
  cut : Nat
  state_eq : Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i) =
    Q.trace.state (Q.run.2.ownKey v) cut
  label : Nat
  time_nonneg : 0 ≤ (stateAt S Q.run.2 Q.hn v i).now
  time_bound : (stateAt S Q.run.2 Q.hn v i).now ≤ Q.run.2.horizon
  repaired : D.query + (4 * (Q.index : Time) + 6) * Q.params.Δ <
    (stateAt S Q.run.2 Q.hn v i).now
  readPoint : Regimes.ReadPoint Q.trace cut (stateAt S Q.run.2 Q.hn v i).now
  awake : Q.trace.awake (Q.run.2.ownKey v) (stateAt S Q.run.2 Q.hn v i).now
  joined : Q.trace.JoinedAt (Q.run.2.ownKey v) (stateAt S Q.run.2 Q.hn v i).now
  latest : (label : Int) = (SA.latestView Q.params
    (Q.trace.state (Q.run.2.ownKey v) cut).ac
    (Node.frame (Q.trace.state (Q.run.2.ownKey v) cut)) (stateAt S Q.run.2 Q.hn v i).now).2
  reset_le : D.resetTime ≤ Q.params.ts label
  sync : SyncACWindowBefore (honestKeys S Q.run.2)
    (Q.trace.HonestBlocks (honestKeys S Q.run.2)) D.resetTime
    (stateAt S Q.run.2 Q.hn v i).now Q.trace.projAC
  catchup : CatchACWindowBefore Q.trace.projAC (honestKeys S Q.run.2)
    (Q.trace.HonestBlocks (honestKeys S Q.run.2)) D.resetTime (2 * Q.params.Δ)
    (stateAt S Q.run.2 Q.hn v i).now
  fault : (honestKeys S Q.run.2)ᶜ.ncard <
    {x | x ∈ honestKeys S Q.run.2 ∧ Q.trace.awake x (Q.params.ts label + Q.params.Δ) ∧
      Q.trace.JoinedAt x (Q.params.ts label + Q.params.Δ)}.ncard

section EndpointProducers
variable (Q : HealthyPreparationQuery S A V)
  (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
  (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) Q.cap Q.index
    Q.ready Q.heal Q.run)
  (W : HealthyBaseTiming S A V Q)
  (states : ∀ k, Q.cut ≤ k → k ≤ cutMap S Q.run.2 Q.hn Q.run.2.events.length →
    HealthyStateFacts S A V Q W.slot k)

include h0 hb hp W states

omit h0 hb hp W states in
/-- Every completed own call is no later than the reader's stored clock, even
when its simulation cut is not ordered against a chosen read representative. -/
theorem healthy_own_call_time_le_now {v : V} {i q : Nat}
    (hqi : q < cutMap S Q.run.2 Q.hn i) (hq : Q.trace.IsCall (Q.run.2.ownKey v) q) :
    Q.trace.time q ≤ (stateAt S Q.run.2 Q.hn v i).now := by
  obtain ⟨ell, hnode, hlabel⟩ := hq
  obtain ⟨_, p, e, _, he, hpq, _, _, hnode', htime, _⟩ :=
    simTrace_cut S Q.run.2 Q.hn (by rw [hlabel]; simp)
  have hpi : p < i := by
    by_contra h
    have := cutMap_mono S Q.run.2 Q.hn (show i ≤ p by omega)
    omega
  have hev : e.node = v := Q.run.2.key.symm.injective (hnode'.symm.trans hnode)
  rw [htime, ← now_after_local_event S Q.run.2 Q.hn Q.valid he hev]
  exact now_mono S Q.run.2 Q.hn Q.valid v (by omega)

set_option linter.unusedSectionVars false in
/-- The repair schedule of the preparation initializer: the joint (E) tuple of
`healthy_preparation_initialize` keeps its reset time, service delay and query
(`healthy_repair_schedule_of_preparation`). -/
theorem healthy_repair_schedule : Nonempty (HealthyRepairSchedule S A V Q) := by
  obtain ⟨W', ⟨Dprep⟩⟩ := healthy_preparation_initialize S A V Q h0 hb hp
  obtain ⟨D, -⟩ := healthy_repair_schedule_of_preparation S A V Q W' Dprep
  exact ⟨D⟩

omit h0 hp W states in
/-- Any bounded operational opening repairs the post-update source cover. No
current-read geometry or prior repair invariant is used. -/
theorem healthy_receiver_repair_of_opening (D : HealthyRepairSchedule S A V Q)
    (O : HealthyRepairOpening S A V Q D)
    (hc : Healing.CatchRun Q.trace (honestKeys S Q.run.2) Q.gst (2 * Q.params.Δ)) :
    HealthyReceiverRepair S A V Q D O := by
  have hd := Q.params.toParams.hΔ
  have hTb : Q.params.ts O.slot + 6 * Q.params.Δ ≤ Q.run.2.horizon := by
    linarith [O.bounded, D.reserve]
  have hR : Healing.drainTime Q.params D.resetTime ≤ Q.params.ts O.slot := by
    have := (le_max_left _ _).trans ((le_max_right _ _).trans D.lower)
    exact this.trans O.fresh.le
  have hgu : SA.gbar Q.gst + 4 * Q.params.Δ ≤ Q.params.ts O.slot := by
    have := (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans D.lower)))
    exact this.trans O.fresh.le
  have hjoin : Q.params.ts (Q.params.slot (SA.gbar Q.gst) + 1 : Nat) ≤ Q.params.ts O.slot := by
    have hbase := (SA.ts_le_iff_le_slot Q.params (SA.gbar_nonneg Q.gst)
      (Q.params.slot (SA.gbar Q.gst))).mpr le_rfl
    simp only [SA.SAParams.ts] at hbase hgu ⊢
    push_cast at hbase hgu ⊢
    linarith
  intro y hy _
  obtain ⟨j, ell, _, hu, _⟩ := D.reset.update_toFG_calls hy hjoin hTb
  have ht : Q.trace.time j = Q.params.ts O.slot + 6 * Q.params.Δ := hu.2.2.1
  refine ⟨j, ell, hu, ht, ht ▸ hTb, ?_⟩
  intro R hlookup
  obtain ⟨x, hx, q, s, CV, hqj, hqt, hs, hsource⟩ :=
    UpTo.operational_update_recent_source D.reset hc O.ready.1 rfl O.proposes O.label
      hR hgu hTb hy hu hlookup
  exact ⟨x, hx, q, s, R, CV, hqj, hqt, O.old_lt.le.trans hs, hsource, .refl⟩

set_option linter.unusedSectionVars false in
/-- Repair cover retains the actual source-time bound at the stored clock. -/
theorem healthy_current_record_sources_before_now (D : HealthyRepairSchedule S A V Q)
    (O : HealthyRepairOpening S A V Q D) (hrepair : HealthyReceiverRepair S A V Q D O)
    {v : V} {i : Nat} (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hv : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i)) :
    let R := ((SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)))
        (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).ac.latestConfirmed).getD
          (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).fg.F)
    R = (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).fg.F ∨
      ∃ x ∈ honestKeys S Q.run.2, ∃ q s B CV,
        q < cutMap S Q.run.2 Q.hn i ∧
        Q.trace.time q ≤ (stateAt S Q.run.2 Q.hn v i).now ∧
        D.cleanLabel + 2 * Q.params.k + 1 ≤ s ∧
        (SA.ResultAt Q.trace.projAC x q s B CV ∨ SA.OptimisticLockAt Q.trace.projAC x q s B CV) ∧
        Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R B := by
  let y := Q.run.2.ownKey v
  let n := cutMap S Q.run.2 Q.hn i
  let T := Q.params.ts O.slot + 6 * Q.params.Δ
  have hy := honest_ownKey (S := S) hv.1
  have hd := Q.params.toParams.hΔ
  have hready : Q.ready < T := by
    have : Q.ready ≤ D.query := (le_max_left _ _).trans D.lower
    dsimp [T]
    linarith [O.fresh]
  have hTcut : T < Q.run.2.cutTime i := by
    have hh : Q.heal ≤ Q.run.2.cutTime i := hi.2
    dsimp [T]
    linarith [O.bounded, D.reserve]
  have hTb : T ≤ Q.run.2.horizon := by
    dsimp [T]
    linarith [O.bounded, D.reserve]
  have hT0 : 0 ≤ T := by
    have : 0 ≤ Q.ready := by
      change 0 ≤ max Q.gst 0 + (Sys (family S) V).cDur (K S A) Q.run + 1
      have := D.duration_bound
      have := le_max_right Q.gst 0
      linarith
    exact this.trans hready.le
  have hr : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v T := by
    refine ⟨hv.1, fun t ht htt => Q.healthy.2.1.2 v hv.1 t ?_ (htt.trans hTb)⟩
    change max Q.gst 0 + (Sys (family S) V).cDur (K S A) Q.run + 1 < T at hready
    have := (le_max_right _ _).trans ht
    linarith
  obtain ⟨a, ell, ha, hat, hab, hcover⟩ := hrepair y hy
    (ready_transport S Q.run.2 Q.hn Q.valid hT0 hTb hr)
  have han : a < n := by
    obtain ⟨_, p, e, _, he, _, hap, _, _, htime, _⟩ :=
      simTrace_cut S Q.run.2 Q.hn
        (by have hh := (Compose.projAC_callAt.mp ha.1).2; rw [hh]; simp)
    have hpi : p < i := by
      by_contra h
      have hip : i ≤ p := by omega
      have ht : Q.run.2.cutTime i ≤ Q.trace.time a := by
        rw [htime]
        cases i with
        | zero => exact (Q.valid.in_horizon e (List.mem_of_getElem? he)).1
        | succ i =>
          have hplen := (List.getElem?_eq_some_iff.mp he).1
          have hil : i < Q.run.2.events.length := by omega
          have hei : Q.run.2.events[i]? = some Q.run.2.events[i] := List.getElem?_eq_getElem hil
          simp only [Model.Run.cutTime, hei]
          rcases keyLe_of_index_lt S Q.run.2 Q.valid hei he (by omega) with ht | ht
          · exact ht.le
          · exact ht.1.le
      change Q.trace.time a = T at hat
      linarith
    exact lt_of_lt_of_le hap (cutMap_mono S Q.run.2 Q.hn (by omega))
  have hU := Compose.honest_blocks_coherent D.reset.run.toLocalRun D.reset.noColl
  have hatnow := healthy_own_call_time_le_now S A V Q han ⟨_, Compose.projAC_callAt.mp ha.1⟩
  have hind : ∀ k, a + 1 ≤ k → k ≤ n → ∀ R,
      SA.lookup (Node.frame (Q.trace.state y k)) (Q.trace.state y k).ac.latestConfirmed = some R →
      ∃ x ∈ honestKeys S Q.run.2, ∃ q s C CV,
        q < k ∧ Q.trace.time q ≤ (stateAt S Q.run.2 Q.hn v i).now ∧ D.oldLabel ≤ s ∧
        (SA.ResultAt Q.trace.projAC x q s C CV ∨ SA.OptimisticLockAt Q.trace.projAC x q s C CV) ∧
        Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R C := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro _ R hR
      obtain ⟨x, hx, q, s, C, CV, hqa, hqt, hs, hC, hRC⟩ := hcover R hR
      exact ⟨x, hx, q, s, C, CV, by omega, hqt.trans hatnow, hs, hC, hRC⟩
    | succ k hak ih =>
      intro hkn R hR
      rcases Compose.record_step_origin D.reset.run hy k with heq | ⟨C, hC, hCr, s, CV, hs⟩
      · obtain ⟨x, hx, q, s, B, DV, hqk, hqb, hsl, hB, hRB⟩ :=
          ih (by omega) R (record_lookup_of_later D.reset.run D.reset.noColl hy
            (Nat.le_succ k) heq hR)
        exact ⟨x, hx, q, s, B, DV, by omega, hqb, hsl, hB, hRB⟩
      · obtain ⟨hRm, hRr⟩ := SA.lookup_eq_some hR
        have hRC : R = C := hU.1 ⟨y, hy, k + 1, hRm.1⟩ ⟨y, hy, k, hC⟩
          (hRr.trans hCr.symm)
        have htk : T ≤ Q.trace.time k := by
          dsimp [T]
          rw [← hat]
          exact D.reset.run.time_mono (by omega)
        have hsl : D.oldLabel ≤ s := by
          have hus : O.slot ≤ s := by
            rcases hs with ⟨ell, hu, _⟩ | ⟨ell, A, ho, hslot, _⟩
            · have ht : Q.trace.time k = Q.params.ts s + 6 * Q.params.Δ := hu.2.2.1
              dsimp [T] at htk
              have hh := (SA.ts_le_iff Q.params).mp
                (show Q.params.ts O.slot ≤ Q.params.ts s by linarith)
              omega
            · have hh := (SA.ts_le_iff_le_slot Q.params (D.reset.run.time_nonneg k) O.slot).mp
                (show Q.params.ts O.slot ≤ Q.trace.time k by dsimp [T] at htk; linarith)
              change Q.params.slot (Q.trace.time k) = s at hslot
              omega
          exact O.old_lt.le.trans hus
        have hkb : Q.trace.time k ≤ (stateAt S Q.run.2 Q.hn v i).now := by
          apply healthy_own_call_time_le_now S A V Q (show k < cutMap S Q.run.2 Q.hn i by omega)
          rcases hs with ⟨ell, hu, _⟩ | ⟨ell, A, ho, _⟩
          · exact ⟨_, Compose.projAC_callAt.mp hu.1⟩
          · exact ⟨_, Compose.projAC_callAt.mp ho.1⟩
        exact ⟨y, hy, k, s, C, CV, Nat.lt_succ_self _, hkb, hsl, hs, by rw [hRC]; exact .refl⟩
  cases hl : SA.lookup (Node.frame (Q.trace.state y n)) (Q.trace.state y n).ac.latestConfirmed with
  | none => exact Or.inl (by simp only [Option.getD_none])
  | some R =>
    obtain ⟨x, hx, q, s, C, CV, hqn, hqb, hs, hC, hRC⟩ := hind n (by omega) le_rfl R hl
    exact Or.inr ⟨x, hx, q, s, C, CV, hqn, hqb, D.old_bound.trans hs, hC,
      by simpa only [hl, Option.getD_some] using hRC⟩

end EndpointProducers

end Consensus.Goldilocks.Refinement
end
