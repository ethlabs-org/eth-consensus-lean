module
public import ConsensusLean.Lemmas.Problem.DerivedFacts
public import ConsensusLean.Spec.Problem.CorrectProtocol
public import ConsensusLean.Lemmas.Problem.Facts.Atoms
public import ConsensusLean.Lemmas.Problem.Facts.Network
public import ConsensusLean.Lemmas.Problem.Facts.Properties
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Consequences of a correct protocol (L0 facts)

Corollaries of `CorrectProtocol`: final agreement and healthy final safety, compatibility
through an outage, safety and resilience of the past (`*_prefix`), and active
service of a provided final or available output (`CorrectProtocol.served`). -/

namespace Consensus

namespace System

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Accountable safety, non-framing and faults below the accountable fraction give
agreement of `g`. -/
theorem agree_of_accountable (S : System V) (hL : S.Laws) (r : S.Run) (hvalid : S.Valid r)
    {g : S.schema.Id}
    {t₀ : Time} {α : ℚ} (hacc : S.AccountablySafe r α g t₀) (hnf : S.NonFraming r)
    (hb : (S.trace r).point.FaultsBelow α) : (S.trace r).Agree g t₀ := by
  classical
  intro u v i j hi hj hu hv
  rcases hacc u v i j hi hj hu hv with hc | hcard
  · exact hc
  · exfalso
    have hsub : Consensus.convicted (S.convicts r) (S.view r u i ∪ S.view r v j) ⊆
        (S.trace r).point.faultyAt (S.trace r).point.horizon := by
      intro x hx
      have hx' : S.convicts r (S.view r u i ∪ S.view r v j) x := by
        unfold Consensus.convicted at hx; simpa using hx
      by_contra hxh
      have hdh : max ((S.trace r).cutTime i) ((S.trace r).cutTime j) ≤
          (S.trace r).point.horizon :=
        max_le ((hL.trace r hvalid).cutTime_le_horizon i hi.1)
          ((hL.trace r hvalid).cutTime_le_horizon j hj.1)
      apply hnf x (max ((S.trace r).cutTime i) ((S.trace r).cutTime j))
        (fun hf => hxh ((S.trace r).point.faultyAt_mono hdh hf))
      refine hL.convicts_mono r _ _ x ?_ hx'
      rintro o (ho | ho)
      · exact ⟨u, i, hi.1, le_max_left _ _, hu, ho⟩
      · exact ⟨v, j, hj.1, le_max_right _ _, hv, ho⟩
    change (Fintype.card V : ℚ) * α ≤
      (Consensus.convicted (S.convicts r) (S.view r u i ∪ S.view r v j)).card at hcard
    have hc : ((Consensus.convicted (S.convicts r) (S.view r u i ∪ S.view r v j)).card : ℚ) ≤
        ((S.trace r).point.faultyAt (S.trace r).point.horizon).card := by
      exact_mod_cast Finset.card_le_card hsub
    rw [EnvPoint.faultsBelow_iff] at hb
    unfold EnvPoint.faultCount at hb
    linarith

end System

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type}

/-- A live claim met on an active witness serves a transaction: one submitted
to an honest node is in the `g`-read of another honest node, which was never
submitted it. -/
theorem Trace.TxLive.served {V Id : Type} {tr : Trace V Tx Id} {c : Time}
    {g : Id} {start D : Time} (hl : tr.TxLive c g start D) (ha : tr.point.TxLiveActive c start D) :
    ∃ x u w t t', tr.point.HonestAt u t ∧ tr.point.HonestAt w t' ∧ w ≠ u ∧
      x ∈ tr.point.submit u t ∧ (∀ τ, x ∉ tr.point.submit w τ) ∧ t' ≤ tr.point.horizon ∧
      x ∈ tr.readAt g w t' := by
  obtain ⟨x, t, t', u, w, ht0, hu, hua, hx, hne, hnw, hdl, hth, hr⟩ := ha
  exact ⟨x, u, w, t, t', hu, hr.1, hne, hx, hnw, hth,
    hl x t t' ⟨u, t, ht0, le_rfl, hu, hua, hx⟩ hdl hth w hr⟩

namespace CorrectProtocol

variable {S : System V} {X : Progress S Prog} {K : Contract Prog}

/-- Final agreement in every environment with faults below `α`. -/
theorem final_agree (h : CorrectProtocol S X K) {g : S.schema.Id}
    (hg : S.schema.output .final = some g)
    (r : S.Run) (hv : S.Valid r) (hb : (S.pt r).FaultsBelow K.params.α) :
    (S.trace r).Agree g 0 ∨ S.Excuse r :=
  (h.behaviour.finalAccountable g hg r hv trivial).imp
    (fun ha => S.agree_of_accountable h.behaviour.laws r hv ha
      (h.behaviour.nonFraming r hv) hb) id

/-- Final safety in the healthy regime: the faults are below `β ≤ α`. -/
theorem final_safe_healthy (h : CorrectProtocol S X K) {g : S.schema.Id}
    (hg : S.schema.output .final = some g) (r : S.Run) (hv : S.Valid r) {gst : Time}
    (hH : S.Healthy K gst r) : (S.trace r).Safe g 0 ∨ S.Excuse r := by
  have hb : (S.pt r).FaultsBelow K.params.α :=
    hH.2.1.faultsBelow.mono _ h.behaviour.admissible.α_range.1
  exact (h.final_agree hg r hv hb).imp
    (fun ha => Trace.safe_iff.mpr ⟨ha, h.behaviour.finalMonotone g hg r hv⟩) id

/-- Through an outage, what a node ready at `T` read as stable is compatible
with the final read of every reader ready from the recovery point on (both
are prefixes of its available read). -/
theorem persists_final_compatible (h : CorrectProtocol S X K) {g gf : S.schema.Id}
    (hs : S.schema.output .stable = some g) (hf : S.schema.output .final = some gf)
    (r : S.Run) (hv : S.Valid r) {T b₀ b₁ : Time} (hO : S.Outage X.toExternal K T b₀ b₁ r)
    {v w : V} (hvr : (S.pt r).Ready (S.cDur K r) v T) {t : Time}
    (ht : S.recoveryAt K b₁ r ≤ t) (hth : t ≤ (S.pt r).horizon)
    (hr : (S.pt r).Ready (S.cDur K r) w t) :
    Compatible ((S.trace r).readAt g v T) ((S.trace r).readAt gf w t) ∨ S.Excuse r := by
  have ht0 : 0 ≤ t := by
    obtain ⟨hT, hl, h01, -⟩ := hO.times
    have hlag : (0 : Time) ≤ (K.params.lag : Time) * (S.pt r).env.ΔAC :=
      mul_nonneg (Nat.cast_nonneg _) (S.pt r).env.ΔAC_pos.le
    have hrec : (0 : Time) ≤ (K.params.recovery : Time) * (S.pt r).env.ΔAC :=
      mul_nonneg (Nat.cast_nonneg _) (S.pt r).env.ΔAC_pos.le
    unfold System.recoveryAt at ht
    linarith
  have htime : (S.trace r).cutTime ((S.trace r).endCut t) ≤ t :=
    Nat.findGreatest_spec (P := fun i => (S.trace r).cutTime i ≤ t)
      (Nat.zero_le (S.trace r).cuts) (show (S.trace r).cutTime 0 ≤ t by
      rw [(h.behaviour.laws.trace r hv).cutTime_zero]; exact ht0)
  have hwh : (S.pt r).HonestAt w ((S.trace r).cutTime ((S.trace r).endCut t)) :=
    fun hf => hr.1 ((S.pt r).faultyAt_mono htime hf)
  rcases h.behaviour.persists g hs T b₀ b₁ r hv hO with hp | he
  · left
    have h1 := hp v hvr t ht hth w hr
    have hcut : (S.trace r).endCut t ≤ (S.trace r).cuts := Nat.findGreatest_le _
    have h2 : (S.trace r).readAt gf w t <+:
        (S.trace r).readAt (resilienceTarget S.schema g) w t := by
      unfold resilienceTarget
      cases ha : S.schema.output .available with
      | some ga =>
        exact h.behaviour.nested .final .available gf ga (by decide) hf ha r hv w _ hcut hwh
      | none =>
        exact h.behaviour.nested .final .stable gf g (by decide) hf hs r hv w _ hcut hwh
    exact List.prefix_or_prefix_of_prefix h1 h2
  · exact Or.inr he

/-- A half-open deadline `max a g + d − 1` is at or after the start, for a positive delay. -/
private theorem le_max_add_sub_one {a g d : Time} (hd : 0 < d) : a ≤ max a g + d - 1 := by
  have : (1 : Time) ≤ d := hd
  linarith [le_max_left a g]

/-- A half-open deadline `a + d − 1` is at or after the start, for a positive delay. -/
private theorem le_add_sub_one {a d : Time} (hd : 0 < d) : a ≤ a + d - 1 := by
  have : (1 : Time) ≤ d := hd
  linarith

omit [Fintype V] [DecidableEq V] in
/-- Run quantities that depend only on `Δ` agree on a prefix. -/
private theorem cDur_prefix {r r' : S.Run} {b : Time} (hP : (S.trace r').PrefixOf (S.trace r) b) :
    S.cDur K r' = S.cDur K r := by
  unfold System.cDur; rw [hP.env]

/-- Sleepy safety of the past: a run synchronous and sleepy up to `b` is safe
for ready readers at cuts up to `b`, whatever happens after `b`. -/
theorem sleepySafe_prefix (h : CorrectProtocol S X K) {cap : Capability} {g : S.schema.Id}
    (hcap : cap = .available ∨ cap = .stable) (hg : S.schema.output cap = some g)
    (r : S.Run) (hv : S.Valid r) {b : Time} (hb0 : 0 ≤ b) (hbh : b ≤ (S.pt r).horizon)
    (hs : (S.log r).SyncUntil (S.pt r) b)
    (hθ : (S.pt r).SleepyOn K.params.θ (S.cDur K r) (S.aheadDur K r) 0 b) :
    (S.trace r).ReadySafeUpTo (S.cDur K r) g 0 b ∨ S.Excuse r := by
  obtain ⟨r', hv', hP, -, hL, hE, -⟩ := h.adequate.prefixClosed r hv b hb0 hbh
  have hc := cDur_prefix (K := K) hP
  have ha : S.aheadDur K r' = S.aheadDur K r := by
    unfold System.aheadDur; rw [hP.env]
  have hreg : S.Sleepy K r' := by
    unfold System.Sleepy
    rw [hc, ha, show S.pt r' = { S.pt r with horizon := b } from hP.point]
    refine ⟨?_, hθ.prefix hbh (by linarith [h.behaviour.admissible.θ_range.2])
      h.behaviour.admissible.θ_range.1⟩
    have hd : (S.log r).Delivers (S.pt r) (fun a => max a 0 + (S.pt r).env.ΔAC - 1)
        (fun a => max a 0 + (S.pt r).env.ΔFG - 1) b :=
      hs.reindex (f := fun a => max a 0) (fun a => le_max_left a 0) (fun _ => rfl) (fun _ => rfl)
        le_rfl
    exact hd.prefix hL hbh
      (fun _ => le_max_add_sub_one (S.pt r).env.ΔAC_pos)
      (fun _ => le_max_add_sub_one (S.pt r).env.ΔFG_pos)
  rcases h.behaviour.sleepySafe cap g hcap hg r' hv' hreg with hr | he
  · rw [hc] at hr; exact Or.inl (hP.readySafeUpTo hr)
  · exact Or.inr (hE he)

/-- Sleepy liveness for deadlines in a prefix, independently of later compromises. -/
theorem sleepyLive_prefix (h : CorrectProtocol S X K) {cap : Capability} {g : S.schema.Id}
    (hcap : cap = .available ∨ cap = .stable) (hg : S.schema.output cap = some g)
    (r : S.Run) (hv : S.Valid r) (i : K.Idx) {b : Time} (hb0 : 0 ≤ b)
    (hbh : b ≤ (S.pt r).horizon) (hs : (S.log r).SyncUntil (S.pt r) b)
    (hθ : (S.pt r).SleepyOn K.params.θ (S.cDur K r) (S.aheadDur K r) 0 b)
    (hp : S.prog X K cap i 0 b r) :
    (∀ x t t', (S.pt r).SubmittedToSome x t →
      max t 0 + (S.pt r).env.ΔAC + S.lat K cap i r ≤ t' →
      t' ≤ b → ∀ v, (S.pt r).Ready (S.cDur K r) v t' →
        x ∈ (S.trace r).readAt g v t') ∨ S.Excuse r := by
  obtain ⟨r', hv', hP, _, hL, hE, hX, -⟩ := h.adequate.prefixClosed r hv b hb0 hbh
  have hc := cDur_prefix (K := K) hP
  have ha : S.aheadDur K r' = S.aheadDur K r := by
    unfold System.aheadDur; rw [hP.env]
  have hlat : S.lat K cap i r' = S.lat K cap i r := by
    unfold System.lat; rw [hP.env]
  have hreg : S.Sleepy K r' := by
    unfold System.Sleepy
    rw [hc, ha, show S.pt r' = { S.pt r with horizon := b } from hP.point]
    refine ⟨?_, hθ.prefix hbh (by linarith [h.behaviour.admissible.θ_range.2])
      h.behaviour.admissible.θ_range.1⟩
    have hd := hs.reindex (f := fun a => max a 0) (fun a => le_max_left a 0)
      (fun _ => rfl) (fun _ => rfl) le_rfl
    exact hd.prefix hL hbh
      (fun _ => le_max_add_sub_one (S.pt r).env.ΔAC_pos)
      (fun _ => le_max_add_sub_one (S.pt r).env.ΔFG_pos)
  have hpr : S.prog X K cap i 0 (S.pt r').horizon r' := by
    rw [show (S.pt r').horizon = b from congrArg EnvPoint.horizon hP.point]
    unfold System.prog at hp ⊢
    rw [hc]
    exact hX _ _ _ _ le_rfl hp
  rcases h.behaviour.sleepyLive cap g hcap hg i r' hv' ⟨hreg, hpr⟩ with hl | he
  · rw [hc, hlat] at hl
    exact Or.inl (hP.txLive hl)
  · exact Or.inr (hE he)

/-- Healed safety of the past: a run partially synchronous with GST `gst` and
healthy up to `b` (FG delay within its bound), with progress on `[ready, heal]` and
`heal ≤ b`, is
safe for ready readers at cuts in `[heal, b]`, whatever happens after `b`. -/
theorem healedSafe_prefix (h : CorrectProtocol S X K) {cap : Capability} {g : S.schema.Id}
    (hcap : cap = .available ∨ cap = .stable) (hg : S.schema.output cap = some g)
    (r : S.Run) (hv : S.Valid r) (i : K.Idx) (gst : Time) {b : Time} (hb0 : 0 ≤ b)
    (hbh : b ≤ (S.pt r).horizon)
    (hs : (S.log r).Delivers (S.pt r) (fun a => max a gst + (S.pt r).env.ΔAC - 1)
      (fun a => max a gst + (S.pt r).env.ΔFG - 1) b)
    (hH : (S.pt r).HealthyOn K.params.β gst b)
    (hrat : (S.pt r).env.ΔFG ≤ (K.params.fgDelay : Time) * (S.pt r).env.ΔAC)
    (hp : S.prog X K cap i (S.ready K gst r) (S.heal K cap i gst r) r)
    (hhb : S.heal K cap i gst r ≤ b) :
    (S.trace r).ReadySafeUpTo (S.cDur K r) g (S.heal K cap i gst r) b ∨ S.Excuse r := by
  obtain ⟨r', hv', hP, -, hL, hE, hX, -⟩ := h.adequate.prefixClosed r hv b hb0 hbh
  have hc := cDur_prefix (K := K) hP
  have hheal : S.heal K cap i gst r' = S.heal K cap i gst r := by
    unfold System.heal; rw [hP.env]
  have hready : S.ready K gst r' = S.ready K gst r := by
    unfold System.ready; rw [hc]
  have hreg : S.Healthy K gst r' := by
    unfold System.Healthy
    rw [show S.pt r' = { S.pt r with horizon := b } from hP.point]
    refine ⟨?_, hH, hrat⟩
    exact hs.prefix hL hbh
      (fun _ => le_max_add_sub_one (S.pt r).env.ΔAC_pos)
      (fun _ => le_max_add_sub_one (S.pt r).env.ΔFG_pos)
  have hpr : S.prog X K cap i (S.ready K gst r') (S.heal K cap i gst r') r' := by
    rw [hready, hheal]
    unfold System.prog at hp ⊢
    rw [hc]
    exact hX _ _ _ _ hhb hp
  rcases h.behaviour.healedSafe cap g hcap hg i gst r' hv' ⟨hreg, hpr⟩ with hr | he
  · rw [hc, hheal] at hr; exact Or.inl (hP.readySafeUpTo hr)
  · exact Or.inr (hE he)

/-- Healthy liveness for deadlines in a prefix, with progress only up to its horizon. -/
theorem healthyLive_prefix (h : CorrectProtocol S X K) {cap : Capability} {g : S.schema.Id}
    (hg : S.schema.output cap = some g) (r : S.Run) (hv : S.Valid r) (i : K.Idx)
    (gst : Time) {b : Time} (hb0 : 0 ≤ b) (hbh : b ≤ (S.pt r).horizon)
    (hs : (S.log r).Delivers (S.pt r) (fun a => max a gst + (S.pt r).env.ΔAC - 1)
      (fun a => max a gst + (S.pt r).env.ΔFG - 1) b)
    (hH : (S.pt r).HealthyOn K.params.β gst b)
    (hrat : (S.pt r).env.ΔFG ≤ (K.params.fgDelay : Time) * (S.pt r).env.ΔAC)
    (hp : S.prog X K cap i (S.ready K gst r) b r) :
    (∀ x t t', (S.pt r).SubmittedToSome x t →
      max t (S.heal K cap i gst r) + (S.pt r).env.ΔAC + S.lat K cap i r ≤ t' →
      t' ≤ b → ∀ v, (S.pt r).Ready (S.cDur K r) v t' →
        x ∈ (S.trace r).readAt g v t') ∨ S.Excuse r := by
  obtain ⟨r', hv', hP, _, hL, hE, hX, -⟩ := h.adequate.prefixClosed r hv b hb0 hbh
  have hc := cDur_prefix (K := K) hP
  have hheal : S.heal K cap i gst r' = S.heal K cap i gst r := by
    unfold System.heal; rw [hP.env]
  have hready : S.ready K gst r' = S.ready K gst r := by
    unfold System.ready; rw [hc]
  have hlat : S.lat K cap i r' = S.lat K cap i r := by
    unfold System.lat; rw [hP.env]
  have hreg : S.Healthy K gst r' := by
    unfold System.Healthy
    rw [show S.pt r' = { S.pt r with horizon := b } from hP.point]
    exact ⟨hs.prefix hL hbh
      (fun _ => le_max_add_sub_one (S.pt r).env.ΔAC_pos)
      (fun _ => le_max_add_sub_one (S.pt r).env.ΔFG_pos), hH, hrat⟩
  have hpr : S.prog X K cap i (S.ready K gst r') (S.pt r').horizon r' := by
    rw [hready, show (S.pt r').horizon = b from congrArg EnvPoint.horizon hP.point]
    unfold System.prog at hp ⊢
    rw [hc]
    exact hX _ _ _ _ le_rfl hp
  rcases h.behaviour.healthyLive cap g hg i gst r' hv' ⟨hreg, hpr⟩ with hl | he
  · rw [hc, hheal, hlat] at hl
    exact Or.inl (hP.txLive hl)
  · exact Or.inr (hE he)

/-- Outage resilience of the past: a run in the outage regime up to `b`
(synchronous for deadlines up to `b₀`, partially synchronous with GST `b₁` up
to `b`, η-sleepy on `[0, b]`, with the no-sleep window and cohort count of
`System.Outage` cut at `b`; the selected committees satisfy the retained cohort inequality,
cut at `b`, at the times of the fixed band `[bandStart, bandEnd]` up to `b`, and are η-sleepy on
`[0, b]` with the committee look-ahead `committeeAheadDur`) keeps what nodes ready at `T` read
as stable, for ready readers at reading times in `[b₁ + recovery·Δ, b]`, whatever happens after
`b`. -/
theorem outage_prefix (h : CorrectProtocol S X K) {g : S.schema.Id}
    (hg : S.schema.output .stable = some g) (r : S.Run) (hv : S.Valid r)
    {T b₀ b₁ b : Time} (hb0 : 0 ≤ b) (hbh : b ≤ (S.pt r).horizon)
    (hT : OutageTimes K.params (S.pt r).env.ΔAC T b₀ b₁)
    (hs : (S.log r).SyncUntil (S.pt r) b₀)
    (hps : (S.log r).Delivers (S.pt r) (fun a => max a b₁ + (S.pt r).env.ΔAC - 1)
      (fun a => max a b₁ + (S.pt r).env.ΔFG - 1) b)
    (hθ : (S.pt r).EtaSleepyOn K.params.θ ((K.params.η : Time) * (S.pt r).env.ΔAC)
      (S.cDur K r) (S.aheadDur K r) 0 b)
    (hns : ((S.pt r).retain
      (min (min (b₁ + (K.params.noSleep : Time) * (S.pt r).env.ΔAC) b +
        (K.params.cohortAhead : Time) * (S.pt r).env.ΔAC) b)).NoSleepOn
      (min (max 0 (b₀ - (K.params.noSleep : Time) * (S.pt r).env.ΔAC)) b)
      (min (b₁ + (K.params.noSleep : Time) * (S.pt r).env.ΔAC) b))
    (hco : ((S.pt r).retain
      (min (min (b₁ + (K.params.noSleep : Time) * (S.pt r).env.ΔAC) b +
        (K.params.cohortAhead : Time) * (S.pt r).env.ΔAC) b)).CohortOn
      (min (max 0 (b₀ - (K.params.noSleep : Time) * (S.pt r).env.ΔAC)) b)
      (min (b₁ + (K.params.noSleep : Time) * (S.pt r).env.ΔAC) b))
    (hcommitteeCohort : (({ S.pt r with horizon := b } : EnvPoint V).retain
      (min (min (b₁ + (K.params.noSleep : Time) * (S.pt r).env.ΔAC) b +
        (K.params.cohortAhead : Time) * (S.pt r).env.ΔAC) b)).CommitteeCohortOn
      (X.selected (S.pt r).env (X.ext r))
      (min (max 0 (b₀ - (K.params.noSleep : Time) * (S.pt r).env.ΔAC)) b)
      (min (b₁ + (K.params.noSleep : Time) * (S.pt r).env.ΔAC) b)
      (S.bandStart K b₀ r) (S.bandEnd K b₀ r))
    (hcommitteeSleepy : ({ S.pt r with horizon := b } : EnvPoint V).CommitteeSleepyOn
      (X.selected (S.pt r).env (X.ext r)) K.params.θ
      ((K.params.η : Time) * (S.pt r).env.ΔAC) (S.cDur K r)
      (S.committeeAheadDur K r) 0 b) :
    (S.trace r).ProtectedReadyUpTo (S.cDur K r) g (resilienceTarget S.schema g) T
      (S.recoveryAt K b₁ r) b ∨ S.Excuse r := by
  obtain ⟨r', hv', hP, -, hL, hE, -, hselected⟩ :=
    h.adequate.prefixClosed r hv b hb0 hbh
  have hc := cDur_prefix (K := K) hP
  have hΔ := (S.pt r).env.ΔAC_pos
  have hpt : S.pt r' = { S.pt r with horizon := b } := hP.point
  have hst : S.outageStart K b₀ r' =
      min (max 0 (b₀ - (K.params.noSleep : Time) * (S.pt r).env.ΔAC)) b := by
    unfold System.outageStart; rw [hP.env, hpt]
  have hen : S.outageEnd K b₁ r' = min (b₁ + (K.params.noSleep : Time) * (S.pt r).env.ΔAC) b := by
    unfold System.outageEnd; rw [hP.env, hpt]
  have ha : S.aheadDur K r' = S.aheadDur K r := by
    unfold System.aheadDur; rw [hP.env]
  have hcohort : S.cohortAt K b₁ r' =
      min (min (b₁ + (K.params.noSleep : Time) * (S.pt r).env.ΔAC) b +
        (K.params.cohortAhead : Time) * (S.pt r).env.ΔAC) b := by
    unfold System.cohortAt; rw [hen, hP.env, hpt]
  have hrec : S.recoveryAt K b₁ r' = S.recoveryAt K b₁ r := by
    unfold System.recoveryAt; rw [hP.env]
  have hbandStart : S.bandStart K b₀ r' = S.bandStart K b₀ r := by
    unfold System.bandStart; rw [hP.env]
  have hbandEnd : S.bandEnd K b₀ r' = S.bandEnd K b₀ r := by
    unfold System.bandEnd; rw [hbandStart, hP.env]
  have hcommitteeAhead : S.committeeAheadDur K r' = S.committeeAheadDur K r := by
    unfold System.committeeAheadDur; rw [hP.env]
  have hselection : X.selected (S.pt r').env (X.ext r') =
      X.selected (S.pt r).env (X.ext r) := funext hselected
  have hreg : S.Outage X.toExternal K T b₀ b₁ r' := by
    unfold System.Outage
    rw [hselection, hc, ha, hcohort, hst, hen, hbandStart, hbandEnd, hcommitteeAhead, hpt]
    refine ⟨hT, ⟨?_, ?_⟩, hθ.prefix hbh
      (by linarith [h.behaviour.admissible.θ_range.2]) h.behaviour.admissible.θ_range.1,
      hns, hco, hcommitteeCohort, hcommitteeSleepy⟩
    · exact hs.prefix hL hbh (fun _ => le_add_sub_one hΔ)
        (fun _ => le_add_sub_one (S.pt r).env.ΔFG_pos)
    · exact hps.prefix hL hbh (fun _ => le_max_add_sub_one hΔ)
        (fun _ => le_max_add_sub_one (S.pt r).env.ΔFG_pos)
  have hTb : T ≤ S.recoveryAt K b₁ r := by
    obtain ⟨-, hl, h01, -⟩ := hT
    have : (0 : Time) ≤ (K.params.lag : Time) * (S.pt r).env.ΔAC := by positivity
    have : (0 : Time) ≤ (K.params.recovery : Time) * (S.pt r).env.ΔAC := by positivity
    unfold System.recoveryAt
    linarith
  rcases h.behaviour.persists g hg T b₀ b₁ r' hv' hreg with hr | he
  · rw [hc, hrec] at hr; exact Or.inl (hP.protectedReadyUpTo hTb hr)
  · exact Or.inr (hE he)

/-- Active service of a provided final or available output `g` (capability
`cap`): with at least five validators, at every index, `Δ > 1` and GST `gst ≥ 0`,
some clean witness in the healthy regime from `gst`, with the progress of `cap`
at the index, has a transaction submitted to one honest node in the `g`-read of
another honest node that was never submitted it. From the healthy witness of
`Realizable` and `Behaviour.healthyLive`; the witness has no excuse. -/
theorem served (h : CorrectProtocol S X K) (hn : 5 ≤ Fintype.card V) {cap : Capability}
    {g : S.schema.Id} (_hcap : cap = .final ∨ cap = .available)
    (hg : S.schema.output cap = some g) (i : K.Idx) (Δ gst : Time) (hΔ : 1 < Δ)
    (hgst : 0 ≤ gst) :
    ∃ r, S.Witness r ∧ (S.pt r).env.ΔAC = Δ ∧ S.Healthy K gst r ∧
      S.prog X K cap i (S.ready K gst r) (S.pt r).horizon r ∧
      ∃ x u w t t', (S.pt r).HonestAt u t ∧ (S.pt r).HonestAt w t' ∧ w ≠ u ∧
        x ∈ (S.pt r).submit u t ∧ (∀ τ, x ∉ (S.pt r).submit w τ) ∧
        t' ≤ (S.pt r).horizon ∧ x ∈ (S.trace r).readAt g w t' := by
  have hrat : Δ ≤ (K.params.fgDelay : Time) * Δ :=
    le_mul_of_one_le_left (by linarith) (by exact_mod_cast K.params.fgDelay.pos)
  obtain ⟨r, ⟨hw, hd, -⟩, ⟨-, hH, hp, ha⟩, -⟩ :=
    (h.realizable hn).healthy cap i Δ Δ gst hΔ hΔ hrat hgst
  refine ⟨r, hw, hd, hH, hp, ?_⟩
  rcases h.behaviour.healthyLive cap g hg i gst r hw.1 ⟨hH, hp⟩ with hl | he
  · exact hl.served ha
  · exact absurd he hw.2.1

end CorrectProtocol

end Consensus

end
