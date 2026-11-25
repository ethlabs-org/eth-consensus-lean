module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.EngineTransport
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Truncation

@[expose] public section

/-! # The release hold of the generic service and the regime transport at `0`

`Generic.Service` takes a release hold `hold` (default `0`): its signed-row clause serves a signing
only when the signer is honest at `max (time i) g + hold`, in the form of `SyncOnAt.attestation`.
`RegimeTransport` takes the same hold, and its healthy leg serves signed rows at `ΔFG + hold`.
`ServiceNoHold` and `RegimeTransportNoHold` restate both as they were before the hold, verbatim.
At `hold = 0` each agrees with its restatement (`service_zero_iff`, `regimeTransport_zero_iff`):
every statement that reads them at the default keeps its meaning.

The premises bundle `Premises`, the healing obligations `ACHealing`, the local record
`ACCorrectLocal`, the healing contracts that read `Service` or `Premises`, `HealthyReadPoint` and
the claim suppliers `DeadlinePremisesSupply`, `FinalReadTransport`, `HighCanonicalSupply` and
`PreparationPremisesSupply` take the same hold (and the suppliers an FG delay `ΔF`, default
`E.ΔFG`). Each `…NoHold` below is main's form without the hold, verbatim but for the names; at
the defaults each Prop agrees with it (`…_zero_iff`) and each record is equivalent to it
(`…ZeroEquiv`). -/

namespace Consensus.Goldilocks.Test.ServiceHold

open Shape Blocks Generic

section Service

variable {P : Params} {A : NodeAC P}

/-- `Generic.Service` as stated before the release hold. -/
structure ServiceNoHold (tr : RunTrace A) (H : Time → Set (Fin P.n)) (g ΔF b : Time) :
    Prop where
  deltaF : 0 < ΔF
  message : ∀ x i m, x ∈ H (tr.time i) → tr.SendOrAdmitAt x i m →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) P.Δ ≤ tr.time j →
      tr.MsgDeliveredBy y j (tr.time i) (max (tr.time i) g) m
  block : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) P.Δ ≤ tr.time j →
      tr.BlockDeliveredBy y j (tr.time i) (max (tr.time i) g) B
  relay : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → g ≤ tr.time i →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) P.Δ ≤ tr.time j →
      Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j (max (tr.time i) g) B
  signedRow : ∀ x i att, x ∈ H (tr.time i) → tr.SignAt x i att →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.time j ≤ b →
      tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
      ∃ k ≤ j, tr.ProcessAttAt y k att ∧ tr.time k < tr.deadline y k (max (tr.time i) g) ΔF

/-- **At hold `0`, `Generic.Service` is the service before the hold.** -/
theorem service_zero_iff {tr : RunTrace A} {H : Time → Set (Fin P.n)} {g ΔF b : Time} :
    Service tr H g ΔF b ↔ ServiceNoHold tr H g ΔF b :=
  ⟨fun ⟨d, m, bl, r, s, _⟩ => ⟨d, m, bl, r, fun x i att hx hs =>
      s x i att hx hs fun _ _ _ _ h => (h rfl).elim⟩,
    fun ⟨d, m, bl, r, s⟩ => ⟨d, m, bl, r, fun x i att hx hs _ => s x i att hx hs, d.le⟩⟩

end Service

section Transport

variable {P : Params} {A : NodeAC P} {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}

/-- `RegimeTransport` as stated before the release hold. -/
structure RegimeTransportNoHold (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop where
  sleepy : rho.ExecutionValid → ¬ rho.HashCollision →
    (Sys F V).Sleepy (shapeProgress F V).toExternal K ⟨E, rho⟩ →
    SleepyServicePrefix C M.trace M.honest E.ΔFG C.look rho.horizon
  healthy : rho.ExecutionValid → ¬ rho.HashCollision → ∀ g,
    (Sys F V).Healthy (shapeProgress F V).toExternal K g ⟨E, rho⟩ →
    ServiceNoHold M.trace M.honest g E.ΔFG rho.horizon ∧
    (∀ y t, max g 0 ≤ t → t ≤ rho.horizon → y ∈ M.honest t → M.trace.awake y t) ∧
    (∀ d, 0 ≤ d → d ≤ rho.horizon → ((M.honest d)ᶜ.ncard : ℚ) < K.params.β * P.n) ∧
    (∀ t d, max g 0 ≤ t → t ≤ rho.horizon → 0 ≤ d → d ≤ rho.horizon →
      (M.committee t).Nonempty →
      (((↑(M.committee t) : Set (Fin P.n)) ∩ (M.honest d)ᶜ).ncard : ℚ) <
        K.params.βK * (M.committee t).card)
  ready : ∀ c v i, i ≤ rho.events.length → rho.point.Ready c v (rho.cutTime i) →
    ReadyRead M c (M.validator.symm v) (M.cut i) (rho.cutTime i)

/-- **At hold `0`, `RegimeTransport` is the regime transport before the hold.** -/
theorem regimeTransport_zero_iff {M : RunMap rho payload} {K : Contract ProgressReq}
    {C : ACCorrectLocal A M.signer} : RegimeTransport M K C ↔ RegimeTransportNoHold M K C := by
  constructor
  · rintro ⟨s, h, r⟩
    refine ⟨s, fun hv hc g hg => ?_, r⟩
    obtain ⟨hs, rest⟩ := h hv hc g hg
    rw [add_zero] at hs
    exact ⟨service_zero_iff.mp hs, rest⟩
  · rintro ⟨s, h, r⟩
    refine ⟨s, fun hv hc g hg => ?_, r⟩
    obtain ⟨hs, rest⟩ := h hv hc g hg
    rw [add_zero]
    exact ⟨service_zero_iff.mpr hs, rest⟩

end Transport

section Premises

open AC (gbar)
open Healing (FirstCutAfter cutZ)
open Healing.Growing (HZ IsReset CatchRun NoRestartAfter)

variable {P : Params} {A : NodeAC P}

/-- `Generic.Premises` as stated before the release hold. -/
structure PremisesNoHold (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (cm : Time → Finset (Fin P.n)) (βK : ℚ)
    (proposer : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (sg : A.Msg → Fin P.n) (g ΔF b : Time) : Prop where
  committee : CommitteeFaultsUpTo βK cm H g b
  noColl : Compose.NoCollRun dg tr
  sync : ServiceNoHold tr H g ΔF b
  awake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t
  faults : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1
  catchUp : CatchRun tr H g (2 * P.Δ)
  noRestart : NoRestartAfter tr H (gbar g)
  timeoutDelay : ∀ s, P.slotTime s + 6 * P.Δ + ΔF ≤ P.slotTime (s + P.δt)
  slotLen : ∀ s, P.slotTime s + 4 * P.Δ ≤ P.slotTime (s + 1)
  snapshot : ∃ k, FirstCutAfter tr k (cutZ P g) ∧ tr.time k ≤ b
  nonempty : (H b).Nonempty

/-- **At hold `0`, `Premises` is the premises bundle before the hold.** -/
theorem premises_zero_iff {tr : RunTrace A} {H : Time → Set (Fin P.n)}
    {cm : Time → Finset (Fin P.n)} {βK : ℚ} {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {sg : A.Msg → Fin P.n} {g ΔF b : Time} :
    Premises tr H cm βK proposer dg sg g ΔF b ↔ PremisesNoHold tr H cm βK proposer dg sg g ΔF b :=
  ⟨fun ⟨c, n, s, a, f, cu, nr, td, sl, sn, ne⟩ =>
      ⟨c, n, service_zero_iff.mp s, a, f, cu, nr, td, sl, sn, ne⟩,
    fun ⟨c, n, s, a, f, cu, nr, td, sl, sn, ne⟩ =>
      ⟨c, n, service_zero_iff.mpr s, a, f, cu, nr, td, sl, sn, ne⟩⟩

/-- `Generic.ACHealing` as stated before the release hold. -/
structure ACHealingNoHold (A : NodeAC P) (sg : A.Msg → Fin P.n) (runs : ACRun A sg) where
  warmup : Nat
  follow : Nat
  reportDelay : Nat
  drain : Nat
  Origin : RunTrace A → Fin P.n → Nat → Nat → A.Blk → Prop
  follow_le : ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF b : Time},
    runs.Run cm proposer dg H tr → PremisesNoHold tr H cm βK proposer dg sg g ΔF b → follow ≤ P.δt
  report_in_frame : ∀ {cm proposer dg H tr} {y : Fin P.n} {i : Nat} {R : A.Blk},
    runs.Run cm proposer dg H tr → y ∈ H (tr.time i) → ReportAt tr y i R →
    R ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc (tr.state y i).fg.fcRoot R
  /-- Certificate: no open obligation recorded. The proposal anchor preserves the frame floor. -/
  proposal_floor : ∀ {cm proposer dg H tr} {lo hi : Time} {floor u : Nat} {kindJ : Prop}
    {J B : A.Blk} {z : Fin P.n} {kB : Nat},
    runs.Run cm proposer dg H tr → Compose.NoCollRun dg tr → FrameWindow tr H lo hi floor kindJ J →
    z ∈ H (P.slotTime u) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
    lo ≤ P.slotTime u → P.slotTime u ≤ hi →
    (H (P.slotTime u))ᶜ.ncard < 2 * P.fg.q - P.n →
    floor ≤ ((tr.state z (kB + 1)).fg.σ B.root).h
  /-- After warmup, an honest proposal is reported within one slot plus `2 + reportDelay` delays,
  and later honest proposal heads extend the report. Certificate: cert obligation open:
  honest committee members support an honest proposal after healing. -/
  report_follow : ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF b : Time}
    {s₀ N u floor : Nat} {kindJ : Prop} {J B : A.Blk} {z : Fin P.n} {kB : Nat},
    βK ≤ 1 / 2 →
    runs.Run cm proposer dg H tr → PremisesNoHold tr H cm βK proposer dg sg g ΔF b →
    FrameWindow tr H (P.slotTime s₀)
      (shiftDelay P reportDelay (P.slotTime N + 2 * P.Δ)) floor kindJ J →
    gbar g + 4 * P.Δ ≤ P.slotTime s₀ → s₀ + warmup ≤ u →
    u + 1 ≤ N → shiftDelay P reportDelay (P.slotTime N + 2 * P.Δ) ≤ b →
    HonestProposal tr H proposer u z kB B →
    ∀ y, y ∈ H (shiftDelay P reportDelay (P.slotTime (u + 1) + 2 * P.Δ)) →
      ∃ i R, y ∈ H (tr.time i) ∧ ReportAt tr y i R ∧ P.slotTime u ≤ tr.time i ∧
        tr.time i ≤ shiftDelay P reportDelay (P.slotTime (u + 1) + 2 * P.Δ) ∧
        Anc (tr.HonestBlocksAt H) B R ∧
        ∀ x, u + follow ≤ x → x ≤ N → ∀ w c d, w ∈ H (tr.time c) →
          ProposalHeadAt tr w c d → tr.time c = P.slotTime x → Anc (tr.HonestBlocksAt H) R d.head
  /-- A high honest report after a reset has an earlier origin extending it.
  Certificate: no open obligation recorded. -/
  report_origin : ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF a b : Time}
    {y : Fin P.n} {i : Nat} {R : A.Blk},
    βK ≤ 1 / 2 →
    runs.Run cm proposer dg H tr → PremisesNoHold tr H cm βK proposer dg sg g ΔF b →
    IsReset tr H g a → a ≤ b → y ∈ H (tr.time i) → tr.time i ≤ b → ReportAt tr y i R →
    HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h →
    ∃ r ≤ i, ∃ j B, y ∈ H (tr.time r) ∧ Origin tr y r j B ∧
      B ∈ (tr.state y r).fg.tree ∧ Anc (tr.HonestBlocksAt H) R B
  /-- High honest FG sources after a reset are compatible across all slots.
  Certificate: cert obligation open: same-slot FG-source safety plus C1.1 across slots,
  including the analogue excluding high sources before cutZ. -/
  origins_comparable : ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF a b : Time} {x x' : Fin P.n}
    {i j i' j' : Nat} {B B' : A.Blk},
    βK ≤ 1 / 2 →
    runs.Run cm proposer dg H tr → PremisesNoHold tr H cm βK proposer dg sg g ΔF b →
    IsReset tr H g a → a ≤ b →
    x ∈ H (max (cutZ P g) (tr.time i)) → Origin tr x i j B → tr.time i ≤ b →
    HZ tr H g + 1 ≤ ((tr.state x i).fg.σ B.root).h →
    x' ∈ H (max (cutZ P g) (tr.time i')) → Origin tr x' i' j' B' → tr.time i' ≤ b →
    HZ tr H g + 1 ≤ ((tr.state x' i').fg.σ B'.root).h →
    Compatible (tr.HonestBlocksAt H) B B'
  /-- Canonical high sources yield chained honest proposals after the AC's drain bound.
  Certificate: cert obligation open: the certificate healing bound. -/
  heal_after_reset : ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF a b : Time},
    βK ≤ 1 / 2 →
    runs.Run cm proposer dg H tr → PremisesNoHold tr H cm βK proposer dg sg g ΔF b →
    IsReset tr H g a → a ≤ b →
    HighCanonical Origin tr H g b → HealedFrom tr H proposer (P.slotOf a + drain) b

/-- **At hold `0`, `ACHealing` is the healing record before the hold.** -/
def acHealingZeroEquiv (A : NodeAC P) (sg : A.Msg → Fin P.n) (runs : ACRun A sg) :
    ACHealing A sg runs ≃ ACHealingNoHold A sg runs where
  toFun O := ⟨O.warmup, O.follow, O.reportDelay, O.drain, O.Origin,
    fun hr hp => O.follow_le hr (premises_zero_iff.mpr hp), O.report_in_frame, O.proposal_floor,
    fun hβ hr hp => O.report_follow hβ hr (premises_zero_iff.mpr hp),
    fun hβ hr hp => O.report_origin hβ hr (premises_zero_iff.mpr hp),
    fun hβ hr hp => O.origins_comparable hβ hr (premises_zero_iff.mpr hp),
    fun hβ hr hp => O.heal_after_reset hβ hr (premises_zero_iff.mpr hp)⟩
  invFun O := ⟨O.warmup, O.follow, O.reportDelay, O.drain, O.Origin,
    fun hr hp => O.follow_le hr (premises_zero_iff.mp hp), O.report_in_frame, O.proposal_floor,
    fun hβ hr hp => O.report_follow hβ hr (premises_zero_iff.mp hp),
    fun hβ hr hp => O.report_origin hβ hr (premises_zero_iff.mp hp),
    fun hβ hr hp => O.origins_comparable hβ hr (premises_zero_iff.mp hp),
    fun hβ hr hp => O.heal_after_reset hβ hr (premises_zero_iff.mp hp)⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Premises

section Healing

open AC (gbar)
open Healing (FirstCutAfter cutZ)
open Healing.Growing (HZ IsReset CatchRun NoRestartAfter)

variable {P : Params} (A : NodeAC P) (sg : A.Msg → Fin P.n)
variable {runs : ACRun A sg}

/-- `reset_of_high_proposal_at` as stated before the release hold. -/
def reset_of_high_proposal_atNoHold (O : ACHealing A sg runs) : Prop :=
  ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF b : Time} {s₀ u N floor : Nat}
    {kindJ : Prop} {J B : A.Blk}
    {z : Fin P.n} {kB : Nat},
    βK ≤ 1 / 2 → CommitteeFaultsUpTo βK cm H g b →
    SlotWindowWithin tr H O.reportDelay s₀ N floor kindJ J →
    runs.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    ServiceNoHold tr H g ΔF b → (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    (∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) →
    CatchRun tr H g (2 * P.Δ) → NoRestartAfter tr H (gbar g) →
    (∀ s, P.slotTime s + 4 * P.Δ ≤ P.slotTime (s + 1)) →
    (∀ s, P.slotTime s + 6 * P.Δ + ΔF ≤ P.slotTime (s + P.δt)) →
    (∃ k, FirstCutAfter tr k (cutZ P g) ∧ tr.time k ≤ b) →
    gbar g + 4 * P.Δ ≤ P.slotTime s₀ → s₀ ≤ u → s₀ + O.warmup ≤ u →
    u + 1 ≤ N → shiftDelay P O.reportDelay (P.slotTime N + 2 * P.Δ) ≤ b → (H b).Nonempty →
    z ∈ H (P.slotTime u + P.Δ) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
    HZ tr H g + 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h →
    ∃ a, IsReset tr H g a ∧ a ≤ shiftDelay P O.reportDelay (P.slotTime (u + 1) + 2 * P.Δ)

/-- `round_of_warm_at` as stated before the release hold. -/
def round_of_warm_atNoHold (O : ACHealing A sg runs) : Prop :=
  ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF b T : Time} {s₀ u x N floor : Nat} {kindJ : Prop}
    {J B X : A.Blk} {z : Fin P.n} {kB : Nat} {p : Fin P.n} {kX : Nat},
    βK ≤ 1 / 2 → CommitteeFaultsUpTo βK cm H g b →
    SlotWindowWithin tr H O.reportDelay s₀ N floor kindJ J →
    runs.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    ServiceNoHold tr H g ΔF b → (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    (∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) →
    CatchRun tr H g (2 * P.Δ) → NoRestartAfter tr H (gbar g) →
    (∀ s, P.slotTime s + 4 * P.Δ ≤ P.slotTime (s + 1)) →
    (∀ s, shiftDelay P O.reportDelay (P.slotTime (s + 1) + 2 * P.Δ) + ΔF ≤
      P.slotTime (s + P.δt)) →
    (∃ k, FirstCutAfter tr k (cutZ P g) ∧ tr.time k ≤ b) →
    gbar g + 4 * P.Δ ≤ P.slotTime s₀ → s₀ ≤ u → s₀ + O.warmup ≤ u → O.follow ≤ P.δt →
    (∀ s, P.slotTime s + 6 * P.Δ + ΔF ≤ P.slotTime (s + P.δt)) →
    u + P.δt ≤ x → x ≤ N → shiftDelay P O.reportDelay (P.slotTime N + 2 * P.Δ) ≤ b →
    (H b).Nonempty → T ≤ b →
    NoAdvance tr H g T → shiftDelay P O.reportDelay (P.slotTime (u + 1) + 2 * P.Δ) < T →
    z ∈ H (P.slotTime u + P.Δ) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
    p ∈ H (tr.time kX) → p = proposer x → tr.ProposesAt p kX X → X.slot = x →
    B ∈ (tr.state p (kX + 1)).fg.tree ∧ X ∈ (tr.state p (kX + 1)).fg.tree ∧
      ((tr.state p (kX + 1)).fg.σ B.root).h + 1 ≤ ((tr.state p (kX + 1)).fg.σ X.root).h

/-- `high_row_source_at` as stated before the release hold. -/
def high_row_source_atNoHold (O : ACHealing A sg runs) : Prop :=
  ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF a b : Time}
    {v : Fin P.n} {d : Nat} {att : FG.Att P.n},
    βK ≤ 1 / 2 → runs.Run cm proposer dg H tr →
    PremisesNoHold tr H cm βK proposer dg sg g ΔF b → IsReset tr H g a → a ≤ b →
    v ∈ H (max (cutZ P g) (tr.time d)) → tr.time d ≤ b →
    tr.SignAt v d att → HZ tr H g + 1 ≤ att.h →
    ∃ r < d, ∃ l Og, HighOrigin A sg O tr H g v r l Og ∧
      ∃ E ∈ (tr.state v r).fg.tree, (tr.state v r).fg.Anc E Og ∧
        E.root = att.T ∧ ((tr.state v r).fg.σ E.root).h = att.h ∧
        ((tr.state v r).fg.σ E.root).Th = E.root

/-- `no_high_contest_at` as stated before the release hold. -/
def no_high_contest_atNoHold (_O : ACHealing A sg runs) : Prop :=
  ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF a b : Time} {p : Fin P.n} {i : Nat},
    βK ≤ 1 / 2 → runs.Run cm proposer dg H tr →
    PremisesNoHold tr H cm βK proposer dg sg g ΔF b → IsReset tr H g a → a ≤ b →
    p ∈ H (tr.time i) → tr.time i ≤ b →
    ¬ ((tr.state p i).fg.Contest ∧ HZ tr H g + 2 ≤ (tr.state p i).fg.hmax)

/-- `high_entry_eq_at` as stated before the release hold. -/
def high_entry_eq_atNoHold (O : ACHealing A sg runs) : Prop :=
  ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF a b : Time} {x x' : Fin P.n} {i j i' j' : Nat}
    {B B' Z₁ Z₂ : A.Blk} {y₁ y₂ : Fin P.n} {m₁ m₂ : Nat} {t₁ t₂ : Time},
    βK ≤ 1 / 2 → runs.Run cm proposer dg H tr →
    PremisesNoHold tr H cm βK proposer dg sg g ΔF b → IsReset tr H g a → a ≤ b →
    HighOrigin A sg O tr H g x i j B → tr.time i ≤ b →
    HighOrigin A sg O tr H g x' i' j' B' → tr.time i' ≤ b →
    Anc (tr.HonestBlocksAt H) Z₁ B → Anc (tr.HonestBlocksAt H) Z₂ B' →
    0 ≤ t₁ → (∀ q < m₁, tr.time q ≤ t₁) → y₁ ∈ H t₁ →
    0 ≤ t₂ → (∀ q < m₂, tr.time q ≤ t₂) → y₂ ∈ H t₂ →
    Z₁ ∈ (tr.state y₁ m₁).fg.tree → Z₂ ∈ (tr.state y₂ m₂).fg.tree →
    ((tr.state y₁ m₁).fg.σ Z₁.root).h = ((tr.state y₂ m₂).fg.σ Z₂.root).h →
    ((tr.state y₁ m₁).fg.σ Z₁.root).Th = Z₁.root →
    ((tr.state y₂ m₂).fg.σ Z₂.root).Th = Z₂.root → Z₁.root = Z₂.root

/-- `rise_reset_rounds_at` as stated before the release hold. -/
def rise_reset_rounds_atNoHold (O : ACHealing A sg runs) : Prop :=
  ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF b T : Time}
    {s₀ N Gp floor : Nat} {kindJ : Prop} {J : A.Blk},
    βK ≤ 1 / 2 → CommitteeFaultsUpTo βK cm H g b →
    SlotWindowWithin tr H O.reportDelay s₀ N floor kindJ J →
    runs.Run cm proposer dg H tr → Compose.NoCollRun dg tr → ServiceNoHold tr H g ΔF b →
    (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    (∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) →
    CatchRun tr H g (2 * P.Δ) → NoRestartAfter tr H (gbar g) →
    (∀ s, P.slotTime s + 4 * P.Δ ≤ P.slotTime (s + 1)) →
    (∀ s, shiftDelay P O.reportDelay (P.slotTime (s + 1) + 2 * P.Δ) + ΔF ≤
      P.slotTime (s + P.δt)) →
    (∃ k, FirstCutAfter tr k (cutZ P g) ∧ tr.time k ≤ b) →
    gbar g + 4 * P.Δ ≤ P.slotTime s₀ → O.follow ≤ P.δt → 1 ≤ Gp →
    (∀ s, P.slotTime s + 6 * P.Δ + ΔF ≤ P.slotTime (s + P.δt)) →
    ProposalGap tr H proposer Gp s₀ N → shiftDelay P O.reportDelay (P.slotTime N + 2 * P.Δ) ≤ b →
    (H b).Nonempty → T ≤ b → NoAdvance tr H g T →
    ∀ (r : Nat) {u : Nat} {z : Fin P.n} {kB : Nat} {B : A.Blk},
      s₀ ≤ u → s₀ + O.warmup ≤ u → u + r * (P.δt + Gp - 1) + 1 ≤ N →
      shiftDelay P O.reportDelay (P.slotTime (u + r * (P.δt + Gp - 1) + 1) + 2 * P.Δ) ≤ T →
      z ∈ H (P.slotTime u + P.Δ) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
      HZ tr H g + 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h + r →
      ∃ a, IsReset tr H g a ∧
        a ≤ shiftDelay P O.reportDelay (P.slotTime (u + r * (P.δt + Gp - 1) + 1) + 2 * P.Δ)

/-- **At hold `0`, the healing contracts are those before the hold.** -/
theorem healing_contracts_zero_iff (O : ACHealing A sg runs) :
    (reset_of_high_proposal_at A sg O ↔ reset_of_high_proposal_atNoHold A sg O) ∧
    (round_of_warm_at A sg O ↔ round_of_warm_atNoHold A sg O) ∧
    (high_row_source_at A sg O ↔ high_row_source_atNoHold A sg O) ∧
    (no_high_contest_at A sg O ↔ no_high_contest_atNoHold A sg O) ∧
    (high_entry_eq_at A sg O ↔ high_entry_eq_atNoHold A sg O) ∧
    (rise_reset_rounds_at A sg O ↔ rise_reset_rounds_atNoHold A sg O) := by
  simp only [reset_of_high_proposal_at, reset_of_high_proposal_atNoHold, round_of_warm_at,
    round_of_warm_atNoHold, high_row_source_at, high_row_source_atNoHold, no_high_contest_at,
    no_high_contest_atNoHold, high_entry_eq_at, high_entry_eq_atNoHold, rise_reset_rounds_at,
    rise_reset_rounds_atNoHold, service_zero_iff, premises_zero_iff, and_self]

end Healing

section Local

open AC (gbar)
open Healing.Growing (IsReset)

variable {P : Params}

/-- `Generic.ACCorrectLocal` as stated before the release hold. -/
structure ACCorrectLocalNoHold (A : NodeAC P) (sg : A.Msg → Fin P.n) where
  /-- Protocol-supplied durations, not fixed instance coefficients. -/
  look : Time
  catchUp : Time
  margin : Time
  latency : Time
  hold : Time
  /-- Fixed local outage recovery duration, not chosen separately for each reader. -/
  recovery : Time
  /-- Fixed outage participation threshold and durations, matched to the contract separately. -/
  θ : ℚ
  outageEta : Time
  outageLag : Time
  outageBudget : Time
  committeeLook : Time
  /-- The local outage policy cannot start recovery before the outage ends. -/
  recovery_nonneg : 0 ≤ recovery
  /-- One run/start owner for the local and healing obligations. -/
  run : ACRun A sg
  /-- AC-owned message service, allowing fresh delivery or retained protocol evidence. -/
  served : RunTrace A → Fin P.n → Nat → Time → A.Msg → Prop
  served_of_delivered : ∀ {cm proposer dg H tr} {y j τ m}, run.Run cm proposer dg H tr →
    tr.MsgDeliveredBy y j τ τ m → served tr y j τ m
  /-- Healing is a separate protocol obligation, not implied by this record's endpoint claims. -/
  healing : ACHealingNoHold A sg run
  /-- The transaction/input projection of a block, supplied as data. -/
  payload : A.Blk → Set Nat
  /-- Durations cannot make readiness or deadlines negative. -/
  durations : 0 ≤ look ∧ 0 ≤ catchUp ∧ 0 ≤ margin ∧ 0 ≤ latency ∧ 0 ≤ hold
  /-- L1: the confirmed tip is held, extends the finalized root and precedes the head. -/
  tipsValid : ∀ (cm : Time → Finset (Fin P.n)) (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (H : Time → Set (Fin P.n))
    (tr : RunTrace A), run.Run cm proposer dg H tr →
    ∀ y i, y ∈ H (tr.time i) →
      tr.confirmedAt y i ∈ (Node.frame (tr.state y i)).tree ∧
      (Node.frame (tr.state y i)).Anc (tr.finalizedAt y i) (tr.confirmedAt y i) ∧
      (Node.frame (tr.state y i)).Anc (tr.confirmedAt y i) (tr.headAt y i)

/-- **At hold `0`, `ACCorrectLocal` is the local record before the hold.** -/
def acCorrectLocalZeroEquiv (A : NodeAC P) (sg : A.Msg → Fin P.n) :
    ACCorrectLocal A sg ≃ ACCorrectLocalNoHold A sg where
  toFun C := ⟨C.look, C.catchUp, C.margin, C.latency, C.hold, C.recovery, C.θ, C.outageEta,
    C.outageLag, C.outageBudget, C.committeeLook, C.recovery_nonneg, C.run, C.served,
    C.served_of_delivered, acHealingZeroEquiv A sg C.run C.healing, C.payload, C.durations,
    C.tipsValid⟩
  invFun C := ⟨C.look, C.catchUp, C.margin, C.latency, C.hold, C.recovery, C.θ, C.outageEta,
    C.outageLag, C.outageBudget, C.committeeLook, C.recovery_nonneg, C.run, C.served,
    C.served_of_delivered, (acHealingZeroEquiv A sg C.run).symm C.healing, C.payload,
    C.durations, C.tipsValid⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {A : NodeAC P}

/-- `HealthyReadPoint` as stated before the release hold. -/
structure HealthyReadPointNoHold {sg : A.Msg → Fin P.n} (C : ACCorrectLocal A sg) : Prop where
  /-- L6: healed agreement requires an honest opening proposal; reads use actual times. -/
  healed : ∀ cm βK proposer dg H (tr : RunTrace A) ΔF g a b s₁,
    βK ≤ 1 / 2 →
    C.run.Run cm proposer dg H tr → PremisesNoHold tr H cm βK proposer dg sg g ΔF b →
    IsReset tr H g a → a ≤ b → P.slotOf a + C.healing.drain ≤ s₁ →
    HealedFrom tr H proposer s₁ b →
    max g 0 ≤ P.slotTime s₁ →
    ((∃ z k X, HonestProposal tr H proposer s₁ z k X) →
      P.slotTime s₁ + 6 * P.Δ ≤ b → gbar g + 4 * P.Δ ≤ P.slotTime s₁ →
      ∀ y z i j t u, P.slotTime s₁ + C.margin < t →
      P.slotTime s₁ + C.margin < u →
      ReadyReadPoint tr H b C.catchUp y i t → ReadyReadPoint tr H b C.catchUp z j u →
      ReadBoundary tr y i → ReadBoundary tr z j →
      Compatible (tr.HonestBlocksAt H) (confirmedRead tr y i t) (confirmedRead tr z j u)) ∧
    ∀ z k X, HonestProposal tr H proposer s₁ z k X → 0 ≤ tr.time k → tr.time k ≤ b →
      ∀ y j t, tr.time k + C.margin ≤ t → ReadyReadPoint tr H b C.catchUp y j t →
      ReadBoundary tr y j → t < tr.time j →
      Anc (tr.HonestBlocksAt H) X (confirmedRead tr y j t)
  /-- L7: a ready proposal after the reset drain is confirmed within the latency. -/
  proposal : ∀ cm βK proposer dg H (tr : RunTrace A) ΔF g a b healed,
    βK ≤ 1 / 2 →
    C.run.Run cm proposer dg H tr → PremisesNoHold tr H cm βK proposer dg sg g ΔF b →
    IsReset tr H g a → a ≤ b → max g 0 + C.margin ≤ healed →
    ∀ B k y j t, ReadyProposal tr H C.catchUp C.hold B k →
    P.slotOf a + C.healing.drain ≤ B.slot → gbar g + 4 * P.Δ ≤ P.slotTime B.slot →
    0 ≤ tr.time k → tr.time k ≤ b → tr.time k + C.hold ≤ b → healed ≤ tr.time k →
    tr.time k + C.latency ≤ t → ReadyReadPoint tr H b C.catchUp y j t →
    ReadBoundary tr y j → t < tr.time j →
    Anc (tr.HonestBlocksAt H) B (confirmedRead tr y j t)

/-- **At hold `0`, `HealthyReadPoint` is the read point before the hold.** -/
theorem healthyReadPoint_zero_iff {sg : A.Msg → Fin P.n} (C : ACCorrectLocal A sg) :
    HealthyReadPoint C ↔ HealthyReadPointNoHold C :=
  ⟨fun ⟨h, p⟩ => ⟨fun cm βK proposer dg H tr ΔF g a b s₁ hβ hr hp =>
      h cm βK proposer dg H tr ΔF g a b s₁ hβ hr (premises_zero_iff.mpr hp),
    fun cm βK proposer dg H tr ΔF g a b healed hβ hr hp =>
      p cm βK proposer dg H tr ΔF g a b healed hβ hr (premises_zero_iff.mpr hp)⟩,
    fun ⟨h, p⟩ => ⟨fun cm βK proposer dg H tr ΔF g a b s₁ hβ hr hp =>
      h cm βK proposer dg H tr ΔF g a b s₁ hβ hr (premises_zero_iff.mp hp),
    fun cm βK proposer dg H tr ΔF g a b healed hβ hr hp =>
      p cm βK proposer dg H tr ΔF g a b healed hβ hr (premises_zero_iff.mp hp)⟩⟩

end Local

section Claims

set_option autoImplicit false

variable {P : Params} {A : NodeAC P} {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}

/-- `DeadlinePremisesSupply` as stated before the release hold. -/
def DeadlinePremisesSupplyNoHold (M : RunMap rho payload) (K : Contract ProgressReq) : Prop :=
  rho.ExecutionValid → ¬ rho.HashCollision → ∀ idx gst query,
    (Sys F V).Healthy (shapeProgress F V).toExternal K gst ⟨E, rho⟩ →
    (Sys F V).prog (shapeProgress F V) K .final idx ((Sys F V).ready K gst ⟨E, rho⟩)
      rho.horizon ⟨E, rho⟩ →
    (Sys F V).heal K .final idx gst ⟨E, rho⟩ ≤ query →
    query + (K.params.latency .final idx : Time) * E.ΔAC ≤ rho.horizon →
    (∃ v, rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v
      (query + (K.params.latency .final idx : Time) * E.ΔAC)) →
    PremisesNoHold M.trace (truncH M.honest (query + (K.params.latency .final idx : Time) * E.ΔAC))
      M.committee K.params.βK M.proposer M.digest M.signer gst E.ΔFG
      (query + (K.params.latency .final idx : Time) * E.ΔAC)

/-- `FinalReadTransport` as stated before the release hold. -/
structure FinalReadTransportNoHold (M : RunMap rho payload) (C : ACCorrectLocal A M.signer) :
    Prop where
  cache : ∀ (βK : ℚ) gst query deadline
    (W : FinalProductionWindow M C.catchUp C.hold query deadline),
    βK ≤ 1 / 2 →
    C.run.Run M.committee M.proposer M.digest M.honest M.trace →
    PremisesNoHold M.trace (truncH M.honest deadline) M.committee βK M.proposer M.digest M.signer
      gst
      E.ΔFG deadline →
    (∀ a, M.trace.AcceptAt (W.block a).proposer (W.cut a) (W.block a)) →
    (∀ a b, a ≤ b → Anc (M.trace.HonestBlocksAt M.honest) (W.block a) (W.block b)) →
    (∀ a : Fin 3, ∃ z i j, z ∈ M.honest (M.trace.time i) ∧
      z ∈ M.honest (M.trace.time j) ∧
      W.block a.castSucc ∈ (M.trace.state z i).fg.tree ∧
      W.block a.succ ∈ (M.trace.state z j).fg.tree ∧
      ((M.trace.state z i).fg.σ (W.block a.castSucc).root).h + 1 ≤
        ((M.trace.state z j).fg.σ (W.block a.succ).root).h) →
    ∀ y j t, deadline ≤ t →
    ReadyReadPoint M.trace M.honest rho.horizon C.catchUp y j t →
    ReadBoundary M.trace y j →
    (M.honest t)ᶜ.ncard < 2 * P.q - P.n →
    Anc (M.trace.HonestBlocksAt M.honest) (W.block 0) (M.trace.finalizedAt y j)

/-- `HighCanonicalSupply` as stated before the release hold. -/
def HighCanonicalSupplyNoHold (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop :=
  CommitteeHalfFit K → rho.ExecutionValid → ¬ rho.HashCollision → ∀ gst a,
  (Sys F V).Healthy (shapeProgress F V).toExternal K gst ⟨E, rho⟩ →
  C.run.Run M.committee M.proposer M.digest M.honest M.trace →
  PremisesNoHold M.trace M.honest M.committee K.params.βK M.proposer M.digest M.signer
    gst E.ΔFG rho.horizon →
  Healing.Growing.IsReset M.trace M.honest gst a → a ≤ rho.horizon →
  HighCanonical C.healing.Origin M.trace M.honest gst rho.horizon

/-- `PreparationPremisesSupply` as stated before the release hold. -/
def PreparationPremisesSupplyNoHold (M : RunMap rho payload) (K : Contract ProgressReq) : Prop :=
  HealthyBetaFit K → rho.ExecutionValid → ¬ rho.HashCollision → ∀ cap idx gst,
  (cap = .available ∨ cap = .stable) →
  (Sys F V).Healthy (shapeProgress F V).toExternal K gst ⟨E, rho⟩ →
  (Sys F V).prog (shapeProgress F V) K cap idx ((Sys F V).ready K gst ⟨E, rho⟩)
    ((Sys F V).heal K cap idx gst ⟨E, rho⟩) ⟨E, rho⟩ →
  (Sys F V).heal K cap idx gst ⟨E, rho⟩ ≤ rho.horizon →
  PremisesNoHold M.trace M.honest M.committee K.params.βK M.proposer M.digest M.signer
    gst E.ΔFG rho.horizon

/-- **At the default hold and FG delay, the claim suppliers are those before the hold.** -/
theorem claim_suppliers_zero_iff (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) :
    (DeadlinePremisesSupply M K ↔ DeadlinePremisesSupplyNoHold M K) ∧
    (HighCanonicalSupply M K C ↔ HighCanonicalSupplyNoHold M K C) ∧
    (PreparationPremisesSupply M K ↔ PreparationPremisesSupplyNoHold M K) := by
  simp only [DeadlinePremisesSupply, DeadlinePremisesSupplyNoHold, HighCanonicalSupply,
    HighCanonicalSupplyNoHold, PreparationPremisesSupply, PreparationPremisesSupplyNoHold,
    premises_zero_iff, and_self]

/-- **At the default FG delay and hold `0`, `FinalReadTransport` is the transport before the
hold.** -/
theorem finalReadTransport_zero_iff (M : RunMap rho payload) (C : ACCorrectLocal A M.signer) :
    FinalReadTransport M C ↔ FinalReadTransportNoHold M C :=
  ⟨fun ⟨h⟩ => ⟨fun βK gst query deadline W hβ hr hp =>
      h βK gst query deadline W hβ hr (premises_zero_iff.mpr hp)⟩,
    fun ⟨h⟩ => ⟨fun βK gst query deadline W hβ hr hp =>
      h βK gst query deadline W hβ hr (premises_zero_iff.mp hp)⟩⟩

end Claims

end Consensus.Goldilocks.Test.ServiceHold

end
