module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Boundaries
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.Row
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.RowService
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.CorrectnessEdges
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Truncation
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.GoldilocksBridge
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingRounds
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingEdges

public section

/-! # Goldilocks conditional healing bridges

The shared run interface supplies the canonical committee start, its run laws and the run on the
honest sets truncated after a horizon. Three Goldilocks-side targets are proved from the proved
generic leaves for every supplier: the high-row, no-contest and historical-entry bridges
(`high_row_source_at_of_healing`, `no_high_contest_at_of_healing`, and
`ACHealing.origins_comparable` with `high_entry_eq_at_from`). The high-row target is the
conditional bridge with added premises described at `high_row_source_at_goldilocks`; no
original-premise high-row bridge is provided. The no-contest and historical-entry targets keep
their reset-record interfaces and use truncation: the finite reset record bounds restarts only
up to its horizon, so they use the generic premises on the honest sets truncated after it
(`premises_truncH`, `ACRun.run_truncH`); the historical-entry one compares only the two origins
there and keeps its arbitrary observation times.
These targets use committee-indexed starts, positive matching committee sizes, and membership
facts under collision freedom. Population FG fault bounds remain population bounds; committee
fault bounds are separate. The concrete stock proofs need in-place committee generalisation.

This leaf has an isolated concrete bridge proof closure, not a vocabulary-only closure.
`Kernel.Boundaries` supplies `KernelProof.goldilocksRun_truncH`, used by `run_truncH`.
`Report.Row` supplies the concrete report-row vocabulary.
`RowService` supplies `ResetPremisesUpTo.high_entry_eq_at` and the retained-origin vocabulary
`ResetPremisesUpTo` and `HighOrigin`, with committee-aware reset premises below.
Generic statements do not import this concrete proof closure. The run transport and
concrete sleepy adapters read `goldilocksRunInterface` from it.

No old name: `exists_reset`, `generic_healing`, `highCanonical`, the slot-form
`exists_frameWindow`, and `sign_from_report`.
-/

namespace Consensus.Goldilocks.Generic

open SA (SAParams ReplayOrder Payload gbar)
open Healing Healing.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The shared Goldilocks run interface, starting each node with its committee permission. -/
noncomputable def goldilocksRunInterface (sp : SAParams)
    (ro : ReplayOrder sp (List (FG.Att sp.n))) :
    ACRun (goldilocksNode sp ro) (fun v => v.val) where
  Run cm proposer dg H tr := Growing.GoldilocksRun proposer dg H tr
    (SA.committeeStart sp.genesisRoot (dictOfTime sp cm)) ∧
    0 < sp.committeeSize ∧
    (∀ s, ((dictOfTime sp cm).committee s).ncard = sp.committeeSize) ∧
    (Compose.NoCollRun dg tr → Compose.Growing.CommitteeFacts tr H (dictOfTime sp cm))
  start cm := SA.committeeStart sp.genesisRoot (dictOfTime sp cm)
  start_univ := by
    have h : dictOfTime sp (fun _ => Finset.univ) = SA.CommitteeDict.full sp.n := by
      simp [dictOfTime, SA.CommitteeDict.full]
    rw [h]
    exact SA.committeeStart_full _
  run_local h := h.1.toLocalRun
  run_requirements h y := Compose.requirements_from sp ro (h.1.vstart y)
  run_root h := h.1.genesis_root_ok
  run_truncH h b := ⟨KernelProof.goldilocksRun_truncH h.1 b, h.2.1, h.2.2.1,
    fun hnc => (h.2.2.2 hnc).truncH b⟩

/-- The run projection uses the committee-indexed initial AC states. -/
theorem goldilocksRunInterface_run_iff (cm : Time → Finset (Fin sp.n)) :
    (goldilocksRunInterface sp ro).Run cm proposer dg H tr ↔
      Growing.GoldilocksRun proposer dg H tr
        (SA.committeeStart sp.genesisRoot (dictOfTime sp cm)) ∧
      0 < sp.committeeSize ∧
      (∀ s, ((dictOfTime sp cm).committee s).ncard = sp.committeeSize) ∧
      (Compose.NoCollRun dg tr → Compose.Growing.CommitteeFacts tr H (dictOfTime sp cm)) := by rfl

/-- Conditional high-row bridge corresponding to
`Growing/Healing/Outcome/RowSource.high_row_source_at`. The earlier-origin conclusion and historical
honesty charge are retained, but this target uses the committee-valid run interface and additionally
assumes `βK ≤ 1/2`, `Premises`, `IsReset` at `a ≤ b`, and the signing cutoff `tr.time d ≤ b`. It
proves the conclusion under these added premises, not under the original concrete theorem's
premises. -/
def high_row_source_at_goldilocks {tr : GoldilocksTrace sp ro}
    {H : Time → Set (Fin sp.n)} : Prop := ∀
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {g ΔF a b : Time}
    (_hβ : βK ≤ 1 / 2)
    (_hrun : (goldilocksRunInterface sp ro).Run cm proposer dg H tr)
    (_hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b)
    (_hr : IsReset tr H g a) (_hab : a ≤ b)
    {v : Fin sp.n} {d : Nat} {att : FG.Att sp.n}
    (_hv : v ∈ H (max (cutZ sp.toParams g) (tr.time d))) (_hdb : tr.time d ≤ b)
    (_hs : tr.SignAt v d att)
    (_hh : HZ tr H g + 1 ≤ att.h),
    ∃ r < d, ∃ l O, Healing.Growing.HighOrigin tr H g v r l O ∧
      ∃ E ∈ (tr.state v r).fg.tree, (tr.state v r).fg.Anc E O ∧
        E.root = att.T ∧ ((tr.state v r).fg.σ E.root).h = att.h ∧
        ((tr.state v r).fg.σ E.root).Th = E.root

/-- Original side: `Outcome.no_high_contest_at`. -/
def no_high_contest_at_goldilocks : Prop := ∀ {g ΔF a b : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (_hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {p : Fin sp.n} {i : Nat} (_hpH : p ∈ H (tr.time i)) (_hib : tr.time i ≤ b),
    ¬ ((tr.state p i).fg.Contest ∧ HZ tr H g + 2 ≤ (tr.state p i).fg.hmax)

/-- Original side: `ResetPremisesUpTo.high_entry_eq_at`; arbitrary honesty bounds retained. -/
def high_entry_eq_at_goldilocks
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} : Prop := ∀ {g ΔF a b : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (_hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK) {x x' : Fin sp.n}
    {i j i' j' : Nat} {B B' Z₁ Z₂ : SA.Blk sp.n (List (FG.Att sp.n))}
    (_ho : Healing.Growing.HighOrigin tr H g x i j B) (_hib : tr.time i ≤ b)
    (_ho' : Healing.Growing.HighOrigin tr H g x' i' j' B') (_hi'b : tr.time i' ≤ b)
    (_h₁ : Anc (tr.HonestBlocksAt H) Z₁ B) (_h₂ : Anc (tr.HonestBlocksAt H) Z₂ B')
    {y₁ y₂ : Fin sp.n} {m₁ m₂ : Nat} {t₁ t₂ : Time}
    (_ht₁ : 0 ≤ t₁) (_hle₁ : ∀ q < m₁, tr.time q ≤ t₁) (_hy₁ : y₁ ∈ H t₁)
    (_ht₂ : 0 ≤ t₂) (_hle₂ : ∀ q < m₂, tr.time q ≤ t₂) (_hy₂ : y₂ ∈ H t₂)
    (_hZ₁ : Z₁ ∈ (tr.state y₁ m₁).fg.tree) (_hZ₂ : Z₂ ∈ (tr.state y₂ m₂).fg.tree)
    (_hh : ((tr.state y₁ m₁).fg.σ Z₁.root).h = ((tr.state y₂ m₂).fg.σ Z₂.root).h)
    (_hT₁ : ((tr.state y₁ m₁).fg.σ Z₁.root).Th = Z₁.root)
    (_hT₂ : ((tr.state y₂ m₂).fg.σ Z₂.root).Th = Z₂.root), Z₁.root = Z₂.root

/-! Each consequent below universally closes its committee-indexed target. Historical signing
is charged at the maximum of the snapshot and event time. No ready-majority premise is added. -/

/-- The finite reset record on the honest sets truncated after its horizon `b`: `c_z ≤ b` (the
snapshot cut is by `b`), the interface run (`ACRun.run_truncH`), the bundled premises with
restarts bounded up to `b` (`premises_truncH`; slot spacing from the four-delay grid), and the
reset (`isReset_truncH_iff`). -/
private theorem resetPremisesUpTo_truncH {g ΔF a b : Time} {cm : Time → Finset (Fin sp.n)}
    {βK : ℚ} (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK) :
    cutZ sp.toParams g ≤ b ∧
      (goldilocksRunInterface sp ro).Run cm proposer dg (truncH H b) tr ∧
      Premises tr (truncH H b) cm βK proposer dg (fun v => v.val) g ΔF b ∧
      IsReset tr (truncH H b) g a := by
  obtain ⟨j, hj, hjb⟩ := hp.snapshot
  have hcz : cutZ sp.toParams g ≤ b := hj.2.le.trans hjb
  refine ⟨hcz, (goldilocksRunInterface sp ro).run_truncH
    ⟨hp.run, hp.committee_pos, hp.committeeFacts.hsize, fun _ => hp.committeeFacts⟩ b,
    premises_truncH hp.committeeFaults hp.noColl
      ⟨hp.sync.deltaF, hp.sync.message, hp.sync.block, hp.sync.relay, hp.sync.signedRow⟩
      hp.awake hp.faults hp.catchUp hp.noRestart hp.timeoutDelay
      (slotLen_of_grid fun s => by rw [sp.slotTime_eq]; ring) hp.snapshot
      hp.nonempty,
    (isReset_truncH_iff hcz hp.reset_le).mpr hp.reset⟩

/-- High-row implication for the conditional target `high_row_source_at_goldilocks`, by leaf 12
(`high_row_source_at_of_healing`). The target already takes the bundled premises; the supplier's
origin is the joined stored fast lock (`GoldilocksHealingData`). -/
theorem high_row_source_at_bridge
    (O : ACHealing (goldilocksNode sp ro) (fun v => v.val) (goldilocksRunInterface sp ro))
    (hD : GoldilocksHealingData sp ro O) :
    ∀ {proposer dg tr H}, high_row_source_at_goldilocks (sp := sp) (ro := ro)
      (proposer := proposer) (dg := dg) (tr := tr) (H := H) := by
  intro proposer dg tr H cm βK g ΔF a b hβ hrun hp hr hab v d att hv hdb hs hh
  obtain ⟨-, -, -, -, hOrig⟩ := hD
  obtain ⟨r, hrd, l, Og, ⟨hx, hOr, hOh⟩, hE⟩ :=
    high_row_source_at_of_healing O hβ hrun hp hr hab hv hdb hs hh
  rw [hOrig] at hOr
  exact ⟨r, hrd, l, Og, ⟨hx, hOr.1, hOr.2, hOh⟩, hE⟩

/-- No-contest implication, `Outcome.no_high_contest_at`; committee-aware reset record. The reset
record bounds restarts only up to its horizon `b`, so the no-contest leaf
(`no_high_contest_at_of_healing`) applies on the honest sets truncated after `b`
(`resetPremisesUpTo_truncH`), where the store reader at `time i ≤ b` is honest and `H_z` is
unchanged. -/
theorem no_high_contest_at_bridge
    (O : ACHealing (goldilocksNode sp ro) (fun v => v.val) (goldilocksRunInterface sp ro)) :
    ∀ {proposer dg H tr}, no_high_contest_at_goldilocks (sp := sp) (ro := ro)
      (proposer := proposer) (dg := dg) (H := H) (tr := tr) := by
  intro proposer dg H tr g ΔF a b cm βK hp p i hpH hib
  obtain ⟨hcz, hrun, hP, hres⟩ := resetPremisesUpTo_truncH hp
  have h := no_high_contest_at_of_healing O hp.beta_le hrun hP hres hp.reset_le (p := p)
    ⟨hpH, hib⟩ hib
  rwa [HZ_truncH hcz] at h

/-- Historical-entry implication, `ResetPremisesUpTo.high_entry_eq_at`. Arbitrary observation times
are retained: only the two origins, whose cuts are `≤ b`, are compared on the honest sets truncated
after `b` (`ACHealing.origins_comparable`, through `resetPremisesUpTo_truncH`); their compatibility
over the truncated honest blocks is compatibility over `H`'s, and `high_entry_eq_at_from` applies on
the original run with the original observations and ancestry. -/
theorem high_entry_eq_at_bridge
    (O : ACHealing (goldilocksNode sp ro) (fun v => v.val) (goldilocksRunInterface sp ro))
    (hD : GoldilocksHealingData sp ro O) :
    ∀ {dg H tr proposer}, high_entry_eq_at_goldilocks (sp := sp) (ro := ro)
      (dg := dg) (H := H) (tr := tr) (proposer := proposer) := by
  intro dg H tr proposer g ΔF a b cm βK hp x x' i j i' j' B B' Z₁ Z₂ ho hib ho' hi'b h₁ h₂
    y₁ y₂ m₁ m₂ t₁ t₂ ht₁ hle₁ hy₁ ht₂ hle₂ hy₂ hZ₁ hZ₂ hh hT₁ hT₂
  obtain ⟨-, -, -, -, hOrig⟩ := hD
  obtain ⟨hcz, hrun, hP, hres⟩ := resetPremisesUpTo_truncH hp
  have hc := O.origins_comparable hp.beta_le hrun hP hres hp.reset_le
    ⟨ho.1, max_le hcz hib⟩ (by rw [hOrig]; exact ⟨ho.2.1, ho.2.2.1⟩) hib
    (by rw [HZ_truncH hcz]; exact ho.2.2.2)
    ⟨ho'.1, max_le hcz hi'b⟩ (by rw [hOrig]; exact ⟨ho'.2.1, ho'.2.2.1⟩) hi'b
    (by rw [HZ_truncH hcz]; exact ho'.2.2.2)
  have hsub := honestBlocksAt_truncH_subset (tr := tr) (H := H) b
  exact high_entry_eq_at_from hp.run.toLocalRun hp.noColl (hc.imp (Anc.mono hsub) (Anc.mono hsub))
    h₁ h₂ ht₁ hle₁ hy₁ ht₂ hle₂ hy₂ hZ₁ hZ₂ hh hT₁ hT₂

end Consensus.Goldilocks.Generic
