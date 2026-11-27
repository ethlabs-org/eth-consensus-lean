module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ReportFollow
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GoldilocksBridge
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Deep
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingRounds
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # `ACHealing` fields over the shadow run (draft for the adoption landing)

The Option A fields of the Goldilocks supplier, over `Growing.GoldilocksRun'` and the window
`Healing.FrameWindow' … M isTop J` (the restated milestone `FrameWindow`, field for field). They
are stated unpacked: the run, its committee-indexed start, signing calendar, signing gap and
committee half bound are separate premises, so the run-interface wrapper of the adopted instance
only splits its `Run` conjunction into them. The adoption rename turns the primed names into the
unprimed ones.

* `reportAt_iff_toFGAt'`: an actual report of a node honest at it is an `ac_to_fg` call of the AC
  projection;
* `goldilocks_report_follow'`: the `report_follow` field, from `proposal_report_follow_delayed_at'`
  (`ReportFollow`, standard axioms). -/

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams ReplayOrder Payload gbar)
open Consensus.Goldilocks.Generic
open Consensus.Goldilocks.Healing.Growing (CommitteeHalfUpTo)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}

/-- An actual report of a node honest at it is an `ac_to_fg` call of the AC projection
(`reportAt_iff_toFGAt` over the shadow run). -/
theorem reportAt_iff_toFGAt' {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini) {y : Fin sp.n}
    {i : Nat} (hy : y ∈ H (tr.time i)) {R : AC.Blk sp.n (List (FG.Att sp.n))} :
    ReportAt tr y i R ↔ ∃ ℓ, AC.ToFGAt tr.projAC y i ℓ R := by
  unfold ReportAt AC.ToFGAt
  rw [projAC_state_at' hrun hy]
  refine exists_congr fun ℓ => ?_
  rw [Compose.projAC_callAt]
  rfl

/-- **The `report_follow` field** over the shadow run and the restated window: after warmup the
proposal is reported by nodes honest at the delayed report deadline, and the same report is an
ancestor of later honest proposal heads. -/
theorem goldilocks_report_follow' {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {hold : Time} {g ΔF b : Time} {G : Nat} {sign : Fin sp.n → Time → Bool}
    {s₀ N u M : Nat} {isTop : Prop} {J B : AC.Blk sp.n (List (FG.Att sp.n))} {z : Fin sp.n}
    {kB : Nat}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot (dictOfTime sp cm)))
    (hcal : tr.SignCalendarAt' proposer dg H sign) (hgap : SignGapAt sp.toParams sign G 0)
    (hK : CommitteeHalfUpTo tr H (dictOfTime sp cm) g b)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b hold)
    (hframe : Healing.FrameWindow' tr H (sp.toParams.slotTime s₀)
      (shiftDelay sp.toParams G (sp.toParams.slotTime N + 2 * sp.toParams.Δ)) M isTop J)
    (hm : gbar g + 4 * sp.toParams.Δ ≤ sp.toParams.slotTime s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + 1 ≤ N)
    (hmb : shiftDelay sp.toParams G (sp.toParams.slotTime N + 2 * sp.toParams.Δ) ≤ b)
    (hB : HonestProposal tr H proposer u z kB B) :
    ∀ y, y ∈ H (shiftDelay sp.toParams G (sp.toParams.slotTime (u + 1) + 2 * sp.toParams.Δ)) →
      ∃ i R, y ∈ H (tr.time i) ∧ ReportAt tr y i R ∧ sp.toParams.slotTime u ≤ tr.time i ∧
        tr.time i ≤ shiftDelay sp.toParams G (sp.toParams.slotTime (u + 1) + 2 * sp.toParams.Δ) ∧
        Anc (tr.HonestBlocksAt H) B R ∧
        ∀ x, u + (3 + (G + 3) / 4) ≤ x → x ≤ N → ∀ w c d, w ∈ H (tr.time c) →
          ProposalHeadAt tr w c d → tr.time c = sp.toParams.slotTime x →
          Anc (tr.HonestBlocksAt H) R d.head := by
  intro y hy
  have hts (s : Nat) : sp.toParams.slotTime s = sp.ts s := by
    rw [sp.slotTime_eq]
    rfl
  obtain ⟨hz, hdes, hP, hPs⟩ := hB
  rw [hts] at hz hm
  rw [shiftDelay_eq_add, hts] at hy
  rw [hts, hts] at hframe
  rw [hts] at hmb
  have hmax : max (sp.ts N + 2 * sp.Δ)
      (sp.ts (u + 1 : Nat) + 2 * sp.Δ + (G : Time) * sp.Δ) ≤
      shiftDelay sp.toParams G (sp.ts N + 2 * sp.Δ) := by
    rw [shiftDelay_eq_add]
    have hG : 0 ≤ (G : Time) * sp.Δ := mul_nonneg (by positivity) sp.toParams.hΔ.le
    have hmono := sp.toParams.slotTime_strictMono.monotone hN
    rw [hts, hts] at hmono
    exact max_le (by linarith) (by linarith)
  have ht₀ : 0 ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ := by
    have hΔ := sp.toParams.hΔ
    simp only [ACParams.ts]
    positivity
  obtain ⟨i, ell, R, hyi, hto, hlo, hhi, hPR, hheads⟩ :=
    proposal_report_follow_delayed_at' (hframe.mono le_rfl hmax) hrun hp.noColl
      ⟨hp.sync.deltaF, hp.sync.message, hp.sync.block, hp.sync.relay, hp.sync.signedRow,
      hp.sync.hold_le⟩
      hp.awake hp.faults hp.catchUp hp.noRestart hm hwarm hN (hmax.trans hmb) hz hdes hP hPs
      hcal hgap ht₀ hy hK
  refine ⟨i, R, hyi, (reportAt_iff_toFGAt' hrun hyi).mpr ⟨ell, hto⟩, (hts u).symm ▸ hlo,
    by rw [shiftDelay_eq_add, hts]; exact hhi, hPR, ?_⟩
  intro x hx hxN w c d hw ⟨ℓ, pay, hc, hcall, hd⟩ htc
  exact hheads x (by omega) hxN w c ℓ hw (Compose.projAC_callAt.mpr hc) hcall
    (htc.trans (hts x)) d pay
    (by rw [projAC_state_at' hrun hw]; exact hd)

end Consensus.Goldilocks.Shadow.PU.Growing

end
