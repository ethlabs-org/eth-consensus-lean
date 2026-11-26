module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ReportCover
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PostDrainRenewal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SignedToFG
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.SignGap
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowLocal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.CandidateReport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.OldSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Reports above a unanimous post-drain proposal under a signing calendar

`report_cover_of_unanimous_at` (`Healthy/ReportCover`) reads a report at the update deadline
`t_u + 6Δ` from global signing. Under a signing calendar with gap `G`
(`SignCalendarAt`, `SignGapAt`), a node honest at `t_u + 6Δ + G·Δ` signs at a public time
`t' ∈ [t_u + 6Δ, t_u + 6Δ + G·Δ]` (`SignGapAt.of_public`), and reports there:

* at `t' = t_u + 6Δ`, from the adjacent update and `ac_to_fg` calls of its signing tick
  (`report_of_signTick_unanimous_at`, the stock cover's own step);
* at `t' > t_u + 6Δ`, from a toFG candidate above `P` (`toFG_candidate_post_at`), compatible with
  every candidate of the call (`toFG_candidates_compatible_at_call_at`), which an actual report
  extends (`report_of_compatible_candidate_of_run_at`).

Otherwise a node honest at its report and at `c_z` reports a strictly higher descendant of `P`
by `t_u + 6Δ + G·Δ`. With responsive signing (`G = 0`) this is the stock statement
(`report_cover_of_unanimous_responsive_at`). -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {hold : Time}

/-- **Reports above a unanimous post-drain proposal `P` of slot `u` by `t_u + 6Δ + G·Δ`** under
a signing calendar with gap `G` from `t_u + 6Δ`: every node honest at `t_u + 6Δ + G·Δ` reports a
descendant of `P` by then, or a node honest at its report and at `c_z` reports a strict height
increase above `P` by then. -/
theorem report_cover_delayed_of_unanimous_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt proposer dg H sign)
    {G u : Nat} (hgap : SignGapAt sp.toParams sign G (sp.ts u + 6 * sp.Δ))
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ + G * sp.Δ ≤ b) :
    (∀ y, y ∈ H (sp.ts u + 6 * sp.Δ + G * sp.Δ) → ∃ r e R, AC.ToFGAt tr.projAC y r e R ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ + G * sp.Δ ∧ Anc (tr.HonestBlocksAt H) P R) ∨
    (∃ x r e C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ AC.ToFGAt tr.projAC x r e C ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ + G * sp.Δ ∧ Anc (tr.HonestBlocksAt H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h) := by
  classical
  by_cases hescape : ∃ x r e C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧
      AC.ToFGAt tr.projAC x r e C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ + G * sp.Δ ∧
      Anc (tr.HonestBlocksAt H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h
  · exact Or.inr hescape
  left
  intro y hy
  have hΔ := sp.toParams.hΔ
  have hm := hp.run.time_mono
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hG : (0 : Time) ≤ G * sp.Δ := mul_nonneg (by positivity) hΔ.le
  have hd0 : 0 ≤ sp.ts u + 6 * sp.Δ := by simp only [ACParams.ts]; positivity
  have hstep {m : Nat} : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hjoinu : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) ≤ sp.ts u := by
    have hbase := (AC.ts_le_iff_le_slot sp (AC.gbar_nonneg g) (sp.slot (AC.gbar g))).2 (by rfl)
    simp only [AC.ACParams.ts] at hbase hgu ⊢
    push_cast at hbase hgu ⊢
    linarith only [hbase, hgu]
  have hpubd : sp.toParams.IsPublic (sp.ts u + 6 * sp.Δ) :=
    ⟨4 * (u : Int) + 6, by simp only [ACParams.ts]; ring⟩
  -- the signing time
  obtain ⟨t', ht'1, ht'2, hpub', hsgn⟩ := hgap.of_public (y := y) le_rfl hpubd
  have ht'b : t' ≤ b := (ht'2.trans (by linarith)).trans hTb
  have hyt' : y ∈ H t' := hp.run.antitone (by linarith) hy
  have hawake' : tr.awake y t' :=
    hp.awake y t' hyt' (by linarith [AC.le_gbar g, hjoinu]) ht'b
  rcases eq_or_lt_of_le ht'1 with heq | hlt
  · -- the signing tick at the update deadline
    subst heq
    obtain ⟨j, hsj⟩ := signTickAt_of_calendar hp hcal hyt' hd0 hpub' hawake' hsgn
    rcases report_of_signTick_unanimous_at hp hP hslot hu hPg hun hgu hR ht'b hyt' hsj with
      ⟨r, e, R, h1, h2, h3⟩ | ⟨x, r, e, C, hx, hto', ht, hPC, hh⟩
    · exact ⟨r, e, R, h1, by linarith, h3⟩
    · exact absurd ⟨x, r, e, C, hx, hto', by linarith, hPC, hh⟩ hescape
  · -- a later signing time: a toFG candidate above `P`
    obtain ⟨i, ell, hc, hcall, hti, hji⟩ :=
      hp.toFG_call_of_sign hcal hyt' hjoinu ht'1 ht'b hpub' hawake' hsgn
    have hyi : y ∈ H (tr.time i) := hti ▸ hyt'
    have ht'0 : 0 ≤ t' := by linarith
    have hσ : u + 1 ≤ sp.slot t' := by
      have := (AC.ts_le_iff_le_slot sp ht'0 ((u + 1 : Nat) : Int)).1
        (by have := @hstep u; linarith)
      exact_mod_cast this
    rcases toFG_candidate_post_at hp hP hslot hu hPg hun hgu hR (N := sp.slot t' - 2) y i ell
        hyi hc hcall
        (by rw [hti]; have := @hstep u; linarith) (by rw [hti]; omega) (hti ▸ ht'b) with
      hesc | ⟨B, hB, hPB⟩
    · obtain ⟨x, q, e, C, hx, hto', hq, hPC, hh⟩ := higherReportBy_iff.mp hesc
      exact absurd ⟨x, q, e, C, hx, hto', by linarith, hPC, hh⟩ hescape
    have hBU : B ∈ tr.HonestBlocksAt H :=
      (Compose.Growing.frameIn_at hp.run hp.noColl hyi hc).2 hB.1.1
    have hBg : B.root ≠ sp.genesisRoot := fun hg => hPg (by
      have hBP := ProposalImpl.genesis_root_anc_at hp.run hp.noColl hBU hg hP
      rw [← Anc.antisymm hU hBP hPB]; exact hg)
    obtain ⟨r, e, R, hto', hrt, hBR⟩ := report_of_compatible_candidate_of_run_at hp.run
      hp.noColl hyi hc hcall hji hBg hB
      (toFG_candidates_compatible_at_call_at hp.run hp.noColl hyi hc hB)
    exact ⟨r, e, R, hto', hrt.trans (by rw [hti]; linarith), hPB.trans hBR⟩

/-- **The responsive case `G = 0`**: under a calendar that signs at every public time, the delayed
cover is the stock statement `report_cover_of_unanimous_at`, at `t_u + 6Δ`. -/
theorem report_cover_of_unanimous_responsive_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    (hcal : tr.SignCalendarAt proposer dg H (fun _ _ => true))
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b) :
    (∀ y, y ∈ H (sp.ts u + 6 * sp.Δ) → ∃ r e R, AC.ToFGAt tr.projAC y r e R ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocksAt H) P R) ∨
    (∃ x r e C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ AC.ToFGAt tr.projAC x r e C ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocksAt H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h) := by
  have h := report_cover_delayed_of_unanimous_at hp hcal (G := 0) (signGapAt_true _ _) hP hslot
    hu hPg hun hgu hR (by simpa using hTb)
  simpa using h

end Consensus.Goldilocks.Healing.Growing

end
