module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierViews
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.UnanimityWalk
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.SignTick
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.ServedBase
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: post-reset duty suppliers

The source and transport facts are in `Outcome.Foundation`; the proposal pivot is in
`Outcome.Pivot`; the post-drain slot arithmetic and the voter's walk to the proposal, shared by
both unanimity duties, are in `Outcome.UnanimityWalk`. The duty conclusions here may use all
three without an import cycle. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n}
  {ini : Fin sp.n → (goldilocksNode sp).State} {g ΔF a : Time}

/-- Every awake honest node executes the joined update, whether or not its tick signs. -/
theorem update_call_of_awake {ini}
    (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {u : Nat}
    (hawake : tr.awake y (sp.ts u + 6 * sp.Δ))
    (hjoin : ∀ i, tr.time i = sp.ts u + 6 * sp.Δ →
      AC.joined sp (tr.projAC.state y i) (tr.time i)) :
    ∃ j ell, AC.UpdateAt tr.projAC y j u ell := by
  have hDelta := sp.toParams.hΔ
  have hts : 0 ≤ sp.ts u := by simp only [ACParams.ts]; positivity
  obtain ⟨j, x, fgDue, hg⟩ := hrun.tick_of_awake y hy (sp.ts u + 6 * sp.Δ)
    (by linarith) ⟨4 * (u : Int) + 6, by simp only [ACParams.ts]; ring⟩ hawake
  obtain ⟨hc, ht⟩ := tick_first_cut hg
  exact ⟨j, _, Compose.projAC_callAt.2 hc, rfl, ht, hjoin j ht⟩

/-- With a fast-lock candidate, `ac_to_fg` considers the deepest one, deep sources on or off. -/
private theorem fgSource_of_fast {FGP : Type} {A : AC.ACState sp.n} {Φ : AC.Frm sp.n FGP}
    {t : Time} {C : AC.Blk sp.n FGP}
    (h : AC.deepest Φ (AC.toFGCandidates sp A Φ t) = some C) :
    AC.fgSource sp A Φ t = some C := by
  unfold AC.fgSource
  split <;> simp [h]

/-- A deepest candidate extending a non-genesis block gives an actual report at this call. -/
theorem report_of_deepest_candidate_of_run
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : GoldilocksRun proposer dg H tr ini) (hnoColl : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt y j ell) (hcall : ell.call = .toFG)
    (hjoin : AC.joined sp (tr.projAC.state y j) (tr.time j))
    {P C : AC.Blk sp.n (List (FG.Att sp.n))}
    (_hPg : P.root ≠ sp.genesisRoot)
    (hC : AC.deepest ell.frame (AC.toFGCandidates sp (tr.projAC.state y j)
      ell.frame (tr.time j)) = some C) (hPC : ell.frame.Anc P C) :
    ∃ r ell' R, AC.ToFGAt tr.projAC y r ell' R ∧ tr.time r ≤ tr.time j ∧
      Anc (tr.HonestBlocks H) P R := by
  have hr := (Compose.goldilocks_ac_projection_from hrun hnoColl).localRun
  have hPhiU := (AC.frameIn_of_callAt hr hy hc).2
  refine ⟨j, ell, C, ⟨hc, hcall, ?_⟩, le_rfl, hPC.mono hPhiU⟩
  change (AC.acToFG sp (tr.projAC.state y j) ell.frame (tr.time j)).2 = some C
  simp only [AC.acToFG, hjoin, not_true_eq_false, ↓reduceIte, fgSource_of_fast hC]

/-- A live report candidate compatible with every other candidate supplies an actual report
extending it. -/
theorem report_of_compatible_candidate_of_run
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : GoldilocksRun proposer dg H tr ini) (hnoColl : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt y j ell) (hcall : ell.call = .toFG)
    (hjoin : AC.joined sp (tr.projAC.state y j) (tr.time j))
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hPg : P.root ≠ sp.genesisRoot)
    (hPc : P ∈ AC.toFGCandidates sp (tr.projAC.state y j) ell.frame (tr.time j))
    (hcompat : ∀ C ∈ AC.toFGCandidates sp (tr.projAC.state y j) ell.frame (tr.time j),
      Compatible (tr.HonestBlocks H) C P) :
    ∃ r ell' R, AC.ToFGAt tr.projAC y r ell' R ∧ tr.time r ≤ tr.time j ∧
      Anc (tr.HonestBlocks H) P R := by
  have hr := (Compose.goldilocks_ac_projection_from hrun hnoColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hy hc
  have hsub : AC.toFGCandidates sp (tr.projAC.state y j) ell.frame (tr.time j) ⊆
      ell.frame.tree := fun _ h => h.1.1
  obtain ⟨C, hC⟩ := AC.exists_deepest hPhi hsub ⟨P, hPc⟩
  obtain ⟨hCc, hmax⟩ := AC.deepest_mem hC
  apply report_of_deepest_candidate_of_run hrun hnoColl hy hc hcall hjoin hPg hC
  rcases hcompat C hCc with hCP | hPC
  · by_cases he : P = C
    · exact he ▸ .refl
    have hCPf := AC.anc_tree_of_anc_U hr.coherent hPhi hPhiU (hsub hCc) hCP (hsub hPc)
    have hlt := AC.depth_lt_of_anc hPhi hCPf (Ne.symm he) (hsub hPc)
    rcases hmax P hPc he with h | ⟨h, _⟩ <;> omega
  · exact AC.anc_tree_of_anc_U hr.coherent hPhi hPhiU (hsub hPc) hPC (hsub hCc)

/-- Finite report coverage. The unproduced duties are explicit: a deadline cut with
compatible finality for each reader, and a below-finality actual-report producer.
Neither duty assumes wakefulness after `b`; historical reports have no lower time bound. -/
theorem ResetPremisesUpTo.report_cover_of_compatible_floors {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hcuts : ∀ z ∈ H, ∃ j, tr.time j ≤ sp.ts u + 6 * sp.Δ ∧
      Compatible (tr.HonestBlocks H) (tr.state z j).fg.F P ∧
      (Anc (tr.HonestBlocks H) (tr.state z j).fg.F P →
        ∃ r ell C, AC.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
          Anc (tr.HonestBlocks H) P C)) :
    (∀ z ∈ H, ∃ r ell C, AC.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocks H) P C) ∨
    ∃ z ∈ H, ∃ r ell C, AC.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocks H) P C ∧
      ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h := by
  by_cases hall : ∀ z ∈ H, ∃ r ell C, AC.ToFGAt tr.projAC z r ell C ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C
  · exact Or.inl hall
  push Not at hall
  obtain ⟨z, hz, hn⟩ := hall
  obtain ⟨j, hj, hcompat, hbelow⟩ := hcuts z hz
  rcases hp.finality_below_or_higher_report hz hcompat with
    hF | ⟨v, hv, r, ell, C, hrj, hto, hPC, hlt⟩
  · obtain ⟨r, ell, C, hto, ht, hPC⟩ := hbelow hF
    exact False.elim (hn r ell C hto ht hPC)
  · exact Or.inr ⟨v, hv, r, ell, C, hto, (hp.run.time_mono hrj.le).trans hj, hPC, hlt⟩

/-- Conditional report coverage at actual cuts bounded by the update deadline.
Compatibility discharges the strict-descendant branch using an earlier actual report;
the below-floor branch still needs an actual-report producer (selection alone is not one).
The cuts may be updates or first-loss post-states; no lower bound on report time is imposed. -/
theorem report_cover_of_compatible_floors
    (hp : ResetPremises tr H K proposer dg g ΔF a)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hcuts : ∀ z ∈ H, ∃ j, tr.time j ≤ sp.ts u + 6 * sp.Δ ∧
      Compatible (tr.HonestBlocks H) (tr.state z j).fg.F P ∧
      (Anc (tr.HonestBlocks H) (tr.state z j).fg.F P →
        ∃ r ℓ C, AC.ToFGAt tr.projAC z r ℓ C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
          Anc (tr.HonestBlocks H) P C)) :
    (∀ z ∈ H, ∃ r ℓ C, AC.ToFGAt tr.projAC z r ℓ C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocks H) P C) ∨
    ∃ z ∈ H, ∃ r ℓ C, AC.ToFGAt tr.projAC z r ℓ C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocks H) P C ∧
      ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h :=
  (hp.toUpTo tr H le_rfl).report_cover_of_compatible_floors hcuts

end Consensus.Goldilocks.Healing

end
