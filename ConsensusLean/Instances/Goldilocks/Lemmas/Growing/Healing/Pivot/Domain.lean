module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.RootSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.HighFloor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HeldRoots
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRowSources
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Held-target proposal domain, parametrized only by the shared floor supplier -/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
variable {hold : Time}

/-- The held-target proposal domain, with the high floor source of the proposal call as an
explicit input, with the high-source cover: the floor source may be a covered entry, and the
target is compared with the healed members too (`CompatibleWithOrigins`). -/
theorem held_target_proposal_domain_before_of_sources_covered_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x p : Fin sp.n} {r i u : Nat} (hx : x ∈ H (tr.time r)) (hpH : p ∈ H (tr.time i))
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hBx : B ∈ (tr.state x r).fg.tree)
    {ell : ACLabel (goldilocksNode sp)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    (hheld : Anc (tr.HonestBlocksAt H) ell.frame.F B → B ∈ ell.frame.tree)
    (hseed : ∃ v q m S, HighOrigin tr H g v q m S ∧ tr.time q < sp.ts u ∧
      Compatible (tr.HonestBlocksAt H) B S)
    (hcompare : ResetPremisesUpTo.CompatibleWithOrigins tr H g a b i (sp.slot (tr.time i)) B)
    (hfloorSource : ∀ v q m S, HighOrigin tr H g v q m S → tr.time q ≤ b →
      ((tr.state v q).fg.σ S.root).h < (tr.state p i).fg.headHeightFloor →
      (∃ z q' n O E, q' < i ∧ HighOrigin tr H g z q' n O ∧ n < u ∧
        E ∈ (tr.state p i).fg.tree ∧ Anc (tr.HonestBlocksAt H) E O ∧
        Anc (tr.HonestBlocksAt H) S O ∧
        (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ E.root).h) ∨
      (∃ E ∈ (tr.state p i).fg.tree, CoveredBefore tr H g a b (sp.slot (tr.time i)) i E ∧
        (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ E.root).h)) :
    Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨ B ∈ ell.frame.viableTree ell.frame.tree := by
  have hroot := held_target_proposal_root_before_covered_at hp hx hpH hBx hci hcall hd hti hib
    hheld hseed hcompare
  by_cases hcovered : Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot
  · exact Or.inl hcovered
  have hac := Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl
  have hr := hac.localRun.upTo (hp.run.time_nonneg i)
  have hci' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hci)
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hpH hci'
  have hrootB := hroot.resolve_right hcovered
  have hFB := (hPhi.F_anc_fcRoot.mono hPhiU).trans hrootB
  have hBt := hheld hFB
  have hBy := (frame_tree_subset_at hp.run hp.noColl hpH hci).2 hBt
  have ht := hp.run.time_nonneg i
  have hle : ∀ q < i, tr.time q ≤ tr.time i := fun _ hq => hp.run.time_mono hq.le
  have hreach := fg_reachable_at hp.run ht hle hpH
  have hfr := Outcome.frame_of_call hp.run hpH hci
  have held : ∀ {z q m O}, HighOrigin tr H g z q m O → tr.time q < sp.ts u →
      Anc (tr.HonestBlocksAt H) B O → O ∈ ell.frame.tree := by
    intro z q m O ho hqt hBO
    rcases proposal_holds_old_at hp hpH hci hcall hd hti hib ho hqt with h | h
    · exact h
    · have he := h.antisymm hac.localRun.coherent (hFB.trans hBO)
      exact he ▸ hPhi.rooted.1
  have hdesc : ∃ C ∈ ell.frame.tree, Anc (tr.HonestBlocksAt H) B C ∧
      (tr.state p i).fg.IsViable C := by
    by_cases hfloor : (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ B.root).h
    · exact ⟨B, hBt, .refl, hfloor⟩
    obtain ⟨v, q, m, S, hS, hqt, hBS⟩ := hseed
    have hSsrc := highOrigin_mem_at hp.run hp.noColl hS
    have hv := hp.run.antitone (le_max_right _ _) hS.1
    by_cases hSf : (tr.state p i).fg.headHeightFloor ≤ ((tr.state v q).fg.σ S.root).h
    · have hBS' : Anc (tr.HonestBlocksAt H) B S := by
        rcases hBS with h | h
        · exact h
        · have hSy := mem_of_honest_anc_at hp.run hp.noColl ht hle hpH h hBy
          have hh := h_le_of_store_anc hreach
            (store_anc_of_honest_anc_at hp.run hp.noColl ht hle hpH h hBy)
          rw [← σ_eq_honest_at hp.run hp.noColl (hp.run.time_nonneg q)
            (fun _ hq => hp.run.time_mono hq.le) hv ht hle hpH hSsrc hSy] at hh
          omega
      have hSt := held hS hqt hBS'
      refine ⟨S, hSt, hBS', ?_⟩
      change (tr.state p i).fg.headHeightFloor ≤ _
      rw [← σ_eq_honest_at hp.run hp.noColl (hp.run.time_nonneg q)
        (fun _ hq => hp.run.time_mono hq.le) hv ht hle hpH hSsrc
        ((frame_tree_subset_at hp.run hp.noColl hpH hci).2 hSt)]
      exact hSf
    · rcases hfloorSource v q m S hS (hqt.le.trans (hti ▸ hib)) (lt_of_not_ge hSf) with
        ⟨z, q', n, O, E, hqi, ho, hn, hE, hEO, _, hEf⟩ | ⟨E, hE, hcov, hEf⟩
      swap
      · -- a covered floor entry: the target is below it (S1 against its member, and height)
        obtain ⟨hc, C, s, hC, hsl, hEC⟩ := coveredBefore_iff.1 hcov
        have hBE : Anc (tr.HonestBlocksAt H) B E := by
          have hBC := (ResetPremisesUpTo.compatibleWithOrigins_iff.1 hcompare).2 hc C s hC hsl
          rcases Compose.Growing.compatible_of_anc_left hac.localRun.coherent hEC hBC.symm with
            h | h
          · have hh := h_le_of_store_anc hreach
              (store_anc_of_honest_anc_at hp.run hp.noColl ht hle hpH h hBy)
            omega
          · exact h
        have hEt : E ∈ ell.frame.tree := by
          rw [hfr]
          rw [hfr] at hBt
          exact ⟨hE, hBt.2.trans
            (store_anc_of_honest_anc_at hp.run hp.noColl ht hle hpH hBE hE)⟩
        exact ⟨E, hEt, hBE, hEf⟩
      have hBO : Anc (tr.HonestBlocksAt H) B O := by
        rcases (ResetPremisesUpTo.compatibleWithOrigins_iff.1 hcompare).1 z q' n O hqi ho with h | h
        · exact h
        · have hh := h_le_of_store_anc hreach
            (store_anc_of_honest_anc_at hp.run hp.noColl ht hle hpH (hEO.trans h) hBy)
          omega
      obtain ⟨_, D, CV, _, hf, _⟩ := highOrigin_raw_head_at hp.run hp.noColl ho
      have htime : tr.time q' < sp.ts u := by
        rcases hf with ⟨ell', C, ⟨_, _, htime, _⟩, _⟩ | ⟨ell', A, _, hsl, _⟩
        · have htime' : tr.time q' = sp.ts n + 6 * sp.Δ := htime
          have hle' := hp.run.time_mono hqi.le
          rw [hti, htime'] at hle'
          rw [htime']
          simp only [ACParams.ts] at hle' ⊢
          have hΔ := sp.toParams.hΔ
          have hn2 : (n : Int) + 2 ≤ u := by
            by_contra h
            have hh : (u : Int) ≤ n + 1 := by omega
            linarith [mul_le_mul_of_nonneg_left hh hΔ.le]
          linarith [mul_le_mul_of_nonneg_left hn2 hΔ.le]
        · by_contra h
          have hh := (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg q') u).mp (not_lt.mp h)
          change sp.slot (tr.time q') = n at hsl
          omega
      have hOt := held ho htime hBO
      have hh := h_le_of_store_anc hreach
        (store_anc_of_honest_anc_at hp.run hp.noColl ht hle hpH hEO
          ((frame_tree_subset_at hp.run hp.noColl hpH hci).2 hOt))
      exact ⟨O, hOt, hBO, hEf.trans hh⟩
  obtain ⟨C, hCt, hBC, hCv⟩ := hdesc
  have hrootB' := AC.anc_tree_of_anc_U hac.localRun.coherent hPhi hPhiU hPhi.fcRoot_mem hrootB hBt
  have hBC' := AC.anc_tree_of_anc_U hac.localRun.coherent hPhi hPhiU hBt hBC hCt
  refine Or.inr ⟨hBt, hrootB', C, hCt, ?_, hBC'⟩
  have hCf : C ∈ (Node.frame (tr.state p i)).tree := hfr ▸ hCt
  have hrootC := hrootB'.trans hBC'
  rw [hfr] at hrootC ⊢
  exact ⟨hCf.1, hCf.2, Anc.mono (fun _ h => h.1) hrootC, hCv⟩

/-- The held-target proposal domain, with the high-source cover (`CompatibleWithOrigins`
for the target). -/
theorem held_target_proposal_domain_before_covered_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x p : Fin sp.n} {r i u : Nat} (hx : x ∈ H (tr.time r)) (hpH : p ∈ H (tr.time i))
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hBx : B ∈ (tr.state x r).fg.tree)
    {ell : ACLabel (goldilocksNode sp)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    (hheld : Anc (tr.HonestBlocksAt H) ell.frame.F B → B ∈ ell.frame.tree)
    (hseed : ∃ v q m S, HighOrigin tr H g v q m S ∧ tr.time q < sp.ts u ∧
      Compatible (tr.HonestBlocksAt H) B S)
    (hcompare : ResetPremisesUpTo.CompatibleWithOrigins tr H g a b i (sp.slot (tr.time i)) B) :
    Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨ B ∈ ell.frame.viableTree ell.frame.tree :=
  held_target_proposal_domain_before_of_sources_covered_at hp hx hpH hBx hci hcall hd hti hib
    hheld hseed hcompare fun _ _ _ _ ho hrb hfloor =>
      high_floor_source_at_proposal_or_covered_at hp ho hpH hci hcall hti hrb hib hfloor

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
