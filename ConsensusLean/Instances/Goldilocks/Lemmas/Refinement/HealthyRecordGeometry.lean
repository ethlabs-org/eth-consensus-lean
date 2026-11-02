module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyEffective
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record

/-! # Retained-record provenance and current-frame geometry

An operational update supplies a clean source for every later retained record.
A comparable high seed with guarded local holding supplies current candidacy,
without requiring the seed to be an ancestor of the record.
-/

public section
namespace Consensus.Goldilocks.Refinement

/-- An unchanged record cannot reenter the filtered frame after its finalized floor advances. -/
theorem record_lookup_of_later
    {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i j : Nat} (hij : i ≤ j)
    (heq : (tr.state y j).ac.latestConfirmed = (tr.state y i).ac.latestConfirmed)
    {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : SA.lookup (Node.frame (tr.state y j)) (tr.state y j).ac.latestConfirmed = some R) :
    SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed = some R := by
  have hU := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  obtain ⟨hRm, hroot⟩ := SA.lookup_eq_some hR
  obtain ⟨L, hL, hLroot, _⟩ := Compose.record_origin hrun hnc hy i
  have hLR : L = R := hU.1 ⟨y, hy, i, hL⟩ ⟨y, hy, j, hRm.1⟩
    (hLroot.trans (heq.symm.trans hroot.symm))
  subst L
  have hFR : Anc (tr.HonestBlocks H) (tr.state y i).fg.F R :=
    (Anc.mono (Compose.fg_tree_subset_honest hy j)
      (Regimes.finalized_monotone sp ro dg H tr proposer hrun y hy i j hij)).trans
      (Anc.mono (Compose.fg_tree_subset_honest hy j) hRm.2)
  have hm : R ∈ (Node.frame (tr.state y i)).tree :=
    ⟨hL, Compose.honest_held_anc hrun hnc hy hFR hL⟩
  cases hk : SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed with
  | none => exact False.elim (SA.lookup_eq_none hk ⟨R, hm, hLroot⟩)
  | some B =>
    obtain ⟨hB, hrB⟩ := SA.lookup_eq_some hk
    congr 1
    exact hU.1 ⟨y, hy, i, hB.1⟩ ⟨y, hy, i, hL⟩ (hrB.trans hLroot.symm)

namespace UpTo

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a : Time}

/-- Every later archival record has an exact recent source before its cut,
even if advancing finalization has removed it from the filtered frame. -/
theorem archival_record_source_after_operational_update {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell) {n : Nat} (hjn : j < n) :
    ∃ C ∈ (tr.state y n).fg.tree,
      C.root = (tr.state y n).ac.latestConfirmed ∧
      ∃ l, u ≤ l ∧ Compose.OriginBefore tr H C l n := by
  classical
  have hind : ∀ m, j + 1 ≤ m →
      ∃ C ∈ (tr.state y m).fg.tree,
        C.root = (tr.state y m).ac.latestConfirmed ∧
        ∃ l, u ≤ l ∧ Compose.OriginBefore tr H C l m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      obtain ⟨hPt, _, _, _, _, hrecord⟩ :=
        operational_update_selection hp hc hpH hdesignated hactual hPs hR hgu hTb hy hup
      have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer
        hp.run hp.noColl).localRun
      have hc' := Compose.projAC_callAt.mp hup.1
      have hlaw := hp.run.toLocalRun.cutLaw y hy j _ hc'
      have hframe : Node.frame (tr.state y (j + 1)) = ell.frame := by
        rw [tr.state_succ_of_call hc', hlaw.1]
        exact congrArg Store.toFrame hlaw.2.2.1
      have hstate := Compose.projAC_state hp.run.toLocalRun hy (j + 1)
      rw [tr.projAC.state_succ_of_call hup.1] at hstate
      have hex : ∃ C ∈ ell.frame.tree,
          C.root = (tr.projAC.post j).latestConfirmed := by
        rw [hrecord]
        by_cases hguard : SA.AncR ell.frame P (tr.projAC.state y j).latestConfirmed
        · simp only [SA.updateLatestConfirmed, ite_eq_left hguard]
          obtain ⟨C, hC, hCr, _⟩ := hguard
          exact ⟨C, hC, hCr⟩
        · exact ⟨P, hPt, by simp only [SA.updateLatestConfirmed, ite_eq_right hguard]⟩
      obtain ⟨C, hC, hCr⟩ := hex
      have hlookup : SA.lookup ell.frame (tr.projAC.post j).latestConfirmed = some C := by
        cases hk : SA.lookup ell.frame (tr.projAC.post j).latestConfirmed with
        | none => exact False.elim (SA.lookup_eq_none hk ⟨C, hC, hCr⟩)
        | some B =>
          obtain ⟨hB, hBr⟩ := SA.lookup_eq_some hk
          exact congrArg some ((SA.frameIn_of_callAt hr hy hup.1).1.coherent.1
            hB hC (hBr.trans hCr.symm))
      rw [← hframe, hstate] at hlookup
      obtain ⟨x, hx, q, s, CV, hqj, -, hs, hsource⟩ :=
        operational_update_recent_source hp hc hpH hdesignated hactual hPs hR hgu hTb
          hy hup hlookup
      refine ⟨C, ?_, hCr.trans (congrArg SA.SAState.latestConfirmed hstate), s, hs,
        Compose.originBefore_iff.2 ⟨x, hx, q, by omega, CV, hsource⟩⟩
      rw [← hframe] at hC
      exact hC.1
    | succ m hjm ih =>
      have htree := Compose.tree_mono hp.run.toLocalRun hy (Nat.le_succ m)
      rcases Compose.record_step_origin hp.run hy m with heq | ⟨B, hB, hBr, s, CV, hsource⟩
      · obtain ⟨C, hC, hCr, s, hs, hsource⟩ := ih
        obtain ⟨x, hx, q, hqm, CV, hsource⟩ := Compose.originBefore_iff.1 hsource
        exact ⟨C, htree hC, hCr.trans heq.symm, s, hs,
          Compose.originBefore_iff.2 ⟨x, hx, q, by omega, CV, hsource⟩⟩
      · have htime : sp.ts u + 6 * sp.Δ ≤ tr.time m := by
          rw [← hup.2.2.1]
          exact hp.run.time_mono (by omega)
        have hus : u ≤ s := by
          rcases hsource with ⟨e, hu, _⟩ | ⟨e, A, ho, hslot, _⟩
          · have ht : tr.time m = sp.ts s + 6 * sp.Δ := hu.2.2.1
            have := (SA.ts_le_iff sp).mp (show sp.ts u ≤ sp.ts s by linarith)
            omega
          · have := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg m) u).mp
              (show sp.ts u ≤ tr.time m by linarith [sp.toParams.hΔ])
            change sp.slot (tr.time m) = s at hslot
            omega
        exact ⟨B, htree hB, hBr, s, hus,
          Compose.originBefore_iff.2 ⟨y, hy, m, Nat.lt_succ_self _, CV, hsource⟩⟩
  exact hind n (by omega)

/-- Every later successful record lookup has an exact raw or optimistic source
at least as recent as the operational update. No current-read geometry is used. -/
theorem record_source_after_operational_update {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell) {n : Nat} (hjn : j < n)
    {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hlookup : SA.lookup (Node.frame (tr.state y n))
      (tr.state y n).ac.latestConfirmed = some R) :
    ∃ x ∈ H, ∃ q s CV, q < n ∧ u ≤ s ∧
      (SA.ResultAt tr.projAC x q s R CV ∨ SA.OptimisticLockAt tr.projAC x q s R CV) := by
  obtain ⟨C, hC, hCr, s, hs, hsource⟩ :=
    archival_record_source_after_operational_update hp hc hpH hdesignated hactual hPs
      hR hgu hTb hy hup hjn
  obtain ⟨hR, hRr⟩ := SA.lookup_eq_some hlookup
  have heq : C = R := hp.honest_coherent.1 ⟨y, hy, n, hC⟩ ⟨y, hy, n, hR.1⟩
    (hCr.trans hRr.symm)
  subst C
  obtain ⟨x, hx, q, hq, CV, hsource⟩ := Compose.originBefore_iff.1 hsource
  exact ⟨x, hx, q, s, CV, hq, hs, hsource⟩

/-- A comparable bounded high seed, held whenever it is above finalization,
supplies current candidacy. A local signed entry witnesses any higher floor. -/
theorem guarded_seed_ancestor_candidate_at_state {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y v : Fin sp.n} (hy : y ∈ H) {i q m : Nat}
    (hib : ∀ r < i, tr.time r ≤ b) {P S : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ (Node.frame (tr.state y i)).tree)
    (hseed : Healing.HighOrigin tr H g v q m S) (hqb : tr.time q ≤ b)
    (hhold : Anc (tr.HonestBlocks H) (tr.state y i).fg.F S →
      S ∈ (tr.state y i).fg.tree)
    (hPS : Compatible (tr.HonestBlocks H) P S)
    (hcompare : ∀ x r l B, r < i → Healing.HighOrigin tr H g x r l B →
      Compatible (tr.HonestBlocks H) P B) :
    (Node.frame (tr.state y i)).AncestorCandidate P := by
  have hreach := Compose.fg_reachable hp.run.toLocalRun hy i
  have hPhi := (Store.frame_realization _ _ _ _ hreach).1
  have hPhiU : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocks H :=
    fun X hX => ⟨y, hy, i, hX.1⟩
  have hPy := hPt.1
  have hroot : Compatible (tr.HonestBlocks H) (Node.frame (tr.state y i)).fcRoot P := by
    by_cases hlow : (tr.state y i).fg.hj ≤ Healing.HZ tr H g
    · have hSy := hhold (hp.low_finalized_below_origin hy i hlow hseed)
      exact hp.low_root_of_held_seed_at_state hy hPy hy hseed hSy hlow hPS (fun _ => hPy)
    · exact hp.high_J_root_of_held_at_state_before hy hPy hy (by omega) hcompare
  rcases hroot with hroot | hroot
  swap
  · exact Or.inl (SA.anc_tree_of_anc_U hp.honest_coherent hPhi hPhiU hPt hroot hPhi.fcRoot_mem)
  have hrootf := SA.anc_tree_of_anc_U hp.honest_coherent hPhi hPhiU
    hPhi.fcRoot_mem hroot hPt
  have witness : ∃ E ∈ (tr.state y i).fg.tree,
      Anc (tr.HonestBlocks H) P E ∧
      (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ E.root).h := by
    by_cases hfloor : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ P.root).h
    · exact ⟨P, hPy, .refl, hfloor⟩
    obtain ⟨-, -, -, -, -, -, -, -, -, hSs⟩ := hp.highOrigin_mem hseed
    by_cases hSf : (tr.state y i).fg.headHeightFloor ≤ ((tr.state v q).fg.σ S.root).h
    · have hPS' : Anc (tr.HonestBlocks H) P S := by
        rcases hPS with h | h
        · exact h
        · have hSy := hp.mem_tree_of_anc hy h hPy
          have hSh := Healing.σ_h_le_of_anc hreach (hp.anc_tree_of_anc hy h hPy)
          rw [hp.σ_eq_run hseed.1 hy hSs hSy] at hSf
          omega
      have hFS : Anc (tr.HonestBlocks H) (tr.state y i).fg.F S :=
        (hPt.2.mono (fun X hX => (⟨y, hy, i, hX⟩ : X ∈ tr.HonestBlocks H))).trans hPS'
      have hSy := hhold hFS
      rw [hp.σ_eq_run hseed.1 hy hSs hSy] at hSf
      exact ⟨S, hSy, hPS', hSf⟩
    have hSf' : ((tr.state v q).fg.σ S.root).h < (tr.state y i).fg.headHeightFloor := by omega
    obtain ⟨x, r, l, B, E, hri, ho, -, hE, hEB, -, hEf, -⟩ :=
      hp.high_floor_signed_source_of_row_bound hseed hy (u := sp.slot (tr.time i) + 1)
        (fun W hW att ha z hz d hd hdi r' l O hrd ho => by
          obtain ⟨-, D, CV, -, hfl, -⟩ := hp.highOrigin_mem ho
          have ht : sp.ts l ≤ tr.time r' := by
            rcases hfl with ⟨ell, C, ⟨-, -, ht, -⟩, -⟩ | ⟨ell, A, -, hsl, -⟩
            · change tr.time r' = sp.ts l + 6 * sp.Δ at ht
              linarith [sp.toParams.hΔ]
            · change sp.slot (tr.time r') = l at hsl
              exact (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg r') l).2 (by omega)
          have := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg i) l).1
            (ht.trans (hp.run.time_mono (by omega)))
          omega)
        (fun x r l B hri ho x' r' l' B' hr'i ho' => hp.origins_compatible ho
          (hib r hri) ho' (hib r' hr'i))
        (fun x r l B hri ho => hp.origins_compatible hseed hqb ho (hib r hri)) hSf'
    have hPE : Compatible (tr.HonestBlocks H) P E := by
      rcases hcompare x r l B hri ho with h | h
      · exact SA.anc_total hp.honest_coherent h hEB
      · exact Or.inr (hEB.trans h)
    rcases hPE with hPE | hEP
    · exact ⟨E, hE, hPE, hEf⟩
    · have := Healing.σ_h_le_of_anc hreach (hp.anc_tree_of_anc hy hEP hPy)
      omega
  obtain ⟨E, hE, hPE, hEf⟩ := witness
  have hPEs := hp.anc_tree_of_anc hy hPE hE
  have hEt : E ∈ (Node.frame (tr.state y i)).tree := ⟨hE, hPt.2.trans hPEs⟩
  have hPEf := SA.anc_tree_of_anc_U hp.honest_coherent hPhi hPhiU hPt hPE hEt
  refine Or.inr ⟨hPt, hrootf, E, hEt, ?_, hPEf⟩
  have hRE := hrootf.trans hPEf
  exact ⟨hE, hPt.2.trans hPEs, Anc.mono (fun _ h => h.1) hRE, hEf⟩

end UpTo
end Consensus.Goldilocks.Refinement
