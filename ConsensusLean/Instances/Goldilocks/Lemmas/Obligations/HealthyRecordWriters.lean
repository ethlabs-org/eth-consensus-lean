module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyEffective
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSimulates
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee

public section

/-! # Actual local writers and their retained optimistic locks

The last local change of the record supplies an actual writer and, in the
optimistic case, its post-call normalized fast lock. These temporal certificates
are separate from current-record source cover and candidate geometry. In
particular, no whole-history read invariant is assumed.
-/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

private theorem last_change {f : Nat → Nat} {n : Nat} (hne : f n ≠ f 0) :
    ∃ q < n, f (q + 1) ≠ f q ∧ ∀ m, q < m → m ≤ n → f m = f n := by
  induction n with
  | zero => exact False.elim (hne rfl)
  | succ n ih =>
    by_cases hstep : f (n + 1) = f n
    · obtain ⟨q, hqn, hq, hrest⟩ := ih (fun h => hne (hstep.trans h))
      refine ⟨q, by omega, hq, fun m hqm hmn => ?_⟩
      rcases Nat.eq_or_lt_of_le hmn with rfl | hmn
      · rfl
      · exact (hrest m hqm (by omega)).trans hstep.symm
    · refine ⟨n, by omega, hstep, fun m hnm hmn => ?_⟩
      have : m = n + 1 := by omega
      rw [this]

/-- A changed own record identifies its actual call, selected block and, for an
optimistic selection, the normalized lock left by that same call. -/
theorem record_changed_writer (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {q : Nat}
    (hne : (tr.state y (q + 1)).ac.latestConfirmed ≠ (tr.state y q).ac.latestConfirmed) :
    ∃ ell, tr.projAC.CallAt y q ell ∧
      ∃ R ∈ ell.frame.tree, (tr.state y (q + 1)).ac.latestConfirmed = R.root ∧
        ((∃ s CV, SA.ResultAt tr.projAC y q s R CV) ∨
          ((∃ CV, SA.OptimisticLockAt tr.projAC y q (sp.slot (tr.time q)) R CV) ∧
            ∃ e, (⟨(ell.frame.viableAncestor R).root, sp.slot (tr.time q), true, e⟩ : SA.Lock) ∈
              (tr.state y (q + 1)).ac.locks)) := by
  obtain ⟨B, _, _, s, CV, hs⟩ := (Compose.record_step_origin hrun hy q).resolve_left hne
  obtain ⟨ell, hcall⟩ : ∃ ell, tr.projAC.CallAt y q ell := by
    rcases hs with ⟨ell, hu, _⟩ | ⟨ell, A, ho, _⟩
    · exact ⟨ell, hu.1⟩
    · exact ⟨ell, ho.1⟩
  have hpost : tr.projAC.post q = (tr.state y (q + 1)).ac := by
    rw [← Compose.projAC_state hrun.toLocalRun hy (q + 1), tr.projAC.state_succ_of_call hcall]
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hw := Compose.call_record_writer hr hy hcall
    (by rw [hpost, Compose.projAC_state hrun.toLocalRun hy]; exact hne)
  rw [hpost] at hw
  exact ⟨ell, hcall, hw⟩

/-- A non-genesis current record has a last own writer, with unchanged record
roots thereafter and the actual creation lock in the optimistic case. -/
theorem last_record_writer (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {n : Nat}
    {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : SA.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed = some R)
    (hgen : R.root ≠ sp.genesisRoot) :
    ∃ q < n, ∃ ell, tr.projAC.CallAt y q ell ∧ R ∈ ell.frame.tree ∧
      (∀ m, q < m → m ≤ n → (tr.state y m).ac.latestConfirmed = R.root) ∧
      ((∃ s CV, SA.ResultAt tr.projAC y q s R CV) ∨
        ((∃ CV, SA.OptimisticLockAt tr.projAC y q (sp.slot (tr.time q)) R CV) ∧
          ∃ e, (⟨(ell.frame.viableAncestor R).root, sp.slot (tr.time q), true, e⟩ : SA.Lock) ∈
            (tr.state y (q + 1)).ac.locks)) := by
  obtain ⟨hRm, hRroot⟩ := SA.lookup_eq_some hR
  have hzero : (tr.state y 0).ac.latestConfirmed = sp.genesisRoot := by
    have hinit : tr.state y 0 = Node.init _ := hrun.init y hy
    rw [hinit]; rfl
  obtain ⟨q, hqn, hchange, hrest⟩ :=
    last_change (f := fun m => (tr.state y m).ac.latestConfirmed) (n := n)
      (by rw [← hRroot, hzero]; exact hgen)
  obtain ⟨ell, hcall, B, hB, hBroot, hsource⟩ := record_changed_writer hrun hnc hy hchange
  have hfr := Compose.frame_of_projAC hrun hy hcall
  have hBU : B ∈ tr.HonestBlocks H := ⟨y, hy, q, (hfr ▸ hB).1⟩
  have heq : B = R := (Compose.honest_blocks_coherent hrun.toLocalRun hnc).1
    hBU ⟨y, hy, n, hRm.1⟩
    (hBroot.symm.trans ((hrest (q + 1) (by omega) (by omega)).trans hRroot.symm))
  subst B
  exact ⟨q, hqn, ell, hcall, hB, fun m hqm hmn => (hrest m hqm hmn).trans hRroot.symm,
    hsource⟩

/-- Creation-time holding plus a later finalized-floor guard keeps the writer's
block in every intervening filtered frame, not only in the archival store. -/
theorem writer_mem_frame_between (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {q e n : Nat}
    (hqe : q ≤ e) (hen : e ≤ n) {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hRq : R ∈ (tr.state y q).fg.tree) (hRn : R ∈ (Node.frame (tr.state y n)).tree) :
    R ∈ (Node.frame (tr.state y e)).tree := by
  have hRe := Compose.tree_mono hrun.toLocalRun hy hqe hRq
  have hFR : Anc (tr.HonestBlocks H) (tr.state y e).fg.F R :=
    (Healing.run_F_mono hrun.toLocalRun hy hen).trans
      (hRn.2.mono (Compose.fg_tree_subset_honest hy n))
  exact ⟨hRe, Compose.honest_held_anc hrun hnc hy hFR hRe⟩

namespace UpTo

variable {g ΔF a b : Time}

end UpTo

end Consensus.Goldilocks.Obligations

end
