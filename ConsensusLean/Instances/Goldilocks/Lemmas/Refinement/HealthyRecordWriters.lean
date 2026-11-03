module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyEffective
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyRecordGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepGlobal
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Simulation

public section

/-! # Actual local writers and their retained optimistic locks

The last local change of the record supplies an actual writer and, in the
optimistic case, its post-call normalized fast lock. These temporal certificates
are separate from current-record source cover and candidate geometry. In
particular, no whole-history read invariant is assumed.
-/

namespace Consensus.Goldilocks.Refinement

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

/-- A clean optimistic writer that remains in the final frame is an ancestor
candidate at creation and every intervening cut, including the terminal cut. -/
theorem clean_optimistic_writer_candidate_interval
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {y : Fin sp.n} {q s n : Nat} {R : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (hy : y ∈ H)
    (hop : SA.OptimisticLockAt tr.projAC y q s R CV)
    (hs : Healing.cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hqn : q < n)
    (hprefix : ∀ j < n, tr.time j ≤ b)
    (hRn : R ∈ (Node.frame (tr.state y n)).tree) :
    ∀ e, q ≤ e → e ≤ n → (Node.frame (tr.state y e)).AncestorCandidate R := by
  have hqb := hprefix q hqn
  have hr := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  obtain ⟨_, _, ell, _, hpoint, hRq, _, _⟩ := SA.optimisticLockAt_spec hr hy hop
  have hframe := Compose.frame_of_projAC hp.run hy hpoint.1
  have hRq' : R ∈ (tr.state y q).fg.tree := (hframe ▸ hRq).1
  obtain ⟨v, r, l, S, hseed, hra, hrb, hdeliver⟩ := hp.reset_seed_held_at_call hc
  have haq : a + sp.Δ ≤ tr.time q := by
    have ha0 := (hp.run.time_nonneg r).trans hra
    have hnext : a < sp.ts (sp.slot a + 1 : Nat) :=
      not_le.mp ((SA.ts_le_iff_le_slot sp ha0 ((sp.slot a + 1 : Nat) : Int)).not.mpr
        (by push_cast; omega))
    have hclean : sp.ts (sp.slot a + 2 : Nat) ≤ sp.ts s := by
      apply (SA.ts_le_iff sp).mpr
      rw [Healing.cleanLabel_eq] at hs
      exact_mod_cast (show sp.slot a + 2 ≤ s by omega)
    have htime : sp.ts s ≤ tr.time q := by
      obtain ⟨_, _, _, hslot, _⟩ := hop
      exact (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg q) s).mpr (by
        change sp.slot (tr.time q) = s at hslot
        omega)
    have hΔ := sp.toParams.hΔ
    simp only [SA.SAParams.ts] at hnext hclean htime
    push_cast at hnext hclean htime
    linarith
  intro e hqe hen
  have hRe := writer_mem_frame_between hp.run hp.noColl hy hqe hen hRq' hRn
  apply guarded_seed_ancestor_candidate_at_state hp hy
    (fun j hj => hprefix j (lt_of_lt_of_le hj hen)) hRe hseed hrb
  · intro hFS
    have hFq : Anc (tr.HonestBlocks H) ell.frame.F S := by
      rw [hframe]
      exact (Healing.run_F_mono hp.run.toLocalRun hy hqe).trans hFS
    have hSq := hdeliver y hy q ell hpoint.1 haq hqb hFq
    exact Compose.tree_mono hp.run.toLocalRun hy hqe (hframe ▸ hSq).1
  · exact hp.clean_source_compatible_high_origin hc hy (Or.inr hop) hs hqb hseed hrb
  · intro x j u B hje ho
    exact hp.clean_source_compatible_high_origin hc hy (Or.inr hop) hs hqb ho
      (hprefix j (lt_of_lt_of_le hje hen))

/-- Even a retained writer before the repair update was created no earlier than
the opening slot: its held block extends the operational proposal. A writer
after the update satisfies the same bound directly by time monotonicity. -/
theorem retained_writer_slot_after_update
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {j n q : Nat}
    {ell ellq : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell) (hjn : j < n)
    {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hlookup : SA.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed = some R)
    (hcall : tr.projAC.CallAt y q ellq) (hRq : R ∈ ellq.frame.tree)
    (hrest : ∀ m, q < m → m ≤ n → (tr.state y m).ac.latestConfirmed = R.root) :
    u ≤ sp.slot (tr.time q) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  by_cases hqj : q < j
  · have hframe : Node.frame (tr.state y (j + 1)) = ell.frame := by
      have hcallj := Compose.projAC_callAt.mp hup.1
      obtain ⟨hfr, _, hfg, _⟩ := hp.run.cutLaw y hy j _ hcallj
      rw [tr.state_succ_of_call hcallj, hfr]
      exact congrArg Store.toFrame hfg
    have hpost : tr.projAC.post j = (tr.state y (j + 1)).ac := by
      rw [← Compose.projAC_state hp.run.toLocalRun hy (j + 1),
        tr.projAC.state_succ_of_call hup.1]
    have hRj := writer_mem_frame_between hp.run hp.noColl hy (by omega : q ≤ j + 1)
      (by omega : j + 1 ≤ n) ((Compose.frame_of_projAC hp.run hy hcall ▸ hRq).1)
      (SA.lookup_eq_some hlookup).1
    have hlook : SA.lookup ell.frame (tr.projAC.post j).latestConfirmed = some R := by
      rw [hpost, hrest (j + 1) (by omega) (by omega)]
      rw [hframe] at hRj
      cases he : SA.lookup ell.frame R.root with
      | none => exact False.elim (SA.lookup_eq_none he ⟨R, hRj, rfl⟩)
      | some B =>
        obtain ⟨hB, hBr⟩ := SA.lookup_eq_some he
        have heq : B = R := (SA.frameIn_of_callAt hr hy hup.1).1.coherent.1 hB hRj hBr
        exact congrArg some heq
    have hPR := operational_update_effective_record hp hc hpH hdesignated hactual hPs hR
      hgu hTb hy hup
    rw [hlook] at hPR
    simp only [Option.getD_some] at hPR
    have hslots := Anc.slot_le hp.honest_coherent hPR
    rw [hPs] at hslots
    exact hslots.1.trans (SA.frame_slot_le sp hr hy hcall R hRq)
  · have htime : sp.ts u ≤ tr.time q := by
      have ht : tr.time j = sp.ts u + 6 * sp.Δ := hup.2.2.1
      have hmono := hp.run.time_mono (show j ≤ q by omega)
      linarith [sp.toParams.hΔ]
    exact_mod_cast (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg q) u).1 htime

/-- At slot `s+2`, honest held votes in the actual unlock view extend a clean
optimistic source from slot `s`; only faulty validators can oppose it. -/
private theorem optimistic_unlock_keeps
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {q s j : Nat}
    {R : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hop : SA.OptimisticLockAt tr.projAC x q s R CV)
    (hs : Healing.cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hqb : tr.time q ≤ b)
    (hjb : tr.time j ≤ b) (hslot : sp.slot (tr.time j) = s + 2)
    (hR : R ∈ (Node.frame (tr.state y j)).tree) : Compose.UnlockKeeps tr y j R := by
  intro ell hcall
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hrun.localRun
  have hcallA := Compose.projAC_callAt.2 hcall
  obtain ⟨hfr, hst, _, _⟩ := hp.run.cutLaw y hy j _ hcall
  rw [hfr] at hst
  have hA' : ((SA.goldilocksSA sp (List (FG.Att sp.n)) ro).step y (tr.state y j).ac
      (Node.frame (tr.state y j)) (tr.time j) ell.call).1 = (tr.state y (j + 1)).ac := by
    rw [tr.state_succ_of_call hcall, hst]
  have hpool : ∀ m τ, ∀ v ∈ (tr.state y m).ac.pool τ, v.slot = τ := fun m τ v hv => by
    rw [← Compose.projAC_state hp.run.toLocalRun hy] at hv
    exact (Compose.state_pool_cap hp.run hy m τ).1 v hv
  have hpay : ∀ C ∈ (Node.frame (tr.state y j)).tree, SA.validPayload C := by
    rw [← hfr]
    exact SA.frame_validPayload sp hr hy hcallA
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have hfault := hp.faults
    have hn : 0 < sp.n := sp.toParams.hn
    change 3 * Hᶜ.ncard ≤ sp.n - 1 at hfault
    omega
  apply SA.unlockTarget_unlockView_held_of_honest_slot y ell.call hA'
    (Compose.frameOK_state hp.run.toLocalRun hy j) _ hR (hpool j) (hpool (j + 1)) hpay
    (fun v hv w hw hvH hval hsl =>
      Compose.heldVotes_honest_unique hp.run hp.noColl hy hcall hv hw hvH hval hsl) ?_ hf
  intro v hv hvH hvs Hd hHd hHdr
  obtain ⟨k, e, ⟨ell', hcast⟩, hm⟩ :
      ∃ k e, SA.VoteAt tr.projAC v.val k e ∧ e.msg = v := by
    rcases SA.mem_heldVotes.1 hv with ⟨τ, hv⟩ | ⟨τ, hv⟩ | ⟨C, hC, hv⟩
    · rw [← Compose.projAC_state hp.run.toLocalRun hy] at hv
      obtain ⟨k, _, e, he, hm⟩ := hrun.honest.pool_vote y hy j τ v hv hvH
      exact ⟨k, e, he, hm⟩
    · rw [← Compose.projAC_state hp.run.toLocalRun hy] at hv
      obtain ⟨k, _, e, he, hm⟩ := hrun.honest.pool_vote y hy (j + 1) τ v hv hvH
      exact ⟨k, e, he, hm⟩
    · have hvB : v ∈ SA.blockVotes C := hv.elim id fun hv => (hpay C hC).2 v hv
      obtain ⟨k, _, e, he, hm⟩ := hrun.honest.carried_vote y hy j ell hcallA C
        (hfr.symm ▸ hC) v hvB hvH
      exact ⟨k, e, he, hm⟩
  have hkj : k < j := Compose.cast_lt_of_slot hp.run hp.noColl hvH hcast (by simpa [hm] using hvs)
  obtain ⟨Hd', hHd', hHd'r, hRHd⟩ := hp.fast_source_votes_before hc hx (Or.inr hop)
    (by have := sp.two_le_k; omega) hqb k ((hp.run.time_mono hkj.le).trans hjb)
    v.val hvH ell' e hcast (by rw [hm]; omega)
  have hPhiU : (Node.frame (tr.state y j)).tree ⊆ tr.HonestBlocks H :=
    fun B hB => ⟨y, hy, j, hB.1⟩
  have heq : Hd' = Hd := hp.honest_coherent.1 hHd' (hPhiU hHd)
    (hHd'r.trans ((congrArg Vote.head hm).trans hHdr.symm))
  subst Hd'
  exact Or.inr (SA.anc_tree_of_anc_U hp.honest_coherent
    (Compose.frameOK_state hp.run.toLocalRun hy j) hPhiU hR hRHd hHd)

/-- The actual slot-`s` fast lock survives until the next-result deadline,
provided the held source remains a candidate. This includes slot `s+2`. -/
theorem young_optimistic_lock_persists
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {q s i n : Nat} {t : Time}
    {R : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hop : SA.OptimisticLockAt tr.projAC x q s R CV)
    (hs : Healing.cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hqb : tr.time q ≤ b)
    (hin : i ≤ n) (hread : ∀ j < n, tr.time j ≤ t) (htb : t ≤ b)
    (hyoung : t < sp.ts (s + 1 : Nat) + 6 * sp.Δ)
    (hl : ∃ e, (⟨R.root, s, true, e⟩ : SA.Lock) ∈ (tr.state y i).ac.locks)
    (hframe : ∀ j, i ≤ j → j < n → R ∈ (Node.frame (tr.state y j)).tree ∧
      (Node.frame (tr.state y j)).AncestorCandidate R) :
    ∃ e, (⟨R.root, s, true, e⟩ : SA.Lock) ∈ (tr.state y n).ac.locks := by
  sorry

/-- The next-result alternative at a specified update, so engine callers may
choose the tick known to precede their stored-clock observation. -/
theorem optimistic_result_or_finalized_at_update
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r s j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hop : SA.OptimisticLockAt tr.projAC x r s B CV)
    (hs : Healing.cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC y j (s + 1) ell)
    (hjb : tr.time j ≤ b) (hR : Healing.drainTime sp a ≤ sp.ts (s + 1 + 1 : Nat)) :
    Anc (tr.HonestBlocks H) B (tr.state y j).fg.F ∨
      ∃ D DV, SA.ResultAt tr.projAC y j (s + 1) D DV ∧ Anc (tr.HonestBlocks H) B D := by
  rcases hp.finalized_compatible_clean_source hc hx hy (Or.inr hop) hs hrb
      (fun q hq => (hp.run.time_mono hq.le).trans hjb) with hFB | hBF
  · right
    have hcut := hp.clean_window_timing
      (show Healing.cleanLabel sp a + sp.k + 2 ≤ s by have := sp.two_le_k; omega)
      (s + 1) (by omega)
    have hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts (s + 1 : Nat) := by
      have := Healing.lt_cutZ sp g
      linarith [sp.toParams.hΔ]
    apply optimistic_next_result_of_floor hp hc hx hy hop hs hrb hu hjb hgu hR
    rw [Compose.frame_of_projAC hp.run hy hu.1]
    exact hFB
  · exact Or.inl hBF

end UpTo

section Engine

open Shape

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- A healthy update no later than the stored clock has actually completed.
The equality case uses the engine tick's position, not trace-time comparison. -/
theorem update_before_stored_clock (hvalid : rho.ExecutionValid) {g ΔF a : Time}
    (hp : Healing.ResetPremisesUpTo (simTrace S rho hn) (honestKeys S rho)
      (runProposer S rho hn) (digestOf S rho) g ΔF a rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {i u : Nat}
    (hslot : (S.params (Model.pubOf E) hn).ts
      ((S.params (Model.pubOf E) hn).slot (SA.gbar g) + 1 : Nat) ≤
        (S.params (Model.pubOf E) hn).ts u)
    (ht : (S.params (Model.pubOf E) hn).ts u + 6 * (S.params (Model.pubOf E) hn).Δ ≤
      (stateAt S rho hn v i).now)
    (htb : (stateAt S rho hn v i).now ≤ rho.horizon) :
    ∃ j ell, SA.UpdateAt (simTrace S rho hn).projAC (rho.ownKey v) j u ell ∧
      j < cutMap S rho hn i := by
  let sp := S.params (Model.pubOf E) hn
  let tr := simTrace S rho hn
  let T := sp.ts u + 6 * sp.Δ
  have hT0 : 0 < T := by
    dsimp [T, SA.SAParams.ts]
    have := sp.toParams.hΔ
    positivity
  have hTb : T ≤ rho.horizon := ht.trans htb
  have hgu : SA.gbar g ≤ sp.ts u := by
    have hnext := (SA.ts_le_iff_le_slot sp (SA.gbar_nonneg g)
      ((sp.slot (SA.gbar g) + 1 : Nat) : Int)).not.mpr (by push_cast; omega)
    exact (not_le.mp hnext).le.trans hslot
  have hpub : sp.toParams.IsPublic T :=
    ⟨4 * (u : Int) + 6, by dsimp [T, SA.SAParams.ts]; ring⟩
  have hy : rho.ownKey v ∈ honestKeys S rho := honest_ownKey hv
  have hawake := hp.awake _ hy T (by dsimp [T]; linarith [sp.toParams.hΔ]) hTb
  rw [simTrace_awake_iff, awakeAt_iff] at hawake
  have hawake' : E.awake v T = true := by
    simpa only [Model.Run.ownKey, Equiv.apply_symm_apply] using hawake.1
  obtain ⟨p, he⟩ := List.mem_iff_getElem?.mp (hvalid.tick_total v hv T hT0.le hTb hawake')
  have hnr : ∀ q < i, rho.events[q]? ≠ some (.restart v T) := by
    intro q _ hrestart
    obtain ⟨_, rec, hrec, hnode, htime, ell, hlabel, hcall⟩ :=
      restart_getElem? S rho hn hrestart
    have hrs : tr.RestartAt (rho.ownKey v) (cutMap S rho hn q) := by
      refine ⟨ell, ⟨?_, ?_⟩, hcall⟩
      · rw [simTrace_node, hrec]; exact hnode
      · rw [simTrace_label, hrec, Option.map_some, hlabel]
    have htime' : tr.time (cutMap S rho hn q) = T := by
      rw [simTrace_time, hrec]; exact htime
    have hbound := Healing.restart_le_before hp hy hrs (htime' ▸ hTb)
    rw [htime'] at hbound
    have hbound' : T ≤ sp.ts (sp.slot (SA.gbar g) + 1 : Nat) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hbound
    dsimp [T] at hbound'
    linarith [sp.toParams.hΔ]
  have hpi := tick_before_stored_clock S rho hn hvalid he hT0 ht hnr
  obtain ⟨hgroup, hlen⟩ := simTrace_tick_public_group S rho hn hvalid v hv p T he hpub
  obtain ⟨hcall, htime⟩ := tick_boundary_call S rho hn hvalid hv he hpub
  obtain ⟨ell, hcallA, hcalltick⟩ : ∃ ell,
      tr.projAC.CallAt (rho.ownKey v) (cutMap S rho hn p) ell ∧
        ell.call = .tick := ⟨_, Compose.projAC_callAt.2 hcall, rfl⟩
  refine ⟨cutMap S rho hn p, ell, ⟨hcallA, hcalltick, htime, ?_⟩, ?_⟩
  · have hr := (Compose.goldilocks_ac_projection _ _ _ _ _ _ hp.run hp.noColl).localRun
    unfold SA.joined
    rcases SA.restartTime_state hr hy (cutMap S rho hn p) with h | ⟨r, hrp, hrs, h⟩
    · rw [h]; exact bot_le
    · rw [h]
      apply WithBot.coe_le_coe.mpr
      have hrb := (hp.run.time_mono hrp.le).trans (htime ▸ hTb)
      have hbound := Healing.restart_le_before hp hy (Compose.projAC_restartAt.1 hrs) hrb
      have hsl : sp.slot T = u + 1 :=
        SA.slot_of_mem sp (u + 1)
          (by dsimp [T, SA.SAParams.ts]; linarith [sp.toParams.hΔ])
          (by dsimp [T, SA.SAParams.ts]; linarith [sp.toParams.hΔ])
      change tr.time r ≤ sp.ts ((sp.slot (tr.time _) : Int) - 1)
      rw [htime, hsl]
      simpa using hbound.trans hslot
  · have hpos := List.length_pos_of_ne_nil hgroup.1
    have hmono := cutMap_mono S rho hn (Nat.succ_le_of_lt hpi)
    rw [hlen] at hmono
    omega

end Engine

end Consensus.Goldilocks.Refinement

end
