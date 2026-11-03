module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyRecordGeometry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NonfinalSuppliers
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.FloorUpdate
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepInterval
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.HeadLock

/-! # Finite adoption of an operational confirmed proposal

The same-time suffix after an actual update preserves the selected proposal in
the confirmed read. Later deadline coverage consumes an explicit continuation;
it does not construct the independent healthy preparation or repair suppliers.
-/

public section
namespace Consensus.Goldilocks.Refinement

section FiniteSupply
variable {sp : SA.SAParams}
  {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
  {g ΔF a b : Time}

/-- An actual update's fresh lock and effective record cover every read after
all calls at the update time, even if finalization has passed the proposal. -/
theorem operational_update_read_after
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u)
    (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H)
    {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell)
    (hlock : ∃ e, u + 2 ≤ e ∧ (⟨P.root, u, true, e⟩ : SA.Lock) ∈
      (tr.projAC.post j).locks)
    {J : Nat} (hJ : Regimes.CutAfter tr J (sp.ts u + 6 * sp.Δ)) :
    Anc (tr.HonestBlocks H) P
      (Regimes.readAfter tr y J (sp.ts u + 6 * sp.Δ)) := by
  obtain ⟨ex, hex, hlock⟩ := hlock
  have hΔ := sp.toParams.hΔ
  have ht : tr.time j = sp.ts u + 6 * sp.Δ := hup.2.2.1
  have hjJ : j < J := by
    by_contra hn
    have := hp.run.time_mono (show J ≤ j by omega)
    linarith [hJ.2]
  have hprefix : ∀ e ≤ J, ∀ q < e, tr.time q ≤ b :=
    fun e he q hq => (hJ.1 q (by omega)).trans hTb
  have htime : ∀ e, j ≤ e → e < J → tr.time e = sp.ts u + 6 * sp.Δ := by
    intro e hje heJ
    exact le_antisymm (hJ.1 e heJ) (ht ▸ hp.run.time_mono hje)
  have hslot : sp.slot (sp.ts u + 6 * sp.Δ) = u + 1 := by
    apply SA.slot_of_mem sp (u + 1)
    · simp only [SA.SAParams.ts]; push_cast; nlinarith
    · simp only [SA.SAParams.ts]; push_cast; nlinarith
  have hclean : Healing.cleanLabel sp a + 2 * sp.k + 1 ≤ u := by
    rw [Healing.drainTime_eq] at hR
    have := (SA.ts_le_iff sp).mp hR
    rw [Healing.cleanLabel_eq]
    omega
  obtain ⟨hPt, hconf, -, -, -, -⟩ :=
    UpTo.operational_update_selection hp hc hpH hdesignated hactual hPs hR hgu hTb hy hup
  have hRaw : SA.ResultAt tr.projAC y j u P
      (SA.fastCounted sp (tr.projAC.state y j) ell.frame u P) :=
    ⟨ell, hup, hconf, rfl⟩
  have hframes : ∀ e ≤ J, Compatible (tr.HonestBlocks H) (tr.state y e).fg.F P :=
    fun e he => hp.finalized_compatible_clean_source hc hy hy (Or.inl hRaw)
      hclean (ht ▸ hTb) (hprefix e he)
  have hbase := effective_record_after_ac_call hp.run hy hup.1
    (UpTo.operational_update_effective_record hp hc hpH hdesignated hactual hPs hR hgu hTb
      hy hup)
  have hinterval : EffectiveRecordInterval tr H y (j + 1) J P := by
    apply effectiveRecordInterval_of_candidates_before hp hy
    · intro q hjq hqJ D s CV hsource
      have hqt := htime q (by omega) hqJ
      rcases hsource with ⟨ell', hu', hD, -⟩ | ⟨ell', A', -, -, hsel, -⟩
      · have hsu : s = u := by
          have hs : tr.time q = sp.ts s + 6 * sp.Δ := hu'.2.2.1
          have := (SA.ts_le_iff sp).mp (show sp.ts s ≤ sp.ts u by linarith)
          have := (SA.ts_le_iff sp).mp (show sp.ts u ≤ sp.ts s by linarith)
          omega
        subst s
        have hP := (UpTo.operational_update_selection hp hc hpH hdesignated hactual hPs
          hR hgu hTb hy hu').2.1
        have : D = P := Option.some.inj (hD.symm.trans hP)
        subst D
        exact Or.inl .refl
      · have hlate : sp.ts (sp.slot (tr.time q)) + 2 * sp.Δ ≤ tr.time q := by
          simp only [hqt, hslot]
          simp only [SA.SAParams.ts, Nat.cast_add, Nat.cast_one]
          linarith
        change SA.optimisticSelect sp A' ell'.frame (tr.time q) = some D at hsel
        simp only [SA.optimisticSelect, hlate, or_true, ↓reduceIte] at hsel
        cases hsel
    · intro q _ hqJ
      exact hframes (q + 1) (by omega)
  have hrecord := effective_record_of_interval hp.run hp.noColl hy (by omega) hinterval hbase
  have hΦ := Compose.frameOK_state hp.run.toLocalRun hy J
  have hΦU : (Node.frame (tr.state y J)).tree ⊆ tr.HonestBlocks H :=
    fun X hX => ⟨y, hy, J, hX.1⟩
  have hhead : Anc (tr.HonestBlocks H) P
      (SA.acHead sp (tr.state y J).ac (Node.frame (tr.state y J)) (sp.ts u + 6 * sp.Δ)) := by
    -- Only the nonfinalized arm needs a retained lock. Its frame membership
    -- and normalization are established before invoking lock keep.
    rcases hframes J le_rfl with hFP | hPF
    · have hF : ∀ e ≤ J, Anc (tr.HonestBlocks H) (tr.state y e).fg.F P :=
        fun e he => (Healing.run_F_mono hp.run.toLocalRun hy he).trans hFP
      have hPj : P ∈ (Node.frame (tr.state y j)).tree :=
        (Compose.frame_of_projAC hp.run hy hup.1) ▸ hPt
      have hPe : ∀ e, j ≤ e → e ≤ J → P ∈ (Node.frame (tr.state y e)).tree := by
        intro e hje heJ
        have hheld := Compose.tree_mono hp.run.toLocalRun hy hje hPj.1
        exact ⟨hheld, Compose.honest_held_anc hp.run hp.noColl hy (hF e heJ) hheld⟩
      have hPU : P ∈ tr.HonestBlocks H := ⟨y, hy, j, hPj.1⟩
      have hun := hp.operational_unanimous hc hpH hdesignated hactual hPs hR
        (show sp.ts u ≤ b by linarith)
      have hRnext := hR.trans ((SA.ts_le_iff sp).mpr
        (show (u : Int) ≤ (u + 1 : Nat) by omega))
      have hu : 0 < u := by
        rw [Healing.drainTime_eq] at hR
        have := (SA.ts_le_iff sp).mp hR
        omega
      obtain ⟨v, r, m, S, hseed, hrb, -, hrt⟩ := hp.reset_seed_before_slot hRnext
      have hSP := UpTo.high_origins_before_next_slot_below hp hc hPU
        (fun z hz q e hv hqb hs => hun z hz q e hv hs hqb) hgu hRnext
        (by linarith) hseed hrt hrb
      have hva : ∀ e, j ≤ e → e ≤ J →
          (Node.frame (tr.state y e)).viableAncestor P = P := by
        intro e hje heJ
        apply SA.viableAncestor_self (Compose.frameOK_state hp.run.toLocalRun hy e)
          (hPe e hje heJ)
        exact (UpTo.held_target_ancestor_candidate_at_state hp hy (hprefix e heJ)
          (hPe e hje heJ) hseed hrb hSP (fun x q l B hqe ho =>
            (UpTo.high_origin_compatible_before_update hp hc hPU hPs hu
              (fun z hz q e hv hqb hs => hun z hz q e hv hs hqb) hgu hRnext hTb ho
              (hJ.1 q (by omega))).symm)).symm
      have hlock' : (⟨P.root, u, true, ex⟩ : SA.Lock) ∈ (tr.state y (j + 1)).ac.locks := by
        rw [← Compose.projAC_state hp.run.toLocalRun hy,
          tr.projAC.state_succ_of_call hup.1]
        exact hlock
      have hkept := Compose.lock_keep_interval_view hp.run hy (show j + 1 ≤ J by omega)
        hlock' (B := P) rfl (fun e hje heJ => by
          have he := htime e (by omega) heJ
          refine ⟨?_, hPe e (by omega) heJ.le, hva e (by omega) heJ.le, ?_⟩
          · simp only [he, hslot]; have := sp.two_le_k; omega
          · intro ell' _; left; simp only [he, hslot]; omega)
      have hlive : P ∈ SA.liveLockBlocks sp (tr.state y J).ac.locks
          (Node.frame (tr.state y J)) (sp.ts u + 6 * sp.Δ) := by
        refine ⟨hPe J hjJ.le le_rfl, ⟨P.root, u, true, ex⟩, ?_, rfl⟩
        refine ⟨⟨P.root, u, true, ex⟩, hkept, P, hPe J hjJ.le le_rfl, rfl, ?_, ?_⟩
        · simp only [SA.Lock.LiveAt, hslot]; omega
        · rw [hva J hjJ.le le_rfl]
      apply Anc.mono hΦU
      apply SA.anc_getHead_of_compat hΦ (Or.inl hlive) ?_ (fun _ h => h.1) _ _ .refl
      intro L hL
      obtain ⟨l, hl, B, hB, hBr, hlive, hLB⟩ := SA.mem_liveLockBlocks hΦ hL
      have hPB := hp.clean_source_stored_lock_compatible hc hy hy (Or.inl hRaw)
        hclean (ht ▸ hTb) (hprefix J le_rfl)
        (by rw [Compose.projAC_state hp.run.toLocalRun hy]; exact hl)
        (Healing.drain_stored_lock_label (hR.trans (by linarith)) hlive) (hΦU hB) hBr
      have hanc : Anc (tr.HonestBlocks H) L B := by
        rw [hLB]
        exact (SA.viableAncestor_anc hΦ hB).2.mono hΦU
      have hLP : Compatible (tr.HonestBlocks H) L P := by
        rcases hPB with h | h
        · exact SA.anc_total hp.honest_coherent hanc h
        · exact Or.inl (hanc.trans h)
      exact hLP.elim
        (fun h => Or.inl (SA.anc_tree_of_anc_U hp.honest_coherent hΦ hΦU hL.1 h
          (hPe J hjJ.le le_rfl)))
        (fun h => Or.inr (SA.anc_tree_of_anc_U hp.honest_coherent hΦ hΦU
          (hPe J hjJ.le le_rfl) h hL.1))
    · exact hPF.trans ((hΦ.rooted.2 _ (SA.getHead_mem' hΦ
        (fun _ h => h.1) _ _ _ _)).mono hΦU)
  exact (exposed_prefix_preserved_of_record_head hp.honest_coherent hΦ hΦU).mpr
    ⟨hrecord, hhead⟩

/-- Every honest reader adopts the actual proposal at the end of its update time. -/
theorem operational_proposal_read_after
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u)
    (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    (hlocks : ∀ y ∈ H, ∀ j (ell : ACLabel (goldilocksNode sp ro)),
      SA.UpdateAt tr.projAC y j u ell →
      ∃ e, u + 2 ≤ e ∧ (⟨P.root, u, true, e⟩ : SA.Lock) ∈ (tr.projAC.post j).locks) :
    ∀ y ∈ H, ∀ J,
      Regimes.CutAfter tr J (sp.ts u + 6 * sp.Δ) →
      Anc (tr.HonestBlocks H) P
        (Regimes.readAfter tr y J (sp.ts u + 6 * sp.Δ)) := by
  intro y hy J hJ
  have hstart : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) ≤ sp.ts u := by
    have hg := (SA.ts_le_iff_le_slot sp (SA.gbar_nonneg g) (sp.slot (SA.gbar g))).mpr le_rfl
    have hbound : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) =
        sp.ts (sp.slot (SA.gbar g)) + 4 * sp.Δ := by
      simp only [SA.SAParams.ts]; push_cast; ring
    rw [hbound]
    linarith
  obtain ⟨j, ell, -, hup, -⟩ := hp.update_toFG_calls hy hstart hTb
  exact operational_update_read_after hp hc hpH hdesignated hactual hPs hR hgu hTb hy hup
    (hlocks y hy j ell hup) hJ

end FiniteSupply

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- Initial finite adoption and an independent later-read continuation give
deadline coverage for the same actual confirmed proposal. -/
theorem healthy_confirmed_coverage_of_service
    (Q : ConfirmedQuery S A V) (P : ConfirmedProposal S A V Q)
    {a ΔF : Time} {u : Nat}
    (hp : Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
      (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2)
      Q.gst ΔF a Q.run.2.horizon)
    (hc : Healing.CatchRun Q.trace (honestKeys S Q.run.2)
      Q.gst (2 * Q.params.Δ))
    (hdesignated : P.block.proposer = runProposer S Q.run.2 Q.hn u)
    (hPs : P.block.slot = u)
    (hR : Healing.drainTime Q.params a ≤ Q.params.ts u)
    (hgu : SA.gbar Q.gst + 4 * Q.params.Δ ≤ Q.params.ts u)
    (hmargin : Q.params.ts u + 6 * Q.params.Δ ≤ Q.deadline)
    (hlocks : ∀ y ∈ honestKeys S Q.run.2, ∀ j ell,
      SA.UpdateAt Q.trace.projAC y j u ell →
      ∃ e, u + 2 ≤ e ∧ (⟨P.block.root, u, true, e⟩ : SA.Lock) ∈ (Q.trace.projAC.post j).locks)
    (hcut : ∃ i, Regimes.CutAfter Q.trace i (Q.params.ts u + 6 * Q.params.Δ))
    (hcontinue : ∀ y i j,
      Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) Q.duration y Q.deadline →
      Regimes.CutAfter Q.trace i (Q.params.ts u + 6 * Q.params.Δ) →
      Regimes.CutAfter Q.trace j Q.deadline →
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2))
        (Regimes.readAfter Q.trace y i (Q.params.ts u + 6 * Q.params.Δ))
        (Regimes.readAfter Q.trace y j Q.deadline)) :
    ∀ y j, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) Q.duration y Q.deadline →
      Regimes.CutAfter Q.trace j Q.deadline →
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) P.block
        (Regimes.readAfter Q.trace y j Q.deadline) := by
  obtain ⟨i, hi⟩ := hcut
  intro y j hy hj
  exact (operational_proposal_read_after hp hc P.ready.1 hdesignated P.proposal hPs hR hgu
    (hmargin.trans Q.bounded) hlocks y hy.1 i hi).trans (hcontinue y i j hy hi hj)

end Consensus.Goldilocks.Refinement
