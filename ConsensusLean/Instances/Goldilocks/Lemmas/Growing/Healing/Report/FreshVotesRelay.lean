module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesLocal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Warm-frame relay from a historical honest acceptance

The sender's acceptance is retained at its own cut; service remains owed after compromise.
Only the receiver's execution is retained through the receiving call.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A block in an honest frame has a genuine earlier honest FG acceptance, or is genesis. -/
theorem frame_block_acceptance_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {x : Fin sp.n} {q : Nat}
    (hx : x ∈ H (tr.time q)) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt x q ell) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ ell.frame.tree) :
    B = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload ∨
      ∃ k < q, x ∈ H (tr.time k) ∧ tr.AcceptAt x k B := by
  have hr := hrun.toLocalRun
  have hd := hr.time_nonneg q
  have ht : B ∈ ((tr.upTo (tr.time q)).state x q).fg.tree := by
    rw [RunTrace.upTo_state_of_le hr.time_mono le_rfl]
    rw [(hrun.cutLaw x q _ (Compose.projAC_callAt.mp hc) hx).1] at hB
    exact hB.1
  rcases Compose.tree_cases (hrun.upTo hd).toLocalRun hx ht with hg | ⟨k, hk, ha⟩
  · exact Or.inl hg
  · exact Or.inr ⟨k, hk, hr.antitone (hr.time_mono hk.le) hx,
      ((RunTrace.upTo_acceptAt _).mp ha).2⟩

/-- Post-GST AC acceptance relays with its deadline, even after sender compromise. -/
theorem accepted_relay_before_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b) (hnr : NoRestartAfter tr H (gbar g))
    {x y : Fin sp.n} {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time i)) (ha : tr.projAC.AcceptAt x i B)
    (hgi : gbar g ≤ tr.time i) (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y j ell)
    (hij : tr.time i + sp.Δ ≤ tr.time j)
    (hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧ tr.time k < tr.time i + sp.Δ := by
  have hr := hrun.toLocalRun
  have hd := hr.time_nonneg j
  have hp := hrun.upTo hd
  obtain ⟨a, rfl, ha', hta⟩ := Healing.fg_accept_before
    (hrun.upTo (hr.time_nonneg i)).toLocalRun hx
    (by rw [RunTrace.upTo_projAC]; exact ACTrace.upTo_acceptAt.mpr ⟨le_rfl, ha⟩)
  change tr.time a = tr.time (a + 1) at hta
  have ha' := ((RunTrace.upTo_acceptAt _).mp ha').2
  have hdl : tr.deadline y j (max (tr.time a) g) sp.Δ ≤ tr.time j := by
    rw [hta, max_eq_left ((SA.le_gbar g).trans hgi), ← Compose.projAC_deadline]
    have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := j)
      (fun r hrj hrs => hnr y r (hr.antitone (hr.time_mono hrj) hy)
        (Compose.projAC_restartAt.mp hrs)) (tr.time (a + 1))
    change _ ≤ max (tr.time (a + 1)) (gbar g) + sp.Δ at h
    rw [max_eq_left hgi] at h
    exact h.trans hij
  have hF : ell.frame.F = (tr.state y j).fg.F := by
    rw [(hrun.cutLaw y j _ (Compose.projAC_callAt.mp hc) hy).1]
    rfl
  obtain ⟨k, hkj, hk, hkd⟩ := hsvc.relay x a B (hta ▸ hx) ha'
    (by rw [hta]; exact (SA.le_gbar g).trans hgi) y j hy
    ⟨_, Compose.projAC_callAt.mp hc⟩ hdl (hF ▸ hFB)
  have hkj' : k < j := by
    refine lt_of_le_of_ne hkj ?_
    intro he
    subst k
    cases Option.some.inj (hk.2.symm.trans (Compose.projAC_callAt.mp hc).2)
  have hk' : (tr.upTo (tr.time j)).AcceptAt y k B :=
    (RunTrace.upTo_acceptAt _).mpr ⟨hr.time_mono hkj, hk⟩
  obtain ⟨hacc, htk, _⟩ := Healing.ac_block_after hp.toLocalRun hy hk'
  have hacc' : tr.projAC.AcceptAt y (k + 1) B := by
    rw [RunTrace.upTo_projAC] at hacc
    exact (ACTrace.upTo_acceptAt.mp hacc).2
  have hdead := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := k)
    (fun r hrk hrs => hnr y r (hr.antitone (hr.time_mono (hrk.trans hkj)) hy)
      (Compose.projAC_restartAt.mp hrs)) (tr.time (a + 1))
  change _ ≤ max (tr.time (a + 1)) (gbar g) + sp.Δ at hdead
  rw [max_eq_left hgi, Compose.projAC_deadline] at hdead
  change tr.time (k + 1) = tr.time k at htk
  refine ⟨k + 1, by omega, hacc', ?_⟩
  rw [htk]
  rw [hta, max_eq_left ((SA.le_gbar g).trans hgi)] at hkd
  exact hkd.trans_le hdead

/-- Historical frame membership relays without requiring the sender to remain honest. -/
theorem frame_relay_before_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {x y : Fin sp.n} {q j : Nat} (hx : x ∈ H (tr.time q)) (hy : y ∈ H (tr.time j))
    {ellx elly : ACLabel (goldilocksNode sp ro)}
    (hcx : tr.projAC.CallAt x q ellx) (hcy : tr.projAC.CallAt y j elly)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ellx.frame.tree)
    (hg : gbar g + 2 * sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocksAt H) elly.frame.F B) : B ∈ elly.frame.tree := by
  have hr := hrun.toLocalRun
  have hd := hr.time_nonneg j
  have hp := hrun.upTo hd
  have hc' : (tr.upTo (tr.time j)).projAC.CallAt y j elly := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hcy⟩
  have hac := Compose.goldilocks_ac_projection sp ro dg (H (tr.time j))
    (tr.upTo (tr.time j)) proposer hp (hnc.upTo _)
  have hPh := SA.frameIn_of_callAt hac.localRun hy hc'
  have hFstate : elly.frame.F = (tr.state y j).fg.F := by
    rw [Compose.frame_of_projAC hp hy hc', RunTrace.upTo_state_of_le hr.time_mono le_rfl]
    rfl
  rcases frame_block_acceptance_at hrun hx hcx hB with hgB | ⟨k, hk, hxk, ha⟩
  · obtain ⟨G, hG, hGr, hGp⟩ := SA.genesis_mem_of_call sp hac.localRun hy j elly hc'
    have hBU : B ∈ tr.HonestBlocksAt H := by
      have hs := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
      exact (SA.frameIn_of_callAt (hs.upTo (hr.time_nonneg q)).localRun hx
        ((Trace.upTo_callAt _).mpr ⟨le_rfl, hcx⟩)).2 hB
    have hcoh := Compose.Growing.honest_blocks_coherent_local hr hnc
    have he : B = G := hcoh.1 hBU
      (RunTrace.honestBlocks_upTo_subset hr.time_mono hd hG)
      ((congrArg Block.root hgB).trans hGr.symm)
    rw [he] at hF
    rcases Relation.ReflTransGen.cases_tail hF with heq | ⟨C, _, hpar⟩
    · rw [he]
      exact heq.symm ▸ hPh.1.rooted.1
    · exact (Option.some_ne_none _ (hpar.2.2.symm.trans hGp)).elim
  have hkt : tr.time k + sp.Δ ≤ tr.time j := by
    have hle := hr.time_mono hk.le
    linarith only [hle, hq]
  have accepted : ∃ a < j, tr.AcceptAt y a B := by
    by_cases hnew : gbar g ≤ tr.time k
    · have hdl : tr.deadline y j (max (tr.time k) g) sp.Δ ≤ tr.time j := by
        rw [max_eq_left ((SA.le_gbar g).trans hnew)]
        have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := j)
          (fun r _ hrs => hnr y r (hr.antitone (hr.time_mono ‹r ≤ j›) hy)
            (Compose.projAC_restartAt.mp hrs)) (tr.time k)
        change _ ≤ max (tr.time k) (gbar g) + sp.Δ at h
        rw [max_eq_left hnew] at h
        rw [← Compose.projAC_deadline]
        exact h.trans hkt
      obtain ⟨a, haj, ha, _⟩ := hsvc.relay x k B hxk ha ((SA.le_gbar g).trans hnew)
        y j hy ⟨_, Compose.projAC_callAt.mp hcy⟩ hdl (hFstate ▸ hF)
      refine ⟨a, lt_of_le_of_ne haj ?_, ha⟩
      intro he
      subst a
      cases Option.some.inj (ha.2.symm.trans (Compose.projAC_callAt.mp hcy).2)
    · have hex : ∃ k, gbar g + 2 * sp.Δ ≤ tr.time k := ⟨j, hg⟩
      have hfirst : tr.FirstCutFrom (Nat.find hex) (gbar g + 2 * sp.Δ) :=
        ⟨Nat.find_spec hex, fun a ha => not_le.1 (Nat.find_min hex ha)⟩
      have hle : Nat.find hex ≤ j := Nat.find_min' hex hg
      have hmono := Healing.run_F_mono hp.toLocalRun hy hle
      rw [RunTrace.upTo_state_of_le hr.time_mono (hr.time_mono hle)] at hmono
      rw [RunTrace.upTo_state_of_le hr.time_mono le_rfl] at hmono
      obtain ⟨a, ha, hacc⟩ := hcatch x k B hxk ha (not_le.mp hnew) y _
        (hr.antitone (hfirst.1.trans (hr.time_mono hle)) hy) hfirst
        ((hmono.mono (RunTrace.honestBlocks_upTo_subset hr.time_mono hd)).trans
          (hFstate ▸ hF))
      exact ⟨a, ha.trans_le hle, hacc⟩
  obtain ⟨a, haj, ha⟩ := accepted
  have ha' : (tr.upTo (tr.time j)).AcceptAt y a B :=
    (RunTrace.upTo_acceptAt _).mpr ⟨hr.time_mono haj.le, ha⟩
  obtain ⟨hacc, _, _⟩ := Healing.ac_block_after hp.toLocalRun hy ha'
  have hBF : Anc ((tr.upTo (tr.time j)).HonestBlocks (H (tr.time j))) elly.frame.F B := by
    obtain ⟨ella, hca, hba⟩ := hacc
    have ht := (SA.frameIn_of_callAt hac.localRun hy hca).2
      ((SA.accept_new sp hac.localRun hy ⟨ella, hca, hba⟩).1 ella hca)
    exact RunTrace.anc_upTo_of_right hr hnc hd ht hF
  exact SA.mem_tree_of_acceptAt sp hac.localRun hy hacc (by omega) hc' hBF

end Consensus.Goldilocks.Healing.Growing

end
