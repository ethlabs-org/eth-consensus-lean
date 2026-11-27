module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FastLockRenewalCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.StockWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FreshEndpoint
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.PrimedFresh
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RegularLater
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Deep
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Fast-lock candidates under the fixed-max P-U window -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {hold : Time}

/-- A unanimous warm proposal supplies candidates throughout the P-U window after its update.
The primed witness and later-head induction are used directly, without a stock window. -/
theorem toFG_candidate_pre_within_primed_at' {K : AC.CommitteeDict sp.n}
    {g ΔF b hi : Time} {s₀ u M : Nat} {isTop : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts s₀) hi M isTop J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u) (hhib : hi ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hun : ∀ x j e, x ∈ H (tr.time j) → AC.VoteAt tr.projAC x j e →
      e.msg.slot = u → e.msg.head = P.root)
    (hK : CommitteeHalfUpTo tr H K g b)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ell)
    (hlo : sp.ts (u + 1 : Nat) + 2 * sp.Δ < tr.time i) (hhi : tr.time i ≤ hi) :
    ∃ B ∈ AC.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i),
      Anc (tr.HonestBlocksAt H) P B := by
  have hΔ := sp.toParams.hΔ
  have hk := sp.two_le_k
  have hts {p q : Nat} (hpq : p ≤ q) : sp.ts p ≤ sp.ts q :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast hpq)
  have hstep (a : Nat) : sp.ts (a + 1 : Nat) = sp.ts a + 4 * sp.Δ := AC.ts_succ a
  have hsu := hts (show s₀ ≤ u by omega)
  have hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u := by linarith
  have hib := hhi.trans hhib
  have hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ hi := by linarith
  have hsub {lo hi' : Time} (hl : sp.ts s₀ ≤ lo) (hh : hi' ≤ hi) :
      FrameWindow' tr H lo hi' M isTop J := hframe.mono hl hh
  have hjoin := fun w hw => Goldilocks.Shadow.PU.Growing.joined_voteTime_of_warm_frame_at
    hrun hnr hm (by omega : s₀ + 1 ≤ u) (y := w) hw
  have hyu : y ∈ H (sp.ts (u + 1 : Nat) + 2 * sp.Δ) := hrun.antitone hlo.le hy
  obtain ⟨j₀, ell₀, hu₀, hconf₀, hnv₀, hfast₀, _, hvi₀, _⟩ :=
    Shadow.fresh_fast_lock_update_at (hsub hsu hT) hrun hnc hsvc hawake hf hcatch hnr
      hmargin hjoin (hT.trans hhib) hz hdes hP hPs hun hK hyu
  have ht₀ : tr.time j₀ = sp.ts u + 6 * sp.Δ := hu₀.2.2.1
  have hy₀ : y ∈ H (tr.time j₀) := hrun.antitone (by rw [ht₀]; linarith [hstep u]) hy
  obtain ⟨⟨hPt₀, hPg, _⟩, hPf₀⟩ := (AC.deepest_mem hfast₀).1
  obtain ⟨D₀, CV₀, hfu₀, hPD₀⟩ := Core.fast_update_of_unvetoed_at hy₀ hrun.toCore hnc hu₀
    hconf₀ hPt₀ hPg .refl hnv₀ hPf₀
  have hfr₀ := hrun.toCore.frame_of_projAC_at hy₀ hu₀.1
  have hP₀ : P ∈ (tr.state y j₀).fg.tree := by
    rw [hfr₀, Node.frame_eq, Store.toFrame_tree] at hPt₀
    exact hPt₀.1
  have htp : tr.time kP = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hP.2.2
  have hzp : z ∈ H (sp.ts u) := hrun.antitone (by linarith) hz
  have hpbound := KernelProof.proposal_window_witness hrun hnc hframe hzp hdes hP hPs
    hsu (by linarith [hstep u]) (sp.toParams.fg.faults_lt_quorum_margin
      (hf _ (by rw [← htp]; exact hrun.time_nonneg kP) (by linarith [hstep u])))
  have hzk : z ∈ H (tr.time kP) := htp ▸ hzp
  have hp := hrun.toCore.upTo (hrun.time_nonneg kP)
  have hp' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2⟩
  obtain ⟨hacc, hta, _⟩ := hp.ac_block_after z hzk (hp.accept_of_proposesAt (hnc.upTo _) hzk hp').1
  have hzpa : z ∈ H (tr.time (kP + 1)) := hta ▸ hzk
  rw [RunTrace.upTo_projAC] at hacc
  obtain ⟨ella, hca, hea⟩ := hacc
  have hra := hrun.toCore.acRun_upTo hnc (hrun.time_nonneg (kP + 1))
  have hca' := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, ((Trace.upTo_callAt _).mp hca).2⟩
  have hPpa := (AC.accept_new sp hra.localRun hzpa ⟨ella, hca', hea⟩).1 ella hca'
  rw [hrun.toCore.frame_of_projAC_at hzpa ((Trace.upTo_callAt _).mp hca').2,
    Node.frame_eq, Store.toFrame_tree] at hPpa
  have hwit := Healing.windowWitness_of_frameWindow hrun hnc hframe hzpa hPpa.1 hpbound
  set σ := sp.slot (tr.time i)
  have hσlo : sp.ts σ ≤ tr.time i :=
    (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2 le_rfl
  have huσ : u + 1 ≤ σ := by
    by_contra hn
    have hσhi : tr.time i < sp.ts (σ + 1 : Nat) := by
      by_contra hn'
      have := (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) ((σ + 1 : Nat) : Int)).1
        (not_lt.1 hn')
      omega
    have := hts (show σ + 1 ≤ u + 1 by omega)
    linarith
  obtain ⟨r, hur, hupd, hσr⟩ : ∃ r, u ≤ r ∧ sp.ts r + 6 * sp.Δ < tr.time i ∧ σ ≤ r + 2 := by
    by_cases hlate : sp.ts σ + 2 * sp.Δ < tr.time i
    · refine ⟨σ - 1, by omega, ?_, by omega⟩
      have h := hstep (σ - 1)
      rw [show σ - 1 + 1 = σ by omega] at h
      linarith
    · have hu2 : u + 2 ≤ σ := by
        by_contra hn
        have he : σ = u + 1 := by omega
        rw [he] at hlate
        exact hlate hlo
      refine ⟨σ - 2, by omega, ?_, by omega⟩
      have h1 := hstep (σ - 2)
      have h2 := hstep (σ - 1)
      rw [show σ - 2 + 1 = σ - 1 by omega] at h1
      rw [show σ - 1 + 1 = σ by omega] at h2
      linarith
  have hext : ∀ m, u + 1 ≤ m → m ≤ r + 1 → ∀ x k e, x ∈ H (tr.time k) →
      AC.VoteAt tr.projAC x k e → e.msg.slot = m →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
    intro m hm1 hm2 x k e hx hv hs
    by_cases hur' : u = r
    · subst r
      have he : m = u + 1 := by omega
      exact Shadow.unanimous_next_votes_primed_at' (hsub hsu hT) hrun hnc hsvc hawake hf hcatch hnr
        hmargin hjoin (hT.trans hhib) hz hdes hP hPs hun hK x k e hx hv
        (by
          have ht := (Compose.cast_head_fcRoot
            (hrun.toCore.acRun_upTo hnc (hrun.time_nonneg k)).localRun
            (hrun.toCore.acRun_upTo hnc (hrun.time_nonneg k)).vstart hx
            (AC.upTo_castAt.mpr ⟨le_rfl, hv.choose_spec⟩)).2
          rw [hs, he] at ht
          change tr.time k ≤ _ at ht
          linarith [hstep u]) (by omega)
    · have hreg := Healing.PU.regular_later_heads_at
        (hsub le_rfl (by rw [hstep]; linarith)) hrun hnc hsvc hawake hf hcatch hnr
        (by omega) (by omega) (by omega) hm (by omega : u + 2 ≤ r + 1)
        (by rw [hstep]; linarith) hy₀ (Or.inl ⟨CV₀, hfu₀⟩) hK
      obtain ⟨W, hW, hWr, hDW⟩ := (hreg m hm1 hm2).1 x k e hx hv hs
      exact ⟨W, hW, hWr, hPD₀.trans hDW⟩
  have hfin : ∀ x q, x ∈ H (tr.time q) → sp.ts s₀ ≤ tr.time q → tr.time q ≤ hi →
      tr.time q ≤ b → Anc (tr.HonestBlocksAt H) (tr.state x q).fg.F P := by
    intro x q hx hqlo hqhi hqb
    exact hframe.finalized_below_descendant_at hrun hnc hx hy₀ hzpa
      (sp.toParams.fg.faults_lt_quorum_margin
        (hf _ (le_max_of_le_left (hrun.time_nonneg q))
          (max_le hqb (by rw [ht₀]; linarith [hstep u])))) hqlo hqhi hPpa.1 hpbound hP₀ .refl
  obtain ⟨j, D, CV, hfu, hPD⟩ : ∃ j D CV, AC.FastUpdateAt tr.projAC y j r D CV ∧
      Anc (tr.HonestBlocksAt H) P D := by
    rcases Nat.eq_or_lt_of_le hur with rfl | hlt
    · exact ⟨j₀, D₀, CV₀, hfu₀, hPD₀⟩
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    obtain ⟨j, ellj, hu⟩ := KernelProof.update_call_of_awake_at hrun hnc hawake hnr
      (u := s + 1) (by have := hts (show u ≤ s + 1 by omega); linarith)
      (by rw [hstep]; linarith) (hrun.antitone (by rw [hstep]; linarith) hy)
    have hjt : tr.time j = sp.ts (s + 1 : Nat) + 6 * sp.Δ := hu.2.2.1
    have hyj := hrun.antitone (by rw [hjt]; linarith : tr.time j ≤ tr.time i) hy
    have hsr := hts (show s₀ ≤ s + 1 by omega)
    have hjoinr := fun w hw => Goldilocks.Shadow.PU.Growing.joined_voteTime_of_warm_frame_at
      hrun hnr hm (by omega : s₀ + 1 ≤ s + 1) (y := w) hw
    have hnr' : NoRestartUpTo tr H (gbar g) b :=
      noRestartUpTo_iff.mpr (fun w k hw hr _ => hnr w k hw hr)
    obtain ⟨C, hconf, hPC, D, hfast, hPD⟩ := Core.update_result_extends_of_finalized_at
      hrun.toCore hnc hsvc hawake hf hcatch hnr' (by linarith) hjoinr hfin hPg
      (hext (s + 1) (by omega) (by omega)) hyj hu
      (by rw [hjt]; linarith) (by rw [hjt]; linarith) (by rw [hjt]; linarith) hK
    have hlocks := Core.update_locks_compatible_of_finalized_at hrun.toCore hnc hsvc hawake hf
      hcatch hnr' (by linarith) hsr hjoinr hfin hPg (hext (s + 1) (by omega) (by omega))
      (hext (s + 2) (by omega) (by omega)) hyj hu (by rw [hjt]; linarith)
      (by rw [hjt]; linarith) hK
    have hΦ := hrun.toCore.frameIn_at hnc hyj hu.1
    have hFP : Anc (tr.HonestBlocksAt H) ellj.frame.F P := by
      rw [hrun.toCore.frame_of_projAC_at hyj hu.1, hrun.toCore.frameOf_F]
      exact hfin y j hyj (by rw [hjt]; linarith) (by rw [hjt]; linarith)
        (by rw [hjt]; linarith)
    have hDt := (AC.deepest_mem hfast).1.1.1
    have hPt := AC.frame_mem_of_between sp (hrun.toCore.coherent hnc) hΦ.1 hΦ.2 hDt hPD hFP
    have hPDf := AC.anc_tree_of_anc_U (hrun.toCore.coherent hnc) hΦ.1 hΦ.2 hPt hPD hDt
    have hPCf := AC.anc_tree_of_anc_U (hrun.toCore.coherent hnc) hΦ.1 hΦ.2 hPt hPC
      (AC.deepest_mem hconf).1.1
    exact ⟨j, Core.fast_update_of_unvetoed_at hyj hrun.toCore hnc hu hconf hPt hPg hPCf
      (Core.no_veto_of_lock_roots_compatible_at hrun.toCore hnc hyj hu.1 hPt hlocks)
      ((AC.deepest_mem hfast).1.2.trans (Nat.mul_le_mul_left 2
        (Set.ncard_le_ncard (AC.supporters_antitone sp _ ellj.frame _ _ P D hPDf)
          (Set.toFinite _))))⟩
  have hjt : tr.time j = sp.ts r + 6 * sp.Δ := by obtain ⟨ellj, C, hu, _⟩ := hfu; exact hu.2.2.1
  have hji : j < i := by
    by_contra hn
    have := hrun.time_mono (show i ≤ j by omega)
    linarith
  have hPj : P ∈ (tr.state y j).fg.tree := by
    obtain ⟨ellj, C, hu, _, hD, _⟩ := id hfu
    have hyj := hrun.antitone (hrun.time_mono hji.le) hy
    have hΦ := hrun.toCore.frameIn_at hnc hyj hu.1
    have hFP : Anc (tr.HonestBlocksAt H) ellj.frame.F P := by
      rw [hrun.toCore.frame_of_projAC_at hyj hu.1, hrun.toCore.frameOf_F]
      exact hfin y j hyj (by rw [hjt]; have := hts (show s₀ ≤ r by omega); linarith)
        ((hrun.time_mono hji.le).trans hhi) ((hrun.time_mono hji.le).trans hib)
    have hPt := AC.frame_mem_of_between sp (hrun.toCore.coherent hnc) hΦ.1 hΦ.2
      (AC.deepest_mem hD).1.1.1 hPD hFP
    rw [hrun.toCore.frame_of_projAC_at hyj hu.1, Node.frame_eq, Store.toFrame_tree] at hPt
    exact hPt.1
  have hPk : ∀ k, j ≤ k → k ≤ i → P ∈ (Node.frame (tr.state y k)).tree ∧
      (Node.frame (tr.state y k)).Anc (Node.frame (tr.state y k)).fcRoot P ∧
      P ∈ (Node.frame (tr.state y k)).viableHeads := by
    intro k hjk hki
    have hkt := hrun.time_mono hki
    have hyk := hrun.antitone hkt hy
    have hPk' : P ∈ (tr.state y k).fg.tree := Compose.Growing.tree_mono_at' hrun
      (hrun.time_nonneg k) hyk (fun q hq => hrun.time_mono hq.le) hjk hPj
    obtain ⟨hFP, hvP⟩ := hwit.held y k hyk
      (by have := hrun.time_mono hjk; rw [hjt] at this
          have := hts (show s₀ ≤ r by omega); linarith)
      (hkt.trans hhi) (sp.toParams.fg.faults_lt_quorum_margin
        (hf _ (hrun.time_nonneg k) (hkt.trans hib))) hPk'
    have hFPs := store_anc_of_honest_anc_at' hrun hnc (hrun.time_nonneg k)
      (fun q hq => hrun.time_mono hq.le) hyk hFP hPk'
    have hPt : P ∈ (Node.frame (tr.state y k)).tree := by
      rw [Node.frame_eq, Store.toFrame_tree]
      exact ⟨hPk', hFPs⟩
    have hvHead : P ∈ (Node.frame (tr.state y k)).viableHeads := by
      rw [Node.frame_eq, Store.toFrame_viableHeads]
      exact ⟨hPk', hFPs, hvP⟩
    refine ⟨hPt, ?_, hvHead⟩
    have hΦ := hrun.toCore.frameOK_at (hrun.time_nonneg k) hyk
      (fun q hq => hrun.time_mono hq.le)
    have hsubtree : (Node.frame (tr.state y k)).tree ⊆ tr.HonestBlocksAt H := by
      rw [Node.frame_eq, Store.toFrame_tree]
      exact fun B hB => ⟨y, k, tr.time k, hrun.time_nonneg k,
        (fun q hq => hrun.time_mono hq.le), hyk, hB.1⟩
    apply AC.anc_tree_of_anc_U (hrun.toCore.coherent hnc) hΦ hsubtree hΦ.fcRoot_mem _ hPt
    rw [Node.frame_eq, Store.toFrame_fcRoot]
    exact hFP
  exact Core.toFG_candidate_of_viable_head_at hrun.toCore hnc hK
    (by have := hts (show u ≤ r + 1 by omega); linarith) hfu hPD hy hc hji
    (fun x k e hx hv hs _ => hext (r + 1) (by omega) le_rfl x k e hx hv hs) hPk hib hσr

end Consensus.Goldilocks.Healing.Growing

end
