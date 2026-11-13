module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.ServiceCarry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.CompatibleSides
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Same-slot result comparison using only warm service

Each side releases votes before its own compromise. Only those releases are relayed;
neither writer is required to remain honest at the other writer's observation.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload Vote gbar)
open Compose.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

private def Released (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (X : Fin sp.n) (s : Nat) (D : SA.Blk sp.n (List (FG.Att sp.n))) : Set (Fin sp.n) :=
  {u | ∃ v : Vote sp.n, v.val = u ∧ v.slot = s ∧
    (∃ R ∈ tr.HonestBlocksAt H, R.root = v.head ∧ Anc (tr.HonestBlocksAt H) D R) ∧
    ∃ k, X ∈ H (tr.time k) ∧ tr.projAC.SendOrAdmit X k v ∧ sp.ts s ≤ tr.time k ∧
      tr.time k < sp.ts s + 2 * sp.Δ}

private theorem released_of_fwd
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {d : Time}
    (hd : 0 ≤ d) {X : Fin sp.n} (hX : X ∈ H d) {s : Nat}
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {u : Fin sp.n}
    (hu : u ∈ SA.Fwd (tr.projAC.upTo d) ((tr.upTo d).HonestBlocks (H d)) X s D) :
    u ∈ Released tr H X s D := by
  obtain ⟨v, hvu, hvs, ⟨R, hR, hRr, hDR⟩, k, hsend, h1, h2⟩ := SA.fwd_iff.1 hu
  obtain ⟨hkd, hsend⟩ := (ac_sendOrAdmit_upTo hrun.time_mono).1 hsend
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono hd
  exact ⟨v, hvu, hvs, ⟨R, hsub hR, hRr, hDR.mono hsub⟩, k,
    hrun.antitone hkd hX, hsend, h1, h2⟩

private theorem result_side
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {Y : Fin sp.n} {c s : Nat}
    (hY : Y ∈ H (tr.time c)) {D : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hR : SA.ResultAt tr.projAC Y c s D CV) :
    ∃ (ell : ACLabel (goldilocksNode sp ro)) (S : Set (Fin sp.n)),
      tr.projAC.CallAt Y c ell ∧ tr.time c = sp.ts s + 6 * sp.Δ ∧
      (∀ k ≤ c, tr.projAC.RestartAt Y k → tr.time k ≤ sp.ts s) ∧
      (SA.voters {v | v ∈ (tr.projAC.state Y c).pool s}).ncard < 2 * S.ncard ∧
      S ⊆ Released tr H Y s D ∧
      ∀ u ∈ S, u ∉ SA.equivocators {v | v ∈ (tr.projAC.state Y c).pool s} ∧
        ∃ v ∈ (tr.projAC.state Y c).pool s, v.val = u ∧
          ∃ R ∈ tr.HonestBlocksAt H, R.root = v.head ∧ Anc (tr.HonestBlocksAt H) D R := by
  have hd := hrun.time_nonneg c
  have hr := acRun_upTo hrun hnc hd
  have hst := projAC_upTo_state hrun (y := Y) (le_refl (tr.time c))
  have hmaj := SA.result_majority hR
  obtain ⟨ell, hu, -, rfl⟩ := hR
  have hu' := (sa_updateAt_upTo hrun.time_mono).2 ⟨le_rfl, hu⟩
  obtain ⟨-, hPhiU⟩ := frameIn_at hrun hnc hY hu.1
  refine ⟨ell, _, hu.1, hu.2.2.1, fun k hk hrk => ?_, hmaj, ?_, ?_⟩
  · exact Compose.update_restarts hr.localRun hY hu' k hk
      ((ac_restartAt_upTo tr.projAC).2 ⟨hrun.time_mono hk, hrk⟩)
  · rintro u ⟨v, ⟨hvp, -, hres, R, hR, hRr, hDR⟩, rfl⟩
    have hvp' : v ∈ ((tr.projAC.upTo (tr.time c)).state Y c).pool s := hst.symm ▸ hvp
    have hvs := SA.state_pool_slot sp hr.localRun hY c s v hvp'
    obtain ⟨k, hsend, h1, h2⟩ := SA.admitted_of_held hr.localRun hY hvs hvp' le_rfl
      (fun k _ hstk => by
        rw [hst] at hstk
        have hst' : (tr.projAC.state Y c).voteStamp v < SA.ETime.of (sp.ts s + 2 * sp.Δ) := by
          unfold SA.resolutionTime at hres
          split at hres
          · exact absurd hres (by simp [SA.ETime.of])
          · split_ifs at hres
            · exact absurd hres (by simp [SA.ETime.of])
            · exact lt_of_le_of_lt (le_max_left _ _) hres
        rw [hstk] at hst'
        exact WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hst'))
    obtain ⟨hkc, hsend⟩ := (ac_sendOrAdmit_upTo hrun.time_mono).1 hsend
    exact ⟨v, rfl, hvs, ⟨R, hPhiU hR, hRr, Anc.mono hPhiU hDR⟩, k,
      hrun.antitone hkc hY, hsend, h1, h2⟩
  · rintro u ⟨v, ⟨hvp, hne, -, R, hR, hRr, hDR⟩, rfl⟩
    exact ⟨hne, v, hvp, rfl, R, hPhiU hR, hRr, Anc.mono hPhiU hDR⟩

private theorem optimistic_side
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {X : Fin sp.n} {k s : Nat}
    (hX : X ∈ H (tr.time k)) {D : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hop : SA.OptimisticLockAt tr.projAC X k s D CV)
    (hstock : sp.committeeSize = sp.n) :
    ∃ S : Set (Fin sp.n), 3 * sp.n ≤ 4 * S.ncard ∧ S ⊆ Released tr H X s D := by
  have hd := hrun.time_nonneg k
  obtain ⟨ell, A, -, -, h34, hfwd⟩ := SA.optimistic_side (acRun_upTo hrun hnc hd) hX
    ((sa_optimisticLockAt_upTo hrun.time_mono).2 ⟨le_rfl, hop⟩)
  rw [hstock] at h34
  exact ⟨_, h34, fun u hu => released_of_fwd hrun hd hX (hfwd hu)⟩

private theorem released_held
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    {X Y : Fin sp.n} {c s : Nat} (hm : gbar g ≤ sp.ts s)
    {ell : ACLabel (goldilocksNode sp ro)} (hY : Y ∈ H (tr.time c))
    (hc : tr.projAC.CallAt Y c ell) (ht : tr.time c = sp.ts s + 6 * sp.Δ)
    (hrs : ∀ k ≤ c, tr.projAC.RestartAt Y k → tr.time k ≤ sp.ts s)
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {u : Fin sp.n}
    (hu : u ∈ Released tr H X s D) :
    ∃ v : Vote sp.n, v.val = u ∧
      (∃ R ∈ tr.HonestBlocksAt H, R.root = v.head ∧ Anc (tr.HonestBlocksAt H) D R) ∧
      (v ∈ (tr.projAC.state Y c).pool s ∨
        u ∈ SA.equivocators {w | w ∈ (tr.projAC.state Y c).pool s}) := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨v, rfl, hvs, hR, k, hX, hsend, h1, h2⟩ := hu
  refine ⟨v, rfl, hR, ?_⟩
  have hr := acRun_upTo hrun hnc (hrun.time_nonneg c)
  have hrs' : ∀ k' ≤ c, tr.projAC.RestartAt Y k' → tr.projAC.time k' ≤ tr.time k :=
    fun k' hk' hr' => (hrs k' hk' hr').trans h1
  have hdl := Compose.ac_deadline_le_of_restarts (T := tr.projAC) hrs' (tr.time k)
  change tr.projAC.deadline Y c (tr.time k) ≤ max (tr.time k) (tr.time k) + sp.Δ at hdl
  rw [max_self] at hdl
  have hsync := service_syncACAt hrun hsvc (lo := sp.ts s) (hi := tr.time c)
    ((SA.le_gbar g).trans hm)
  obtain ⟨q, hqc, hq0, hq, hqd⟩ := hsync.1 X k v hX hsend h1
    (by change tr.time k ≤ tr.time c; linarith) Y c ell hY hc
    (by change tr.projAC.deadline Y c (tr.time k) ≤ tr.time c; linarith)
  have hserv : SA.MessageServedBefore tr.projAC Y c (tr.time k) v :=
    (SA.messageServedBefore_iff _ _ _ _).mpr (Or.inl ⟨q, hqc, hq0, hq, hqd⟩)
  have h := SA.held_of_deadline_service hr.localRun hY
    (fun k' hk' hr' => hrs' k' hk' ((ac_restartAt_upTo tr.projAC).1 hr').2)
    (by change tr.time k + sp.Δ ≤ tr.time c; linarith)
    (fun t ht₁ ht₂ => by
      change tr.time k ≤ t at ht₁
      change t < tr.time k + sp.Δ at ht₂
      rw [SA.CompatibleSides.slot_of_lt (s := s) (h1.trans ht₁) (by linarith), hvs]
      omega)
    (sa_messageServedBefore_upTo (d := tr.time c) hrun.time_mono le_rfl hserv)
  rw [projAC_upTo_state hrun le_rfl, hvs] at h
  exact h

private theorem against_update
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    {X Y : Fin sp.n} {c s : Nat} (hm : gbar g ≤ sp.ts s)
    {ell : ACLabel (goldilocksNode sp ro)} (hY : Y ∈ H (tr.time c))
    (hc : tr.projAC.CallAt Y c ell) (ht : tr.time c = sp.ts s + 6 * sp.Δ)
    (hrs : ∀ k ≤ c, tr.projAC.RestartAt Y k → tr.time k ≤ sp.ts s)
    {D DY : SA.Blk sp.n (List (FG.Att sp.n))} {S T : Set (Fin sp.n)}
    (hS : ∀ u ∈ S, u ∉ SA.equivocators {v | v ∈ (tr.projAC.state Y c).pool s} ∧
      ∃ v ∈ (tr.projAC.state Y c).pool s, v.val = u ∧
        ∃ R ∈ tr.HonestBlocksAt H, R.root = v.head ∧ Anc (tr.HonestBlocksAt H) DY R)
    (hT : T ⊆ Released tr H X s D) (hncp : ¬ Compatible (tr.HonestBlocksAt H) D DY) :
    T.ncard + S.ncard ≤ (SA.voters {v | v ∈ (tr.projAC.state Y c).pool s}).ncard := by
  have hU := honestBlocksAt_coherent hrun hnc
  have held := fun {u} (hu : u ∈ Released tr H X s D) =>
    released_held hrun hnc hsvc hm hY hc ht hrs hu
  have hdisj : Disjoint T S := by
    rw [Set.disjoint_left]
    intro u hu huS
    obtain ⟨hne, v', hv', hv'u, R', hR', hR'r, hDR'⟩ := hS u huS
    obtain ⟨v, hvu, ⟨R, hR, hRr, hDR⟩, hv | heq⟩ := held (hT hu)
    · obtain rfl : v = v' := by
        by_contra h
        exact hne ⟨v, hv, v', hv', h, hvu, hv'u⟩
      obtain rfl : R = R' := hU.1 hR hR' (hRr.trans hR'r.symm)
      exact hncp (Anc.total hU hDR hDR')
    · exact hne heq
  rw [← Set.ncard_union_eq hdisj]
  refine Set.ncard_le_ncard ?_
  rintro u (hu | hu)
  · obtain ⟨v, rfl, -, hv | ⟨a, ha, -, -, -, hav, -⟩⟩ := held (hT hu)
    · exact ⟨v, hv, rfl⟩
    · exact ⟨a, ha, hav⟩
  · obtain ⟨-, v, hv, rfl, -⟩ := hS u hu
    exact ⟨v, hv, rfl⟩

/-- Same-slot results agree using only releases after the warm service threshold. -/
theorem result_result_compatible_service_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    {s : Nat} (hm : gbar g ≤ sp.ts s) {x y : Fin sp.n} {c i : Nat}
    (hx : x ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    {C D : SA.Blk sp.n (List (FG.Att sp.n))} {CV DV : Set (Vote sp.n)}
    (hC : SA.ResultAt tr.projAC x c s C CV) (hD : SA.ResultAt tr.projAC y i s D DV) :
    Compatible (tr.HonestBlocksAt H) C D := by
  by_contra hne
  obtain ⟨ell, S, hc, ht, hrs, hmaj, hSF, hS⟩ := result_side hrun hnc hx hC
  obtain ⟨ell', T, hc', ht', hrs', hmaj', hTF, hT⟩ := result_side hrun hnc hy hD
  have h1 := against_update hrun hnc hsvc hm hx hc ht hrs hS hTF (fun h => hne h.symm)
  have h2 := against_update hrun hnc hsvc hm hy hc' ht' hrs' hT hSF hne
  omega

/-- A result and an optimistic origin agree with honesty charged at their own observations. -/
theorem result_optimistic_compatible_service_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    {s : Nat} (hm : gbar g ≤ sp.ts s) {x y : Fin sp.n} {c i : Nat}
    (hx : x ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    {C D : SA.Blk sp.n (List (FG.Att sp.n))} {CV DV : Set (Vote sp.n)}
    (hC : SA.ResultAt tr.projAC x c s C CV) (hD : SA.OptimisticLockAt tr.projAC y i s D DV)
    (hstock : sp.committeeSize = sp.n) :
    Compatible (tr.HonestBlocksAt H) C D := by
  by_contra hne
  obtain ⟨ell, S, hc, ht, hrs, hmaj, -, hS⟩ := result_side hrun hnc hx hC
  obtain ⟨T, h34, hT⟩ := optimistic_side hrun hnc hy hD hstock
  have h1 := against_update hrun hnc hsvc hm hx hc ht hrs hS hT (fun h => hne h.symm)
  have hle := Set.ncard_le_ncard
    (Set.subset_univ (SA.voters {v | v ∈ (tr.projAC.state x c).pool s}))
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hle
  omega

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
