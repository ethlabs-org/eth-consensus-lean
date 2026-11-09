module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Attest
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.FG.Entries
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Cut
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.CutSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Lemmas.Tactic.Linarith
import Mathlib.Algebra.Ring.Divisibility.Basic
meta import Mathlib.Tactic.Ring

public section

/-! # Persistence cut step with faults charged at consumption

The quorum-free entry argument uses the growing FG run and the namer budget at
`t_m + 2Δ`. Only the receiving node's store transitions are retained statically.
-/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload)

private theorem public_le {sp : SAParams} {T : Time} (hT : sp.toParams.IsPublic T) {m : Nat}
    (h : T < sp.ts m + 2 * sp.Δ) : T ≤ sp.ts m + sp.Δ := by
  obtain ⟨q, rfl⟩ := hT
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have e : sp.ts m + 2 * sp.Δ = sp.Δ * (4 * m + 2) := by simp only [SA.SAParams.ts]; ring
  have e' : sp.ts m + sp.Δ = sp.Δ * (4 * m + 1) := by simp only [SA.SAParams.ts]; ring
  rw [e] at h
  rw [e']
  have h₁ : q < 4 * (m : Int) + 2 := lt_of_mul_lt_mul_left h hΔ.le
  exact mul_le_mul_of_nonneg_left (show q ≤ 4 * (m : Int) + 1 by omega) hΔ.le

private theorem exists_cut_time {sp : SAParams}
    {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {e : Node.Event (goldilocksNode sp ro)} (a : Time) :
    ∃ T : Time, sp.toParams.IsPublic T ∧ T ≤ a ∧ a ≤ T + sp.Δ ∧ (T = a → e.phase = 2) ∧
      (a = T + sp.Δ → e.phase ≤ 1) := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hph : e.phase ≤ 2 := by cases e <;> simp [Node.Event.phase]
  by_cases hpub : sp.toParams.IsPublic a
  · by_cases he : e.phase ≤ 1
    · refine ⟨a - sp.Δ, ?_, by linarith, by linarith, fun h => by linarith, fun _ => he⟩
      exact dvd_sub hpub (dvd_refl _)
    · exact ⟨a, hpub, le_rfl, by linarith, fun _ => by omega, fun h => by linarith⟩
  · refine ⟨sp.Δ * (a / sp.Δ), dvd_mul_right _ _, Int.mul_ediv_self_le hΔ.ne',
      (Int.lt_mul_ediv_self_add hΔ).le, fun h => absurd ⟨_, h.symm⟩ hpub, fun h => ?_⟩
    exact absurd ⟨a / sp.Δ + 1, h.trans (by ring)⟩ hpub

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Time → Set (Fin sp.n)} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
  {proposer : Nat → Fin sp.n} {ΔF : Time} {x : Fin sp.n} {i₀ s m : Nat}
  {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}

/-- The persistence cut invariant follows from the invariant at all earlier cuts. -/
theorem cut_inv_step (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV) (k : Nat)
    (ih : ∀ j < k, VoteInv tr H s m B j ∧ CutInv tr H s m B j) :
    CutInv tr H s m B k := by
  classical
  rw [cutInv_iff]
  rintro y hy ⟨c, hc⟩ hk₀ hk₁
  have hlocal := hrun.toLocalRun.upTo (hrun.time_nonneg k)
  have hfg := fg_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val) tr proposer
    (Compose.requirements sp ro) hrun.genesis_root_ok hrun.toLocalRun hp.noColl
  let ft : FGTrace sp.toParams (Payload sp.n) := tr.projFG.upTo (tr.time k)
  have hr := hfg.upTo (hrun.time_nonneg k)
  have hs (z : Fin sp.n) (i : Nat) (hi : i ≤ k + 1) :
      ft.store z i = tr.projFG.store z i := by
    exact congrArg Prod.fst (Trace.upTo_state tr.projFG z (i := i)
      (fun l hl => hrun.time_mono (show l ≤ k by omega)))
  have hpstate (z : Fin sp.n) (hz : z ∈ H (tr.time k)) (i : Nat) (hi : i ≤ k + 1) :
      tr.projFG.store z i = (tr.state z i).fg := by
    have h := Compose.projFG_state hlocal hz i
    rw [RunTrace.upTo_projFG,
      Trace.upTo_state tr.projFG z (fun l hl => hrun.time_mono (show l ≤ k by omega)),
      Trace.upTo_state tr z (fun l hl => hrun.time_mono (show l ≤ k by omega))] at h
    exact congrArg Prod.fst h
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hT₀ : sp.toParams.IsPublic (sp.ts (s + 1 : Nat) + sp.Δ) :=
    ⟨4 * (s + 1 : Nat) + 1, by simp only [SA.SAParams.ts]; ring⟩
  have hc' := (Trace.upTo_callAt tr).mpr ⟨le_rfl, hc⟩
  obtain ⟨j₀, e, hg, hj₀k, hkj₀⟩ := hlocal.grouped y hy k c hc'
  have hg' := (RunTrace.upTo_groupAt hrun.time_mono).mp hg |>.2
  obtain ⟨T, hTpub, hTa, haT, hTeq, haeq⟩ := exists_cut_time (e := e) (tr.time k)
  have hTle : T ≤ sp.ts m + sp.Δ := public_le hTpub (lt_of_le_of_lt hTa hk₁)
  have hrows : ∀ v j a, v ∈ H (tr.time j) → tr.projFG.SignAt v j a →
      sp.ts (s + 1 : Nat) + sp.Δ < tr.time j → tr.time j ≤ T →
      ∀ E ∈ excludedEntries tr H s B, a.T ≠ E.root := by
    rintro v j a hv ⟨src, hsc⟩ h₁ h₂ E hE
    have hsc' := Compose.projFG_callAt.mp hsc
    have hjk : j < k := by
      by_contra hjk
      have hkj := hrun.time_mono (not_lt.mp hjk)
      have hTa' : T = tr.time k := le_antisymm hTa (hkj.trans h₂)
      exact hjk (sign_before_delivery hrun hv hy hsc' hg' (hTeq hTa') hj₀k
        (le_antisymm (h₂.trans hTa) hkj))
    exact attest_not_excluded hrun hp hv ⟨src, hsc'⟩ h₁ (h₂.trans hTle)
      (fun i hi => ih i (hi.trans hjk)) E hE
  have hown : ∀ j ≤ k, ∀ X, tr.AcceptAt y j X → tr.time j = T + sp.Δ →
      X.proposer = y ∧ sp.toParams.slotTime X.slot = T + sp.Δ := by
    intro j hj X hX htj
    have hak : tr.time k = T + sp.Δ := le_antisymm haT (htj ▸ hrun.time_mono hj)
    have he1 := haeq hak
    have hX' := (Trace.upTo_callAt tr).mpr ⟨hrun.time_mono hj, hX⟩
    obtain ⟨j₂, e₂, hg₂, hj₂, hj₂'⟩ := hlocal.grouped y hy j _ hX'
    change (tr.upTo (tr.time k)).GroupAt proposer dg y j₂ (tr.time j) e₂ at hg₂
    simp only [Trace.upTo_time] at hj₂'
    rw [htj, ← hak] at hg₂
    rw [← hak]
    rcases lt_trichotomy j₂ j₀ with hlt | rfl | hgt
    · exact Compose.accept_in_tick hlocal hy hg₂
        ((hlocal.phase_order y hy y hy j₂ j₀ _ e₂ e hg₂ hg hlt).trans he1) hj₂
        (by rw [htj, ← hak] at hj₂'; exact hj₂') hX'
    · exact Compose.accept_in_tick hlocal hy hg₂ ((group_phase hg₂ hg).le.trans he1) hj₂
        (by rw [htj, ← hak] at hj₂'; exact hj₂') hX'
    · have := group_start hg hg₂ hgt.le (by omega)
      omega
  have hex : ∃ j, sp.ts s ≤ tr.time j := ⟨k, hk₀⟩
  let b := Nat.find hex
  have hbk : b ≤ k := Nat.find_min' hex hk₀
  have hb : sp.ts s ≤ tr.time b := Nat.find_spec hex
  have hmin : ∀ j < b, tr.time j < sp.ts s := fun j hj => not_le.mp (Nat.find_min hex hj)
  have hK := hp.clean.caches y b (hrun.antitone hk₀ hy) ⟨hb, hmin⟩
  have hchain : ∀ i, b ≤ i → i ≤ k → ∀ X, tr.AcceptAt y i X →
      (∀ A' ∈ (ft.store y (i + 1)).tree,
        (ft.store y (i + 1)).Anc A' X → ∀ Jb,
        (ft.store y (i + 1)).blocks
          ((ft.store y (i + 1)).σ A'.root).J = some Jb →
        Compatible (tr.HonestBlocksAt H) Jb B) ∧
      (¬ Compatible (tr.HonestBlocksAt H) X B → ∀ Pc,
        Anc (tr.HonestBlocksAt H) Pc X → Anc (tr.HonestBlocksAt H) Pc B →
        (∀ Q, Anc (tr.HonestBlocksAt H) Q X → Anc (tr.HonestBlocksAt H) Q B →
          Anc (tr.HonestBlocksAt H) Q Pc) →
        ((ft.store y (i + 1)).σ X.root).h ≤
          ((ft.store y (i + 1)).σ Pc.root).h + 1) := by
    intro i hbi hik X hX
    have hXi := (Trace.upTo_callAt tr.projFG).mpr
      ⟨hrun.time_mono hik, Compose.projFG_callAt.mpr hX⟩
    have hKb : Compatible (tr.HonestBlocksAt H) (ft.store y b).F B := by
      rw [hs y b (by omega), hpstate y hy b (by omega)]
      exact hK.1
    apply Store.scope_block_of hr hy hb hmin hKb hbi hXi
    intro E hE h A hA hAX hh hTh
    obtain ⟨hnc, z, hz, j, hjs, hjmin, ha, hne⟩ := Store.mem_excludedEntries.mp hE
    have hjk : j ≤ k := by by_contra h; exact (not_lt_of_ge hk₀) (hjmin k (by omega))
    rw [hs z j (by omega), hpstate z hz j (by omega)] at ha hne
    have hE' : E ∈ excludedEntries tr H s B :=
      ⟨hnc, z, j, hrun.antitone hk₀ hz, ⟨hjs, hjmin⟩, ha, hne⟩
    have ht : tr.time i < T + sp.Δ ∨
        (tr.time i = T + sp.Δ ∧ X.proposer = y ∧
          sp.toParams.slotTime X.slot = T + sp.Δ) := by
      rcases ((hrun.time_mono hik).trans haT).lt_or_eq with hi | hi
      · exact Or.inl hi
      · exact Or.inr ⟨hi, hown i hik X hX hi⟩
    have core := Store.Growing.quorum_free_entries sp.toParams (Payload sp.n) _ H
      (tr.HonestBlocksAt H) tr.projFG (excludedEntries tr H s B)
      (sp.ts (s + 1 : Nat) + sp.Δ) T (sp.ts m + 2 * sp.Δ) y hfg hT₀ hTpub
      (by linarith) hp.clean.fgAttCut hrows i X
      (hrun.antitone (hrun.time_mono hik) hy) (Compose.projFG_callAt.mpr hX) ht E hE' h A
    rw [hs y (i + 1) (by omega)] at hA hAX hh hTh ⊢
    exact core hA hAX hh hTh
  have hcache : ∀ j, b ≤ j → j ≤ k + 1 →
      Compatible (tr.HonestBlocksAt H) (ft.store y j).F B ∧
      Compatible (tr.HonestBlocksAt H) (ft.store y j).J B := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      intro _
      rw [hs y b (by omega), hpstate y hy b (by omega)]
      exact hK
    | succ j hbj ih =>
      intro hjk
      have ih := ih (by omega)
      rcases Store.store_step hr hy j with he | ⟨X, hX, hXo⟩ | ⟨a, -, he⟩
      · rw [he]; exact ih
      · obtain ⟨hJ, hF⟩ := Store.onBlock_FJ hXo
        have hJc : Compatible (tr.HonestBlocksAt H)
            (ft.store y (j + 1)).J B := by
          rcases hJ with hJ | hJ
          · rw [hJ]; exact ih.2
          · exact (hchain j hbj (by omega) X
              (Compose.projFG_callAt.mp ((Trace.upTo_callAt _).mp hX).2)).1 X
              (Store.accept_mem hr hy hX) .refl _ hJ
        refine ⟨?_, hJc⟩
        rcases hF with hF | hF
        · rw [hF]; exact ih.1
        · exact Store.compatible_of_anc hr.coherent (hF.mono (hr.tree_subset y hy _)) hJc
      · obtain ⟨atts, he'⟩ := (ft.store y j).onAttestation_eq a
        rw [he, he']; exact ih
  have hS : ft.store y (k + 1) = (tr.post k).fg := by
    rw [hs y (k + 1) le_rfl, hpstate y hy (k + 1) le_rfl, Trace.state_succ_of_call _ hc]
  refine ⟨?_, fun X hX => ?_⟩
  · simpa only [hS] using hcache (k + 1) (by omega) le_rfl
  · simpa only [hS] using hchain k hbk le_rfl X hX

end Consensus.Goldilocks.Compose.Growing

end
