module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.PersistKernel
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Induction
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks suppliers for the conditional persistence kernel -/

namespace Consensus.Goldilocks.Compose
open SA (SAParams ReplayOrder Vote Payload)
variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Set (Fin sp.n)} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {proposer : Nat → Fin sp.n} {ΔF : Time} {x : Fin sp.n} {i₀ s m : Nat}
  {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}

private theorem cut_eq (k : Nat) : FG.Persist.CutInv tr H (sp.ts s) (sp.ts m + sp.Δ) B k ↔
    CutInv tr H s m B k := by
  have he : sp.ts m + sp.Δ + sp.Δ = sp.ts m + 2 * sp.Δ := by ring
  rw [cutInv_iff]
  simp only [FG.Persist.CutInv, he]

/-- The concrete vote step supplies only the opaque AC invariant. -/
theorem kernel_voteStep (hrun : GoldilocksRun proposer dg H tr)
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV) :
    FG.Persist.VoteStep tr H (sp.ts s) (sp.ts m + sp.Δ) B (VoteInv tr H s m B) :=
  fun k ih => vote_step hrun hp k fun j hj => ⟨(ih j hj).1, (cut_eq j).mp (ih j hj).2⟩

/-- Actual honest source compatibility, retaining stored-block provenance and strict cuts. -/
theorem kernel_sourceStep (hrun : GoldilocksRun proposer dg H tr)
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV) :
    FG.Persist.SourceStep tr H (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) (sp.ts m + sp.Δ) B
      (VoteInv tr H s m B) := by
  intro j ih v hv ℓ C hcall hto hC hlo hhi
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hp.noColl
  have hr := hrun'.localRun
  have hpc := projAC_callAt.mpr hcall
  have hToFG : SA.ToFGAt tr.projAC v j ℓ C :=
    ⟨hpc, hto, by rw [projAC_state hrun.toLocalRun hv]; exact hC⟩
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hs1 := (SA.ts_lt_iff sp).mpr (show ((s : Nat) : Int) < ((s + 1 : Nat) : Int) by omega)
  have hsm := (SA.ts_le_iff sp).mpr (Int.ofNat_le.mpr hp.lt)
  have hframe : ∀ k ≤ j, ∀ ℓk, tr.projAC.CallAt v k ℓk → sp.ts s ≤ tr.time k →
      Compatible (tr.HonestBlocks H) ℓk.frame.F B := by
    intro k hk ℓk hck hk₀
    rw [frame_of_projAC hrun hv hck]
    exact (FG.Persist.state_caches hrun.toLocalRun
      (fun y hy i h₁ h₂ => hp.clean.caches y hy i ⟨h₁, h₂⟩) k
      (fun i hi => (ih i (by omega)).2) hv hk₀
      (fun i hi => by have := hrun.time_mono (show i ≤ j by omega); linarith)).1
  have hcase : (∃ i < j, ∃ ℓ' e, SA.CastAt tr.projAC v i ℓ' e ∧ e.msg.slot = s + 1 ∧
      Compatible (tr.HonestBlocks H) ℓ'.frame.F B) ∨
      (∃ k < j, tr.projAC.RestartAt v k ∧ sp.ts s < tr.time k) := by
    refine (vote_or_restart hrun hp hv hToFG hlo).imp_left ?_
    rintro ⟨i, hi, ℓ', e, hce, hsl⟩
    have hts : sp.ts e.msg.slot ≤ tr.time i :=
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).mpr (by rw [(SA.castAt_spec hr hv hce).2.1])
    rw [hsl] at hts
    exact ⟨i, hi, ℓ', e, hce, hsl, hframe i hi.le ℓ' hce.1 (by linarith)⟩
  have hsync := syncAC_mono (sync_projection sp.toParams (goldilocksNode sp ro) dg H
    (fun v => v.val) tr proposer ΔF (sp.ts s) (sp.ts m + sp.Δ) hrun.toLocalRun hp.sync) le_rfl
    (by linarith : sp.ts (s + 1 : Nat) + sp.Δ ≤ sp.ts m + sp.Δ)
  obtain ⟨ℓw, D, hcw, hflD, hBD⟩ := hp.fastLock
  have hΦwU : ℓw.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hr.frameLaw x hp.writer_honest i₀ ℓw hcw with
      ⟨-, Φ₀, -, -, h⟩ | ⟨i, ℓ', -, -, -, h⟩ <;> exact h.1.2
  exact SA.source_compatible_stored sp _ ro proposer H _ tr.projAC hrun' s m x v i₀ j B D CV ℓ C
    hp.writer_honest hflD (hBD ▸ Anc.mono hΦwU (SA.anc_viableAncestor ℓw.frame D)) hsync
    hp.carry (faulty_lt_half hrun hp) hv hToFG hlo hhi
    (fun z hz i hi e ⟨ℓz, hcz, hez⟩ h₁ h₂ =>
      (voteInv_iff.mp (ih i hi).1 z hz ℓz e ⟨hcz, hez⟩ h₁ h₂).2) hcase

/-- A new specialization; old C1.1 proof bodies and consumers remain unchanged. -/
theorem kernel_persist_inv (hrun : GoldilocksRun proposer dg H tr)
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV) :
    ∀ k, VoteInv tr H s m B k ∧ CutInv tr H s m B k := by
  have hpub : ∀ r : Nat, sp.toParams.IsPublic (sp.ts r + sp.Δ) := fun r =>
    ⟨4 * r + 1, by simp only [SA.SAParams.ts]; ring⟩
  have hK1 : ∀ E ∈ Store.excludedEntries H (tr.HonestBlocks H) tr.projFG (sp.ts s) B,
      E ∈ excludedEntries tr H s B := by
    intro E hE
    obtain ⟨hnc, z, hz, j, h₁, h₂, h₃, h₄⟩ := Store.mem_excludedEntries.mp hE
    have he : tr.projFG.store z j = (tr.state z j).fg := by
      change (tr.projFG.state z j).1 = _; rw [projFG_state hrun.toLocalRun hz]
    rw [he] at h₃ h₄
    exact ⟨hnc, z, hz, j, ⟨h₁, h₂⟩, h₃, h₄⟩
  have hi := FG.Persist.contract tr H proposer (fun v => v.val) dg (Compose.requirements sp ro)
    hrun.toLocalRun hrun.genesis_root_ok hp.noColl (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ)
    (sp.ts m + sp.Δ) B (VoteInv tr H s m B) (hpub _) (hpub _)
    (fun y hy j h₁ h₂ => hp.clean.caches y hy j ⟨h₁, h₂⟩)
    (fun E hE => hp.clean.fgAttCut E (hK1 E (Store.mem_excludedEntries.mpr hE)))
    (kernel_voteStep hrun hp) (kernel_sourceStep hrun hp)
  exact fun k => ⟨(hi k).1, (cut_eq k).mp (hi k).2⟩

end Consensus.Goldilocks.Compose
