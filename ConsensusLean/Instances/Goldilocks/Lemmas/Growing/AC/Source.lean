module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Base
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Compatible
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Source age at an honest call

The source's lock history is local to the caller, so retention at the call preserves it.
-/

namespace Consensus.Goldilocks.AC.Growing

private theorem source_age_const (sp : ACParams)
    {FGP : Type} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP}
    (hrun : ACLocalRun (goldilocksAC sp FGP) H U tr)
    (τ : Time) (x : Fin sp.n) (i : Nat) (ℓ : ACLabel (goldilocksAC sp FGP))
    (C : Blk sp.n FGP) (hx : x ∈ H) (hto : ToFGAt tr x i ℓ C)
    (hslot : sp.slot τ + 3 ≤ sp.slot (tr.time i)) :
    (∃ j ≤ i, ∃ s' B' CV', FastLockAt tr x j s' B' CV' ∧ τ < tr.time j ∧
      sp.slot (tr.time i) ≤ s' + 2 ∧ Anc U C B') ∨
    (∃ D a, sp.deepDepth = some D ∧
      deepest ℓ.frame (toFGCandidates sp (tr.state x i) ℓ.frame (tr.time i)) = none ∧
      deepAnchor sp (tr.state x i) ℓ.frame (tr.time i) = some a ∧
      C ∈ toFGDeepCandidates sp D a (tr.state x i) ℓ.frame (tr.time i)) := by
  obtain ⟨hc, -, hC⟩ := hto
  obtain ⟨-, hfast | ⟨D, a, hD, ha, hnf, hdeep⟩⟩ := toFG_source hC
  rotate_left
  · exact Or.inr ⟨D, a, hD, hnf, ha, hdeep⟩
  left
  obtain ⟨hCv, l, hl, hlb, hlf, hls⟩ := hfast
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := hl
  obtain ⟨j, hj, B', CV', hfl, L, hL, hLr, hLB'⟩ :=
    fast_lock_provenance hrun (fun _ => voteStart_initial _) hx i l₀ hl₀ hlf
  have hU := hrun.coherent
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
    rcases hrun.frameLaw x hx i ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
      exact h.1
  refine ⟨j, hj.le, l₀.slot, B', CV', hfl, ?_, hls, ?_⟩
  · have h1 : sp.slot τ + 1 ≤ l₀.slot := by simp only at hls; omega
    have hτ : τ < sp.ts (l₀.slot : Int) := by
      rcases le_or_gt 0 τ with h0 | h0
      · refine lt_of_lt_of_le (not_le.1 fun h => ?_)
          ((ts_le_iff sp (a := (sp.slot τ : Int) + 1) (b := l₀.slot)).2 (by omega))
        have := ((ts_le_iff_le_slot sp h0) _).1 h
        omega
      · refine lt_of_lt_of_le h0 ?_
        simp only [ACParams.ts]
        have := sp.toParams.hΔ
        positivity
    rcases hfl with ⟨ℓ', C', ⟨-, -, ht, -⟩, -⟩ | ⟨ℓ', A', -, hs, -⟩
    · rw [ht]
      have := sp.toParams.hΔ
      linarith
    · refine lt_of_lt_of_le hτ ?_
      rw [← hs]
      exact ((ts_le_iff_le_slot sp (hrun.time_nonneg j)) _).2 le_rfl
  · have hCt : C ∈ ℓ.frame.tree := hCv.1
    obtain ⟨hvat, hva⟩ := viableAncestor_anc hΦ hB₀
    have hCe : C = ℓ.frame.viableAncestor B₀ := hU.1 (hΦU hCt) (hΦU hvat) hlb.symm
    have hLe : L = B₀ := hU.1 hL (hΦU hB₀) (hLr.trans hB₀r.symm)
    subst hCe hLe
    exact (Anc.mono hΦU hva).trans hLB'

theorem source_age (sp : ACParams) : SourceAge sp := by
  intro FGP H U tr hr τ x i ℓ C hx hto hslot
  rcases source_age_const sp
      (hr.upTo (hr.time_nonneg i)) τ x i ℓ C hx
      ((upTo_toFGAt hr.time_mono).mpr ⟨le_rfl, hto⟩) hslot with
    ⟨j, hji, s, B, CV, hfl, ht, hs, hanc⟩ | ⟨D, a, hD, hnf, ha, hdeep⟩
  · exact Or.inl ⟨j, hji, s, B, CV, (upTo_fastLockAt hr.time_mono).mp hfl |>.2, ht, hs, hanc⟩
  · have hst : (tr.upTo (tr.time i)).state x i = tr.state x i :=
      Trace.upTo_state tr x fun k hk => hr.time_mono hk.le
    rw [hst, Trace.upTo_time] at hnf ha hdeep
    exact Or.inr ⟨D, a, hD, hnf, ha, hdeep⟩

end Consensus.Goldilocks.AC.Growing

end
