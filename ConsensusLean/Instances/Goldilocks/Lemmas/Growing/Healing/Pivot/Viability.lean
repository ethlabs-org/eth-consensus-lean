module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.OldSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Contest
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRowSources

public section

/-! # Viability of held historical high origins -/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- A held origin is viable or below the actual root at its independently honest reader. -/
theorem held_high_origin_viable_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} {c : Nat} (hpH : p ∈ H (tr.time c))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt p c ell)
    (hcb : tr.time c ≤ b) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B)
    (hib : tr.time i ≤ b) (_ht : sp.ts (j + 1 : Nat) ≤ tr.time c)
    (hBt : B ∈ ell.frame.tree) :
    B ∈ ell.frame.viableTree ell.frame.tree ∨ ell.frame.Anc B ell.frame.fcRoot := by
  have ht := hp.run.time_nonneg c
  have hle : ∀ q < c, tr.time q ≤ tr.time c := fun _ hq => hp.run.time_mono hq.le
  have hreach := fg_reachable_at hp.run ht hle hpH
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hac.localRun.upTo ht
  have hc' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hc)
  have hU := hac.localRun.coherent
  have hsub : (tr.state p c).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨p, c, tr.time c, ht, hle, hpH, h⟩
  have hfr := Outcome.frame_of_call hp.run hpH hc
  have hBf : B ∈ (Node.frame (tr.state p c)).tree := hfr ▸ hBt
  have hBh := hp.high_of_anc_at ho ht hle hpH hBf.1 .refl
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hc'
  have hroot : Compatible (tr.HonestBlocksAt H) ell.frame.fcRoot B := by
    by_cases hhigh : HZ tr H g + 1 ≤ (tr.state p c).fg.hj
    · exact hp.high_J_root_of_held_at_call_before_at hpH hBf.1 hpH hcb hc hhigh
        (fun _ r _ _ hrc hO => hp.origins_compatible_at ho hib hO
          ((hp.run.time_mono hrc.le).trans hcb))
    rw [hfr]
    change Compatible _ (tr.state p c).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs with hchoose
    · have hJB : (tr.state p c).fg.Anc (tr.state p c).fg.J B := by
        by_contra hn
        have hmax := (Store.cache_invariants _ _ _ _ hreach).2.2.2.2.1 B hBf.1
        exact hchoose.2 ⟨hchoose.1, B, hBf.1, hBf.2, by omega, hn⟩
      exact Or.inl (hJB.mono hsub)
    · have hh := finalized_compatible_high_origin_at hp hpH hcb ho hib
      exact hh
  rcases hroot with hfB | hBfroot
  swap
  · exact Or.inr (SA.anc_tree_of_anc_U hU hPhi hPhiU hBt hBfroot hPhi.fcRoot_mem)
  have hfB' := SA.anc_tree_of_anc_U hU hPhi hPhiU hPhi.fcRoot_mem hfB hBt
  have hfBs : (tr.state p c).fg.Anc (tr.state p c).fg.fcRoot B := by
    rw [hfr] at hfB'
    exact hfB'.mono (fun _ h => h.1)
  have hdesc : ∃ C ∈ (tr.state p c).fg.tree, (tr.state p c).fg.Anc B C ∧
      (tr.state p c).fg.IsViable C := by
    by_cases hfloor : (tr.state p c).fg.headHeightFloor ≤ ((tr.state p c).fg.σ B.root).h
    · exact ⟨B, hBf.1, .refl, hfloor⟩
    have hlow := lt_of_not_ge hfloor
    have hcon : ¬ (tr.state p c).fg.Contest := by
      intro h
      have hh := hlow
      unfold Store.headHeightFloor at hh
      simp only [h, ↓reduceIte] at hh
      exact Outcome.no_high_contest_at hp hpH hcb ⟨h, by omega⟩
    have hfl : (tr.state p c).fg.headHeightFloor = (tr.state p c).fg.hmax - 1 := by
      unfold Store.headHeightFloor
      simp only [hcon, ↓reduceIte]
    rw [hfl] at hlow
    obtain ⟨_, _, _, _, _, ⟨C, hC, hCh⟩, _⟩ := Store.cache_invariants _ _ _ _ hreach
    obtain ⟨E, hE, hEC, hEh, hET⟩ := entry_at_height hreach hC
      (h := (tr.state p c).fg.hmax - 1) (by omega) (by omega)
    obtain ⟨_, _, _, _, v, d, _, hdc, _, _, r, hrd, l, O, hoO, hEO⟩ :=
      hp.left_entry_origin_at ht hle hpH hcb hE hET (by omega) hEC (by omega)
    have hcmp : Compatible (tr.HonestBlocksAt H) E B := by
      rcases hp.origins_compatible_at hoO
          ((hp.run.time_mono (show r ≤ c by omega)).trans hcb) ho hib with h | h
      · exact Or.inl (hEO.trans h)
      · exact Anc.total hU hEO h
    have hBE : Anc (tr.HonestBlocksAt H) B E := by
      rcases hcmp with h | h
      · have hh := σ_h_le_of_anc hreach
          (store_anc_of_honest_anc_at hp.run hp.noColl ht hle hpH h hBf.1)
        omega
      · exact h
    refine ⟨C, hC, (store_anc_of_honest_anc_at hp.run hp.noColl ht hle hpH hBE hE).trans hEC, ?_⟩
    change (tr.state p c).fg.headHeightFloor ≤ _
    omega
  obtain ⟨C, hC, hBC, hvC⟩ := hdesc
  have hCf : C ∈ (Node.frame (tr.state p c)).tree := ⟨hC, hBf.2.trans hBC⟩
  have hCt : C ∈ ell.frame.tree := hfr ▸ hCf
  have hCv : C ∈ ell.frame.viableHeads := by
    rw [hfr]
    exact ⟨hC, hCf.2, hfBs.trans hBC, hvC⟩
  exact Or.inl ⟨hBt, hfB', C, hCt, hCv,
    SA.anc_tree_of_anc_U hU hPhi hPhiU hBt (hBC.mono hsub) hCt⟩

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
