module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.OldSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.LeftEntry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.High
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRowSources

public section

/-! # Viability of held historical high origins -/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
variable {hold : Time}

/-- A held origin is in the viable tree at its independently honest reader. The frame's root is
`Σ.F`, so a block of the frame is above it. A block below `h_max − 1` is below the entry at
`h_max − 1` of a maximal block (compared through its left entry); a block at `h_max − 1` is viable
in a gap frame, and in a top frame it extends `Σ.J` or lies below `Σ.J`, which is viable (compared
through `Σ.J`'s left entry). -/
theorem held_high_origin_viable_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {p : Fin sp.n} {c : Nat} (hpH : p ∈ H (tr.time c))
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt p c ell)
    (hcb : tr.time c ≤ b) {x : Fin sp.n} {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B)
    (hib : tr.time i ≤ b) (_ht : sp.ts (j + 1 : Nat) ≤ tr.time c)
    (hBt : B ∈ ell.frame.tree) :
    B ∈ ell.frame.viableTree ell.frame.tree ∨ ell.frame.Anc B ell.frame.fcRoot := by
  have ht := hp.run.time_nonneg c
  have hle : ∀ q < c, tr.time q ≤ tr.time c := fun _ hq => hp.run.time_mono hq.le
  have hreach := fg_reachable_at hp.run ht hle hpH
  have hac := Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl
  have hr := hac.localRun.upTo ht
  have hc' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hc)
  have hU := hac.localRun.coherent
  have hsub : (tr.state p c).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨p, c, tr.time c, ht, hle, hpH, h⟩
  have hanc : ∀ {X Y : AC.Blk sp.n (List (FG.Att sp.n))}, Anc (tr.HonestBlocksAt H) X Y →
      Y ∈ (tr.state p c).fg.tree → (tr.state p c).fg.Anc X Y :=
    fun h hY => store_anc_of_honest_anc_at hp.run hp.noColl ht hle hpH h hY
  have hfr := Outcome.frame_of_call hp.run hpH hc
  have hBf : B ∈ (Node.frame (tr.state p c)).tree := hfr ▸ hBt
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hpH hc'
  have hBs : B ∈ (tr.state p c).fg.tree := hBf.1
  have hFB : (tr.state p c).fg.Anc (tr.state p c).fg.F B := hBf.2
  have hBh : HZ tr H g + 1 ≤ ((tr.state p c).fg.σ B.root).h :=
    hp.high_of_anc_at ho ht hle hpH hBs .refl
  obtain ⟨-, hJm, hFJ, ⟨Bj, hBj, hBjJ, hBjhj⟩, hmax, ⟨C, hC, hCh⟩, -⟩ :=
    Store.cache_invariants _ _ _ _ hreach
  have hjm : (tr.state p c).fg.hj < (tr.state p c).fg.hmax := by
    have := Store.hj_lt_h hreach hBj
    have := hmax Bj hBj
    omega
  -- the left entry of a held entry `E` above `B`'s height is compatible with `B`
  have hcmp : ∀ {E W : AC.Blk sp.n (List (FG.Att sp.n))}, E ∈ (tr.state p c).fg.tree →
      ((tr.state p c).fg.σ E.root).Th = E.root → HZ tr H g + 1 ≤ ((tr.state p c).fg.σ E.root).h →
      (tr.state p c).fg.Anc E W → ((tr.state p c).fg.σ E.root).h < ((tr.state p c).fg.σ W.root).h →
      Compatible (tr.HonestBlocksAt H) E B := by
    intro E W hE hET hEh hEW hlt
    obtain ⟨_, _, _, _, v, d, _, hdc, _, _, hor⟩ :=
      hp.left_entry_origin_or_covered_at ht hle hpH hcb hE hET hEh hEW hlt
    rcases hor with ⟨r, hrd, l, O, hoO, hEO⟩ | ⟨-, hcov⟩
    · rcases hp.origins_compatible_at hoO
          ((hp.run.time_mono (show r ≤ c by omega)).trans hcb) ho hib with h | h
      · exact Or.inl (hEO.trans h)
      · exact Anc.total hU hEO h
    · exact hcov.compatible_highOrigin hp.run hp.noColl hib ho
  -- a viable held descendant of `B`
  have hdesc : ∃ W ∈ (tr.state p c).fg.tree, (tr.state p c).fg.Anc B W ∧
      (tr.state p c).fg.IsViable W := by
    by_cases hm : (tr.state p c).fg.hmax ≤ ((tr.state p c).fg.σ B.root).h
    · exact ⟨B, hBs, .refl, Or.inl hm⟩
    by_cases hlow : ((tr.state p c).fg.σ B.root).h + 2 ≤ (tr.state p c).fg.hmax
    · obtain ⟨E, hE, hEC, hEh, hET⟩ := entry_at_height hreach hC (h := (tr.state p c).fg.hmax - 1)
        (by omega) (by omega)
      have hBE : Anc (tr.HonestBlocksAt H) B E := by
        rcases hcmp hE hET (by omega) hEC (by omega) with h | h
        · have := h_le_of_store_anc hreach (hanc h hBs)
          omega
        · exact h
      exact ⟨C, hC, (hanc hBE hE).trans hEC, Or.inl hCh.ge⟩
    have hBm : ((tr.state p c).fg.σ B.root).h + 1 = (tr.state p c).fg.hmax := by omega
    by_cases hgap : (tr.state p c).fg.hj + 1 < (tr.state p c).fg.hmax
    · exact ⟨B, hBs, .refl, Or.inr ⟨hBm, Or.inl hgap⟩⟩
    obtain ⟨EJ, hEJ, hEJr, hEJB, hcase⟩ := Store.J_entry_of_reachable hreach hBj
    obtain rfl : EJ = (tr.state p c).fg.J := hU.1 (hsub hEJ) (hsub hJm) (hEJr.trans hBjJ)
    rcases hcase with hg | ⟨hJh, hJT⟩
    · exact ⟨B, hBs, .refl, Or.inr ⟨hBm, Or.inr
        (hg ▸ (Store.accepted_tree _ _ _ _ hreach).2.2.2 B hBs)⟩⟩
    have hJlt : ((tr.state p c).fg.σ (tr.state p c).fg.J.root).h <
        ((tr.state p c).fg.σ Bj.root).h := by
      have := Store.hj_lt_h hreach hBj
      omega
    rcases hcmp hJm hJT (by omega) hEJB hJlt with h | h
    · exact ⟨B, hBs, .refl, Or.inr ⟨hBm, Or.inr (hanc h hBs)⟩⟩
    · exact ⟨(tr.state p c).fg.J, hJm, hanc h hJm, Or.inr ⟨by omega, Or.inr .refl⟩⟩
  obtain ⟨W, hW, hBW, hvW⟩ := hdesc
  have hfB : Anc (tr.HonestBlocksAt H) ell.frame.fcRoot B := by
    rw [hfr]
    exact hFB.mono hsub
  have hfB' := AC.anc_tree_of_anc_U hU hPhi hPhiU hPhi.fcRoot_mem hfB hBt
  have hWf : W ∈ (Node.frame (tr.state p c)).tree := ⟨hW, hFB.trans hBW⟩
  have hWt : W ∈ ell.frame.tree := hfr ▸ hWf
  have hWv : W ∈ ell.frame.viableHeads := by
    rw [hfr]
    exact ⟨hW, hWf.2, hvW⟩
  exact Or.inl ⟨hBt, hfB', W, hWt, hWv,
    AC.anc_tree_of_anc_U hU hPhi hPhiU hBt (hBW.mono hsub) hWt⟩

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
