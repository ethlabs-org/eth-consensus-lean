module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.RootBound
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC

public section

/-! # Honest-cast anchors relative to the old-source pivot -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- A current-slot lock has an earlier supporter honest at that vote's own cut;
other live locks and the finalized root are bounded by the supplied historical pivot. -/
theorem reset_vote_anchor_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {u : Nat} {P Q D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPU : P ∈ tr.HonestBlocksAt H) (hR : drainTime sp a ≤ sp.ts u)
    (hPQ : P.parent = some Q.root) (hQU : Q ∈ tr.HonestBlocksAt H)
    (hDQ : Anc (tr.HonestBlocksAt H) D Q) (hDU : D ∈ tr.HonestBlocksAt H)
    (hDold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocksAt H) O D)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b)
    (hE : ∀ x j' e', x ∈ H (tr.time j') → j' < j → SA.VoteAt tr.projAC x j' e' →
      e'.msg.slot = u → e'.msg.head = P.root)
    (hlocks : ∀ l ∈ e.readPoint.locks, l.slot ≠ u →
      sp.slot (tr.time j) ≤ l.slot + sp.k →
      ∀ L ∈ ell.frame.tree, L.root = l.block →
        Anc (tr.HonestBlocksAt H) (ell.frame.viableAncestor L) Q) :
    Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint ell.frame (tr.time j)) D ∨
      (Anc (tr.HonestBlocksAt H) D (SA.getAnchor sp e.readPoint ell.frame (tr.time j)) ∧
        Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint ell.frame (tr.time j)) P) := by
  have hrun := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hrun.upTo (hp.run.time_nonneg j)
  have hc' := SA.upTo_castAt.mpr (And.intro le_rfl hcy)
  have hU := hrun.localRun.coherent
  have hPhi := Outcome.frame_realized hp.run hy hcy.1
  have hPhiU := Outcome.frame_tree_subset hp.run hy hcy.1
  have hDP : Anc (tr.HonestBlocksAt H) D P := hDQ.trans (.single ⟨hQU, hPU, hPQ⟩)
  have hat := Compose.anchor_tree hPhi e.readPoint (tr.time j)
  have haS := Compose.anchor_mem ell.frame e.readPoint (tr.time j)
  generalize SA.getAnchor sp e.readPoint ell.frame (tr.time j) = an at hat haS ⊢
  rcases haS with ⟨_, l', hl', hl'r⟩ | haf
  swap
  · rw [Set.mem_singleton_iff.1 haf]
    exact Or.inl (hp.reset_vote_root_below_bound_at hR hDU hDold hy hcy hes hjb)
  obtain ⟨l, hl, B, hB, hBr, hlive, rfl⟩ := hl'
  obtain rfl : an = ell.frame.viableAncestor B :=
    hPhi.coherent.1 hat (SA.viableAncestor_anc hPhi hB).1 hl'r.symm
  have haB : Anc (tr.HonestBlocksAt H) (ell.frame.viableAncestor B) B :=
    Anc.mono hPhiU (SA.anc_viableAncestor _ B)
  by_cases hls : l.slot = u
  · obtain ⟨Phi', A', D', _, hPhi'U, _, h34, hpool, _, L, hLU, hLr, hLD'⟩ :=
      SA.lock_origin_readPoint hr hy hc' l hl (by rw [hes, hls]; omega)
    obtain rfl : L = B := hU.1 hLU (hPhiU hB) (hLr.trans hBr.symm)
    have hf : 2 * (H (tr.time j))ᶜ.ncard < sp.n := by
      have := hp.faults (tr.time j) (hp.run.time_nonneg j) hjb
      have := Fin.pos y
      omega
    obtain ⟨x, ⟨v, hv, rfl, R, hRt, hRr, hDR⟩, hxH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := (H (tr.time j))ᶜ)
        (t := SA.optimisticVoters sp A' Phi' l.slot D') (by omega)
    have hvH : v.val ∈ H (tr.time j) := not_not.1 hxH
    obtain ⟨hvs, j', hj', e', hv', rfl⟩ := hpool v hv hvH
    have hvote := SA.upTo_voteAt.mp hv'
    have hvHon : e'.msg.val ∈ H (tr.time j') :=
      hp.run.antitone (hp.run.time_mono hj'.le) hvH
    have hRP : R = P := hU.1 (hPhi'U hRt) hPU
      (hRr.trans (hE _ _ _ hvHon hj' hvote.2 (hvs.trans hls)))
    rw [hRP] at hDR
    have haP := haB.trans (hLD'.trans (Anc.mono hPhi'U hDR))
    rcases Anc.total hU haP hDP with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, haP⟩
  · have haQ := hlocks l hl hls
      (hlive.trans ((SA.castAt_readPoint_locksWF hr.localRun hy hc').cap hl)) B hB hBr
    rcases Anc.total hU haQ hDQ with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, haQ.trans (.single ⟨hQU, hPU, hPQ⟩)⟩

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo
