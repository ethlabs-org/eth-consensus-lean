module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.RootBound
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC

public section

/-! # Honest-cast anchors relative to the old-source pivot -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
variable {hold : Time}

/-- A current-slot lock has an earlier supporter honest at that vote's own cut;
other live locks and the finalized root are bounded by the supplied historical pivot. -/
theorem reset_vote_anchor_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u j : Nat} {P Q D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPU : P ∈ tr.HonestBlocksAt H) (hR : drainTime sp a ≤ sp.ts u)
    (hPQ : P.parent = some Q.root) (hQU : Q ∈ tr.HonestBlocksAt H)
    (hDQ : Anc (tr.HonestBlocksAt H) D Q) (hDU : D ∈ tr.HonestBlocksAt H)
    (hDold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocksAt H) O D)
    (hDcov : HighSourceCover tr H g a b → ∀ C s, HealedMemberBefore tr H g a b C s j → s < u →
      Anc (tr.HonestBlocksAt H) C D)
    {y : Fin sp.n} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hcy : AC.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b)
    (hE : ∀ x j' e', x ∈ H (tr.time j') → j' < j → AC.VoteAt tr.projAC x j' e' →
      e'.msg.slot = u → e'.msg.head = P.root)
    (hlocks : ∀ l ∈ e.readPoint.locks, l.slot ≠ u →
      sp.slot (tr.time j) ≤ l.slot + sp.k →
      ∀ L ∈ ell.frame.tree, L.root = l.block →
        Anc (tr.HonestBlocksAt H) (ell.frame.viableAncestor L) Q) :
    Anc (tr.HonestBlocksAt H) (AC.getAnchor sp e.readPoint ell.frame (tr.time j)) D ∨
      (Anc (tr.HonestBlocksAt H) D (AC.getAnchor sp e.readPoint ell.frame (tr.time j)) ∧
        Anc (tr.HonestBlocksAt H) (AC.getAnchor sp e.readPoint ell.frame (tr.time j)) P) := by
  have hrun := Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl
  have hr := hrun.upTo (hp.run.time_nonneg j)
  have hc' := AC.upTo_castAt.mpr (And.intro le_rfl hcy)
  have hU := hrun.localRun.coherent
  have hPhi := Outcome.frame_realized hp.run hy hcy.1
  have hPhiU := Outcome.frame_tree_subset hp.run hy hcy.1
  have hDP : Anc (tr.HonestBlocksAt H) D P := hDQ.trans (.single ⟨hQU, hPU, hPQ⟩)
  have hat := Compose.anchor_tree hPhi e.readPoint (tr.time j)
  have haS := Compose.anchor_mem ell.frame e.readPoint (tr.time j)
  generalize AC.getAnchor sp e.readPoint ell.frame (tr.time j) = an at hat haS ⊢
  rcases haS with ⟨_, l', hl', hl'r⟩ | haf
  swap
  · rw [Set.mem_singleton_iff.1 haf]
    exact Or.inl ((hp.cast_root_anc_analysis_root_at hy hcy).trans
      (hp.reset_vote_root_below_bound_at hR hDU hDold hDcov hy hcy hes hjb))
  obtain ⟨l, hl, B, hB, hBr, hlive, rfl⟩ := hl'
  obtain rfl : an = ell.frame.viableAncestor B :=
    hPhi.coherent.1 hat (AC.viableAncestor_anc hPhi hB).1 hl'r.symm
  have haB : Anc (tr.HonestBlocksAt H) (ell.frame.viableAncestor B) B :=
    Anc.mono hPhiU (AC.anc_viableAncestor _ B)
  by_cases hls : l.slot = u
  · obtain ⟨Phi', A', D', _, hPhi'U, _, h34, hpool, hsubA, L, hLU, hLr, hLD'⟩ :=
      AC.lock_origin_readPoint hr hy hc' l hl (by rw [hes, hls]; omega)
    obtain rfl : L = B := hU.1 hLU (hPhiU hB) (hLr.trans hBr.symm)
    obtain ⟨k, hkj, hsubk⟩ := hsubA
    have hK : AC.optimisticVoters sp A' Phi' l.slot D' ⊆
        (Generic.dictOfTime sp cm).committee l.slot := by
      rintro x ⟨v, hv, rfl, -⟩
      have hv' := hsubk hv
      rw [Trace.upTo_state tr.projAC y (fun _ hk' => hp.run.time_mono (by omega))] at hv'
      exact hp.committeeFacts.hP.1 _ y hy (k + 1) (fun _ hk' => hp.run.time_mono (by omega))
        l.slot v hv'
    have hgu : AC.gbar g ≤ sp.ts u := hp.gbar_le_ts_of_clean_at (by
      rw [Healing.drainTime_eq] at hR
      have := (AC.ts_le_iff sp).1 hR
      rw [Healing.cleanLabel_eq]
      push_cast at this
      omega)
    have hub : sp.ts u ≤ b := by
      have h := (AC.castAt_specU hr.localRun.toU hy hc').2.1
      have hsl : sp.slot (tr.time j) = u := by rw [← hes]; exact h.symm
      exact ((AC.ts_le_iff_le_slot sp (hp.run.time_nonneg j) u).2
        (by exact_mod_cast hsl.ge)).trans hjb
    have hf := hp.committee_cs2_at (s := l.slot) (hls ▸ hgu) (hls ▸ hub)
      (hp.run.time_nonneg j) hjb
    have hpos := hp.committee_pos
    obtain ⟨x, hxOV, hxH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard
        (s := (Generic.dictOfTime sp cm).committee l.slot ∩ (H (tr.time j))ᶜ)
        (t := AC.optimisticVoters sp A' Phi' l.slot D') (by omega)
    obtain ⟨v, hv, rfl, R, hRt, hRr, hDR⟩ := hxOV
    have hvH : v.val ∈ H (tr.time j) := by
      by_contra hvH
      exact hxH ⟨hK ⟨v, hv, rfl, R, hRt, hRr, hDR⟩, hvH⟩
    obtain ⟨hvs, j', hj', e', hv', rfl⟩ := hpool v hv hvH
    have hvote := AC.upTo_voteAt.mp hv'
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
      (hlive.trans ((AC.castAt_readPoint_locksWFU (hr := hr.localRun.toU) hr.vstart hy
        hc').cap hl)) B hB hBr
    rcases Anc.total hU haQ hDQ with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, haQ.trans (.single ⟨hQU, hPU, hPQ⟩)⟩

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo
