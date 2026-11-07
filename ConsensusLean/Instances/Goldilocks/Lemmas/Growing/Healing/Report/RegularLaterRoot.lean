module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularFast
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes

public section

/-! # Later heads below a common finality root -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload)
open Compose.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The common root constrains every later head without retaining the origin writer. -/
theorem later_heads_of_common_root_at {s₀ s N floor : Nat} {kindJ : Prop}
    {J D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hs₀ : s₀ ≤ s) (hk : kindJ)
    (hDJ : Anc (tr.HonestBlocksAt H) D J) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e → e.msg.slot = r →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg D) ∧
      (s + 2 ≤ r → ∀ y i ell, y ∈ H (tr.time i) → tr.projAC.CallAt y i ell →
        ell.call = .proposal → tr.time i = sp.ts r → ∀ d pay,
        (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) D d.head) := by
  have hts {a b : Nat} (hab : a ≤ b) : sp.ts a ≤ sp.ts b :=
    (SA.ts_le_iff sp).mpr (by exact_mod_cast hab)
  have hroot y i (hy : y ∈ H (tr.time i)) (hlo : sp.ts s₀ ≤ tr.time i)
      (hhi : tr.time i ≤ sp.ts N + sp.Δ) : (tr.state y i).fg.fcRoot = J :=
    (ite_eq_left ((hframe.kind_iff y i hy hlo hhi).mpr hk)).trans
      (hframe.root_eq y i hy hlo hhi hk)
  intro r hrlo hrN
  constructor
  · intro y i ev hy ⟨ell, hc, he⟩ hes
    have hr := (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun
    have hc' := sa_castAt_upTo.mpr ⟨le_rfl, hc, he⟩
    obtain ⟨hPhi, hPhiU⟩ := frameIn_at hrun hnc hy hc
    have hsl := (SA.castAt_spec hr hy hc').2.1.symm.trans hes
    change sp.slot (tr.time i) = r at hsl
    have hlo : sp.ts s₀ ≤ tr.time i :=
      (SA.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).mpr (by rw [hsl]; omega)
    have hhi := SA.vote_time_le hr hy ⟨ell, hc'.1, he⟩
    change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at hhi
    rw [hsl] at hhi
    obtain ⟨W, hW, hWr, hRW⟩ := SA.castAt_head_anc hr hy hc' (Or.inr rfl)
      (fun L hL => (SA.liveLockBlock_candidate hPhi hL).elim
        (fun h => Or.inr h.2.1) Or.inl) Relation.ReflTransGen.refl
    have hRW := hRW.mono hPhiU
    rw [frame_of_projAC_at hrun hy hc] at hRW
    change Anc (tr.HonestBlocksAt H) (tr.state y i).fg.fcRoot W at hRW
    rw [hroot y i hy hlo (hhi.trans (add_le_add_left (hts hrN) _))] at hRW
    exact ⟨W, hPhiU hW, hWr, hDJ.trans hRW⟩
  · intro _ y i ell hy hc hcall hti d pay hd
    obtain ⟨hPhi, hPhiU⟩ := frameIn_at hrun hnc hy hc
    have hRW : Anc (tr.HonestBlocksAt H) ell.frame.fcRoot d.head := by
      rw [(SA.acProposal_head hd).2]
      exact (SA.anc_getHead_of_compat hPhi (Or.inr rfl)
        (fun L hL => (SA.liveLockBlock_candidate hPhi hL).elim
          (fun h => Or.inr h.2.1) Or.inl)
        (fun B (hB : B ∈ ell.frame.viableTree ell.frame.tree) => hB.1)
        _ _ Relation.ReflTransGen.refl).mono hPhiU
    rw [frame_of_projAC_at hrun hy hc] at hRW
    change Anc (tr.HonestBlocksAt H) (tr.state y i).fg.fcRoot _ at hRW
    have hlo : sp.ts s₀ ≤ tr.time i := by rw [hti]; exact hts (by omega)
    have hhi : tr.time i ≤ sp.ts N + sp.Δ := by
      rw [hti]; exact (hts hrN).trans (le_add_of_nonneg_right sp.toParams.hΔ.le)
    rw [hroot y i hy hlo hhi] at hRW
    exact hDJ.trans hRW

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
