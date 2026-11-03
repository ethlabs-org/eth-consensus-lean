module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowParents
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ProposalWindow
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Healed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.EngineSteps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Records
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.FinPair
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ProposalWindowUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedClientUpTo

public section

/-! # Goldilocks Refinement: parents above a crossing report, through a horizon (#137)

consensus-lean#137 (finite-horizon port). `crossed_parents_above` and the
`window_justifies_or_parents_above` family from `HealedUpTo … b` and `HSSharedUpTo … b`. C3
through the horizon needs `t_s ≤ b`, so case (A) bounds the parents of the honest proposals of
slots `s` with `v + Δ ≤ t_s ≤ b`. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **Parents above a crossing report, through the horizon.** `crossed_parents_above` from the
horizon premises (`HealedUpTo … b`, `HSSharedUpTo … b`). -/
theorem crossed_parents_above_upTo (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {gR tH b : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : HealedUpTo tr H proposer gR tH b h₀ E)
    {z : Fin sp.n} (hz : z ∈ H) {r : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hto : SA.ToFGAt tr.projAC z r ell C)
    (htH : tH ≤ tr.time r) {h : Nat} (hlt : h < ((tr.state z r).fg.σ C.root).h)
    {s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.HonestProposalRun tr H proposer s P) (hs : tr.time r + sp.Δ ≤ sp.ts s)
    (hsb : sp.ts s ≤ b) :
    ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) C Pr ∧
      ∀ y ∈ H, ∀ k, Pr ∈ (tr.state y k).fg.tree → h < ((tr.state y k).fg.σ Pr.root).h := by
  obtain ⟨hCf, l, hl, hlb, hlf, -⟩ := toFG_live_fast_lock hto
  obtain ⟨Pr, hPr, hpar, hCPr⟩ :=
    hH.c3 z hz r ell hto.1 htH l hl hlf C hCf hlb.symm s P hP hs hsb
  refine ⟨Pr, hPr, hpar, hCPr, fun y hy k hPrk => ?_⟩
  have hCz : C ∈ (tr.state z r).fg.tree := Healing.mem_tree_of_frame hrun hz hto.1 hCf
  have hCk : C ∈ (tr.state y k).fg.tree := Healing.mem_of_honest_anc hrun hnc hy hCPr hPrk
  have hle := Healing.h_le_of_store_anc (Compose.fg_reachable hrun.toLocalRun hy k)
    (Healing.store_anc_of_honest_anc hrun hnc hy hCPr hPrk)
  rw [Healing.σ_eq_honest hrun hnc hz hy hCz hCk] at hlt
  omega

end Consensus.Goldilocks.Refinement

end
