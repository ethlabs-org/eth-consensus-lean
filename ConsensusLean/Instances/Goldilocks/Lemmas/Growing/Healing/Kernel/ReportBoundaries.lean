module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.Row

public section

/-! # Frozen per-cut report suppliers for reset rounds

The reader stays honest through the report deadline, not through a later proposal.
The original proposer stays honest through its vote deadline only. Later proposal calls
and historical signatures retain their own honesty cuts.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A warm proposal supplies a historical report followed by later honest proposal heads. -/
theorem proposal_report_follow_at
    {g ΔF b : Time} {s₀ u N floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + 1 ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {y : Fin sp.n} (hy : y ∈ H (sp.ts (u + 1 : Nat) + 2 * sp.Δ)) :
    ∃ i ell R, y ∈ H (tr.time i) ∧ SA.ToFGAt tr.projAC y i ell R ∧
      sp.ts u ≤ tr.time i ∧ tr.time i ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ ∧
      Anc (tr.HonestBlocksAt H) P R ∧
      ∀ x, u + 3 ≤ x → x ≤ N → ∀ w c ellp, w ∈ H (tr.time c) →
        tr.projAC.CallAt w c ellp → ellp.call = .proposal → tr.time c = sp.ts x →
        ∀ d pay, (SA.acProposal sp (tr.projAC.state w c) ellp.frame (tr.time c)).2 =
          some (d, pay) → Anc (tr.HonestBlocksAt H) R d.head := by
  sorry

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
