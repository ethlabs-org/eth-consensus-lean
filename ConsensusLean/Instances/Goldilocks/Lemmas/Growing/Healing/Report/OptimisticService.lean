module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.ServiceCarry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.OptimisticPrefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC

public section

/-! # Optimistic prefix following under finite healing service -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A viable prefix of an optimistic write is reached at the next-slot cast. -/
theorem optimistic_prefix_before_at
    {g ΔF b : Time} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) {s : Nat} (hm : gbar g ≤ sp.ts s)
    {x y : Fin sp.n} {c i : Nat} (hx : x ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    {D B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hopt : SA.OptimisticLockAt tr.projAC x c s D CV)
    (hBD : Anc (tr.HonestBlocksAt H) B D)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) (hFD : Anc (tr.HonestBlocksAt H) ell.frame.F D)
    (hB : B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    (haB : ell.frame.Anc (SA.getAnchor sp e.readPoint ell.frame (tr.time i)) B) :
    ell.frame.Anc B (SA.getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
      (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s) := by
  have hcarry := carry_of_service_senders hrun hnc hsvc hcatch hm hy hc hes
    (CV := CV) fun v hv => by
      obtain ⟨hvs, ⟨k, hk, hsend, hlo, hhi⟩, Hv, -, hroot, hanc, hacc⟩ :=
        Compose.Growing.optimistic_writer_votes_at hrun hnc hx hopt v hv
      refine ⟨hvs, ⟨x, k, hk, hsend, hlo, hhi⟩, Hv, hroot, hFD.trans hanc, ?_⟩
      exact hacc.imp_right fun ⟨k', hk', hacc', htime⟩ => ⟨x, k', hk', hacc', htime⟩
  have hhalf : 2 * (H (tr.time i))ᶜ.ncard < sp.n := by
    have hbound := hf _ (hrun.time_nonneg i) hib
    have hn : 0 < sp.n := sp.toParams.hn
    omega
  rw [← SA.viableTree_voteDomain_eq_of_viable ⟨B, hB⟩]
  exact SA.Growing.optimistic_prefix_of_carry_at
    (Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc)
    hx hopt hBD hhalf hy hc hes hcarry
    (SA.viableTree_voterBlockTree_subset_voteDomain hB) haB

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
