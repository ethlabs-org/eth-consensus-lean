module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.ServiceCarry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.OptimisticPrefix
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularTransfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Optimistic prefix following under finite healing service -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
variable {hold : Time}

namespace Core

variable {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n →
    Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}

/-- A viable prefix of an optimistic write is reached at the next-slot cast, at the slot
committees `K` of a run from `K`'s committee start. -/
theorem optimistic_prefix_before_at {K : AC.CommitteeDict sp.n}
    {g ΔF b : Time} (hrun : GoldilocksRunCore u frameOf proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) {s : Nat} (hm : gbar g ≤ sp.ts s)
    {x y : Fin sp.n} {c i : Nat} (hx : x ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    {D B : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (hopt : AC.OptimisticLockAt tr.projAC x c s D CV)
    (hBD : Anc (tr.HonestBlocksAt H) B D)
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) (hFD : Anc (tr.HonestBlocksAt H) ell.frame.F D)
    (hB : B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    (haB : ell.frame.Anc (AC.getAnchor sp e.readPoint ell.frame (tr.time i)) B)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ell.frame.Anc B (AC.getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame (s + 1)))
      (AC.mergedVoteView sp e.readPoint ell.frame (s + 1)) s) := by
  have hac := hrun.acRun hnc
  have hrx := (hac.upTo (hrun.time_nonneg c)).localRun
  have hry := (hac.upTo (hrun.time_nonneg i)).localRun
  have hc' := AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hcarry := carry_of_service_senders hrun hnc hsvc hcatch hm hy hc hes
    (CV := CV) fun v hv => by
      obtain ⟨hvs, ⟨k, hk, hlo, hhi⟩, Hv, -, hroot, hanc, hacc⟩ :=
        Compose.optimistic_writer_votes hrx hac.vstart hx
          ((AC.upTo_optimisticLockAt hrun.time_mono).mpr ⟨le_rfl, hopt⟩) v hv
      obtain ⟨hkt, hk⟩ := (ACTrace.upTo_sendOrAdmit hrun.time_mono).mp hk
      refine ⟨hvs, ⟨x, k, hrun.antitone hkt hx, hk, hlo, hhi⟩, Hv, hroot,
        hFD.trans hanc, ?_⟩
      exact hacc.imp_right fun ⟨k', hk', htime⟩ => by
        obtain ⟨hkt', hk'⟩ := ACTrace.upTo_acceptAt.mp hk'
        exact ⟨x, k', hrun.antitone hkt' hx, hk', htime⟩
  have hsb : sp.ts s ≤ b := by
    have hslot := (AC.castAt_specU hry.toU hy hc').2.1
    change e.msg.slot = sp.slot (tr.time i) at hslot
    have hti : sp.ts ((s + 1 : Nat) : Int) ≤ tr.time i :=
      (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2 (by rw [← hslot, hes])
    have := (AC.ts_le_iff sp).2 (show (s : Int) ≤ ((s + 1 : Nat) : Int) by omega)
    linarith
  rw [← AC.viableTree_voteDomain_eq_of_viable ⟨B, hB⟩]
  exact AC.Growing.optimistic_prefix_of_carry_at
    hac K hK.facts.hP
    (hrun.committeeTAt hK.facts hnc) hK.facts.hsize
    hx hopt hBD (hK.cs2 s hm hsb _ (hrun.time_nonneg i) hib) hy hc hes hcarry
    (AC.viableTree_voterBlockTree_subset_voteDomain hB) haB

end Core

/-- The stock run supplies the shared optimistic prefix argument. -/
theorem optimistic_prefix_before_at {K : AC.CommitteeDict sp.n}
    {g ΔF b : Time} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) {s : Nat} (hm : gbar g ≤ sp.ts s)
    {x y : Fin sp.n} {c i : Nat} (hx : x ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    {D B : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (hopt : AC.OptimisticLockAt tr.projAC x c s D CV)
    (hBD : Anc (tr.HonestBlocksAt H) B D)
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) (hFD : Anc (tr.HonestBlocksAt H) ell.frame.F D)
    (hB : B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    (haB : ell.frame.Anc (AC.getAnchor sp e.readPoint ell.frame (tr.time i)) B)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ell.frame.Anc B (AC.getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame (s + 1)))
      (AC.mergedVoteView sp e.readPoint ell.frame (s + 1)) s) :=
  Core.optimistic_prefix_before_at hrun.toCore hnc hsvc _hawake hcatch hm hx hy
    hopt hBD hc hes hib hFD hB haB hK

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
