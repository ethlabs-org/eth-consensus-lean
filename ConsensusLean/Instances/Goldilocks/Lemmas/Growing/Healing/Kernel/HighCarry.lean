module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.ResetSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.FaultBound
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift

public section

/-! # Post-GST carries without catch-up

Each send and head acceptance keeps its own honest writer. Post-GST receipts
need only ordinary reset service, not catch-up service.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- Historical sends and post-GST head acceptances suffice for a carry, without Catch. -/
theorem carry_of_post_gst_senders_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {s : Nat} (hgs : g ≤ sp.ts s)
    {y : Fin sp.n} {i : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hc : SA.CastAt tr.projAC y i ell e) (hs : e.msg.slot = s + 1)
    {CV : Set (Vote sp.n)}
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ w k, w ∈ H (tr.time k) ∧ tr.projAC.SendOrAdmit w k v ∧ sp.ts s ≤ tr.time k ∧
        tr.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv : SA.Blk sp.n (List (FG.Att sp.n)), Hv.root = v.head ∧
        Anc (tr.HonestBlocksAt H) ell.frame.F Hv ∧
        ∃ w k, w ∈ H (tr.time k) ∧ tr.projAC.AcceptAt w k Hv ∧
          g ≤ tr.time k ∧ tr.time k < sp.ts s + 2 * sp.Δ) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV := by
  have hm := hp.run.time_mono
  have hd := hp.run.time_nonneg i
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hac.localRun.upTo hd
  have hc' := (SA.upTo_castAt).mpr ⟨le_rfl, hc⟩
  have hsync := reset_syncACAt hp (lo := g) (hi := sp.ts s + 2 * sp.Δ) le_rfl
  have hcarry := Compose.Growing.carryAt_of_delivered hr (fun _ => SA.voteStart_initial _) hy hc'
      hs (CV := CV) fun v hv => by
    obtain ⟨hvs, ⟨w, k, hw, hsend, hk1, hk2⟩, Hv, hHvr, hFHv,
      w', kw, hw', hacc, hgk, hkwt⟩ := hW v hv
    refine ⟨hvs, ⟨tr.time k, hk1, hk2, fun hdl => ?_⟩, Hv, hHvr,
      Or.inl ⟨tr.time kw, hkwt, fun hdl => ?_⟩⟩
    · rw [Compose.Growing.ac_deadline_upTo (trA := tr.projAC) (d := tr.time i) hm le_rfl] at hdl
      obtain ⟨k', hk', hk1', ⟨ell', hc', hm'⟩, hk2'⟩ := hsync.1 w k v hw hsend
        (hgs.trans hk1) hk2.le y i ell hy hc.1 hdl
      exact (SA.messageServedBefore_iff _ _ _ _).mpr (Or.inl ⟨k', hk', hk1',
        ⟨ell', (Trace.upTo_callAt _).mpr ⟨hm hk', hc'⟩, hm'⟩,
        by rw [Compose.Growing.ac_deadline_upTo (trA := tr.projAC) (d := tr.time i) hm (hm hk')]
           exact hk2'⟩)
    · rw [Compose.Growing.ac_deadline_upTo (trA := tr.projAC) (d := tr.time i) hm le_rfl] at hdl
      obtain ⟨ky, hky, ⟨ella, hca, hcall⟩, hkyt⟩ := hsync.2 w' kw Hv hw' hacc hgk hkwt.le
        y i ell hy hc.1 hdl hFHv
      exact ⟨ky, hky, ⟨ella, (Trace.upTo_callAt _).mpr ⟨hm hky, hca⟩, hcall⟩,
        by rw [Compose.Growing.ac_deadline_upTo (trA := tr.projAC) (d := tr.time i) hm (hm hky)]
           exact hkyt⟩
  refine ⟨hcarry.awake.1, hcarry.joined, fun v hv => ?_, hcarry.holds⟩
  obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads v hv
  refine ⟨Hv, hHv, hHvr, fun X hX => ?_⟩
  exact (hacc X hX).imp_right
    fun ⟨k, hk, hkt⟩ => ⟨k, (ACTrace.upTo_acceptAt.mp hk).2, hkt⟩

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
