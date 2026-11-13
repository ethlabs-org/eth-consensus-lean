module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.ServiceCarry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularSupport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay

public section

/-! # Regular fast-lock transport with finite healing service -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload Vote gbar)
open Compose.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A fast lock's votes and heads have honest historical writer events. -/
theorem fastLock_writer_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {x : Fin sp.n} {c s : Nat}
    (hx : x ∈ H (tr.time c)) {D : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hfl : SA.FastLockAt tr.projAC x c s D CV) :
    ∀ v ∈ CV, v.slot = s ∧
      (∃ k, x ∈ H (tr.time k) ∧ tr.projAC.SendOrAdmit x k v ∧ sp.ts s ≤ tr.time k ∧
        tr.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ tr.HonestBlocksAt H, Hv.root = v.head ∧ Anc (tr.HonestBlocksAt H) D Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, x ∈ H (tr.time k) ∧ tr.projAC.AcceptAt x k Hv ∧
          tr.time k < sp.ts s + 2 * sp.Δ) := by
  have hd := hrun.time_nonneg c
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono hd
  intro v hv
  obtain ⟨hvs, ⟨k, hk, hlo, hhi⟩, Hv, hHv, hroot, hDHv, hacc⟩ :=
    Healing.fastLock_writer (acRun_upTo hrun hnc hd).localRun hx
      ((SA.upTo_fastLockAt hrun.time_mono).mpr ⟨le_rfl, hfl⟩) v hv
  obtain ⟨hkt, hk⟩ := (ac_sendOrAdmit_upTo hrun.time_mono).mp hk
  refine ⟨hvs, ⟨k, hrun.antitone hkt hx, hk, hlo, hhi⟩, Hv, hsub hHv, hroot,
    hDHv.mono hsub, hacc.imp_right fun ⟨k', hk', ht⟩ => ?_⟩
  obtain ⟨hkt', hk'⟩ := (ac_acceptAt_upTo _).mp hk'
  exact ⟨k', hrun.antitone hkt' hx, hk', ht⟩

/-- Fast-lock carry does not require the writer to remain honest at the next cast. -/
theorem fastLock_carry_service_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) {s : Nat} (hm : gbar g ≤ sp.ts s)
    {x y : Fin sp.n} {c i : Nat} (hx : x ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC x c s D CV)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hs : e.msg.slot = s + 1)
    (hFD : Anc (tr.HonestBlocksAt H) ell.frame.F D) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV := by
  apply carry_of_service_senders hrun hnc hsvc hcatch hm hy hc hs
  intro v hv
  obtain ⟨hvs, ⟨k, hk, hsend, hlo, hhi⟩, Hv, -, hroot, hanc, hacc⟩ :=
    fastLock_writer_at hrun hnc hx hfl v hv
  refine ⟨hvs, ⟨x, k, hk, hsend, hlo, hhi⟩, Hv, hroot, hFD.trans hanc, ?_⟩
  exact hacc.imp_right fun ⟨k', hk', hacc', ht⟩ => ⟨x, k', hk', hacc', ht⟩

/-- The regular fast transfer step with service and fault margins at the receiving cut, at the
full committee (`hstock`, §S.2 scope-(ii) item). -/
theorem first_transfer_service_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s : Nat} (hm : gbar g ≤ sp.ts s)
    {x y : Fin sp.n} {c i : Nat} (hx : x ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    {B D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC x c s D CV) (hBD : Anc (tr.HonestBlocksAt H) B D)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) (hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B)
    (hviab : SA.ViableAtVote ell e (s + 1) B)
    (hearlier : SA.EarlierVotesExtendAt tr.projAC H (tr.HonestBlocksAt H) i (s + 1) B)
    (hstock : sp.committeeSize = sp.n) :
    SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hslot := (castAt_spec_at hrun hnc hy hc).2.1.symm.trans hs
  have hprev : gbar g ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1) := by
    change sp.slot (tr.time i) = s + 1 at hslot
    rw [hslot, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega]
    exact hm
  have hfb := faultBound_of_service_at hrun hawake hf hnr (hrun.time_nonneg i) hprev hib
  exact SA.Growing.first_transfer_stored hac _ (fun _ => SA.CommitteeP.full)
    (fun _ => SA.CommitteeT.full) (SA.size_binding_full hstock) hx hfl hBD hy hc hs
    (service_syncACAt hrun hsvc ((SA.le_gbar g).trans hm))
    (fastLock_carry_service_at hrun hnc hsvc hcatch hm hx hy hfl hc hs (hFB.trans hBD))
    ((SA.ncard_inter_full_lt_iff _ _ _).2 hfb) (SA.Growing.cs2_full_of_faultBoundAt hstock hfb)
    hviab hearlier

/-- Finite service compares the receiver's merged votes with an independently honest writer. -/
theorem writer_merged_service_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    {s : Nat} (hm : gbar g ≤ sp.ts s)
    {x y : Fin sp.n} {c i : Nat} (hx : x ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    {ellx ell : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC x c s ellx) {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hs : e.msg.slot = s + 1) :
    ∀ v ∈ (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.projAC.state x c).pool s ∨
        v.val ∈ SA.equivocators {w | w ∈ (tr.projAC.state x c).pool s} := by
  exact SA.Growing.writer_merged
    (Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc)
    hx hu hy hc hs (service_syncACAt hrun hsvc ((SA.le_gbar g).trans hm))

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
