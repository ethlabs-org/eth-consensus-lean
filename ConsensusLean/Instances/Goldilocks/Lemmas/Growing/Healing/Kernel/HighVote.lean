module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighCarrySteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Next
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Projection

public section

/-! # High-origin vote transfer with explicit domain and earlier-vote inputs

The induction supplies viability and strictly earlier votes. Carries are the
independent no-Catch steps, and all counts are charged at the consuming cast.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- Once the held-target domain is established, first or next transfer extends the origin. -/
theorem high_vote_extends_of_domain_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {i j k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) (hkb : tr.time k ≤ b) (hj : j < e.msg.slot)
    (hvi : Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
      B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
    (hprior : ∀ z q e', q < k → Compose.Growing.HVoteAt tr H z q e' →
      j < e'.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B) :
    SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have ⟨hPhi, hPhiU⟩ := Compose.Growing.frameIn_at hp.run hp.noColl hy hc.1
  obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, _⟩ :=
    Compose.Growing.cast_head_fcRoot_at hp.run hp.noColl hy hc
  rcases hvi with hBf | hvi
  · exact ⟨Hd, hPhiU hHd, hHdr, hBf.trans (hfHd.mono hPhiU)⟩
  have hF := (hPhi.rooted.2 B hvi.1.1).mono hPhiU
  have hslot := (Compose.Growing.castAt_spec_at hp.run hp.noColl hy hc).2.1
  have hts : sp.ts e.msg.slot ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg k) _).mpr (by rw [hslot])
  have hcut := hp.cutZ_le_ts_of_highOrigin_at ho hib
  have hf := fault_bound_late_at hp
    (hcut.trans (((SA.ts_le_iff sp).mpr (show (j : Int) ≤ e.msg.slot by omega)).trans hts)) hkb
  have he : SA.EarlierVotesExtendAt tr.projAC H (tr.HonestBlocksAt H) k e.msg.slot B := by
    intro z q hq hz e' hv hs
    exact hprior z q e' hq (Compose.Growing.hVoteAt_iff.2 ⟨hz, hv⟩) (by omega)
  by_cases hs : e.msg.slot = j + 1
  · obtain ⟨CV, ellx, D, hcx, hfl, hBD⟩ := ho.2.2.1
    have htree := (frame_tree_subset_at hp.run hp.noColl ho.1 hcx).2
    have hsub : ellx.frame.tree ⊆ tr.HonestBlocksAt H := fun _ h =>
      ⟨x, i, tr.time i, hp.run.time_nonneg i, fun _ hq => hp.run.time_mono hq.le,
        ho.1, htree h⟩
    have hBD' : Anc (tr.HonestBlocksAt H) B D := by
      rw [hBD]
      exact (SA.anc_viableAncestor ellx.frame D).mono hsub
    have hgj : g ≤ sp.ts j := by
      linarith [lt_cutZ sp g, le_gbar g, sp.toParams.hΔ]
    exact SA.Growing.first_transfer_stored hac ho.1 hfl hBD' hy hc hs
      (reset_syncACAt hp hgj)
      (first_carry_of_finalized_anc_at hp ho hib ⟨ellx, D, hcx, hfl, hBD⟩ hy hc hkb hs hF)
      hf (Or.inl (by simpa only [← hs] using hvi)) (by simpa only [hs] using he)
  · obtain ⟨m, hm⟩ : ∃ m, e.msg.slot = m + 1 := ⟨e.msg.slot - 1, by omega⟩
    have hjm : j < m := by omega
    refine SA.Growing.next_transfer sp _ ro H _ tr.projAC proposer hac m y k B ell e
      hy hc hm ?_ ?_ ?_ hf
      (Or.inl (by simpa only [← hm] using hvi)) ?_
    · intro z q e' hz hv hs'
      obtain ⟨ell', hc'⟩ := hv
      have hslot' := (Compose.Growing.castAt_spec_at hp.run hp.noColl hz hc').2.1
      have hqk : q < k := by
        by_contra hn
        have := SA.slot_mono sp (hp.run.time_nonneg k) (hp.run.time_mono (by omega : k ≤ q))
        omega
      exact hprior z q e' hqk (Compose.Growing.hVoteAt_iff.2 ⟨hz, ell', hc'⟩) (by omega)
    · apply hp.half_committee_at
        (hcut.trans ((SA.ts_le_iff sp).mpr (show (j : Int) ≤ m by omega)))
        (htb := hkb)
      have hn : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      rw [hm, hn] at hts
      change sp.ts m + sp.Δ ≤ tr.time k
      linarith [sp.toParams.hΔ]
    · have hcarry := later_carry_of_finalized_anc_at hp ho hib hy hc hkb hm hjm hF
        (fun z q e' hq hv hs => hprior z q e' hq hv (by omega))
      have ht : tr.projAC.time = tr.time := by rfl
      rw [ht]
      simpa only [Compose.Growing.hVoteAt_iff, and_assoc] using hcarry
    · simpa only [hm] using he

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
