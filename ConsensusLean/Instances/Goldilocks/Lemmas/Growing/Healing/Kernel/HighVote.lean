module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighCarrySteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Next
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Projection
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # High-origin vote transfer with explicit domain and earlier-vote inputs

The induction supplies viability and strictly earlier votes. Carries are the
independent no-Catch steps, and all counts are charged at the consuming cast.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams Vote Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
variable {hold : Time}

/-- Once the held-target domain is established, first or next transfer extends the origin. -/
theorem high_vote_extends_of_domain_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i j k : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) (hkb : tr.time k ≤ b) (hj : j < e.msg.slot)
    (hvi : Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
      B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
    (hprior : ∀ z q e', q < k → Compose.Growing.HVoteAt tr H z q e' →
      j < e'.msg.slot → AC.VoteExtends (tr.HonestBlocksAt H) e'.msg B) :
    AC.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hrun := hp.run
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hp.noColl
  have hx := hrun.antitone (le_max_right _ _) ho.1
  have ⟨hPhi, hPhiU⟩ := Compose.Growing.frameIn_at hrun hp.noColl hy hc.1
  obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, _⟩ :=
    Compose.Growing.cast_head_fcRoot_at hrun hp.noColl hy hc
  rcases hvi with hBf | hvi
  · exact ⟨Hd, hPhiU hHd, hHdr, hBf.trans (hfHd.mono hPhiU)⟩
  have hF := (hPhi.rooted.2 B hvi.1.1).mono hPhiU
  have hslot := (Compose.Growing.castAt_spec_at hrun hp.noColl hy hc).2.1
  have hts : sp.ts e.msg.slot ≤ tr.time k :=
    (AC.ts_le_iff_le_slot sp (hrun.time_nonneg k) _).mpr (by rw [hslot])
  have hcut := hp.cutZ_le_ts_of_highOrigin_at ho
  have hck : cutZ sp.toParams g ≤ tr.time k :=
    hcut.trans (((AC.ts_le_iff sp).mpr (show (j : Int) ≤ e.msg.slot by omega)).trans hts)
  -- the slot committees from the origin's label on are bounded at the cast
  have hgsl : ∀ {u : Nat}, j ≤ u → AC.gbar g ≤ sp.ts u := fun hu =>
    Healing.gbar_le_of_cutZ_le sp (hcut.trans ((AC.ts_le_iff sp).mpr (by exact_mod_cast hu)))
  have hsb : ∀ {u : Nat}, u ≤ e.msg.slot → sp.ts u ≤ b := fun hu =>
    (((AC.ts_le_iff sp).mpr (by exact_mod_cast hu)).trans hts).trans hkb
  have hPK := hp.committeeFacts.hP
  have hTK := hp.committeeFacts.committeeTAt hrun hp.noColl
  have he : AC.EarlierVotesExtendAt tr.projAC H (tr.HonestBlocksAt H) k e.msg.slot B := by
    intro z q hq hz e' hv hs
    exact hprior z q e' hq (Compose.Growing.hVoteAt_iff.2 ⟨hz, hv⟩) (by omega)
  by_cases hs : e.msg.slot = j + 1
  · obtain ⟨CV, ellx, D, hcx, hfl, hBD⟩ := ho.2.2.1
    have htree := (frame_tree_subset_at hrun hp.noColl hx hcx).2
    have hsub : ellx.frame.tree ⊆ tr.HonestBlocksAt H := fun _ h =>
      ⟨x, i, tr.time i, hrun.time_nonneg i, fun _ hq => hrun.time_mono hq.le,
        hx, htree h⟩
    have hBD' : Anc (tr.HonestBlocksAt H) B D := by
      rw [hBD]
      exact (AC.anc_viableAncestor ellx.frame D).mono hsub
    have hgj : g ≤ sp.ts j := by
      linarith [lt_cutZ sp g, AC.le_gbar g, sp.toParams.hΔ]
    exact AC.Growing.first_transfer_stored hac _
      (fun t => AC.CommitteePAt.upTo hrun.time_mono hrun.antitone hPK t)
      (AC.CommitteeTAt.upTo hrun.antitone hTK) hp.committeeFacts.hsize hx hfl hBD' hy hc hs
      (reset_syncACAt hp hgj)
      (first_carry_of_finalized_anc_at hp ho ⟨ellx, D, hcx, hfl, hBD⟩ hy hc hkb hs hF)
      (faultBoundK_late_at hp (hgsl le_rfl) (hsb (by omega)) hck le_rfl hkb)
      (hp.committee_cs2_at (hgsl (by omega)) (hsb (by omega)) (hrun.time_nonneg k) hkb)
      (Or.inl (by simpa only [← hs] using hvi)) (by simpa only [hs] using he)
  · obtain ⟨m, hm⟩ : ∃ m, e.msg.slot = m + 1 := ⟨e.msg.slot - 1, by omega⟩
    have hjm : j < m := by omega
    refine AC.Growing.next_transfer_from hac _ hPK hTK
      hp.committeeFacts.hsize hy hc hm ?_ ?_ ?_
      (faultBoundK_late_at hp (hgsl (by omega)) (hsb (by omega)) hck le_rfl hkb)
      (hp.committee_cs2_at (hgsl (by omega)) (hsb (by omega)) (hrun.time_nonneg k) hkb)
      (Or.inl (by simpa only [← hm] using hvi)) ?_
    · intro z q e' hz hv hs'
      obtain ⟨ell', hc'⟩ := hv
      have hslot' := (Compose.Growing.castAt_spec_at hrun hp.noColl hz hc').2.1
      have hqk : q < k := by
        by_contra hn
        have := AC.slot_mono sp (hrun.time_nonneg k) (hrun.time_mono (by omega : k ≤ q))
        omega
      exact hprior z q e' hqk (Compose.Growing.hVoteAt_iff.2 ⟨hz, ell', hc'⟩) (by omega)
    · apply hp.half_committee_at
        (hcut.trans ((AC.ts_le_iff sp).mpr (show (j : Int) ≤ m by omega)))
        (htb := hkb)
      have hn : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
        simp only [ACParams.ts]; push_cast; ring
      rw [hm, hn] at hts
      change sp.ts m + sp.Δ ≤ tr.time k
      linarith [sp.toParams.hΔ]
    · have hcarry := later_carry_of_finalized_anc_at hp ho hy hc hkb hm hjm hF
        (fun z q e' hq hv hs => hprior z q e' hq hv (by omega))
      have ht : tr.projAC.time = tr.time := by rfl
      rw [ht]
      simpa only [Compose.Growing.hVoteAt_iff, and_assoc] using hcarry
    · simpa only [hm] using he

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
